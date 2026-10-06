#!/usr/bin/env python3
"""Plan or incrementally compile a dependency-ready module slice without Lake.

Default is read-only planning; --build explicitly starts compilation. Supply --lean
and --lean-path after the canonical dependency artifacts are ready. No ambient
LEAN_PATH, source path, reference VC/IL output, dependency fetch or autobuild is used.
Sources are read from source-manifests/production.json, checked against its supplied
output hashes, and parsed with the sibling extractor's header parser. Actual source
imports determine dependency order. A --target builds only its local import closure.

Sources use output_module/path, module/path or target_module/target_path fields.
At least one output hash is mandatory (converted_sha256 is preferred). Every
present alias in HASH_FIELDS must be valid and equal; null/conflicts are rejected.
Revisions passed with --revision NAME=SHA are recorded as supplied, not authenticated.
Fresh outputs go to .lake/build/lib/lean; logs and receipts are retained per run in
.lake/build/module-slice. This driver is not an axiom audit or certification tool.

--jobs defaults to 2 (maximum 16); each compiler uses -j1. Successful local entries
are reused only after checking source/compiler/options, ordered dependency pins,
the complete external artifact inventory, transitive local keys and all outputs.
Old serial receipts lack external fingerprints: importing one requires BOTH
--legacy-receipt and --attest-legacy-dependencies-unchanged. That explicit operator
attestation is retained as provenance, never inferred from timestamps or Git pins.

--repair-overlay directly consumes source-manifests/repairs.json, schema_version=1,
policy=visibility-private-removal-v1, baseline_manifest_sha256 binding, and ordered
id/path/old/new/preimage_sha256/postimage_sha256 records (unique literals, count=1).
The sibling verify_source_repairs.verify_overlay enforces its policy and hashes.
Repaired effective rows have only converted_sha256=final, separate
mechanical_baseline_sha256, and repair_provenance (base/ledger/patch hashes and
ordered records). The mechanical baseline is reconstructed by reversing literals
and checked against the frozen manifest; the standalone verifier additionally
reconstructs pinned Git blobs. Neither sources nor production.json are edited.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import heapq
import fcntl
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid


MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
REVISION = re.compile(r"[0-9a-f]{40}\Z")
LOCAL_ROOTS = {"VaughtConjecture", "InfinitaryLogic", "PalomarProof", "Palomar", "Tests"}
ARTIFACT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
HASH_FIELDS = ("output_sha256", "transformed_sha256", "converted_sha256", "target_sha256", "sha256")
STRICT_OPTIONS = ("-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                  "-Dbackward.privateInPublic=false", "-DwarningAsError=true",
                  "-Dlinter.deprecated=false", "-Dlinter.all=false")
IL_OPTIONS = ("-DautoImplicit=true", "-DrelaxedAutoImplicit=true",
              "-Dbackward.privateInPublic=false", "-DwarningAsError=true",
              "-Dlinter.deprecated=false", "-Dlinter.all=false")
CACHE_SCHEMA = 1


class BuildError(ValueError):
    pass


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def json_digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def contained(root: Path, relative: str) -> Path:
    part = PurePosixPath(relative)
    if not relative or part.is_absolute() or any(p in {".", ".."} for p in part.parts):
        raise BuildError(f"unsafe relative path: {relative!r}")
    path = root.joinpath(*part.parts)
    current = root
    for component in part.parts:
        current = current / component
        if current.is_symlink():
            raise BuildError(f"symlink is not permitted: {current}")
    if not path.resolve().is_relative_to(root):
        raise BuildError(f"path escapes repository: {path}")
    return path


def load_parser(root: Path):
    path = root / "scripts/extract_proof_sources.py"
    spec = importlib.util.spec_from_file_location("module_slice_header_parser", path)
    if spec is None or spec.loader is None:
        raise BuildError(f"cannot load header parser: {path}")
    helper = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = helper
    spec.loader.exec_module(helper)
    return helper.parse_header


@dataclass(frozen=True)
class Source:
    module: str
    path: Path
    relative: str
    sha256: str
    imports: tuple[str, ...]
    supplied: dict


def effective_options(source: Source) -> tuple[str, ...]:
    return IL_OPTIONS if source.module.startswith("InfinitaryLogic.") else STRICT_OPTIONS


def effective_source_hash(row: dict, name: str) -> str:
    values = [row[key] for key in HASH_FIELDS if key in row]
    if not values or any(not isinstance(value, str) or not SHA256.fullmatch(value) for value in values):
        raise BuildError(f"{name}: a valid non-null effective output SHA256 is required for every present hash alias")
    if len(set(values)) != 1:
        raise BuildError(f"{name}: conflicting output SHA256 aliases")
    return values[0]


def read_sources(root: Path, manifest: dict, parse_header) -> dict[str, Source]:
    rows = manifest.get("sources", manifest.get("modules"))
    if not isinstance(rows, list) or not rows:
        raise BuildError("production manifest needs a nonempty sources/modules array")
    sources = {}
    for row in rows:
        if not isinstance(row, dict):
            raise BuildError("source records must be objects")
        name = row.get("target_module", row.get("output_module", row.get("module")))
        relative = row.get("target_path", row.get("path"))
        if not isinstance(name, str) or not MODULE.fullmatch(name):
            raise BuildError(f"unsupported module name: {name!r}")
        if name in sources:
            raise BuildError(f"duplicate module: {name}")
        expected_path = name.replace(".", "/") + ".lean"
        if relative != expected_path:
            raise BuildError(f"{name}: expected source path {expected_path}, got {relative!r}")
        path = contained(root, relative)
        if not path.is_file():
            raise BuildError(f"missing production source: {path}")
        data = path.read_bytes()
        observed = hashlib.sha256(data).hexdigest()
        supplied_hash = effective_source_hash(row, name)
        if observed != supplied_hash:
            raise BuildError(f"{name}: source hash mismatch ({observed} != {supplied_hash})")
        header = parse_header(data.decode("utf-8"))
        if not header.module:
            raise BuildError(f"{name}: legacy source lacks module header")
        imports = tuple(item.module for item in header.imports)
        if any(n.startswith("Mathlib.ModelTheory.Infinitary") for n in imports):
            raise BuildError(f"{name}: original fork-only infinitary import remains")
        sources[name] = Source(name, path, relative, observed, imports, row)
    for source in sources.values():
        for name in source.imports:
            if name.split(".")[0] in LOCAL_ROOTS and name not in sources:
                raise BuildError(f"{source.module}: local import absent from manifest: {name}")
    return sources


def apply_repair_overlay(root: Path, production_bytes: bytes, repairs_bytes: bytes) -> tuple[dict, dict]:
    effective, overlay = json.loads(production_bytes), json.loads(repairs_bytes)
    if not isinstance(overlay, dict) or not isinstance(overlay.get("repairs"), list):
        raise BuildError("repair overlay requires an ordered repairs array")
    grouped = {}
    for record in overlay["repairs"]:
        if (not isinstance(record, dict) or not isinstance(record.get("path"), str)
                or not isinstance(record.get("old"), str) or not record["old"]
                or not isinstance(record.get("new"), str) or not record["new"]):
            raise BuildError("invalid ordered repair record")
        grouped.setdefault(record["path"], []).append(record)
    for row in effective["sources"]:
        effective_source_hash(row, row.get("output_module", row.get("module", "?")))
    for relative, expected in effective.get("tool_hashes", {}).items():
        if digest(contained(root, relative)) != expected:
            raise BuildError(f"frozen source producer changed: {relative}")
    scripts = root / "scripts"
    saved_path = list(sys.path)
    sys.path.insert(0, str(scripts))
    try:
        for name in ("extract_proof_sources", "prepare_proof_slice"):
            loaded = sys.modules.get(name)
            if loaded is not None and Path(loaded.__file__).resolve() != (scripts / (name + ".py")).resolve():
                raise BuildError(f"foreign repair verifier import: {name}")
        spec = importlib.util.spec_from_file_location("module_slice_repair_verifier", scripts / "verify_source_repairs.py")
        if spec is None or spec.loader is None:
            raise BuildError("cannot load sibling repair verifier")
        verifier = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = verifier
        spec.loader.exec_module(verifier)
    finally:
        sys.path[:] = saved_path
    def current(relative):
        return contained(root, relative).read_bytes()
    def baseline(row):
        contents = current(row["path"])
        for record in reversed(grouped.get(row["path"], [])):
            old, new = record["old"], record["new"]
            text = contents.decode("utf-8")
            matches = []
            for match in re.finditer(re.escape(new), text):
                start, end = match.span()
                if (not new.endswith("\n") and end < len(text)
                        and (text[end].isalnum() or text[end] in "_'!?.")):
                    continue
                if text[text.rfind("\n", 0, start) + 1:start].strip():
                    continue
                if verifier.code_position(text, start):
                    matches.append((start, end))
            if len(matches) != 1:
                raise BuildError(f"reverse repair literal must occur once: {record.get('id')}")
            start, end = matches[0]
            contents = (text[:start] + old + text[end:]).encode("utf-8")
        return contents
    summary = verifier.verify_overlay(production_bytes, repairs_bytes, baseline, current)
    for row in effective["sources"]:
        records = grouped.get(row["path"])
        if not records:
            continue
        before = effective_source_hash(row, row.get("output_module", row.get("module", "?")))
        for alias in HASH_FIELDS:
            row.pop(alias, None)
        row["converted_sha256"] = records[-1]["postimage_sha256"]
        row["mechanical_baseline_sha256"] = before
        row["repair_provenance"] = {"baseline_manifest_sha256": summary["baseline_manifest_sha256"],
                                    "repair_manifest_sha256": summary["repair_manifest_sha256"],
                                    "patch_sha256": json_digest(records), "records": records}
    return effective, summary


def build_order(sources: dict[str, Source], targets: list[str]) -> list[str]:
    selected = set()
    pending = list(targets or sources)
    while pending:
        name = pending.pop()
        if name not in sources:
            raise BuildError(f"target is absent from manifest: {name}")
        if name in selected:
            continue
        selected.add(name)
        pending.extend(n for n in sources[name].imports if n in sources)
    dependencies = {name: set(sources[name].imports).intersection(selected) for name in selected}
    consumers = {name: [] for name in selected}
    for name, deps in dependencies.items():
        for dep in deps:
            consumers[dep].append(name)
    ready = [name for name, deps in dependencies.items() if not deps]
    heapq.heapify(ready)
    result = []
    while ready:
        name = heapq.heappop(ready)
        result.append(name)
        for consumer in consumers[name]:
            dependencies[consumer].remove(name)
            if not dependencies[consumer]:
                heapq.heappush(ready, consumer)
    if len(result) != len(selected):
        cycle = sorted(name for name, deps in dependencies.items() if deps)
        raise BuildError(f"local import cycle: {', '.join(cycle[:20])}")
    return result


def dependency_paths(value: str, output: Path) -> list[Path]:
    parts = value.split(os.pathsep)
    if not value or any(not p for p in parts):
        raise BuildError("--lean-path must contain explicit nonempty absolute artifact directories")
    paths = []
    for part in parts:
        given = Path(part)
        if not given.is_absolute():
            raise BuildError(f"relative dependency path is not allowed: {given}")
        path = given.resolve()
        if not path.is_dir():
            raise BuildError(f"dependency artifact directory does not exist: {path}")
        if path == output or path.is_relative_to(output):
            raise BuildError("supply only dependency paths; project outputs are prepended by the driver")
        if any(p in {"InfinitaryLogic", "computable-model-theory"} for p in path.parts):
            raise BuildError(f"project/reference proof artifacts are forbidden: {path}")
        for prefix in LOCAL_ROOTS:
            if (path / prefix).exists() or (path / (prefix + ".olean")).exists():
                raise BuildError(f"dependency path contains local proof artifacts ({prefix}): {path}")
        if path not in paths:
            paths.append(path)
    return paths


def validate_output_roots(output: Path):
    if output.is_symlink():
        raise BuildError(f"symlink project output: {output}")
    if output.exists():
        for entry in output.iterdir():
            if entry.is_symlink() or entry.name.split(".", 1)[0] not in LOCAL_ROOTS:
                raise BuildError(f"foreign or symlink root in prepended project output: {entry}")


def external_root_owners(paths: list[Path]) -> dict[str, Path]:
    """Lean selects the first root DIRECTORY or root.olean, not first full file.

    Require disjoint official root ownership even for unused/transitive roots.
    Empty earlier root directories are shadows too; do not silently fall through.
    """
    owners = {}
    for base in dict.fromkeys(paths):
        for entry in base.iterdir():
            name = entry.name if entry.is_dir() else entry.name.removesuffix(".olean") if entry.suffix == ".olean" else ""
            if not name or "." in name or not MODULE.fullmatch(name):
                continue
            if entry.is_symlink() or name in LOCAL_ROOTS:
                raise BuildError(f"noncanonical/symlink root in external artifacts: {entry}")
            if name in owners and owners[name] != base:
                raise BuildError(f"ambiguous ordered external root {name}: {owners[name]} shadows {base}")
            owners[name] = base
    return owners


def validate_external_imports(sources: dict[str, Source], order: list[str], paths: list[Path],
                              core: Path, output: Path):
    validate_output_roots(output)
    search = list(dict.fromkeys(paths + [core]))
    owners = external_root_owners(search)
    external = sorted({dep for name in order for dep in sources[name].imports if dep not in sources})
    for name in external:
        if not MODULE.fullmatch(name):
            raise BuildError(f"unsupported external import name: {name}")
        relative = Path(name.replace(".", "/") + ".olean")
        matches = [path / relative for path in search if (path / relative).is_file()]
        if not matches:
            raise BuildError(f"missing explicit dependency artifact: {name}")
        if len(matches) != 1:
            raise BuildError(f"ambiguous external artifact {name}: {matches}")
        owner = owners.get(name.split(".")[0])
        if owner is None or owner / relative != matches[0]:
            raise BuildError(f"actual ordered Lean root does not resolve validated artifact: {name}")
    return external


def require_space(root: Path, floor: int):
    free = shutil.disk_usage(root).free
    if free < floor:
        raise BuildError(f"disk floor reached: {free} free bytes < {floor} bytes")
    return free


def stop_process(process: subprocess.Popen):
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            process.wait()
            return
        try:
            process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()


def artifact_records(root: Path, base: Path, name: str) -> list[dict]:
    result = []
    for suffix in ARTIFACT_SUFFIXES:
        path = contained(root, str((base / (name.replace(".", "/") + suffix)).relative_to(root)))
        if not path.is_file():
            raise BuildError(f"missing compiler artifact: {path}")
        result.append({"path": str(path.relative_to(root)), "bytes": path.stat().st_size,
                       "sha256": digest(path)})
    return result


def valid_artifacts(root: Path, output: Path, name: str, records) -> bool:
    try:
        return artifact_records(root, output, name) == records
    except (OSError, ValueError):
        return False


def inventory(paths: list[Path], floor_root: Path, floor: int, hash_files: bool) -> list[dict]:
    """Fingerprint all external/core files, not just directly imported .oleans.

    This intentionally includes transitive imports, IR and native libraries. No
    stat-only cache is used across runs. Stat inventories guard in-flight changes;
    a second full hash pass checks bytes before the run can be marked passed.
    """
    result = []
    for base in paths:
        rows = []
        for parent, dirs, files in os.walk(base, followlinks=False):
            dirs.sort()
            relative_parent = os.path.relpath(parent, base)
            for name in dirs + sorted(files):
                path = Path(parent) / name
                if path.is_symlink():
                    raise BuildError(f"symlink in dependency artifacts: {path}")
            for name in sorted(files):
                require_space(floor_root, floor)
                path = Path(parent) / name
                before = path.stat()
                relative = name if relative_parent == "." else relative_parent + "/" + name
                row = {"path": relative, "bytes": before.st_size,
                       "mtime_ns": before.st_mtime_ns, "ctime_ns": before.st_ctime_ns}
                if hash_files:
                    row["sha256"] = digest(path)
                after = path.stat()
                stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
                if any(getattr(after, field) != getattr(before, field) for field in stable_fields):
                    raise BuildError(f"dependency artifact changed while inspecting: {path}")
                rows.append(row)
        result.append({"path": str(base), "files": rows})
    return result


def inventory_stats(snapshot: list[dict]) -> list[dict]:
    return [{"path": tree["path"], "files": [{k: v for k, v in row.items() if k != "sha256"}
                                             for row in tree["files"]]} for tree in snapshot]


def ordered_pins(root: Path, paths: list[Path]) -> list[dict]:
    manifest = root / "lake-manifest.json"
    if not manifest.is_file():
        raise BuildError("cache provenance requires root lake-manifest.json")
    config = json.loads(manifest.read_text())
    packages = {row["name"]: row for row in config["packages"]}
    pins = []
    for path in paths:
        if path.parts[-4:] != (".lake", "build", "lib", "lean"):
            raise BuildError(f"dependency provenance needs package .lake/build/lib/lean: {path}")
        repo = path.parents[3]
        row = packages.get(repo.name)
        if not row or row.get("type") != "git":
            raise BuildError(f"dependency is not a pinned Git package: {repo}")
        def git(*args):
            return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()
        revision, url = git("rev-parse", "HEAD"), git("remote", "get-url", "origin")
        if revision != row.get("rev") or url != row.get("url"):
            raise BuildError(f"dependency checkout differs from canonical manifest: {repo}")
        pins.append({"path": str(path), "name": repo.name, "revision": revision, "url": url})
    return pins


def module_key(source: Source, context_key: str, completed: dict) -> str:
    return json_digest({"schema": CACHE_SCHEMA, "context_key": context_key,
                        "module": source.module, "path": source.relative,
                        "source_sha256": source.sha256, "imports": source.imports,
                        "dependencies": [{"module": name, "key": completed[name]["cache_key"],
                                          "artifacts": completed[name]["artifacts"]}
                                         for name in dict.fromkeys(source.imports) if name in completed]})


def read_cache(path: Path, root: Path, output: Path, name: str, key: str) -> dict | None:
    if path.is_symlink():
        raise BuildError(f"symlink cache entry: {path}")
    try:
        value = json.loads(path.read_text())
        if (value.get("schema") == CACHE_SCHEMA and value.get("module") == name
                and value.get("cache_key") == key and value.get("exit_code") == 0
                and value.get("status") in {"fresh", "reused", "legacy-attested"}
                and valid_artifacts(root, output, name, value.get("artifacts"))):
            return value
    except (OSError, ValueError, AttributeError):
        pass
    return None


def legacy_candidates(path: Path | None, context: dict, sources: dict[str, Source],
                      root: Path, output: Path) -> tuple[dict, dict | None]:
    if path is None:
        return {}, None
    data = path.read_bytes()
    old = json.loads(data)
    # These are necessary checks, NOT evidence of past external artifact bytes.
    for field in ("compiler", "compiler_sha256", "compiler_version", "strict_options",
                  "dependency_paths", "revisions_as_supplied", "output", "header_parser_sha256"):
        if old.get(field) != context.get(field):
            raise BuildError(f"legacy receipt provenance mismatch: {field}")
    if old.get("kind") != "serial-module-slice-build":
        raise BuildError("--legacy-receipt must be an original serial driver receipt")
    old_sources = {row["module"]: row["sha256"] for row in old["sources"]}
    candidates = {}
    for row in old["results"]:
        name = row["module"]
        if (row.get("exit_code") == 0 and name in sources
                and old_sources.get(name) == sources[name].sha256
                and valid_artifacts(root, output, name, row.get("artifacts"))):
            command = [context["compiler"], "-j1", "-R", str(root), *effective_options(sources[name]),
                       "-o", str(output / (name.replace(".", "/") + ".olean")), sources[name].relative]
            if row.get("command") == command:
                candidates[name] = row
    provenance = {"kind": "operator-attested-legacy-dependency-continuity",
                  "receipt": str(path.resolve()), "receipt_sha256": hashlib.sha256(data).hexdigest(),
                  "limitation": "Original receipt did not hash external dependencies; operator attests "
                                "their pins, bytes and compiler runtime were unchanged since that run."}
    return candidates, provenance


def run_schedule(root: Path, output: Path, run: Path, sources: dict[str, Source],
                 order: list[str], jobs: int, lean: Path, environment: dict, floor: int,
                 receipt: dict, receipt_path: Path, context_key: str,
                 legacy: dict, legacy_provenance: dict | None, guard,
                 keep_going: bool = False) -> int:
    cache_dir = contained(root, ".lake/build/module-slice/cache-v1")
    cache_dir.mkdir(exist_ok=True)
    selected = set(order)
    dependencies = {name: set(sources[name].imports) & selected for name in order}
    consumers = {name: [] for name in order}
    for name, deps in dependencies.items():
        for dep in deps:
            consumers[dep].append(name)
    ready = [name for name in order if not dependencies[name]]
    heapq.heapify(ready)
    completed, active, failed = {}, {}, set()
    def finish(name, result):
        completed[name] = result
        receipt["results"].append(result)
        write_receipt(cache_dir / (name + ".json"), {**result, "schema": CACHE_SCHEMA})
        write_receipt(receipt_path, receipt)
        for consumer in consumers[name]:
            dependencies[consumer].remove(name)
            if not dependencies[consumer]:
                heapq.heappush(ready, consumer)
    try:
        while ready or active:
            require_space(root, floor)
            guard(False)
            while ready and len(active) < jobs:
                require_space(root, floor)
                validate_output_roots(output)
                # Observe exits before dispatching another job, including very
                # fast failures during initial queue filling or cache reuse.
                if any(task[0].poll() is not None for task in active.values()):
                    break
                name = heapq.heappop(ready)
                source = sources[name]
                if digest(source.path) != source.sha256:
                    raise BuildError(f"source changed after planning: {name}")
                # Every direct local output must still match its completed hash.
                for dep in set(source.imports) & selected:
                    if not valid_artifacts(root, output, dep, completed[dep]["artifacts"]):
                        raise BuildError(f"local dependency changed during run: {dep}")
                key = module_key(source, context_key, completed)
                cached = read_cache(cache_dir / (name + ".json"), root, output, name, key)
                if cached:
                    result = {**cached, "status": "reused", "reused_from": cached.get("receipt"),
                              "receipt": str(receipt_path), "seconds": 0.0}
                    print(f"[reuse {len(completed)+1}/{len(order)}] {name}", flush=True)
                    finish(name, result)
                    continue
                # A legacy result is reusable only when all local parents also
                # came from this same legacy run, never from fresh replacement.
                old = legacy.get(name)
                if (old and valid_artifacts(root, output, name, old.get("artifacts"))
                        and all(completed[dep].get("legacy_provenance") == legacy_provenance
                                for dep in set(source.imports) & selected)):
                    result = {**old, "status": "legacy-attested", "cache_key": key,
                              "legacy_provenance": legacy_provenance, "receipt": str(receipt_path)}
                    print(f"[legacy-attested {len(completed)+1}/{len(order)}] {name}", flush=True)
                    finish(name, result)
                    continue
                stage = contained(root, str((run / "staging" / name).relative_to(root)))
                stage.mkdir(parents=True, exist_ok=False)
                artifact = stage / (name.replace(".", "/") + ".olean")
                artifact.parent.mkdir(parents=True, exist_ok=True)
                log = run / "logs" / (name + ".log")
                options = effective_options(source)
                command = [str(lean), "-j1", "-R", str(root), *options,
                           "-o", str(artifact), source.relative]
                print(f"[start; completed {len(completed)}/{len(order)}] {name}", flush=True)
                handle = log.open("xb")
                try:
                    process = subprocess.Popen(command, cwd=root, env=environment, stdout=handle,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                finally:
                    handle.close()
                active[name] = (process, stage, log, command, key, time.monotonic())
            finished = sorted(name for name, task in active.items() if task[0].poll() is not None)
            # Process failures before successes and before scheduling more jobs.
            finished.sort(key=lambda name: active[name][0].returncode == 0)
            if keep_going and any(active[name][0].returncode == 0 for name in finished):
                # Cache successes only after a fresh batch provenance check,
                # even when a later independent failure prevents a passed run.
                guard(True)
            for name in finished:
                process, stage, log, command, key, started = active.pop(name)
                result = {"module": name, "command": command, "exit_code": process.returncode,
                          "status": "fresh" if process.returncode == 0 else "failed",
                          "cache_key": key, "receipt": str(receipt_path),
                          "seconds": round(time.monotonic() - started, 3),
                          "log": str(log.relative_to(root)), "log_sha256": digest(log)}
                if process.returncode != 0:
                    receipt["results"].append(result)
                    failed.add(name)
                    receipt["failed_modules"] = sorted(failed)
                    receipt.setdefault("failed_module", name)
                    label = "Failed" if keep_going else "Stopped"
                    print(f"{label} at {name}; compiler exited {process.returncode}. Log: {log}", file=sys.stderr)
                    if not keep_going:
                        receipt["status"] = "compile-failed"
                        write_receipt(receipt_path, receipt)
                        return 1
                    write_receipt(receipt_path, receipt)
                    continue  # Never finish(), cache, or unblock this failure.
                # Batch completions share the periodic external-inventory check;
                # source/output hashes remain per-module, with a full final replay.
                guard(False)
                if digest(sources[name].path) != sources[name].sha256:
                    raise BuildError(f"source changed during compilation: {name}")
                staged = artifact_records(root, stage, name)
                for record in staged:
                    src = root / record["path"]
                    dst = contained(root, str((output / src.relative_to(stage)).relative_to(root)))
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    os.replace(src, dst)
                result["artifacts"] = artifact_records(root, output, name)
                finish(name, result)
            if active:
                time.sleep(0.2)
        blocked, pending = set(), list(failed)
        while pending:
            for name in consumers[pending.pop()]:
                if name not in failed and name not in blocked:
                    blocked.add(name)
                    pending.append(name)
        if selected - completed.keys() - failed != blocked:
            raise BuildError("scheduler stalled before completing dependency closure")
        receipt["failed_modules"] = sorted(failed)
        receipt["blocked_modules"] = sorted(blocked)
        for name in sorted(blocked):
            receipt["results"].append({"module": name, "status": "blocked",
                                       "blocked_by": sorted(dependencies[name])})
        for name, result in completed.items():
            if not valid_artifacts(root, output, name, result["artifacts"]):
                raise BuildError(f"local artifact changed during run: {name}")
        return 0
    finally:
        for name, (process, stage, log, command, key, started) in active.items():
            stop_process(process)
            receipt["results"].append({"module": name, "status": "cancelled",
                                       "exit_code": process.returncode, "log": str(log.relative_to(root)),
                                       "log_sha256": digest(log), "command": command})
        write_receipt(receipt_path, receipt)


def supplied_revisions(values: list[str]) -> dict[str, str]:
    result = {}
    for item in values:
        name, separator, revision = item.partition("=")
        if not separator or not name or not REVISION.fullmatch(revision) or name in result:
            raise BuildError(f"expected unique NAME=full-lowercase-SHA revision: {item!r}")
        result[name] = revision
    return result


def write_receipt(path: Path, receipt: dict):
    # Replace only this run's receipt, never another run or any source file.
    temporary = path.with_suffix(".json.new")
    temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--manifest", type=Path, default=Path("source-manifests/production.json"))
    parser.add_argument("--repair-overlay", type=Path, help="reviewed literal repairs with before/after source hashes")
    parser.add_argument("--lean", type=Path, required=True, help="explicit installed compiler; no elan/Lake lookup")
    parser.add_argument("--lean-path", required=True, help="colon-separated official dependency artifact directories only")
    parser.add_argument("--target", action="append", default=[], help="local target; repeatable, default entire manifest")
    parser.add_argument("--revision", action="append", default=[], help="record supplied NAME=40-character-SHA")
    parser.add_argument("--disk-floor-gib", type=float, default=2.0, help="minimum free space; cannot be below 2 GiB")
    parser.add_argument("--jobs", type=int, choices=range(1, 17), default=2,
                        help="maximum dependency-ready Lean processes (default 2, maximum 16)")
    parser.add_argument("--legacy-receipt", type=Path, help="optional original serial receipt to bootstrap")
    parser.add_argument("--attest-legacy-dependencies-unchanged", action="store_true",
                        help="explicitly attest legacy run's external pins/artifact bytes/runtime stayed unchanged")
    parser.add_argument("--keep-going", action="store_true",
                        help="continue independent modules after compiler errors; never ignore provenance/disk errors")
    parser.add_argument("--build", action="store_true", help="execute the plan; otherwise no outputs are written")
    args = parser.parse_args(argv)
    receipt = None
    receipt_path = None
    lock = None
    try:
        root = args.root.resolve(strict=True)
        if not root.is_dir():
            raise BuildError("repository root must be a directory")
        if bool(args.legacy_receipt) != args.attest_legacy_dependencies_unchanged:
            raise BuildError("legacy reuse requires BOTH --legacy-receipt and explicit "
                             "--attest-legacy-dependencies-unchanged")
        if not args.disk_floor_gib >= 2.0 or args.disk_floor_gib == float("inf"):
            raise BuildError("disk floor must be finite and at least 2 GiB")
        floor = int(args.disk_floor_gib * 1024 ** 3)
        require_space(root, floor)
        output = contained(root, ".lake/build/lib/lean")
        run_parent = contained(root, ".lake/build/module-slice")
        manifest_path = args.manifest if args.manifest.is_absolute() else root / args.manifest
        manifest_bytes = manifest_path.read_bytes()
        manifest = json.loads(manifest_bytes)
        if not isinstance(manifest, dict):
            raise BuildError("production manifest must be an object")
        overlay_path, overlay_bytes, repair_summary = None, None, None
        if args.repair_overlay:
            overlay_path = args.repair_overlay if args.repair_overlay.is_absolute() else root / args.repair_overlay
            overlay_bytes = overlay_path.read_bytes()
            manifest, repair_summary = apply_repair_overlay(root, manifest_bytes, overlay_bytes)
        parse_header = load_parser(root)
        sources = read_sources(root, manifest, parse_header)
        order = build_order(sources, args.target)
        paths = dependency_paths(args.lean_path, output)
        lean = args.lean.resolve(strict=True)
        if not args.lean.is_absolute() or not lean.is_file() or not os.access(lean, os.X_OK):
            raise BuildError("--lean must be an absolute executable file path")
        core = lean.parent.parent / "lib/lean"
        if not core.is_dir():
            raise BuildError(f"compiler core artifact path not found: {core}")
        external = validate_external_imports(sources, order, paths, core, output)
        revisions = supplied_revisions(args.revision)
        plan = {"kind": "dependency-ready-module-slice-plan", "manifest": str(manifest_path),
                "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
                "modules": order, "external_imports": external,
                "dependency_paths": [str(path) for path in paths],
                "output": str(output), "disk_floor_bytes": floor,
                "revisions_as_supplied": revisions, "jobs": args.jobs, "keep_going": args.keep_going,
                "repair_overlay": {"path": str(overlay_path), "sha256": hashlib.sha256(overlay_bytes).hexdigest()}
                                  if overlay_bytes is not None else None,
                "repair_verification": repair_summary,
                "legacy_receipt": str(args.legacy_receipt) if args.legacy_receipt else None}
        if not args.build:
            print(json.dumps(plan, indent=2))
            print("Plan only; pass --build when the official dependency paths are ready.", file=sys.stderr)
            return 0
        environment = os.environ.copy()
        environment.pop("LEAN_SRC_PATH", None)
        if environment.get("LD_PRELOAD") or environment.get("LD_LIBRARY_PATH"):
            raise BuildError("unset LD_PRELOAD/LD_LIBRARY_PATH for compiler runtime provenance")
        environment["LEAN_PATH"] = os.pathsep.join(str(p) for p in [output] + paths + [core])
        run_parent.mkdir(parents=True, exist_ok=True)
        lock_path = contained(root, ".lake/build/module-slice/build.lock")
        lock = lock_path.open("a")
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise BuildError("another module-slice builder holds the output lock")
        pins = ordered_pins(root, paths)
        configuration = {name: digest(root / name) for name in
                         ("lake-manifest.json", "lakefile.lean", "lakefile.toml", "lean-toolchain")
                         if (root / name).is_file()}
        compiler_version = subprocess.check_output([str(lean), "--version"], env=environment, text=True).strip()
        print("Fingerprinting complete official dependency and compiler artifact inventories...", flush=True)
        snapshot = inventory(paths + [core], root, floor, True)
        context = {"schema": CACHE_SCHEMA, "compiler": str(lean), "compiler_sha256": digest(lean),
                   "compiler_version": compiler_version, "strict_options": list(STRICT_OPTIONS),
                   "upstream_IL_options": list(IL_OPTIONS),
                   "compiler_threads": 1, "root": str(root), "output": str(output),
                   "dependency_paths": [str(path) for path in paths], "ordered_pins": pins,
                   "external_root_owners": {name: str(path) for name, path in external_root_owners(paths + [core]).items()},
                   "external_artifacts": [{"path": tree["path"],
                                           "files": [{k: v for k, v in row.items()
                                                      if k not in {"mtime_ns", "ctime_ns"}}
                                                     for row in tree["files"]]} for tree in snapshot],
                   "revisions_as_supplied": revisions, "configuration_sha256": configuration,
                   "lean_environment": {k: v for k, v in environment.items() if k.startswith("LEAN_")},
                   "driver_sha256": digest(Path(__file__)),
                   "header_parser_sha256": digest(root / "scripts/extract_proof_sources.py")}
        if overlay_bytes is not None:
            context["repair_verifier_sha256"] = digest(root / "scripts/verify_source_repairs.py")
            context["repair_producer_sha256"] = digest(root / "scripts/prepare_proof_slice.py")
        context_key = json_digest(context)
        legacy, legacy_provenance = legacy_candidates(args.legacy_receipt, context, sources, root, output)
        stats = inventory_stats(snapshot)
        last_check = 0.0
        def guard(force=False):
            nonlocal last_check
            validate_output_roots(output)
            if not force and time.monotonic() - last_check < 5:
                return
            if inventory(paths + [core], root, floor, False) != stats:
                raise BuildError("external dependency/core artifacts changed during build")
            validate_external_imports(sources, order, paths, core, output)
            if ordered_pins(root, paths) != pins:
                raise BuildError("dependency Git pins changed during build")
            if any(digest(root / name) != sha for name, sha in configuration.items()):
                raise BuildError("canonical configuration changed during build")
            if digest(lean) != context["compiler_sha256"]:
                raise BuildError("compiler changed during build")
            last_check = time.monotonic()
        run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
        run = run_parent / run_id
        run.mkdir(parents=True, exist_ok=False)
        (run / "logs").mkdir()
        output.mkdir(parents=True, exist_ok=True)
        receipt_path = run / "receipt.json"
        context_path = run / "cache-context.json"
        write_receipt(context_path, context)
        supplied_path = run / "source-manifest.json"
        write_receipt(supplied_path, manifest)
        receipt = {**plan, "kind": "dependency-ready-module-slice-build", "status": "running",
                   "cache_schema": CACHE_SCHEMA, "context_key": context_key,
                   "cache_context": {"path": str(context_path), "sha256": digest(context_path)},
                   "legacy_provenance": legacy_provenance,
                   "compiler": context["compiler"], "compiler_sha256": context["compiler_sha256"],
                   "compiler_version": compiler_version, "strict_options": list(STRICT_OPTIONS),
                   "upstream_IL_options": list(IL_OPTIONS),
                   "driver_sha256": context["driver_sha256"],
                   "header_parser_sha256": context["header_parser_sha256"],
                   "source_records_as_supplied": {"path": str(supplied_path), "sha256": digest(supplied_path)},
                   "sources": [{"module": name, "path": sources[name].relative,
                                "sha256": sources[name].sha256} for name in order],
                   "results": [], "free_bytes_at_start": require_space(root, floor)}
        write_receipt(receipt_path, receipt)
        status = run_schedule(root, output, run, sources, order, args.jobs, lean, environment,
                              floor, receipt, receipt_path, context_key, legacy, legacy_provenance, guard,
                              keep_going=args.keep_going)
        if status:
            return status
        if manifest_path.read_bytes() != manifest_bytes:
            raise BuildError("production manifest changed during build")
        if overlay_path is not None and overlay_path.read_bytes() != overlay_bytes:
            raise BuildError("repair overlay changed during build")
        for name in order:
            if digest(sources[name].path) != sources[name].sha256:
                raise BuildError(f"source changed during build: {name}")
        last_check = 0.0
        guard(True)
        if inventory(paths + [core], root, floor, True) != snapshot:
            raise BuildError("external artifact fingerprint changed during build")
        receipt["status"] = "compile-failed" if receipt.get("failed_modules") else "passed"
        receipt["free_bytes_at_end"] = require_space(root, floor)
        write_receipt(receipt_path, receipt)
        counts = {status: sum(row["status"] == status for row in receipt["results"])
                  for status in ("fresh", "reused", "legacy-attested")}
        if receipt.get("failed_modules"):
            print(f"Independent modules finished; failed={receipt['failed_modules']}, "
                  f"blocked_count={len(receipt['blocked_modules'])}. Receipt: {receipt_path}", file=sys.stderr)
            return 1  # Full final provenance/hash validation above still ran.
        print(f"Passed {len(order)} modules; {counts}. Receipt: {receipt_path}")
        return 0
    except KeyboardInterrupt:
        if receipt is not None:
            receipt["status"] = "interrupted"
            write_receipt(receipt_path, receipt)
        print("Interrupted; completed logs and receipts are retained.", file=sys.stderr)
        return 130
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if receipt is not None:
            receipt["status"] = "stopped"
            receipt["error"] = str(error)
            write_receipt(receipt_path, receipt)
        print(f"error: {error}", file=sys.stderr)
        return 2
    finally:
        if lock is not None:
            lock.close()


if __name__ == "__main__":
    raise SystemExit(main())
