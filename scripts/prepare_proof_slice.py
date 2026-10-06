#!/usr/bin/env python3
"""Prepare the pinned production source-import slice; never build or fetch.

Default: dry-run conflict/equality inventory. --apply creates missing generated
files only after checking every existing output. --check verifies byte-for-byte
idempotence including the production manifest. Reserved pilot sources must exist
and match, and are never written. Partial I/O failure leaves new files in place;
rerunning safely verifies those bytes and completes missing outputs.

Imports are followed across VC, IL, and exactly five fork infinitary cores.
Other Mathlib/Architect/core imports are unexpanded external boundaries. The
canonical external Mathlib pin is recorded, not resolved or certified here.
This is a whole-source import closure, not a minimal proof-term dependency slice.
Python 3.10+, Git 2.45+. No local repository paths enter public metadata.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sys

import extract_proof_sources as extraction


VC_COMMIT = extraction.PINNED_COMMIT
IL_COMMIT = "eb9f12dc983778eec067c0875170798efd34c7f0"
CORE_COMMIT = "346a4bd3f95e8591976c91259badc6d2c300f638"
CANONICAL_MATHLIB_COMMIT = "c55e6e786f49471c72fbddbec5415808896aec1e"
ARCHITECT_COMMIT = "f45833e26c68aa947044145184f8881a75392e30"
CORE_NAMES = ("Syntax", "Semantics", "IndexCoding", "Reindex", "QuantifierRank")
RENAMES = {
    "Mathlib.ModelTheory.Infinitary." + name: "PalomarProof.Infinitary." + name
    for name in CORE_NAMES
}
RESERVED = frozenset({
    "VaughtConjecture/CountableCover.lean",
    "PalomarProof/Infinitary/Syntax.lean",
    "PalomarProof/Infinitary/Semantics.lean",
    "InfinitaryLogic/Lomega1omega/Syntax.lean",
    "InfinitaryLogic/Lomega1omega/Semantics.lean",
})
MANIFEST_PATH = "source-manifests/production.json"
SOURCE_REPOS = {
    "VC": "private-working-development",
    "IL": "https://github.com/cameronfreer/infinitary-logic",
    "InfinitaryCore": "https://github.com/cameronfreer/mathlib4",
}
EXTERNAL_ROOTS = frozenset({"Mathlib", "Architect", "Init", "Lean", "Std", "Lake"})


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def owner_of(module: str) -> str | None:
    if module == "VaughtConjecture" or module.startswith("VaughtConjecture."):
        return "VC"
    if module == "InfinitaryLogic" or module.startswith("InfinitaryLogic."):
        return "IL"
    if module.startswith("Mathlib.ModelTheory.Infinitary."):
        if module not in RENAMES:
            raise extraction.Unsupported(f"unapproved fork infinitary module: {module}")
        return "InfinitaryCore"
    if module.split(".", 1)[0] not in EXTERNAL_ROOTS:
        raise extraction.Unsupported(f"unapproved external import: {module}")
    return None


def rewrite_imports(text: str) -> tuple[str, list[dict]]:
    """Rewrite only the module identifier span in header import directives."""
    header = extraction.parse_header(text)
    original_body = text[header.body_start:]
    edits, replacements = [], []
    for item in header.imports:
        if item.module not in RENAMES:
            continue
        scanner = extraction.Scanner(text)
        scanner.pos = item.keyword_start + len("import")
        if scanner.peek().value == "all":
            scanner.take()
        start = scanner.peek().start
        replacement = RENAMES[item.module]
        edits.append((start, item.end, replacement))
        replacements.append({"from": item.module, "to": replacement})
    for start, end, replacement in reversed(edits):
        text = text[:start] + replacement + text[end:]
    # Guard the comment/doc/declaration/proof suffix against future rewrite bugs.
    if text[extraction.parse_header(text).body_start:] != original_body:
        raise AssertionError("import rewrite changed body suffix")
    return text, replacements


@dataclass
class ProductionPlan:
    manifest: dict
    files: dict[str, bytes]

    def outputs(self) -> dict[str, bytes]:
        return {**self.files, MANIFEST_PATH: extraction.manifest_json(self.manifest).encode("utf-8")}


def build_plan(snapshots: dict, endpoint: str = extraction.ENDPOINT,
               tool_hashes: dict | None = None) -> ProductionPlan:
    files, sources, licenses, repository_rows = {}, [], {}, {}
    for owner in ("VC", "IL", "InfinitaryCore"):
        snapshot = snapshots[owner]
        contents = snapshot.read("LICENSE")
        output = f"source-manifests/licenses/{owner}/LICENSE"
        files[output] = contents
        licenses[owner] = {
            "path": output, "source_path": "LICENSE", "sha256": sha256(contents),
            "source_repo": SOURCE_REPOS[owner], "source_commit": snapshot.commit,
        }
        repository_rows[owner] = {
            "source_repo": SOURCE_REPOS[owner], "source_commit": snapshot.commit,
            "license": licenses[owner],
        }
    pending, seen, external = [endpoint], set(), set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        owner = owner_of(module)
        if owner is None:
            external.add(module)
            continue
        snapshot = snapshots[owner]
        source_path = module.replace(".", "/") + ".lean"
        if source_path not in snapshot.entries:
            raise extraction.Unsupported(f"{owner}: missing tracked source at {snapshot.commit}: {source_path}")
        original = snapshot.read(source_path)
        try:
            original_text = original.decode("utf-8")
            original_header = extraction.parse_header(original_text)
            converted_text = extraction.convert_module(original_text)
            converted, replacements = rewrite_imports(converted_text)
        except (UnicodeError, extraction.Unsupported) as error:
            raise extraction.Unsupported(f"{owner}:{source_path}: {error}") from error
        imports = [item.module for item in original_header.imports]
        if not original_header.prelude:
            imports.append("Init")
        pending.extend(sorted(set(imports), reverse=True))
        output_module = RENAMES.get(module, module)
        output_path = output_module.replace(".", "/") + ".lean"
        data = converted.encode("utf-8")
        if output_path in files:
            raise extraction.Unsupported(f"colliding production output: {output_path}")
        files[output_path] = data
        transforms = []
        if module != output_module:
            transforms.append({"operation": "relocate-module-path", "from": module, "to": output_module})
        transforms.append({"operation": "module-public-expose-header",
                           "changed": converted_text != original_text})
        transforms.append({"operation": "rewrite-header-import-module-paths", "replacements": replacements})
        sources.append({
            "module": module, "output_module": output_module, "source_path": source_path,
            "path": output_path, "owner": owner, "source_repo": SOURCE_REPOS[owner],
            "source_commit": snapshot.commit,
            "original_sha256": sha256(original), "converted_sha256": sha256(data),
            "original_bytes": len(original), "converted_bytes": len(data),
            "license_path": licenses[owner]["path"],
            "upstream_license_sha256": licenses[owner]["sha256"],
            "source_imports": [item.manifest() for item in original_header.imports],
            "implicit_imports": [] if original_header.prelude else ["Init"],
            "transform_sequence": transforms,
        })
    manifest = {
        "schema_version": 1, "kind": "production-source-import-closure",
        "proof_term_closure": "not-computed", "endpoint": endpoint,
        "sources": sorted(sources, key=lambda row: row["path"]),
        "source_counts": dict(sorted(Counter(row["owner"] for row in sources).items())),
        "repositories": repository_rows,
        "tool_hashes": dict(sorted((tool_hashes or {}).items())),
        "external_imports_unexpanded": sorted(external),
        "external_configuration": {
            "Mathlib": {"repo": "https://github.com/leanprover-community/mathlib4",
                        "commit": CANONICAL_MATHLIB_COMMIT},
            "Architect": {"repo": "https://github.com/hanwenzhu/LeanArchitect",
                          "commit": ARCHITECT_COMMIT},
            "Lean": {"toolchain": "leanprover/lean4:v4.35.0-rc3"},
            "verified_by_this_tool": False,
        },
        "limitations": [
            "Whole source-file import closure, not a minimal declaration or proof-term closure.",
            "Mechanical header visibility conversion and five header-only import path rewrites; no statement/proof edits.",
            "No dependency resolution, checkout, build, elaboration, axiom audit, or Palomar eligibility verification.",
            "Canonical external Mathlib is required; its configured pin is recorded, not checked here.",
            "Fork-derived infinitary cores retain original declarations and upstream attribution at new module paths.",
        ],
    }
    return ProductionPlan(manifest, files)


def preflight(plan: ProductionPlan, destination: Path, check: bool = False) -> tuple[list[str], list[str]]:
    """Validate ALL outputs before any creation; conflicts never become overwrites."""
    destination = destination.absolute()
    if destination.is_symlink() or not destination.is_dir():
        raise extraction.Unsupported(f"destination must be an existing nonsymlink directory: {destination}")
    missing, equal, conflicts = [], [], []
    for relative, contents in sorted(plan.outputs().items()):
        path = extraction.safe_relative(relative)
        target = destination.joinpath(*path.parts)
        parent = target.parent
        unsafe_parent = False
        while parent != destination:
            if parent.is_symlink() or (parent.exists() and not parent.is_dir()):
                unsafe_parent = True
                break
            parent = parent.parent
        if unsafe_parent or target.is_symlink():
            conflicts.append(f"{relative}: symlink or non-directory ancestor")
        elif target.exists():
            if not target.is_file():
                conflicts.append(f"{relative}: not a regular file")
            elif target.read_bytes() != contents:
                conflicts.append(f"{relative}: existing bytes differ (expected SHA256 {sha256(contents)})")
            else:
                equal.append(relative)
        elif relative in RESERVED:
            conflicts.append(f"{relative}: reserved pilot is missing; parent/Russell must prepare it")
        elif check:
            conflicts.append(f"{relative}: missing")
        else:
            missing.append(relative)
    if conflicts:
        raise extraction.Unsupported("production equality/conflict check failed:\n" + "\n".join(conflicts))
    return missing, equal


def prepare(plan: ProductionPlan, destination: Path) -> tuple[int, int]:
    missing, equal = preflight(plan, destination)
    outputs = plan.outputs()
    for relative in missing:
        # A concurrently created file is verified, never overwritten. Reserved
        # sources were excluded by preflight, even if the caller requests apply.
        target = destination.joinpath(*extraction.safe_relative(relative).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            with target.open("xb") as stream:
                stream.write(outputs[relative])
        except FileExistsError:
            if target.is_symlink() or target.read_bytes() != outputs[relative]:
                raise extraction.Unsupported(f"concurrent output conflict; not overwritten: {relative}")
    preflight(plan, destination, check=True)
    return len(missing), len(equal)


def load_snapshots(reference: Path, il_repo: Path | None, mathlib_repo: Path | None) -> dict:
    return {
        "VC": extraction.GitSnapshot(reference, VC_COMMIT),
        "IL": extraction.GitSnapshot(il_repo or reference / ".lake/packages/InfinitaryLogic", IL_COMMIT),
        "InfinitaryCore": extraction.GitSnapshot(mathlib_repo or reference / ".lake/packages/mathlib", CORE_COMMIT),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True, help="existing VC reference repo")
    parser.add_argument("--il-repo", type=Path, help="optional existing pinned IL repository")
    parser.add_argument("--mathlib-repo", type=Path, help="optional existing pinned fork repository")
    parser.add_argument("--destination", type=Path, default=Path.cwd())
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--apply", action="store_true", help="create missing production files after preflight")
    action.add_argument("--check", action="store_true", help="require exact output/manifest equality")
    args = parser.parse_args(argv)
    try:
        tool_paths = (Path(__file__).resolve(), Path(extraction.__file__).resolve())
        hashes = {"scripts/" + path.name: sha256(path.read_bytes()) for path in tool_paths}
        plan = build_plan(load_snapshots(args.reference, args.il_repo, args.mathlib_repo), tool_hashes=hashes)
        expected = {"VC": 750, "IL": 154, "InfinitaryCore": 5}
        if plan.manifest["source_counts"] != expected:
            raise extraction.Unsupported(f"pinned production counts differ: {plan.manifest['source_counts']}; expected {expected}")
        if args.apply:
            created, equal = prepare(plan, args.destination)
            status = "prepared-and-checked"
        else:
            missing, matching = preflight(plan, args.destination, check=args.check)
            created, equal = len(missing), len(matching)
            status = "checked" if args.check else "dry-run"
        print(json.dumps({
            "status": status, "source_counts": plan.manifest["source_counts"],
            "source_bytes": sum(row["converted_bytes"] for row in plan.manifest["sources"]),
            "created" if args.apply else "missing": created, "equal_existing": equal,
            "manifest": MANIFEST_PATH,
            "manifest_sha256": sha256(plan.outputs()[MANIFEST_PATH]),
            "external_imports_unexpanded": len(plan.manifest["external_imports_unexpanded"]),
        }, indent=2, sort_keys=True))
    except (OSError, UnicodeError, extraction.Unsupported) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
