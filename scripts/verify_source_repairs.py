#!/usr/bin/env python3
"""Read-only verification of audited visibility repairs over the frozen slice.

Reconstruct the full mechanical plan from pinned Git blobs and frozen transforms,
replay ordered unique literal replacements, and check every pre/post SHA256.
All other production source, license, and producer bytes must still match their
original manifest hashes. Never edit sources, regenerate provenance, or build.
Policy v1 permits only removal of private from a named declaration prefix.
Policy v2 additionally permits explicitly recorded public Mathlib import additions;
types, proof bodies, attributes, and local instances are unchanged.
Contexts following any backtick outside comments/strings are unsupported: the
verifier deliberately does not attempt to parse Lean syntax quotations or decide
where they end. Even a closed earlier quotation or quoted name requires review.
The builder consumes this single ledger: baseline_manifest_sha256 and ordered
id/path/old/new/preimage_sha256/postimage_sha256 records. repair_chain_sha256
hashes compact sorted JSON of the records (ensure_ascii=True, UTF-8, no trailing
newline); the ledger's raw-byte SHA256 binds all repair text and provenance.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import prepare_proof_slice as producer


REPAIRS_PATH = "source-manifests/repairs.json"
DECLARATION_PREFIX = re.compile(
    r"(?:@\[reducible\] )?private (?:noncomputable )?"
    r"(?:def|abbrev|opaque|theorem|lemma) [A-Za-z_][A-Za-z_0-9'!?]*(?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*[ \t]?"
)
HASH = re.compile(r"[0-9a-f]{64}\Z")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def patch_digest(replacements: list) -> str:
    return sha256(json.dumps(replacements, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def source_target(relative: str) -> None:
    path = producer.extraction.safe_relative(relative)
    allowed = (
        relative.startswith("VaughtConjecture/"),
        relative.startswith("InfinitaryLogic/"),
        relative.startswith("PalomarProof/Infinitary/"),
    )
    if str(path) != relative or not any(allowed) or path.suffix != ".lean" or any(p.startswith(".") for p in path.parts):
        raise ValueError(f"target is outside the canonical production source roots: {relative}")


def verify_mechanical_plan(production_bytes: bytes, plan: producer.ProductionPlan) -> None:
    if production_bytes != plan.outputs()[producer.MANIFEST_PATH]:
        raise ValueError("frozen production manifest differs from the full pinned mechanical plan")


def code_position(text: str, position: int) -> bool:
    """Reject comments/strings and fail closed after a code backtick.

    A line that looks like a declaration may instead be inside a syntax quotation
    in another declaration's body. Without a full Lean parser, reject all later
    candidates rather than guessing quotation boundaries or custom syntax.
    """
    scanner = producer.extraction.Scanner(text)
    index = 0
    while index < position:
        if text.startswith("/-", index):
            end = scanner.block_end(index)
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
        else:
            raw = re.match(r'r(#+)?"', text[index:])
            if raw and (index == 0 or not (text[index - 1].isalnum() or text[index - 1] == "_")):
                closing = '"' + (raw.group(1) or "")
                close = text.find(closing, index + len(raw.group()))
                end = len(text) if close < 0 else close + len(closing)
            elif text[index] == '"':
                end = index + 1
                while end < len(text):
                    if text[end] == "\\":
                        end += 2
                    elif text[end] == '"':
                        end += 1
                        break
                    else:
                        end += 1
            elif text[index] == "`":
                return False
            else:
                index += 1
                continue
        if end > position:
            return False
        index = end
    return True


def replay(contents: bytes, record: dict) -> bytes:
    for field in ("id", "path", "old", "new", "explanation"):
        if not isinstance(record.get(field), str) or not record[field].strip():
            raise ValueError(f"repair requires nonempty {field}")
    for field in ("preimage_sha256", "postimage_sha256"):
        if not isinstance(record.get(field), str) or not HASH.fullmatch(record[field]):
            raise ValueError(f"repair requires full lowercase {field}")
    pairs = [{"old": record["old"], "new": record["new"], "count": 1}]
    if sha256(contents) != record["preimage_sha256"]:
        raise ValueError(f"{record['id']}: preimage SHA256 mismatch")
    text = contents.decode("utf-8")
    for pair in pairs:
        if not isinstance(pair, dict) or type(pair.get("count")) is not int or pair["count"] != 1:
            raise ValueError("visibility replacements require count=1")
        old, new = pair.get("old"), pair.get("new")
        import_repair = record.get("kind") == "explicit-public-import"
        if import_repair:
            module_name = r"Mathlib(?:\.[A-Za-z_][A-Za-z_0-9']*)+"
            if (not re.fullmatch(r"public import " + module_name + r"\n", old)
                    or not new.startswith(old)
                    or not re.fullmatch(r"public import " + module_name + r"\n", new[len(old):])):
                raise ValueError(f"{record['id']}: expected one anchored public Mathlib import addition")
        elif (not isinstance(old, str) or not isinstance(new, str)
                or not DECLARATION_PREFIX.fullmatch(old) or new != old.replace("private ", "", 1)):
            raise ValueError(f"{record['id']}: unsupported change; only private removal from a declaration prefix is allowed")
        if text.count(old) != 1:
            raise ValueError(f"{record['id']}: old literal must occur exactly once")
        position = text.index(old)
        line_start = text.rfind("\n", 0, position) + 1
        end = position + len(old)
        if text[line_start:position].strip() or not code_position(text, position):
            raise ValueError(f"{record['id']}: replacement is not at a code declaration prefix")
        if not import_repair and end < len(text) and (text[end].isalnum() or text[end] in "_'!?."):
            raise ValueError(f"{record['id']}: partial declaration name")
        if import_repair:
            header = producer.extraction.parse_header(text)
            if end > header.body_start:
                raise ValueError(f"{record['id']}: import addition is outside the header")
            body = text[header.body_start:]
        text = text.replace(old, new, 1)
        if import_repair and text[producer.extraction.parse_header(text).body_start:] != body:
            raise ValueError(f"{record['id']}: import addition changed the source body")
    repaired = text.encode("utf-8")
    if sha256(repaired) != record["postimage_sha256"]:
        raise ValueError(f"{record['id']}: postimage SHA256 mismatch")
    return repaired


def verify_overlay(production_bytes: bytes, repairs_bytes: bytes, baseline_loader, current_reader) -> dict:
    production, overlay = json.loads(production_bytes), json.loads(repairs_bytes)
    if overlay.get("schema_version") != 1 or overlay.get("policy") not in {
            "visibility-private-removal-v1", "visibility-and-explicit-import-v2"}:
        raise ValueError("unsupported repair manifest schema/policy")
    if overlay.get("policy") == "visibility-private-removal-v1" and any(
            r.get("kind") == "explicit-public-import" for r in overlay.get("repairs", [])):
        raise ValueError("explicit import additions require policy v2")
    if overlay.get("baseline_manifest") != producer.MANIFEST_PATH:
        raise ValueError("repair baseline must be the frozen production manifest")
    if overlay.get("baseline_manifest_sha256") != sha256(production_bytes):
        raise ValueError("frozen production manifest SHA256 mismatch")
    if not isinstance(overlay.get("repairs"), list):
        raise ValueError("repairs must be an ordered array")
    rows = {row["path"]: row for row in production["sources"]}
    if len(rows) != len(production["sources"]):
        raise ValueError("duplicate production source paths")
    for path, row in rows.items():
        source_target(path)
        if not isinstance(row.get("converted_sha256"), str) or not HASH.fullmatch(row["converted_sha256"]):
            raise ValueError(f"{path}: required mechanical converted_sha256 is missing/null/invalid")
        if any(key in row for key in ("output_sha256", "transformed_sha256", "target_sha256", "sha256")):
            raise ValueError(f"{path}: ambiguous output hash alias; only converted_sha256 is accepted")
    states, ids = {}, set()
    for record in overlay["repairs"]:
        if not isinstance(record, dict):
            raise ValueError("repair records must be objects")
        path = record.get("path")
        if not isinstance(path, str):
            raise ValueError("repair requires a source path")
        source_target(path)
        if path not in rows:
            raise ValueError(f"repair path is outside the frozen source slice: {path}")
        expected_module = rows[path].get("output_module", path[:-5].replace("/", "."))
        if "module" in record and record["module"] != expected_module:
            raise ValueError(f"repair module/path mismatch: {path}")
        if record.get("id") in ids:
            raise ValueError(f"duplicate repair id: {record.get('id')}")
        ids.add(record.get("id"))
        if path not in states:
            baseline = baseline_loader(rows[path])
            if sha256(baseline) != rows[path]["converted_sha256"]:
                raise ValueError(f"{path}: reconstructed mechanical baseline SHA256 mismatch")
            states[path] = baseline
        states[path] = replay(states[path], record)
    final_hashes = {}
    for path, row in sorted(rows.items()):
        expected = sha256(states[path]) if path in states else row["converted_sha256"]
        actual = sha256(current_reader(path))
        if actual != expected:
            raise ValueError(f"{path}: unrecorded source change; expected {expected}, actual {actual}")
        final_hashes[path] = expected
    return {
        "status": "checked", "sources_checked": len(rows),
        "repairs_checked": len(overlay["repairs"]), "repaired_files": len(states),
        "baseline_manifest_sha256": sha256(production_bytes),
        "repair_manifest_sha256": sha256(repairs_bytes),
        "repair_chain_sha256": patch_digest(overlay["repairs"]),
        "source_tree_sha256": sha256(producer.extraction.manifest_json(final_hashes).encode("utf-8")),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", required=True, help="read-only overlay acceptance")
    parser.add_argument("--reference", type=Path, required=True, help="existing pinned VC reference repository")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    try:
        root = args.root.absolute()
        if root.is_symlink() or not root.is_dir():
            raise ValueError("root must be an existing nonsymlink directory")

        def read_current(relative: str) -> bytes:
            path = producer.extraction.safe_relative(relative)
            target = root.joinpath(*path.parts)
            parent = target
            while parent != root:
                if parent.is_symlink():
                    raise ValueError(f"symlink input is not accepted: {relative}")
                parent = parent.parent
            if not target.is_file():
                raise ValueError(f"missing regular input: {relative}")
            return target.read_bytes()

        production_bytes = read_current(producer.MANIFEST_PATH)
        repairs_bytes = read_current(REPAIRS_PATH)
        production = json.loads(production_bytes)
        expected_tools = {"scripts/extract_proof_sources.py", "scripts/prepare_proof_slice.py"}
        if set(production["tool_hashes"]) != expected_tools:
            raise ValueError("frozen producer tool inventory mismatch")
        for path, expected in production["tool_hashes"].items():
            if sha256(read_current(path)) != expected:
                raise ValueError(f"frozen producer changed: {path}")
        mechanical = producer.build_plan(
            producer.load_snapshots(args.reference, None, None), tool_hashes=production["tool_hashes"],
        )
        verify_mechanical_plan(production_bytes, mechanical)
        result = verify_overlay(production_bytes, repairs_bytes,
                                lambda row: mechanical.files[row["path"]], read_current)
        result["pinned_mechanical_plan_checked"] = True
        for repository in production["repositories"].values():
            license_row = repository["license"]
            if sha256(read_current(license_row["path"])) != license_row["sha256"]:
                raise ValueError(f"upstream license changed: {license_row['path']}")
        result["licenses_checked"] = len(production["repositories"])
        result["producer_files_checked"] = len(production["tool_hashes"])
        print(json.dumps(result, sort_keys=True, indent=2))
    except (OSError, ValueError, UnicodeError, KeyError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
