#!/usr/bin/env python3
"""Inventory/extract a pinned, project-owned Lean source import closure.

This is a source-file closure, NOT a proof-term closure or Palomar certificate.
No dependencies are read/fetched and no Lean elaboration or build is performed.
Only Git blobs at a full commit ID are eligible; worktree/index contents are ignored.
Extraction preserves original bytes, copyright headers, and tracked license notices.
The separate convert command is a conservative pure stdin/stdout transformation.

Header grammar follows Lean 4.35 Module/Syntax.lean: optional module, optional
prelude, repeated [public] [meta] import [all] IDENT (one name per directive).
Whitespace, line comments, and nested ordinary block comments can span lines;
doc comments begin the body. ASCII and escaped identifier components are supported.
This intentionally does not validate declaration syntax or resolve package ownership.
Requires Python 3.10+ and Git 2.45+ (lazy fetches and replacement objects disabled).
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


ENDPOINT = "VaughtConjecture.Knight.ExpansionDomainEndpoint"
PINNED_COMMIT = "57d74cd8309696d242614aeaede028e56321cfe3"
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9'!?]*\Z")
HEADER_WORDS = {"module", "prelude", "public", "private", "meta", "import", "all"}
RESERVED = HEADER_WORDS | {
    "namespace", "section", "end", "def", "theorem", "lemma", "example",
    "axiom", "opaque", "abbrev", "instance", "class", "structure", "inductive",
    "open", "variable", "set_option", "noncomputable", "syntax", "macro",
}
EXCLUDED_DIRS = {".lake", ".git"}
NOTICE = re.compile(r"(?:LICENSE|LICENCE|COPYING|NOTICE|COPYRIGHT|AUTHORS)(?:[._-].*)?\Z", re.I)


class Unsupported(ValueError):
    """Input requires manual review; never return a partial conversion."""


@dataclass(frozen=True)
class Token:
    value: str
    start: int
    end: int


class Scanner:
    """Lazy scanner: inventory never tokenizes statement or proof bodies."""

    def __init__(self, text: str):
        self.text = text
        self.pos = 0
        self.cached: Token | None = None

    def block_end(self, start: int) -> int:
        depth, pos = 1, start + 2
        while pos < len(self.text):
            pair = self.text[pos:pos + 2]
            if pair == "/-":
                depth += 1
                pos += 2
            elif pair == "-/":
                depth -= 1
                pos += 2
                if not depth:
                    return pos
            else:
                pos += 1
        raise Unsupported(f"unterminated block comment at character {start}")

    def trivia_end(self, pos: int) -> int:
        while pos < len(self.text):
            if self.text[pos].isspace():
                pos += 1
            elif self.text.startswith("--", pos):
                newline = self.text.find("\n", pos)
                pos = len(self.text) if newline < 0 else newline + 1
            elif self.text.startswith("/-", pos) and not self.text.startswith(("/--", "/-!"), pos):
                pos = self.block_end(pos)
            else:
                break
        return pos

    def peek(self) -> Token:
        if self.cached is None:
            start = self.trivia_end(self.pos)
            end = start
            if start < len(self.text):
                char = self.text[start]
                if self.text.startswith(("/--", "/-!"), start):
                    end = start + 3  # Do not inspect the body comment here.
                elif char == "«":
                    close = self.text.find("»", start + 1)
                    if close < 0:
                        raise Unsupported(f"unterminated escaped identifier at {start}")
                    end = close + 1
                elif char.isalpha() or char == "_":
                    end = start + 1
                    while end < len(self.text) and (self.text[end].isalnum() or self.text[end] in "_'!?"):
                        end += 1
                else:
                    end = start + 1
            self.cached = Token(self.text[start:end], start, end)
        return self.cached

    def take(self) -> Token:
        token = self.peek()
        self.pos, self.cached = token.end, None
        return token


def component(value: str) -> str:
    if value.startswith("«") and value.endswith("»"):
        result = value[1:-1]
    elif IDENT.fullmatch(value) and value not in RESERVED:
        result = value
    else:
        raise Unsupported(f"unsupported module identifier component: {value!r}")
    if not result or result in {".", ".."} or any(c in result for c in "/\\\x00\r\n«»"):
        raise Unsupported(f"unsafe module identifier component: {value!r}")
    return result


def module_name(parts: tuple[str, ...]) -> str:
    return ".".join(p if IDENT.fullmatch(p) and p not in RESERVED else f"«{p}»" for p in parts)


def module_namespace(name: str) -> str:
    return module_name((component(Scanner(name).take().value),))


def read_name(scanner: Scanner) -> tuple[str, int]:
    first = scanner.take()
    parts = [component(first.value)]
    end = first.end
    while end < len(scanner.text) and scanner.text[end] == ".":
        scanner.take()
        next_token = scanner.take()
        if next_token.start != end + 1:
            raise Unsupported("whitespace or trailing dot in module identifier")
        parts.append(component(next_token.value))
        end = next_token.end
    # Lean also permits non-ASCII letter-like/subscript continuations which
    # Python's isalnum may not recognize. Fail instead of truncating an import.
    if end < len(scanner.text) and ord(scanner.text[end]) >= 128 and not scanner.text[end].isspace():
        raise Unsupported("unsupported non-ASCII module identifier continuation")
    return module_name(tuple(parts)), end


@dataclass(frozen=True)
class Import:
    module: str
    public: bool
    meta: bool
    all: bool
    start: int
    keyword_start: int
    end: int

    def manifest(self) -> dict:
        return {"module": self.module, "public": self.public, "meta": self.meta, "all": self.all}


@dataclass(frozen=True)
class Header:
    module: bool
    prelude: bool
    start: int
    body_start: int
    imports: tuple[Import, ...]


def parse_header(text: str) -> Header:
    if text.startswith("\ufeff"):
        raise Unsupported("UTF-8 BOM requires manual header review")
    scanner = Scanner(text)
    start = scanner.peek().start
    has_module = scanner.peek().value == "module"
    if has_module:
        scanner.take()
    prelude = scanner.peek().value == "prelude"
    if prelude:
        scanner.take()
    imports = []
    while scanner.peek().value in {"public", "meta", "import"}:
        saved = (scanner.pos, scanner.cached)
        begin = scanner.peek().start
        public = scanner.peek().value == "public"
        if public:
            scanner.take()
        meta = scanner.peek().value == "meta"
        if meta:
            scanner.take()
        if scanner.peek().value != "import":
            scanner.pos, scanner.cached = saved
            break  # public section / meta def is a body command.
        keyword = scanner.take()
        all_import = scanner.peek().value == "all"
        if all_import:
            scanner.take()
        name, end = read_name(scanner)
        if not has_module and (public or meta or all_import):
            raise Unsupported("public/meta/import all requires an existing module header")
        if public and all_import:
            raise Unsupported("public import all is not supported by Lean")
        imports.append(Import(name, public, meta, all_import, begin, keyword.start, end))
    body = scanner.peek()
    bad_modifiers = False
    if body.value in {"private", "meta", "public"}:
        probe = Scanner(text)
        probe.pos = body.start
        while probe.peek().value in {"private", "meta", "public"}:
            probe.take()
        bad_modifiers = probe.peek().value == "import"
    if body.value in {"module", "prelude", "import", "all"} or bad_modifiers:
        raise Unsupported(f"unsupported or misplaced header directive at {body.start}")
    if body.value in {".", ",", ";"} and imports:
        raise Unsupported(f"unsupported import punctuation at {body.start}")
    return Header(has_module, prelude, start, body.start, tuple(imports))


def section_prefix(text: str, pos: int) -> tuple[bool, str, bool] | None:
    """Recognize visibility on the first section, including interleaved comments."""
    scanner = Scanner(text)
    scanner.pos = pos
    exposed = scanner.peek().value == "@"
    if exposed:
        for expected in ("@", "[", "expose", "]"):
            if scanner.take().value != expected:
                return None
    visibility = ""
    if scanner.peek().value in {"public", "private"}:
        visibility = scanner.take().value
    special = False
    for modifier in ("noncomputable", "meta"):
        if scanner.peek().value == modifier:
            special = True
            scanner.take()
    if scanner.peek().value != "section":
        return None
    return exposed, visibility, special


def insertion_start(text: str, pos: int) -> int:
    """Insert before line indentation so it remains attached to the original token."""
    line_start = text.rfind("\n", 0, pos) + 1
    return line_start if not text[line_start:pos].strip() else pos


def convert_module(text: str) -> str:
    """Return only header/section insertions; preserve all original body bytes.

    Existing module files are accepted unchanged only when already canonical:
    public non-meta imports and an initial @[expose] public section. Other
    existing module arrangements, meta imports, and import-all need manual review.
    Legacy explicit private declarations remain private. Elaboration and
    visibility review are still required; this is not semantic certification.
    """
    header = parse_header(text)
    scanner = Scanner(text)
    pos = header.body_start
    # Keep module/namespace documentation ahead of the inserted section. A /--
    # declaration docstring must stay immediately ahead of its declaration.
    while text.startswith("/-!", pos):
        pos = scanner.trivia_end(scanner.block_end(pos))
    prefix = section_prefix(text, pos)
    canonical = prefix == (True, "public", False)
    if header.module:
        if canonical and all(i.public and not i.meta and not i.all for i in header.imports):
            return text
        raise Unsupported("existing module visibility/exposure requires manual review")
    if prefix and (prefix[0] or prefix[1]):
        raise Unsupported("existing public/expose section requires manual review")
    pos = insertion_start(text, pos)
    module_pos = insertion_start(text, header.start)
    newline = "\r\n" if "\r\n" in text else "\n"
    module_prefix = newline if module_pos and text[module_pos - 1] not in "\r\n" else ""
    edits = [(module_pos, module_prefix + "module" + newline + newline)]
    edits.extend((i.keyword_start, "public ") for i in header.imports)
    section = "@[expose] public section" + newline + newline
    if pos != module_pos and pos and text[pos - 1] not in "\r\n":
        section = newline + newline + section
    edits.append((pos, section))
    # Apply later insertions first, including ties, to put module before section.
    for position, insertion in reversed(sorted(edits, key=lambda edit: edit[0])):
        text = text[:position] + insertion + text[position:]
    return text


@dataclass(frozen=True)
class Entry:
    mode: str
    kind: str
    oid: str


def safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "\\" in value or "\x00" in value:
        raise Unsupported(f"unsafe relative path: {value!r}")
    return path


class GitSnapshot:
    def __init__(self, repo: Path, commit: str):
        if not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", commit):
            raise Unsupported("--commit must be a full lowercase Git commit ID, not a ref")
        self.repo = repo
        self.commit = self.git("rev-parse", "--verify", commit + "^{commit}").decode().strip()
        if self.commit != commit:
            raise Unsupported("resolved commit differs from requested commit")
        self.entries: dict[str, Entry] = {}
        for row in self.git("ls-tree", "-r", "-z", self.commit).split(b"\0"):
            if row:
                metadata, raw_path = row.split(b"\t", 1)
                mode, kind, oid = metadata.decode("ascii").split()
                path = raw_path.decode("utf-8")
                safe_relative(path)
                self.entries[path] = Entry(mode, kind, oid)

    def git(self, *args: str) -> bytes:
        process = subprocess.run(
            ["git", "--no-replace-objects", "--no-lazy-fetch", "-C", str(self.repo), *args],
            capture_output=True, check=False,
        )
        if process.returncode:
            raise Unsupported(process.stderr.decode("utf-8", errors="replace").strip())
        return process.stdout

    def read(self, path: str) -> bytes:
        entry = self.entries[path]
        if entry.kind != "blob" or entry.mode not in {"100644", "100755"}:
            raise Unsupported(f"not a regular tracked source/license: {path} ({entry.mode})")
        return self.git("cat-file", "blob", entry.oid)


@dataclass
class Extraction:
    manifest: dict
    files: dict[str, bytes]

    def write(self, destination: Path) -> None:
        """Create a NEW directory; refuse merges, symlinks, and overwrites."""
        destination.mkdir(parents=False, exist_ok=False)
        for relative, contents in sorted(self.files.items()):
            target = destination.joinpath(*safe_relative(relative).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open("xb") as stream:
                stream.write(contents)
        with (destination / "source-manifest.json").open("x", encoding="utf-8", newline="\n") as stream:
            stream.write(manifest_json(self.manifest))


def plan_extraction(snapshot: GitSnapshot, endpoint: str = ENDPOINT,
                    source_roots: tuple[str, ...] = (".",)) -> Extraction:
    roots = tuple(sorted({safe_relative(root) for root in source_roots}, key=str))
    if not roots:
        raise Unsupported("at least one source root is required")
    sources: dict[str, str] = {}
    for path in sorted(snapshot.entries):
        relative = PurePosixPath(path)
        if relative.suffix != ".lean" or EXCLUDED_DIRS.intersection(relative.parts):
            continue
        for root in roots:
            if relative.is_relative_to(root):
                parts = relative.relative_to(root).with_suffix("").parts
                name = module_name(parts)
                if name in sources and sources[name] != path:
                    raise Unsupported(f"ambiguous tracked module {name}: {sources[name]}, {path}")
                sources[name] = path
    if endpoint not in sources:
        raise Unsupported(f"endpoint is not a tracked source at {snapshot.commit}: {endpoint}")
    owned_namespaces = {module_namespace(name) for name in sources}
    pending, seen, files, rows, external = [endpoint], set(), {}, [], set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name not in sources:
            if module_namespace(name) in owned_namespaces:
                raise Unsupported(f"missing project import at pinned commit: {name}")
            external.add(name)
            continue
        path = sources[name]
        original = snapshot.read(path)
        try:
            header = parse_header(original.decode("utf-8"))
        except (UnicodeError, Unsupported) as error:
            raise Unsupported(f"{path}: {error}") from error
        files[path] = original
        implicit = [] if header.prelude else ["Init"]
        imports = [i.module for i in header.imports] + implicit
        pending.extend(sorted(set(imports), reverse=True))
        rows.append({"module": name, "path": path,
                     "sha256": hashlib.sha256(original).hexdigest(), "bytes": len(original),
                     "module_header": header.module, "prelude": header.prelude,
                     "imports": [i.manifest() for i in header.imports], "implicit_imports": implicit})
    licenses = []
    for path in sorted(snapshot.entries):
        relative = PurePosixPath(path)
        if NOTICE.fullmatch(relative.name) and not EXCLUDED_DIRS.intersection(relative.parts):
            contents = snapshot.read(path)
            files[path] = contents
            licenses.append({"path": path, "sha256": hashlib.sha256(contents).hexdigest(), "bytes": len(contents)})
    if not licenses:
        raise Unsupported("no tracked license/notice found; preservation requires manual review")
    manifest = {
        "schema_version": 1,
        "kind": "project-source-import-closure",
        "proof_term_closure": "not-computed",
        "upstream_commit": snapshot.commit,
        "endpoint": endpoint,
        "source_roots": [str(root) for root in roots],
        "external_imports_unexpanded": sorted(external),
        "sources": sorted(rows, key=lambda row: row["module"]),
        "licenses": licenses,
        "limitations": [
            "Whole source files, not the minimal declaration/proof-term dependency closure.",
            "External imports are boundaries; package resolution and transitive external imports are not checked.",
            "Header syntax only; no elaboration, axiom audit, build, or Palomar eligibility verification.",
            "Module names support ASCII and escaped components; unsupported header forms fail.",
            "License preservation covers tracked LICENSE/LICENCE/COPYING/NOTICE/COPYRIGHT/AUTHORS names; review custom notices.",
        ],
    }
    return Extraction(manifest, files)


def manifest_json(manifest: dict) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("inventory", "extract"):
        sub = subparsers.add_parser(command, help="dry-run JSON inventory" if command == "inventory" else "copy original blobs into a new directory")
        sub.add_argument("--repo", type=Path, required=True)
        sub.add_argument("--commit", required=True, help="full immutable commit ID")
        sub.add_argument("--endpoint", default=ENDPOINT)
        sub.add_argument("--source-root", action="append", help="tracked source root relative to repository (repeatable; default .)")
        if command == "extract":
            sub.add_argument("--destination", type=Path, required=True, help="new, nonexistent directory; parent must exist")
    subparsers.add_parser("convert", help="pure module conversion: UTF-8 stdin to stdout; refuses unsupported cases")
    args = parser.parse_args(argv)
    try:
        if args.command == "convert":
            original = sys.stdin.buffer.read().decode("utf-8")
            sys.stdout.buffer.write(convert_module(original).encode("utf-8"))
        else:
            snapshot = GitSnapshot(args.repo, args.commit)
            extraction = plan_extraction(snapshot, args.endpoint, tuple(args.source_root or ["."]))
            if args.command == "extract":
                extraction.write(args.destination)
            sys.stdout.write(manifest_json(extraction.manifest))
    except (OSError, UnicodeError, Unsupported) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
