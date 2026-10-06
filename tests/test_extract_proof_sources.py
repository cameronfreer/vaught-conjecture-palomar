"""Small in-memory fixtures: no commits, dependency downloads, or Lean builds."""

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import MagicMock, mock_open, patch


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "extract_proof_sources.py"
SPEC = importlib.util.spec_from_file_location("extract_proof_sources", SCRIPT)
tool = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = tool
SPEC.loader.exec_module(tool)
COMMIT = tool.PINNED_COMMIT


class MemorySnapshot:
    """An exact-commit tracked tree; untracked/index bytes have no interface."""

    def __init__(self, blobs, modes=None):
        self.commit = COMMIT
        self.blobs = {path: value.encode() if isinstance(value, str) else value
                      for path, value in blobs.items()}
        self.entries = {
            path: tool.Entry((modes or {}).get(path, "100644"), "blob",
                             hashlib.sha1(value).hexdigest())
            for path, value in self.blobs.items()
        }
        self.reads = []

    def read(self, path):
        self.reads.append(path)
        if self.entries[path].mode not in {"100644", "100755"}:
            raise tool.Unsupported("not a regular tracked source/license")
        return self.blobs[path]


class HeaderTests(unittest.TestCase):
    def names(self, text):
        return [item.module for item in tool.parse_header(text).imports]

    def test_nested_and_line_comments(self):
        text = (
            "/- Copyright LICENSE /- import Fake.Nested -/ -/\n"
            "-- import Fake.Line\n"
            "import /- gap -/\n  VaughtConjecture.One\n"
            "import VaughtConjecture.Two -- import Fake.Tail\n"
            "namespace N\nimport Fake.Body\n"
        )
        self.assertEqual(self.names(text), ["VaughtConjecture.One", "VaughtConjecture.Two"])

    def test_modifiers_multiline_and_prelude(self):
        header = tool.parse_header(
            "module\nprelude\npublic\n/- gap -/meta\nimport\nFoo.Bar\n"
            "meta import all Foo.Private\nimport Foo.Ordinary\n@[expose] public section\n"
        )
        self.assertTrue(header.module)
        self.assertTrue(header.prelude)
        self.assertEqual([item.manifest() for item in header.imports], [
            {"module": "Foo.Bar", "public": True, "meta": True, "all": False},
            {"module": "Foo.Private", "public": False, "meta": True, "all": True},
            {"module": "Foo.Ordinary", "public": False, "meta": False, "all": False},
        ])

    def test_doc_comments_are_body_boundaries(self):
        for doc in ("/-! module docs import Fake.Doc -/", "/-- declaration docs -/"):
            with self.subTest(doc=doc):
                self.assertEqual(self.names("import Real.One\n" + doc + "\nimport Fake.Body"), ["Real.One"])
                self.assertEqual(self.names(doc + "\nimport Fake.Body"), [])

    def test_body_is_not_lexed_or_searched(self):
        for body in ('def s := "import Fake.String"', "namespace N\n/- unterminated",
                     'syntax "import" ident : command', "private def f := 1",
                     "public section\nimport Fake.Body", "meta def f := 1"):
            with self.subTest(body=body):
                self.assertEqual(self.names("import Real.One\n" + body), ["Real.One"])

    def test_escaped_names_and_apostrophes(self):
        self.assertEqual(self.names("import Foo.«a.b».«with spaces».Bar'\n"),
                         ["Foo.«a.b».«with spaces».Bar'"])
        self.assertEqual(self.names("import «Foo».Bar"), ["Foo.Bar"])

    def test_question_and_exclamation_identifier_continuations(self):
        text = "import Foo!.Bar?\nimport Later.Module\nnamespace N\n"
        self.assertEqual(self.names(text), ["Foo!.Bar?", "Later.Module"])

    def test_unrecognized_unicode_continuation_cannot_truncate_import(self):
        for suffix in ("℘", "ⱼ"):
            text = f"import Foo{suffix}\nimport Later.Module\n"
            with self.subTest(suffix=suffix), self.assertRaises(tool.Unsupported):
                tool.parse_header(text)

    def test_unsupported_headers(self):
        cases = [
            "import", "import Foo.", "import Foo. Bar", "import Foo .Bar",
            "import Foo, Bar", "import Foo;", "import Foo\nprelude",
            "prelude\nmodule\nimport Foo", "module\nmodule\nimport Foo",
            "public import Foo", "meta import Foo", "import all Foo",
            "module\npublic import all Foo", "module\nprivate import Foo",
            "module\nprivate /- comment -/ import Foo",
            "module\nmeta /- comment -/ public import Foo",
            "/- never closed", "import Foo.«never closed", "import Δ.Module",
            "import Foo.«../escape»", "import Foo.«..»", "\ufeffimport Foo",
        ]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(tool.Unsupported):
                tool.parse_header(text)

    def test_no_import_or_prelude_only(self):
        self.assertEqual(self.names("theorem f : True := by trivial"), [])
        self.assertTrue(tool.parse_header("prelude\n-- tail").prelude)


class ConversionTests(unittest.TestCase):
    def test_identifier_suffix_does_not_move_header_into_body(self):
        body = "namespace N\nprivate def hidden := 1\nend N\n"
        original = "import Foo!.Bar?\nimport Later.Module\n" + body
        converted = tool.convert_module(original)
        self.assertEqual(converted,
                         "module\n\npublic import Foo!.Bar?\npublic import Later.Module\n"
                         "@[expose] public section\n\n" + body)
        self.assertEqual(tool.convert_module(converted), converted)

    def test_first_body_indentation_and_docstring_remain_attached(self):
        for body in (
            "  namespace N\n  theorem f : True := by\n    trivial\n  end N\n",
            "  /-- API docs -/\n  theorem f : True := by\n    trivial\n",
        ):
            with self.subTest(body=body):
                converted = tool.convert_module("import Foo\n\n" + body)
                self.assertEqual(converted,
                                 "module\n\npublic import Foo\n\n@[expose] public section\n\n" + body)

    def test_no_import_indentation_keeps_module_before_section(self):
        body = "  /-- API docs -/\n  theorem f : True := by trivial\n"
        converted = tool.convert_module(body)
        self.assertEqual(converted, "module\n\n@[expose] public section\n\n" + body)
        self.assertEqual(tool.convert_module(converted), converted)

    def test_copyright_namespace_comment_and_body_are_preserved(self):
        copyright = "/-\nCopyright (c) Test. Released under LICENSE.\n-/\n"
        docs = "/-! # A namespace\nKeep this text byte-for-byte.\n-/\n\n"
        body = (
            "namespace N\n\n/-- API docstring -/\n"
            "theorem f : True := by\n  trivial\n\n"
            "private def hidden := 2\npublic def visible := 3\nend N\n"
        )
        original = copyright + "import\n  Foo.Bar -- keep tail\n\n" + docs + body
        converted = tool.convert_module(original)
        expected = (
            copyright + "module\n\npublic import\n  Foo.Bar -- keep tail\n\n"
            + docs + "@[expose] public section\n\n" + body
        )
        self.assertEqual(converted, expected)
        self.assertEqual(tool.convert_module(converted), converted)
        self.assertEqual(converted[converted.index("namespace N"):], body)

    def test_module_before_prelude(self):
        self.assertEqual(tool.convert_module("-- copyright\nprelude\nimport Foo\n"),
                         "-- copyright\nmodule\n\nprelude\npublic import Foo\n@[expose] public section\n\n")

    def test_no_import_and_declaration_docstring(self):
        body = "/-- Keep attached -/\ntheorem f : True := by trivial\n"
        self.assertEqual(tool.convert_module(body), "module\n\n@[expose] public section\n\n" + body)
        self.assertEqual(tool.convert_module("def f := 1"), "module\n\n@[expose] public section\n\ndef f := 1")

    def test_leading_module_doc_without_imports(self):
        text = "/- copyright -/\n/-! # Docs -/\nnamespace N\nend N\n"
        self.assertEqual(tool.convert_module(text),
                         "/- copyright -/\nmodule\n\n/-! # Docs -/\n@[expose] public section\n\nnamespace N\nend N\n")

    def test_newlines_and_empty_sources(self):
        converted = tool.convert_module("/- copyright -/\r\nimport Foo\r\n\r\ndef x := 1\r\n")
        self.assertNotIn("\n", converted.replace("\r\n", ""))
        self.assertTrue(converted.endswith("def x := 1\r\n"))
        self.assertEqual(tool.convert_module(""), "module\n\n@[expose] public section\n\n")
        self.assertEqual(tool.convert_module("-- trailing copyright"),
                         "-- trailing copyright\nmodule\n\n@[expose] public section\n\n")

    def test_canonical_module_and_private_public_boundaries_unchanged(self):
        text = (
            "module\npublic import Foo\n/-! docs -/\n@[expose] public section\n"
            "namespace N\nprivate def hidden := 1\npublic def shown := 2\nend N\n"
        )
        self.assertEqual(tool.convert_module(text), text)

    def test_section_modifiers_with_comments(self):
        canonical = (
            "module\npublic import Foo\n@[/- gap -/ expose]\n"
            "public /- gap -/ section\nprivate def hidden := 1\n"
        )
        self.assertEqual(tool.convert_module(canonical), canonical)
        for text in (
            "public /- gap -/ section\ndef f := 1",
            "@[expose] /- gap -/ section\ndef f := 1",
            "private /- gap -/ section\ndef f := 1",
            "public noncomputable /- gap -/ section\ndef f := 1",
        ):
            with self.subTest(text=text), self.assertRaisesRegex(tool.Unsupported, "manual review"):
                tool.convert_module(text)

    def test_refuses_existing_module_visibility(self):
        cases = [
            "module\nimport Foo\n@[expose] public section\ndef f := 1",
            "module\npublic import Foo\npublic section\ndef f := 1",
            "module\npublic import Foo\nprivate def hidden := 1",
            "module\nmeta import Foo\n@[expose] public section",
            "module\npublic meta import Foo\n@[expose] public section",
            "module\nimport all Foo\n@[expose] public section",
            "public section\ndef f := 1",
            "@[expose] public section\ndef f := 1",
        ]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(tool.Unsupported):
                tool.convert_module(text)

    def test_single_line_header_preserves_body(self):
        converted = tool.convert_module("import Foo theorem f : True := by trivial")
        self.assertTrue(converted.endswith("theorem f : True := by trivial"))
        self.assertIn("public import Foo \n\n@[expose]", converted)


class InventoryTests(unittest.TestCase):
    def fixture(self):
        return {
            "VaughtConjecture/Endpoint.lean": (
                b"/- Copyright retained -/\r\nimport\r\n VaughtConjecture.Helper\r\n"
                b"import Mathlib.Data.Nat.Basic\r\nnamespace E\r\ndef f := 1\r\nend E\r\n"
            ),
            "VaughtConjecture/Helper.lean": (
                "module\npublic import VaughtConjecture.Endpoint\n"
                "meta import Lean.Elab.Command\n@[expose] public section\ndef h := 2\n"
            ),
            "VaughtConjecture/Unused.lean": "import VaughtConjecture.Missing\n",
            ".lake/packages/pkg/Dependency.lean": "import VaughtConjecture.Missing\n",
            "LICENSE": b"Original Apache license bytes\n",
            "docs/NOTICE.txt": b"Original notice\n",
            "LICENSES/LICENSE-MIT": b"Additional license\n",
            ".lake/packages/pkg/LICENSE": b"Dependency license: not read\n",
            "README.md": b"not a source\n",
        }

    def plan(self, snapshot=None):
        return tool.plan_extraction(snapshot or MemorySnapshot(self.fixture()), "VaughtConjecture.Endpoint")

    def test_transitive_cycle_external_boundary_and_only_owned_sources(self):
        snapshot = MemorySnapshot(self.fixture())
        result = self.plan(snapshot)
        self.assertEqual(set(result.files), {
            "VaughtConjecture/Endpoint.lean", "VaughtConjecture/Helper.lean",
            "LICENSE", "docs/NOTICE.txt", "LICENSES/LICENSE-MIT",
        })
        self.assertEqual(result.manifest["external_imports_unexpanded"],
                         ["Init", "Lean.Elab.Command", "Mathlib.Data.Nat.Basic"])
        self.assertEqual(result.manifest["kind"], "project-source-import-closure")
        self.assertEqual(result.manifest["proof_term_closure"], "not-computed")
        self.assertEqual(result.manifest["upstream_commit"], COMMIT)
        self.assertEqual(len(snapshot.reads), 5)

    def test_original_bytes_hashes_licenses_and_no_conversion(self):
        fixture = self.fixture()
        result = self.plan()
        for row in result.manifest["sources"] + result.manifest["licenses"]:
            original = fixture[row["path"]]
            original = original.encode() if isinstance(original, str) else original
            self.assertEqual(result.files[row["path"]], original)
            self.assertEqual(row["sha256"], hashlib.sha256(original).hexdigest())
            self.assertEqual(row["bytes"], len(original))
        self.assertFalse(result.manifest["sources"][0]["module_header"])

    def test_deterministic_order_independent_of_tree_order(self):
        first = self.plan()
        second = self.plan(MemorySnapshot(dict(reversed(list(self.fixture().items())))))
        self.assertEqual(tool.manifest_json(first.manifest), tool.manifest_json(second.manifest))
        self.assertEqual(json.loads(tool.manifest_json(first.manifest)), first.manifest)

    def test_prelude_suppresses_implicit_init(self):
        result = tool.plan_extraction(MemorySnapshot({
            "P.lean": "module\nprelude\npublic import External.Foo\n",
            "LICENSE": "license",
        }), "P")
        self.assertEqual(result.manifest["sources"][0]["implicit_imports"], [])
        self.assertEqual(result.manifest["external_imports_unexpanded"], ["External.Foo"])

    def test_missing_owned_import_is_error(self):
        fixture = self.fixture()
        fixture["VaughtConjecture/Endpoint.lean"] = "import VaughtConjecture.Untracked"
        with self.assertRaisesRegex(tool.Unsupported, "missing project import"):
            self.plan(MemorySnapshot(fixture))

    def test_missing_endpoint_and_missing_license_are_errors(self):
        with self.assertRaisesRegex(tool.Unsupported, "not a tracked source"):
            tool.plan_extraction(MemorySnapshot(self.fixture()), "VaughtConjecture.Untracked")
        with self.assertRaisesRegex(tool.Unsupported, "no tracked license"):
            tool.plan_extraction(MemorySnapshot({"P.lean": "def f := 1"}), "P")

    def test_symlink_sources_and_licenses_refused(self):
        for target in ("VaughtConjecture/Helper.lean", "LICENSE"):
            with self.subTest(target=target), self.assertRaisesRegex(tool.Unsupported, "not a regular"):
                self.plan(MemorySnapshot(self.fixture(), {target: "120000"}))

    def test_multiple_source_roots_and_ambiguous_sources(self):
        snapshot = MemorySnapshot({
            "src/P.lean": "import Q\n", "lib/Q.lean": "def q := 1",
            "LICENSE": "license",
        })
        result = tool.plan_extraction(snapshot, "P", ("src", "lib"))
        self.assertEqual([row["module"] for row in result.manifest["sources"]], ["P", "Q"])
        snapshot = MemorySnapshot({"src/P.lean": "", "lib/P.lean": "", "LICENSE": "license"})
        with self.assertRaisesRegex(tool.Unsupported, "ambiguous"):
            tool.plan_extraction(snapshot, "P", ("src", "lib"))
        with self.assertRaisesRegex(tool.Unsupported, "unsafe relative"):
            tool.plan_extraction(snapshot, "P", ("../escape",))

    def test_escaped_component_maps_to_literal_filename(self):
        snapshot = MemorySnapshot({
            "P.lean": "import Q.«a.b»", "Q/a.b.lean": "def q := 1", "LICENSE": "license",
        })
        result = tool.plan_extraction(snapshot, "P")
        self.assertIn("Q/a.b.lean", result.files)

    def test_question_and_exclamation_names_resolve_tracked_files(self):
        result = tool.plan_extraction(MemorySnapshot({
            "P.lean": "import Q!.R?\nimport S\n",
            "Q!/R?.lean": "def r := 1\n",
            "S.lean": "def s := 1\n",
            "LICENSE": "license",
        }), "P")
        self.assertEqual([row["module"] for row in result.manifest["sources"]], ["P", "Q!.R?", "S"])

    def test_escaped_namespace_dots_do_not_alias_external_namespace(self):
        snapshot = MemorySnapshot({
            "owned.root/P.lean": "import «external.root».Q",
            "LICENSE": "license",
        })
        result = tool.plan_extraction(snapshot, "«owned.root».P")
        self.assertIn("«external.root».Q", result.manifest["external_imports_unexpanded"])
        snapshot = MemorySnapshot({
            "same.root/P.lean": "import «same.other».Q",
            "LICENSE": "license",
        })
        result = tool.plan_extraction(snapshot, "«same.root».P")
        self.assertIn("«same.other».Q", result.manifest["external_imports_unexpanded"])

    def test_file_context_on_header_error(self):
        with self.assertRaisesRegex(tool.Unsupported, "P.lean"):
            tool.plan_extraction(MemorySnapshot({"P.lean": "import Foo.", "LICENSE": "license"}), "P")


class GitAndCliTests(unittest.TestCase):
    def test_git_reads_pinned_tree_and_blob_ids_only(self):
        original = b"import External.P\n"
        oid = hashlib.sha1(original).hexdigest()
        calls = []

        def run(command, **kwargs):
            calls.append(command)
            self.assertEqual(command[:5],
                             ["git", "--no-replace-objects", "--no-lazy-fetch", "-C", "/read-only-reference"])
            args = command[5:]
            if args == ["rev-parse", "--verify", COMMIT + "^{commit}"]:
                data = (COMMIT + "\n").encode()
            elif args == ["ls-tree", "-r", "-z", COMMIT]:
                data = f"100644 blob {oid}\tP.lean\0".encode()
            elif args == ["cat-file", "blob", oid]:
                data = original
            else:
                self.fail(f"unexpected Git operation: {command}")
            return subprocess.CompletedProcess(command, 0, data, b"")

        with patch.object(tool.subprocess, "run", side_effect=run), patch.object(Path, "read_bytes", side_effect=AssertionError("worktree read")):
            snapshot = tool.GitSnapshot(Path("/read-only-reference"), COMMIT)
            self.assertEqual(snapshot.read("P.lean"), original)
            self.assertEqual(set(snapshot.entries), {"P.lean"})
        self.assertEqual(len(calls), 3)

    def test_mutable_ref_rejected_before_git(self):
        for value in ("HEAD", "main", COMMIT[:8], "--help"):
            with self.subTest(value=value), patch.object(tool.subprocess, "run") as run:
                with self.assertRaisesRegex(tool.Unsupported, "full lowercase"):
                    tool.GitSnapshot(Path("/reference"), value)
                run.assert_not_called()

    def test_symlink_blob_read_rejected(self):
        snapshot = object.__new__(tool.GitSnapshot)
        snapshot.entries = {"P.lean": tool.Entry("120000", "blob", "abc")}
        with patch.object(snapshot, "git") as git, self.assertRaises(tool.Unsupported):
            snapshot.read("P.lean")
        git.assert_not_called()

    def test_git_failure_is_reported(self):
        with patch.object(tool.subprocess, "run", return_value=subprocess.CompletedProcess([], 128, b"", b"missing commit")):
            with self.assertRaisesRegex(tool.Unsupported, "missing commit"):
                tool.GitSnapshot(Path("/reference"), COMMIT)

    def test_inventory_cli_does_not_write(self):
        snapshot = MemorySnapshot({"P.lean": "def p := 1", "LICENSE": "license"})
        stdout = io.StringIO()
        with patch.object(tool, "GitSnapshot", return_value=snapshot), patch.object(tool.Extraction, "write") as write, contextlib.redirect_stdout(stdout):
            status = tool.main(["inventory", "--repo", "/reference", "--commit", COMMIT, "--endpoint", "P"])
        self.assertEqual(status, 0)
        self.assertEqual(json.loads(stdout.getvalue())["upstream_commit"], COMMIT)
        write.assert_not_called()

    def test_conversion_cli_returns_no_partial_output_on_failure(self):
        for text, expected in (("import Foo\nprivate def x := 1\n", 0),
                               ("module\nimport Foo\nprivate def x := 1\n", 2)):
            stdin, stdout = MagicMock(), MagicMock()
            stdin.buffer = io.BytesIO(text.encode())
            stdout.buffer = io.BytesIO()
            stderr = io.StringIO()
            with patch.object(tool.sys, "stdin", stdin), patch.object(tool.sys, "stdout", stdout), contextlib.redirect_stderr(stderr):
                status = tool.main(["convert"])
            self.assertEqual(status, expected)
            if expected:
                self.assertEqual(stdout.buffer.getvalue(), b"")
                self.assertIn("manual review", stderr.getvalue())
            else:
                self.assertIn(b"private def x := 1\n", stdout.buffer.getvalue())

    def test_writer_preserves_bytes_and_manifest_without_real_extraction(self):
        result = tool.plan_extraction(MemorySnapshot({"P.lean": b"/- license -/\r\n", "LICENSE": b"license\r\n"}), "P")
        opened = mock_open()
        destination = Path("/authorized/new-directory")
        with patch.object(Path, "mkdir") as mkdir, patch.object(Path, "open", opened):
            result.write(destination)
        self.assertEqual(mkdir.call_args_list[0].args, ())
        self.assertEqual(mkdir.call_args_list[0].kwargs, {"parents": False, "exist_ok": False})
        writes = [call.args[0] for call in opened.return_value.write.call_args_list]
        self.assertIn(b"license\r\n", writes)
        self.assertIn(b"/- license -/\r\n", writes)
        self.assertIn(tool.manifest_json(result.manifest), writes)
        self.assertEqual([call.args[0] for call in opened.call_args_list], ["xb", "xb", "x"])

    def test_writer_refuses_existing_destination_before_opening(self):
        with patch.object(Path, "mkdir", side_effect=FileExistsError), patch.object(Path, "open") as opened:
            with self.assertRaises(FileExistsError):
                tool.Extraction({}, {}).write(Path("/existing"))
            opened.assert_not_called()


if __name__ == "__main__":
    unittest.main()
