"""Small synthetic Git snapshots and temporary outputs; no builds or commits."""

import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import prepare_proof_slice as tool


class MemorySnapshot:
    def __init__(self, commit, files):
        self.commit = commit
        self.files = {path: value.encode() if isinstance(value, str) else value
                      for path, value in files.items()}
        self.entries = {path: object() for path in files}
        self.reads = []

    def read(self, path):
        self.reads.append(path)
        return self.files[path]


def fixtures():
    vc = {
        "LICENSE": b"Original VC license\r\n",
        "VaughtConjecture/Entry.lean": (
            "/- Copyright VC; LICENSE -/\nimport InfinitaryLogic.Facade\n"
            "import VaughtConjecture.CountableCover\n"
            "import Mathlib.ModelTheory.Infinitary.QuantifierRank\n"
            "import Mathlib.Data.Set.Countable\n/-! Entry docs -/\n"
            "namespace VaughtConjecture.Entry\ntheorem f : True := by trivial\n"
            "end VaughtConjecture.Entry\n"
        ),
        "VaughtConjecture/CountableCover.lean": "/- Copyright VC -/\nimport Mathlib.Data.Set.Countable\ndef cover := 1\n",
        "VaughtConjecture/Unreachable.lean": "import VaughtConjecture.Missing\n",
    }
    il = {
        "LICENSE": b"Original IL license\n",
        "InfinitaryLogic/Facade.lean": (
            "/- Copyright IL -/\nimport\nMathlib.ModelTheory.Infinitary.Semantics\n"
            "import Architect\n/-! Docs mention Mathlib.ModelTheory.Infinitary.Semantics -/\n"
            'def s := "Mathlib.ModelTheory.Infinitary.Semantics"\n'
        ),
    }
    core = {
        "LICENSE": b"Original fork license\n",
        "Mathlib/ModelTheory/Infinitary/Syntax.lean": (
            "/- Copyright fork -/\nmodule\npublic import Mathlib.ModelTheory.Syntax\n"
            "@[expose] public section\nnamespace FirstOrder\ndef SyntaxThing := 1\nend FirstOrder\n"
        ),
        "Mathlib/ModelTheory/Infinitary/Semantics.lean": (
            "/- Copyright fork -/\nmodule\npublic import Mathlib.ModelTheory.Semantics\n"
            "public import Mathlib.ModelTheory.Infinitary.Syntax\n"
            "@[expose] public section\nnamespace FirstOrder\ndef SemanticsThing := 1\nend FirstOrder\n"
        ),
        "Mathlib/ModelTheory/Infinitary/IndexCoding.lean": "import Mathlib.Data.Nat.Find\ndef code := 1\n",
        "Mathlib/ModelTheory/Infinitary/Reindex.lean": (
            "import Mathlib.ModelTheory.Infinitary.Syntax\n"
            "import Mathlib.ModelTheory.Infinitary.Semantics\ndef reindex := 1\n"
        ),
        "Mathlib/ModelTheory/Infinitary/QuantifierRank.lean": (
            "import Mathlib.ModelTheory.Infinitary.IndexCoding\n"
            "import Mathlib.ModelTheory.Infinitary.Reindex\ndef rank := 1\n"
        ),
    }
    return {
        "VC": MemorySnapshot(tool.VC_COMMIT, vc),
        "IL": MemorySnapshot(tool.IL_COMMIT, il),
        "InfinitaryCore": MemorySnapshot(tool.CORE_COMMIT, core),
    }


def plan(snapshots=None):
    return tool.build_plan(snapshots or fixtures(), "VaughtConjecture.Entry",
                           {"scripts/prepare_proof_slice.py": "test-hash"})


class ProductionPlanTests(unittest.TestCase):
    def test_cross_owner_closure_and_external_boundaries(self):
        snapshots = fixtures()
        result = plan(snapshots)
        self.assertEqual(result.manifest["source_counts"], {"IL": 1, "InfinitaryCore": 5, "VC": 2})
        self.assertEqual(result.manifest["external_imports_unexpanded"],
                         ["Architect", "Init", "Mathlib.Data.Nat.Find", "Mathlib.Data.Set.Countable",
                          "Mathlib.ModelTheory.Semantics", "Mathlib.ModelTheory.Syntax"])
        self.assertNotIn("VaughtConjecture/Unreachable.lean", snapshots["VC"].reads)
        self.assertEqual(result.manifest["proof_term_closure"], "not-computed")
        for suffix in tool.CORE_NAMES:
            self.assertIn("PalomarProof/Infinitary/" + suffix + ".lean", result.files)
            self.assertNotIn("Mathlib/ModelTheory/Infinitary/" + suffix + ".lean", result.files)

    def test_original_and_converted_hashes_full_license_provenance(self):
        snapshots = fixtures()
        result = plan(snapshots)
        for row in result.manifest["sources"]:
            snapshot = snapshots[row["owner"]]
            original = snapshot.files[row["source_path"]]
            self.assertEqual(row["original_sha256"], hashlib.sha256(original).hexdigest())
            self.assertEqual(row["converted_sha256"], hashlib.sha256(result.files[row["path"]]).hexdigest())
            self.assertEqual(row["source_commit"], snapshot.commit)
            self.assertEqual(row["source_repo"], tool.SOURCE_REPOS[row["owner"]])
            self.assertEqual(result.files[row["license_path"]], snapshot.files["LICENSE"])
            self.assertEqual(row["upstream_license_sha256"], tool.sha256(snapshot.files["LICENSE"]))
        encoded = json.dumps(result.manifest)
        self.assertNotIn("/home/", encoded)
        self.assertNotIn("vaught-conjecture/density", encoded)
        self.assertIn("private-working-development", encoded)
        self.assertEqual(result.manifest["external_configuration"]["Mathlib"]["commit"],
                         tool.CANONICAL_MATHLIB_COMMIT)
        self.assertFalse(result.manifest["external_configuration"]["verified_by_this_tool"])

    def test_copyright_docs_names_statements_and_proofs_remain(self):
        result = plan()
        core = result.files["PalomarProof/Infinitary/Semantics.lean"].decode()
        self.assertTrue(core.startswith("/- Copyright fork -/"))
        self.assertTrue(core.endswith("namespace FirstOrder\ndef SemanticsThing := 1\nend FirstOrder\n"))
        facade = result.files["InfinitaryLogic/Facade.lean"].decode()
        self.assertIn("public import\nPalomarProof.Infinitary.Semantics", facade)
        self.assertIn("/-! Docs mention Mathlib.ModelTheory.Infinitary.Semantics -/", facade)
        self.assertIn('def s := "Mathlib.ModelTheory.Infinitary.Semantics"', facade)

    def test_transform_sequence_reports_actual_changes(self):
        result = plan()
        row = next(row for row in result.manifest["sources"]
                   if row["path"] == "PalomarProof/Infinitary/Semantics.lean")
        self.assertEqual(row["transform_sequence"], [
            {"operation": "relocate-module-path", "from": "Mathlib.ModelTheory.Infinitary.Semantics",
             "to": "PalomarProof.Infinitary.Semantics"},
            {"operation": "module-public-expose-header", "changed": False},
            {"operation": "rewrite-header-import-module-paths", "replacements": [
                {"from": "Mathlib.ModelTheory.Infinitary.Syntax", "to": "PalomarProof.Infinitary.Syntax"},
            ]},
        ])

    def test_rewrite_only_header_even_with_comments_modifiers_and_repeated_imports(self):
        text = (
            "/- import Mathlib.ModelTheory.Infinitary.Syntax -/\nmodule\n"
            "public /- gap -/ meta import\nMathlib.ModelTheory.Infinitary.Syntax\n"
            "import all Mathlib.ModelTheory.Infinitary.Semantics\n"
            "public import Mathlib.ModelTheory.Infinitary.Syntax\n"
            "/-! Mathlib.ModelTheory.Infinitary.Syntax -/\n"
            'def literal := "Mathlib.ModelTheory.Infinitary.Syntax"\n'
        )
        converted, replacements = tool.rewrite_imports(text)
        self.assertEqual(len(replacements), 3)
        self.assertIn("public /- gap -/ meta import\nPalomarProof.Infinitary.Syntax", converted)
        self.assertIn("import all PalomarProof.Infinitary.Semantics", converted)
        body = text[text.index("/-!"):].encode()
        self.assertTrue(converted.encode().endswith(body))
        self.assertTrue(converted.startswith("/- import Mathlib.ModelTheory.Infinitary.Syntax -/"))

    def test_determinism_and_no_source_snapshot_mutation(self):
        snapshots = fixtures()
        first = plan(snapshots)
        second = plan(dict(reversed(list(snapshots.items()))))
        self.assertEqual(first.outputs(), second.outputs())
        self.assertEqual(snapshots["IL"].files["InfinitaryLogic/Facade.lean"],
                         fixtures()["IL"].files["InfinitaryLogic/Facade.lean"])

    def test_missing_tracked_source_or_unapproved_boundary_fails(self):
        snapshots = fixtures()
        del snapshots["IL"].entries["InfinitaryLogic/Facade.lean"]
        with self.assertRaisesRegex(tool.extraction.Unsupported, "missing tracked"):
            plan(snapshots)
        for module in ("ComputableModelTheory.Secret", "Mathlib.ModelTheory.Infinitary.Unapproved"):
            with self.subTest(module=module), self.assertRaises(tool.extraction.Unsupported):
                tool.owner_of(module)


class FilesystemTests(unittest.TestCase):
    def setUp(self):
        # Tiny temporary fixtures inside the authorized repo, removed after each test.
        self.temporary = tempfile.TemporaryDirectory(prefix=".prepare-test-", dir=ROOT)
        self.addCleanup(self.temporary.cleanup)
        self.destination = Path(self.temporary.name)
        self.plan = plan()
        for relative, contents in self.plan.files.items():
            if relative in tool.RESERVED:
                path = self.destination / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(contents)

    def test_prepare_and_repeat_leave_every_existing_file_and_reserved_pilot_unchanged(self):
        reserved = {relative: (self.destination / relative).stat().st_mtime_ns
                    for relative in tool.RESERVED if relative in self.plan.files}
        created, equal = tool.prepare(self.plan, self.destination)
        self.assertEqual(equal, len(reserved))
        self.assertEqual(created, len(self.plan.outputs()) - len(reserved))
        original_stats = {path: (self.destination / path).stat().st_mtime_ns for path in self.plan.outputs()}
        self.assertEqual(tool.prepare(self.plan, self.destination), (0, len(self.plan.outputs())))
        self.assertEqual(tool.preflight(self.plan, self.destination, check=True)[0], [])
        for relative, contents in self.plan.outputs().items():
            target = self.destination / relative
            self.assertEqual(target.read_bytes(), contents)
            self.assertEqual(target.stat().st_mtime_ns, original_stats[relative])
        for relative, mtime in reserved.items():
            self.assertEqual((self.destination / relative).stat().st_mtime_ns, mtime)

    def test_conflict_stops_before_any_creation_and_preserves_source(self):
        path = self.destination / "VaughtConjecture/Entry.lean"
        path.write_bytes(b"Parent's independent proof changes\n")
        before = set(self.destination.rglob("*"))
        with self.assertRaisesRegex(tool.extraction.Unsupported, "existing bytes differ"):
            tool.prepare(self.plan, self.destination)
        self.assertEqual(set(self.destination.rglob("*")), before)
        self.assertEqual(path.read_bytes(), b"Parent's independent proof changes\n")

    def test_reserved_missing_or_modified_requires_coordination(self):
        target = self.destination / "PalomarProof/Infinitary/Syntax.lean"
        target.unlink()
        with self.assertRaisesRegex(tool.extraction.Unsupported, "parent/Russell"):
            tool.prepare(self.plan, self.destination)
        target.write_bytes(b"Russell's source changes")
        with self.assertRaisesRegex(tool.extraction.Unsupported, "existing bytes differ"):
            tool.prepare(self.plan, self.destination)
        self.assertEqual(target.read_bytes(), b"Russell's source changes")

    def test_existing_manifest_conflict_is_not_overwritten(self):
        manifest = self.destination / tool.MANIFEST_PATH
        manifest.parent.mkdir()
        manifest.write_bytes(b"Parent's different manifest\n")
        with self.assertRaisesRegex(tool.extraction.Unsupported, "production.json"):
            tool.prepare(self.plan, self.destination)
        self.assertEqual(manifest.read_bytes(), b"Parent's different manifest\n")
        self.assertFalse((self.destination / "VaughtConjecture/Entry.lean").exists())

    def test_missing_outputs_in_check_mode_create_nothing(self):
        before = set(self.destination.rglob("*"))
        with self.assertRaisesRegex(tool.extraction.Unsupported, "missing"):
            tool.preflight(self.plan, self.destination, check=True)
        self.assertEqual(set(self.destination.rglob("*")), before)

    def test_symlink_targets_and_ancestors_are_refused(self):
        link = self.destination / "InfinitaryLogic"
        link.symlink_to(self.destination / "VaughtConjecture", target_is_directory=True)
        with self.assertRaisesRegex(tool.extraction.Unsupported, "symlink"):
            tool.prepare(self.plan, self.destination)
        link.unlink()
        target = self.destination / "VaughtConjecture/Entry.lean"
        target.symlink_to(self.destination / "VaughtConjecture/CountableCover.lean")
        with self.assertRaisesRegex(tool.extraction.Unsupported, "symlink"):
            tool.prepare(self.plan, self.destination)

    def test_cli_dry_run_and_check_never_prepare(self):
        modified = plan()
        modified.manifest["source_counts"] = {"VC": 750, "IL": 154, "InfinitaryCore": 5}
        for flags in ([], ["--check"]):
            with self.subTest(flags=flags), patch.object(tool, "load_snapshots"), patch.object(tool, "build_plan", return_value=modified), patch.object(tool, "preflight", return_value=([], ["equal"])), patch.object(tool, "prepare") as prepare, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(tool.main(["--reference", "/existing/reference",
                                            "--destination", str(self.destination), *flags]), 0)
                prepare.assert_not_called()

    def test_cli_rejects_unexpected_pinned_counts_without_preparation(self):
        with patch.object(tool, "load_snapshots"), patch.object(tool, "build_plan", return_value=self.plan), patch.object(tool, "prepare") as prepare, contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(tool.main(["--reference", "/existing/reference", "--apply"]), 2)
            prepare.assert_not_called()


if __name__ == "__main__":
    unittest.main()
