"""Read-only repair replay fixtures; no source writes or compilation."""

import copy
import json
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import verify_source_repairs as tool


PATH = "InfinitaryLogic/Descriptive/Mycielski.lean"
OLD = "@[reducible] private noncomputable def cantorMetricSpace"
NEW = "@[reducible] noncomputable def cantorMetricSpace"
BASELINE = (
    "/- Copyright; LICENSE -/\nmodule\npublic import Mathlib.Topology.MetricSpace.Basic\n"
    "@[expose] public section\nnamespace MycielskiCantor\n"
    + OLD + " : Nat := 1\nattribute [local instance] cantorMetricSpace\n"
    "private theorem untouched : True := by trivial\nend MycielskiCantor\n"
).encode()


def record(before=BASELINE, old=OLD, new=NEW, path=PATH, id="0001"):
    after = before.decode().replace(old, new, 1).encode()
    return {
        "id": id, "path": path, "old": old, "new": new, "explanation": "Audited visibility only.",
        "preimage_sha256": tool.sha256(before), "postimage_sha256": tool.sha256(after),
    }


def fixtures():
    production = {
        "sources": [
            {"path": PATH, "converted_sha256": tool.sha256(BASELINE)},
            {"path": "VaughtConjecture/Unchanged.lean", "converted_sha256": tool.sha256(b"unchanged\n")},
        ],
    }
    production_bytes = json.dumps(production).encode()
    overlay = {
        "schema_version": 1, "policy": "visibility-private-removal-v1",
        "baseline_manifest": tool.producer.MANIFEST_PATH,
        "baseline_manifest_sha256": tool.sha256(production_bytes), "repairs": [record()],
    }
    current = {PATH: BASELINE.replace(OLD.encode(), NEW.encode(), 1),
               "VaughtConjecture/Unchanged.lean": b"unchanged\n"}
    return production_bytes, overlay, current


class ReplayTests(unittest.TestCase):
    def test_explicit_mathlib_import_preserves_body(self):
        old = "public import Mathlib.Topology.MetricSpace.Basic\n"
        new = old + "public import Mathlib.Data.Nat.Cast.Order.Basic\n"
        item = record(BASELINE, old, new)
        item["kind"] = "explicit-public-import"
        self.assertEqual(tool.replay(BASELINE, item), BASELINE.replace(old.encode(), new.encode(), 1))

    def test_import_repair_cannot_inject_code_or_private_modules(self):
        old = "public import Mathlib.Topology.MetricSpace.Basic\n"
        for extra in ("axiom injected : False\n", "public import Other.Trusted\n",
                      "public import Mathlib.Data.Nat.Cast.Order.Basic\naxiom injected : False\n"):
            item = record(BASELINE, old, old + extra)
            item["kind"] = "explicit-public-import"
            with self.assertRaises(ValueError):
                tool.replay(BASELINE, item)

    def test_exact_repair_preserves_signature_proof_and_local_instance(self):
        repaired = tool.replay(BASELINE, record())
        self.assertEqual(repaired, BASELINE.replace(OLD.encode(), NEW.encode(), 1))
        self.assertIn(b"attribute [local instance] cantorMetricSpace\n", repaired)
        self.assertIn(b"private theorem untouched : True := by trivial", repaired)
        self.assertIn(b" : Nat := 1\n", repaired)

    def test_preimage_and_postimage_hashes_are_mandatory(self):
        for key in ("preimage_sha256", "postimage_sha256"):
            altered = record()
            altered[key] = "0" * 64
            with self.subTest(key=key), self.assertRaises(ValueError):
                tool.replay(BASELINE, altered)

    def test_empty_or_ambiguous_literal_is_refused(self):
        duplicate = BASELINE + OLD.encode() + b" : Nat := 2\n"
        with self.assertRaisesRegex(ValueError, "exactly once"):
            tool.replay(duplicate, record(duplicate))
        empty = record()
        empty["old"] = ""
        with self.assertRaises(ValueError):
            tool.replay(BASELINE, empty)

    def test_types_bodies_attributes_instances_and_imports_are_not_repairs(self):
        cases = [
            (OLD, NEW + " : Bool"),
            ("private instance metric", "instance metric"),
            ("attribute [local instance] cantorMetricSpace", "attribute [instance] cantorMetricSpace"),
            (OLD + " : Nat := 1", NEW + " : Nat := 2"),
            ("public import Mathlib.Topology.MetricSpace.Basic", "import Mathlib"),
            ("@[reducible] private noncomputable def cantorMetricSpace",
             "noncomputable def cantorMetricSpace"),
        ]
        for old, new in cases:
            with self.subTest(old=old), self.assertRaises(ValueError):
                tool.replay(BASELINE, record(BASELINE, old, new))

    def test_comments_and_strings_are_not_declarations(self):
        for text in (
            "/-\n" + OLD + "\n-/\n",
            "/--\n" + OLD + "\n-/\n",
            "-- " + OLD + "\n",
            'def s := "\n' + OLD + '\n"\n',
            'def s := r##"\n' + OLD + '\n"##\n',
        ):
            before = text.encode()
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "code declaration"):
                tool.replay(before, record(before))

    def test_partial_declaration_name_is_refused(self):
        before = (OLD + "Extra : Nat := 1\n").encode()
        with self.assertRaisesRegex(ValueError, "partial declaration"):
            tool.replay(before, record(before))

    def test_syntax_quotations_and_later_ambiguous_contexts_are_refused(self):
        old, new = "private def inner", "def inner"
        cases = (
            "def quoted : Lean.Syntax := `(command|\n  private def inner := 1\n)\n",
            "def quoted := `(\n  private def inner := 1\n)\n",
            "def quoted := `(term| `(command|\n  private def inner := 1\n))\n",
            "def quoted := `(term| 1)\nprivate def inner := 1\n",
            "def quotedName := `name\nprivate def inner := 1\n",
            "def quoted := ` [\n  private def inner := 1\n]\n",
        )
        for text in cases:
            before = text.encode()
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "code declaration"):
                tool.replay(before, record(before, old, new))

    def test_backticks_in_comments_and_strings_do_not_block_real_declarations(self):
        prefixes = (
            "/- ` ( /- nested ` -/ ) -/\n",
            "-- `(command|\n",
            'def quotedText := "`(command|"\n',
            'def quotedText := r##"`(command|"##\n',
        )
        for prefix in prefixes:
            before = prefix.encode() + BASELINE
            with self.subTest(prefix=prefix):
                self.assertEqual(tool.replay(before, record(before)),
                                 before.replace(OLD.encode(), NEW.encode(), 1))


class OverlayTests(unittest.TestCase):
    def verify(self, production, overlay, current, baseline=BASELINE):
        return tool.verify_overlay(production, json.dumps(overlay).encode(),
                                   lambda row: baseline, current.__getitem__)

    def test_acceptance_checks_all_sources_without_mutating_provenance(self):
        production, overlay, current = fixtures()
        before = copy.deepcopy((production, overlay, current))
        receipt = self.verify(production, overlay, current)
        self.assertEqual(receipt["sources_checked"], 2)
        self.assertEqual(receipt["repairs_checked"], 1)
        self.assertEqual(receipt["repaired_files"], 1)
        self.assertEqual((production, overlay, current), before)
        self.assertEqual(self.verify(production, overlay, current), receipt)

    def test_frozen_manifest_and_reconstructed_baseline_must_match(self):
        production, overlay, current = fixtures()
        wrong = copy.deepcopy(overlay)
        wrong["baseline_manifest_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "production manifest SHA256"):
            self.verify(production, wrong, current)
        with self.assertRaisesRegex(ValueError, "mechanical baseline SHA256"):
            self.verify(production, overlay, current, b"wrong baseline")

    def test_unrecorded_changes_to_repaired_or_other_source_are_refused(self):
        production, overlay, current = fixtures()
        for path in current:
            altered = dict(current)
            altered[path] += b"-- unrecorded\n"
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "unrecorded source change"):
                self.verify(production, overlay, altered)

    def test_ordered_chain_replays_each_transition(self):
        production, overlay, current = fixtures()
        second_old = "private theorem untouched"
        second_new = "theorem untouched"
        second = record(current[PATH], second_old, second_new, id="0002")
        overlay["repairs"].append(second)
        current[PATH] = current[PATH].replace(second_old.encode(), second_new.encode(), 1)
        self.assertEqual(self.verify(production, overlay, current)["repairs_checked"], 2)
        overlay["repairs"].reverse()
        with self.assertRaisesRegex(ValueError, "preimage SHA256 mismatch"):
            self.verify(production, overlay, current)

    def test_duplicate_ids_and_out_of_slice_paths_are_refused(self):
        production, overlay, current = fixtures()
        overlay["repairs"].append(copy.deepcopy(overlay["repairs"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate repair"):
            self.verify(production, overlay, current)
        for path in ("../outside.lean", "/outside.lean", "VaughtConjecture/Unknown.lean"):
            altered = fixtures()[1]
            altered["repairs"][0]["path"] = path
            with self.subTest(path=path), self.assertRaises(ValueError):
                self.verify(production, altered, current)

    def test_no_repairs_requires_exact_baseline(self):
        production, overlay, current = fixtures()
        overlay["repairs"] = []
        current[PATH] = BASELINE
        receipt = self.verify(production, overlay, current)
        self.assertEqual(receipt["repairs_checked"], 0)
        self.assertEqual(receipt["repaired_files"], 0)

    def test_missing_null_or_ambiguous_output_hashes_cannot_bypass_checks(self):
        production, overlay, current = fixtures()
        for value in (None, "", "0" * 63):
            altered = json.loads(production)
            altered["sources"][1]["converted_sha256"] = value
            encoded = json.dumps(altered).encode()
            manifest = copy.deepcopy(overlay)
            manifest["baseline_manifest_sha256"] = tool.sha256(encoded)
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "missing/null/invalid"):
                self.verify(encoded, manifest, current)
        altered["sources"][1].pop("converted_sha256")
        encoded = json.dumps(altered).encode()
        manifest["baseline_manifest_sha256"] = tool.sha256(encoded)
        with self.assertRaises(ValueError):
            self.verify(encoded, manifest, current)
        altered = json.loads(production)
        altered["sources"][0]["output_sha256"] = tool.sha256(current[PATH])
        encoded = json.dumps(altered).encode()
        manifest["baseline_manifest_sha256"] = tool.sha256(encoded)
        with self.assertRaisesRegex(ValueError, "ambiguous output hash alias"):
            self.verify(encoded, manifest, current)

    def test_external_namespace_and_noncanonical_paths_are_not_targets(self):
        for path in ("Mathlib/Injected.lean", ".lake/injected.lean",
                     "InfinitaryLogic//Fake.lean", "VaughtConjecture/./Fake.lean"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                tool.source_target(path)

    def test_wrong_mechanical_manifest_cannot_be_rebound_by_overlay(self):
        class Plan:
            def outputs(self):
                return {tool.producer.MANIFEST_PATH: b"the pinned mechanical manifest"}
        with self.assertRaisesRegex(ValueError, "full pinned mechanical plan"):
            tool.verify_mechanical_plan(b"edited production manifest", Plan())


if __name__ == "__main__":
    unittest.main()
