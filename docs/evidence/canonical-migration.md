# Canonical-Mathlib migration: local verification

Verified on 2026-10-06 with Lean `v4.35.0-rc3` and canonical Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`.

The final production run `20261006T171246Z-ffac59ae` passed all **909 modules**:
6 fresh compilations and 903 validated cache reuses from earlier passes of this
migration, with zero legacy-attested artifacts. It used 16 single-threaded workers,
keep-going scheduling, and the final source and external-artifact checks.

The source ledger contains 21 repairs across 10 files: 20 removals of private
visibility and one explicit canonical Mathlib import. The recorded repairs change
no theorem statement or proof body. Module-header conversion and five infinitary
module relocations are recorded separately in the frozen production manifest.
The pinned-source verifier checked all 909 files, the complete repair chain, and
the retained licenses. Independent agent source review covered the repair batches.

Replay `run.ExlJcY` exited zero after:

- warnings-as-errors compilation of Solution and the audit;
- transitive standard-axiom checking of the theorem and both adapters;
- rejection of a deliberately wrong theorem statement;
- rejection of the Challenge's intentional `sorryAx` as a proof;
- Comparator acceptance, including NanoDa and Lean default-kernel acceptance;
- final replay-input SHA256 verification.

The packaging regression suite passed all 75 tests. Its first invocation lacked
permission to create temporary fixtures; rerunning with worktree write access
passed. This was not a mathematical or source failure.

The exact digests and compact logs are in `canonical-migration.json`. Full build
receipts and the 213 MiB solution export remain local under `.lake/`; they are not
committed. This is an incremental local build using the official dependency cache
and an existing-artifact replay, **not** a clean-checkout build, a complete
transitive Challenge-import audit, or Palomar certification. The native Lake
fresh-checkout route, official workflow, publication review, and submission remain
separate tasks.
