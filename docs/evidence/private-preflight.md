# Private preflight, 2026-10-06

The proof source snapshot was `cb6757efdc95feb5072ab0314666c599e8a944f5`.
These checks are local preparation, not an official Palomar report.

## Native reproduction

A separate detached checkout began with no project `.lake/build` directory.
Only the pinned public dependency trees and their cached artifacts were copied;
no project proof artifacts were copied. The command
`LEAN_NUM_THREADS=16 lake --no-cache build Palomar.Solution Cli` completed
successfully with **2,832 jobs**. Its log remains in that checkout under
`.lake/private-preflight/native-build.log`.

Replay `run.qtI5zN` then passed against that checkout's newly built artifacts:
strict Solution and axiom-audit compilation, both negative controls, Comparator,
NanoDa, Lean's default kernel, and final replay-input hash checks. The native
build-log SHA256 is
`23e92c230c5e0274c2388a25e9338fa8768b190ff6db204f9bfc8da9770c7b35`.

## Additional kernel

The hash-verified exports from `run.ExlJcY` passed Comparator with Con-Ron
(`--jobs=2`), NanoDa, and Lean's default kernel. Con-Ron reported acceptance of
29,133 declarations. This additional local configuration was not substituted for
the submitted Comparator configuration. The checker choices match the inspected
official pipeline at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
The three-kernel log SHA256 is
`c300b2c3efddf2c1cb618b9e10cd3a27f8697acc6e987d99cbf982d78b5642e2`.

## Metadata and source-envelope checks

The metadata at the proof snapshot passed the upstream v0.4 JSON Schema and the
official Palomar metadata/provenance validator, including taxonomy checks.
The schema revision was `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`;
the Palomar policy revision was `96b034cc31a72a63d4f4041911dce337a85c9a04`.

A read-only agent audit checked all 915 tracked Lean files: module headers,
the 10,000-line bound, and absence of source symlinks and committed build artifacts.
Challenge measured 157 lines and 7,097 bytes. Its recursively expanded source
imports resolved to 2,563 modules in core and the canonical Mathlib dependency
closure, with no bundled proof-library or LeanArchitect imports. This conservative
source scan is not a substitute for Palomar's authoritative dependency audit.

## Publication review

The owner accepted disclosure of the existing Git history, author email, local
note paths, and internal manuscript/audit citations. No history rewrite or source
redaction was performed. A heuristic history scan found no high-signal credentials;
that negative result is not a guarantee that all sensitive material is absent.

The remaining gate before intake is the official reusable workflow on the exact
public commit. Submission and permanent registration are separate decisions.
