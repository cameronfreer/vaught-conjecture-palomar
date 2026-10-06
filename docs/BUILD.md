# Building and checking the package

The toolchain and Git dependencies are pinned in `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`. Mathlib is the canonical upstream repository, not a fork.
The selected infinitary infrastructure is bundled as attributed source.

The normal Lake route for a checkout is:

```sh
lake exe cache get
lake build Palomar.Solution Cli
bash scripts/check_palomar_solution.sh --comparator
```

The first command obtains the official Mathlib cache. The second is the native
build entry point, now checked in a separate checkout with no project artifacts
and a copy of the pinned public dependency cache. The initial local migration
used the dependency-ready compiler driver described below instead.
The final script needs Linux `bwrap`, `jq`, Python 3, and the pinned Lean toolchain's
`leanexport` and Comparator support. It uses existing built artifacts and does not
fetch or build the production proof closure itself.

The replay compiles Challenge, Solution, and controls into separate output trees.
Solution and its axiom audit explicitly use warnings-as-errors. Challenge alone
permits its intentional theorem hole; that hole is rejected when Challenge is
submitted as a purported solution. Native Lake's `Palomar` library therefore has
no library-wide warnings-as-errors setting: the replay's explicit strict Solution
compile is a required gate, not an optional replacement for it.

The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound` in the
theorem and both adapters. Comparator must reject the wrong statement and the
unproved Challenge, then accept the actual Solution with NanoDa and Lean's kernel.
Source-style linters are disabled for the migration; kernel checks and the
`sorry` warning are not disabled.

## Incremental migration driver

`scripts/build_module_slice.py` compiles the 909-module proof closure with one Lean
thread per worker, supporting at most 16 workers. Its accepted configuration uses
`--keep-going`, `--repair-overlay source-manifests/repairs.json`, and **no legacy
receipt**. Do not treat the unreviewed default fail-fast path or legacy-attestation
mode as equivalent to this reviewed configuration.

The driver validates source hashes, the ordered repair ledger, owner-specific
compiler options, compiler/dependency artifact fingerprints, and cached outputs.
Do not edit its inputs during a run. It requires explicit compiler and dependency
paths; `--help` documents the arguments. The initial successful migration reused
only artifacts compiled and checked during this canonical migration, not artifacts
from the original proof development.

The extraction tools and pinned-source repair verifier are maintainer provenance
tools. Replaying extraction requires the original source snapshots; building the
bundled proof and checking its theorem does not.

```sh
python3 -B -m unittest discover -s tests
```

All build outputs, full local receipts, and exported proof files live under
`.lake/` and are excluded from Git. The small committed evidence summaries are
descriptive receipts, not a substitute for rerunning verification. These commands
do not publish the repository or submit an entry to Palomar.

## Official mechanical preflight

After publication, manually dispatch `.github/workflows/palomar-preflight.yml`
with the full commit SHA to verify. It calls the official reusable workflow in
`full` mode with both the workflow reference and `pipeline_commit` pinned to the
same revision, using the approved `palomar-standard-v1` GitHub-hosted profile.
Its public-repository guard prevents accidental dispatch against private sources.

Require the resulting mechanical report to say `status: pass` before submission.
This workflow does not submit an entry, perform editorial review, or register it.
The additional local Con-Ron check used a temporary checker configuration; the
submitted `comparator.json` remains unchanged. Palomar selects its own checkers.
