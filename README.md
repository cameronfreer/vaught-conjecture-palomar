# Infinitary counterexample: certification preparation

Private preparation repository for a prospective Palomar submission. **Not a
registered or certified result, and not yet a standalone buildable extraction.**

The intended statement is the existence of a sentence of countable infinitary
logic in a countable relational language having exactly aleph-one isomorphism
classes of countably infinite models, no finite models, and no nonempty perfect
antichain of model codes in the ordinary product topology.

This is not a claim to refute the first-order Vaught conjecture. The perfect-set
conclusion is stated independently of the continuum hypothesis.

The proof is being extracted from
[vaught-conjecture](https://github.com/cameronfreer/vaught-conjecture), initially
at `57d74cd8309696d242614aeaede028e56321cfe3`. This repository is a derivative
verification package, not an independent rediscovery or a new formalization.
The independent Challenge exposes syntax, semantics, coding and isomorphism;
its Solution supplies the already-proved example.

## Preparation status

- The independent prototype passed local Comparator matching, NanoDa and Lean
  default-kernel replay on 2026-10-06 using the reference project's built pins.
- Source-module conversion, clean-build provenance and the Palomar workflow
  remain outstanding. The current Solution still imports a legacy module.
- Attribution, source citations, assistance history and final metadata are under
  discussion. There is no submission-ready `formalization.yaml` yet.
- No registration or publication action is authorized by these files. The owner
  will approve public visibility and submission separately.

Preserve original copyright and license notices when extracting source. Do not
commit compiled objects, exported proof dumps, dependency checkouts or private
working notes. Extraction tooling must record source hashes and transformations.
