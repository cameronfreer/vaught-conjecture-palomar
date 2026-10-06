# A counterexample to Vaught's conjecture for infinitary logic

**Nathanael Ackerman, Cameron Freer, Robin Knight**

There is a counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$.
This formalization is based on an unpublished draft by Robin Knight.

Specifically, it constructs a sentence in a countable relational language with
exactly $\aleph_1$ isomorphism classes of countable models and no nonempty perfect
set of pairwise nonisomorphic model codes. The perfect-set conclusion does not
assume the continuum hypothesis. This is not a counterexample to the first-order
Vaught conjecture.

The Lean formalization was carried out by Cameron Freer in collaboration with
Nathanael Ackerman and Robin Knight.

## Statement and proof

[Challenge](Palomar/Challenge.lean) gives the independent statement, including
explicit syntax, semantics, model coding and isomorphism.
[Solution](Palomar/Solution.lean) supplies the formal proof.

This repository packages the proof developed in the authors' private working
development. The supporting infinitary model theory builds on
[InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic).

## Status

Preparation for Palomar is in progress. The independent prototype passed local
Comparator, NanoDa and Lean kernel checks; migration to a standalone package on
canonical Mathlib is underway. This repository is not yet a completed standalone
build or a registered Palomar entry.

## License

The formalization is released under the [Apache 2.0 license](LICENSE).
