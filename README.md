# A counterexample to Vaught's conjecture for infinitary logic

**Nathanael Ackerman, Cameron Freer, Robin Knight**

There is a counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$.
This formalization is based on an unpublished draft by Robin Knight.

Specifically, it constructs a sentence in a countable relational language with
exactly $\aleph_1$ isomorphism classes of countable models and no nonempty perfect
set of pairwise nonisomorphic model codes. This is not a counterexample to the
first-order Vaught conjecture.

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

Registered with Palomar as
[PALOMAR-2026-10-07-000001, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000001&version=1)
on October 7, 2026. The registered source snapshot is commit
[`032ccb7a25b0ff6227128aa0aeba549c5901ea9a`](https://github.com/cameronfreer/vaught-conjecture-palomar/tree/032ccb7a25b0ff6227128aa0aeba549c5901ea9a).
See the [registration record](docs/evidence/palomar-registration.md) for the
official verification links. Subsequent commits are not covered by that
registration merely by appearing in this repository.

The standalone module migration on canonical Mathlib passed local verification:
all 909 supporting proof modules, strict Solution compilation, the standard-axiom
audit, Comparator, and NanoDa, Con-Ron, and Lean kernel replay. Wrong-statement and
unproved-challenge controls were rejected as expected. A separate checkout with
no project build artifacts also completed the native Lake build (2,832 jobs),
reusing only the pinned public dependency cache.

See the [verification record](docs/evidence/canonical-migration.md) and
[build instructions](docs/BUILD.md), including the
[private-preflight record](docs/evidence/private-preflight.md) and
[source-alignment account](docs/SOURCE-ALIGNMENT.md). These historical local
checks are separate from the official Palomar verification linked above.

## License

The formalization is released under the [Apache 2.0 license](LICENSE).
