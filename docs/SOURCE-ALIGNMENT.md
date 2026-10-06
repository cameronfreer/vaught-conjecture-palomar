# Source alignment

The formal result constructs an $L_{\omega_1,\omega}$ sentence in a countable
relational language with exactly $\aleph_1$ isomorphism classes of countable
models and no nonempty perfect set of pairwise nonisomorphic model codes.
Its scope is infinitary logic; the first-order Vaught conjecture is outside
this result.

## The formal statement and its interpretation

[Challenge](../Palomar/Challenge.lean) independently specifies the syntax,
semantics, model coding, isomorphism, and final existential statement.
[Solution](../Palomar/Solution.lean) supplies the theorem using the supporting
proof library, without importing the Challenge's unproved existence claim.
Both state the same existential theorem. Their alignment concerns the
underlying definitions as well as that theorem statement.

The syntax is the conventional well-founded syntax of $L_{\omega_1,\omega}$:
equality and relation formulas, implication, individual quantification, and
countable conjunctions and disjunctions. Infinitary branches are indexed by
$\mathbb N$; sentences have no free variables, and bound-variable contexts
are finite. Satisfaction uses ordinary Tarski semantics in an actual
first-order structure: quantifiers range over its domain, and infinitary
conjunctions and disjunctions mean universal and existential quantification
over their indices.

The language has relation symbols of finite arities, with countability stated
for the total collection of symbols, $\Sigma_n R_n$. It has no function or
constant symbols. A structure on $\mathbb N$ is encoded by a Boolean truth
value for each relation symbol and argument tuple, including nullary
relations. `IsoClasses` is the quotient of codes satisfying the sentence by
actual isomorphism: a bijection of $\mathbb N$ preserves every relation
coordinate. The Solution's `isomorphic_iff_library` and
`knight_modelSetoid_eq` connect this explicit relation and its restriction
to models with the proof library's structure isomorphisms and model quotient.

Perfectness is measured in the ordinary product topology on these Boolean
coordinates, each carrying the discrete topology. The perfect-antichain
clause forbids a nonempty perfect subset of that ambient coding space
consisting of pairwise nonisomorphic models.

The Solution chooses the language `knightRelations` and the sentence
`knightSentence`. The cardinality and perfect-antichain clauses concern this
same witness sentence. The formal Challenge also includes `NoFiniteModels`,
excluding every finite carrier, including the empty one; the Solution proves
this additional clause for the same sentence. Thus the quotient of models on
$\mathbb N$ accounts for all its countable models up to isomorphism.

## Relationship to the mathematical source

The source designated **Knight2026** is Robin Knight's unpublished 2026 draft
on a counterexample to infinitary Vaught's conjecture. As recorded in the
[project metadata](../formalization.yaml), the formalization follows its key
result and general approach and incorporates new ideas developed through
human–AI interaction. Cameron Freer carried out the Lean formalization in
collaboration with Nathanael Ackerman and Robin Knight.

This relationship is not a claim of line-by-line transcription or verification
of the manuscript as a whole. The unpublished draft is not available for the
comparison documented here, so no detailed correspondence between its
individual arguments and the formal proof is asserted. An inventory of
material corrections, departures, and new ideas requires an author-approved
comparison with the relevant draft version.

The bundled sources retain development-history comments and references to
unpublished notes. Some comments record intermediate states, including questions
that were subsequently resolved; they are not a synchronized account of the final
development. These references add no formal hypotheses or build dependencies.
The formal declarations and checked dependency closure determine the result.

## Logical foundations

The final transitive axiom audit found no axioms beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The existence result is
therefore supplied by the formal proof under those standard foundations,
without additional axioms. This account concerns the statement and its source
relationship; it makes no claim of clean-checkout reproduction or Palomar
certification.
