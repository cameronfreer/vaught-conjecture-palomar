/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedTrace
public import VaughtConjecture.Knight.ChartKarp

/-! # The terminal trace/menu boundary (#57 — terminal ruling)

**THE TERMINAL BOUNDARY of the provenance/Karp classification route** (#57, 2026-08-26
strategic ruling; scope amended 2026-08-29): `MenuIntersectionSupply` is the FINAL theorem
of the UNIVERSAL trace-family route — the exact residual when isomorphism is fed through
the full `traceFamily` with forth/back at every traced node.  It is no longer the weakest
known classification hypothesis: `Knight/FairPairedChain.lean` compiles a single-chain
consumer (`nonempty_iso_of_fairPairedChain`) whose hypothesis — one fair paired chain from
the seed — is formally weaker (lower quantifier surface; the two-sided joint supply
constructs such a chain, `fairPairedChain_of_jointTraceSupply`).  The open producer
theorem on that route is: same-code receipt sources admit one producer-selected fair
paired chain.  The RANK-ZERO branch keeps its separate interface (#200,
`Knight/EmptySeedBoundary.lean`): two countable block-zero models admit the EMPTY paired
seed with no receipt data, and every seed-generic consumer — menu intersection there, the
fair chain in `Knight/FairPairedChain.lean` — applies to it unchanged.  This module
graduates to main the minimal failure-arm boundary of the experimental stack — the terminal
supply statements and the compiled equivalences that reduce isomorphism of code-matched
sources to menu intersection, and nothing else.

Provenance: re-homed from `VaughtConjecture/Knight/BasedKarp.lean` on `origin/e7/based-karp`
(PR #195: `TraceExtensionSupply`, its exactness, the trace family) and
`VaughtConjecture/Knight/JointChoice.lean` on `origin/e7/joint-choice` (PR #196:
`JointTraceSupply`, `MenuIntersectionSupply`, the equivalences, the seed composite).  The
diagnostic scaffolding of PRs #194–#196 — the `HighCandidate` collapse/spine layer, the
menu probes (`exists_top_coface_both`, `exists_genSat_coface_both`), and the
independent-supply pipeline duplicates — stays behind on those branches.

## The boundary record

Equal complete receipt codes (`StopCode`: run level, cutoff, both source labels,
`⊤`-witness) leave menu intersection as the ONLY missing hypothesis for isomorphism:

* `TraceExtensionSupply` — the independent-choice residual (PR #195's verdict (b)): the
  right witness must actually evaluate, over the node's right occurrence along the shared
  embedding, a cover whose source reduction EQUALS the left-selected cover's.  Exact:
  `traceExtensionSupply_iff` (equivalent to the paired-append lemma, neither an over- nor
  an under-ask).  Refuted as automatically available — the left witness's internal clause
  chooses its fresh-cell labels freely (`HomogeneityFalsify`, `origin/e7/homogeneity-falsify`).
* `JointTraceSupply` — the pre-authorized weakening (PR #196): the paired events chosen
  JOINTLY — some left cover through the scheduled point whose source reduction is
  right-realizable.  Strictly weaker (`jointTraceSupply_of_traceExtensionSupply`); exact
  (`jointTraceSupply_iff_absorb`, equivalent to the absorption lemma).
* `MenuIntersectionSupply` — **the final compiled residual, verbatim**: for every paired
  construction trace and prescribed fresh point on either side (the mirrored form is the
  same Prop at `s.swap`), the two SOURCE-realized menus (`sourceMenuAt` / `sourceMenu`)
  contain a common reduced labelled extension.  `menuIntersection_iff_jointSupply`: the
  lift through the literal reduct links loses nothing — the residual is a SOURCE-to-SOURCE
  question with existential freedom on both sides.
* `exists_seed_iso_of_menuIntersection` — the boundary record, a CONDITIONAL theorem:
  equal complete codes yield a paired seed for which two-sided menu intersection is the
  ONLY hypothesis missing for `Nonempty (R₁.Iso R₂)`.  What is proved outright is the
  complete conditional bridge (seed, chart projections, forth/back bookkeeping, the
  countable Karp theorem); `MenuIntersectionSupply` itself is NOT proved anywhere — it is
  the open residual, and this module does not solve the classification.  The bridge's
  compiled cone is exactly the trace-generated chart family (`traceFamily`, forth/back
  under the joint supply) fed to the mainline Karp bridge
  (`nonempty_iso_of_commonCharts`); nothing quarantined is consumed.

Packaging note (tested 2026-08-26): repackaging `traceFamily` as IL v2.1.0's
`ExtensionPresentation` (State n = traced node + length-`n` projection) compiles but is
NOT smaller — `ExtensionPresentation` has no `symm`, so back duplicates the forth
bookkeeping (here derived from forth via `traceFamily_swap_mem`), and the
`stageLang`/`SameAtomicType` instance plumbing that `nonempty_iso_of_commonCharts`
encapsulates would move into this module.  Since PR #193 that mainline bridge already
routes through `PotentialIso.ofExtensionFamily`/`countable_toEquiv`, so the v2.1.0 API is
in the compiled path either way; the set-based family is kept.

## The terminal ruling (do NOT reopen from inside the construction)

Do NOT launch another proof of `MenuIntersectionSupply` from STP, genSat, failure
certificates, or code equality: the compiled audit (PRs #194–#196) shows those provably
leave the fresh-coordinate labels free —

* STP populates both menus but synchronizes nothing: its extension point, scheme, and every
  non-top fresh cell are its witness's own (one `⊤`-cell constrained, nothing aimed at a
  scheduled point);
* genSat pins the extension SCHEME jointly, and only the scheme (`GenSatFamily D` fixes no
  fresh-cell label value);
* bottomPattern pins the `⊥`/non-`⊥` PATTERN at grades `≤ n` jointly, never the ordinal
  values, and says nothing at grade `n + 1`;
* uniformity / highGradeDominance window a single cell each; neither pins a value;
* equal complete codes are blind beyond the finite seed payload.

With the base face pinned unconditionally (`red_agree_on_base`) the exact unpinned freedom
is the label VALUE at every cell meeting a fresh coordinate.  Proving menu intersection
requires GENUINELY NEW model theory, not construction rearrangement.  This does not declare
the theorem false — the architecture reduced it as far as its hypotheses permit.

**Reopen conditions** (only on genuinely new input):
1. a producer-built subclass representing every source isomorphism class with common menus;
2. a Knight-VC selected-extension theorem determining the reduced coface from shared finite
   provenance;
3. a descriptive-set-theoretic boundedness theorem bypassing fixed-rank classification.

**Morleyization guard**: Morleyization, atomicity, or Scott coding alone only RENAME menu
intersection (a common complete theory with uniform isolation already contains the
empty-chart and one-point transfer obligations); progress requires a concrete extension
selector or a boundedness theorem.

**Mainline placement**: NOT root-exported (the `TopProduction`/`StoppedReceipt` precedent) —
the statements are construction-facing (stopped witnesses, receipts), not clean model-level
theorems; but the module is mainline and fully compiled, imports only mainline modules
(`Knight/PairedTrace.lean`, `Knight/ChartKarp.lean`), and is covered by the build and the
axiom audit. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

/-! ### The source-realized extension menus -/

section Menus

variable {M : Type w} {n k : ℕ}

/-- **The scheduled-point menu** of a source over a base tuple `t₀` along the embedding
`f`: the stage-`ω` labels the source actually evaluates over some extension of `t₀` along
`f` CONTAINING the scheduled point `x`.  The left freedom of the joint choice: which
carrier tuple through `x` — the label over each tuple is the source's own (`eval` is a
function). -/
def sourceMenuAt (R : KnightRealization (blockStage 0) M) (t₀ : Fin n ↪ M) (x : M)
    (f : Fin n ↪ Fin k) : Set (S (blockStage 0).1 k) :=
  {σ | ∃ t : Fin k ↪ M, f.trans t = t₀ ∧ (∃ i : Fin k, t i = x) ∧ R.eval t = some σ}

/-- **The free menu** of a source over a base tuple along an embedding: the stage-`ω`
labels evaluated over SOME extension — the right freedom (no constraint beyond the
base). -/
def sourceMenu (R : KnightRealization (blockStage 0) M) (t₀ : Fin n ↪ M)
    (f : Fin n ↪ Fin k) : Set (S (blockStage 0).1 k) :=
  {σ | ∃ t : Fin k ↪ M, f.trans t = t₀ ∧ R.eval t = some σ}

end Menus

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁} {R₂ : KnightRealization (blockStage 0) M₂}

/-! ### The independent-choice residual and its exactness -/

/-- **The independent-choice residual** (PR #195's verdict (b); NOT proved anywhere —
provably EXACTLY the missing datum, `traceExtensionSupply_iff`): whenever a traced node's
left cover extends to an actually evaluated left cover along an embedding, the right
witness actually evaluates a matching cover — same arity, same shared embedding over the
node's right occurrence, and source reduction EQUAL to the left cover's.  The base-face
cells of that demanded reduction are pinned unconditionally (`red_agree_on_base`); what
this Prop genuinely adds is the label at the cells meeting the FRESH coordinates — the
cells the left witness's internal clause chose freely.  This is RightRealizationSupply
localized to based traces. -/
def TraceExtensionSupply (s : PairedCover hβ₁ hβ₂ W₁ W₂) : Prop :=
  ∀ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) →
    ∀ ⦃k : ℕ⦄ (f : Fin nd.arity ↪ Fin k) (t : Fin k ↪ M₁) (T : S β₁.1 k),
      f.trans t = nd.tuple₁ → W₁.eval t = some T →
      ∃ (t' : Fin k ↪ M₂) (T' : S β₂.1 k),
        f.trans t' = nd.tuple₂ ∧ W₂.eval t' = some T' ∧
        reduceType (blockStage 0).2 hβ₂ T' = reduceType (blockStage 0).2 hβ₁ T

/-- **The decisive lemma, conditional direction**: under the supply, a traced node plus one
actually evaluated left cover extension appends to a paired trace node with THAT left cover —
the appended step's data is the shared embedding (`PairedStep.ofEmb`). -/
theorem pairedTrace_append_of_supply (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent) {s : PairedCover hβ₁ hβ₂ W₁ W₂}
    (hs : TraceExtensionSupply s) {nd : PairedCover hβ₁ hβ₂ W₁ W₂}
    (tr : PairedTrace s nd) {k : ℕ} (f : Fin nd.arity ↪ Fin k) (t : Fin k ↪ M₁)
    (T : S β₁.1 k) (h₁ : f.trans t = nd.tuple₁) (hT : W₁.eval t = some T) :
    ∃ (t' : Fin k ↪ M₂) (T' : S β₂.1 k) (hT' : W₂.eval t' = some T')
      (hred : reduceType (blockStage 0).2 hβ₁ T = reduceType (blockStage 0).2 hβ₂ T'),
      f.trans t' = nd.tuple₂ ∧
      Nonempty (PairedTrace s ⟨k, t, t', T, T', hT, hT', hred⟩) := by
  obtain ⟨t', T', h₂, hT', hred⟩ := hs nd ⟨tr⟩ f t T h₁ hT
  exact ⟨t', T', hT', hred.symm, h₂,
    ⟨tr.step (PairedStep.ofEmb hW₁c hW₂c f h₁ h₂)⟩⟩

/-- **Exactness of the residual**: the supply holds IFF every traced node and every left
cover extension admits a paired appended trace node with that exact left cover — the
compiled statement is neither an over-ask nor an under-ask. -/
theorem traceExtensionSupply_iff (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent) (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    TraceExtensionSupply s ↔
      ∀ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) →
        ∀ ⦃k : ℕ⦄ (f : Fin nd.arity ↪ Fin k) (t : Fin k ↪ M₁) (T : S β₁.1 k)
          (hT : W₁.eval t = some T), f.trans t = nd.tuple₁ →
          ∃ (t' : Fin k ↪ M₂) (T' : S β₂.1 k) (hT' : W₂.eval t' = some T')
            (hred : reduceType (blockStage 0).2 hβ₁ T
              = reduceType (blockStage 0).2 hβ₂ T'),
            f.trans t' = nd.tuple₂ ∧
            Nonempty (PairedTrace s ⟨k, t, t', T, T', hT, hT', hred⟩) := by
  constructor
  · intro hs nd htr k f t T hT h₁
    obtain ⟨tr⟩ := htr
    exact pairedTrace_append_of_supply hW₁c hW₂c hs tr f t T h₁ hT
  · intro h nd htr k f t T h₁ hT
    obtain ⟨t', T', hT', hred, h₂, -⟩ := h nd htr f t T hT h₁
    exact ⟨t', T', h₂, hT', hred.symm⟩

/-! ### The joint-choice supply and its exactness -/

/-- **The joint-choice residual** (the weakening of `TraceExtensionSupply` the decision
matrix pre-authorizes): for every traced node and every scheduled fresh LEFT point, SOME
jointly chosen evaluated pair — a left cover of `W₁` CONTAINING the scheduled point and a
right cover of `W₂`, extending the node's two occurrences under ONE shared embedding, with
EQUAL COMPLETE source reductions.  The left cover is existential (the joint freedom), not
universal (the refuted independent form). -/
def JointTraceSupply (s : PairedCover hβ₁ hβ₂ W₁ W₂) : Prop :=
  ∀ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) → ∀ x : M₁,
    ∃ (k : ℕ) (f : Fin nd.arity ↪ Fin k) (t : Fin k ↪ M₁) (T : S β₁.1 k)
      (t' : Fin k ↪ M₂) (T' : S β₂.1 k),
      f.trans t = nd.tuple₁ ∧ W₁.eval t = some T ∧ (∃ i : Fin k, t i = x) ∧
      f.trans t' = nd.tuple₂ ∧ W₂.eval t' = some T' ∧
      reduceType (blockStage 0).2 hβ₁ T = reduceType (blockStage 0).2 hβ₂ T'

/-- The independent supply implies the joint supply (choose the left cover by `W₁`'s own
directedness through the scheduled point, then transfer): the joint form is a genuine
weakening. -/
theorem jointTraceSupply_of_traceExtensionSupply (hW₁ : W₁.IsModel)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} (hs : TraceExtensionSupply s) :
    JointTraceSupply s := by
  intro nd htr x
  obtain ⟨y, ⟨f, hft, hfp⟩, g, hg⟩ := hW₁.exists_labelledExt_le nd.left
    ⟨fun _ : Fin 1 => x, fun i j _ => Subsingleton.elim i j⟩
  obtain ⟨t', T', h₂, hT', hred⟩ := hs nd htr f y.tuple y.type hft y.eval_eq
  exact ⟨y.arity, f, y.tuple, y.type, t', T', hft, y.eval_eq,
    ⟨g 0, congrArg (fun e : Fin 1 ↪ M₁ => e 0) hg⟩, h₂, hT', hred.symm⟩

/-- **The decisive lemma under the joint supply**: a traced node plus one scheduled fresh
left point admits a paired appended producer event containing the point.  Consistency of
the two witnesses alone suffices — the supply carries its own left event (the independent
form needed `W₁.IsModel` to manufacture one). -/
theorem pairedTrace_absorb_of_jointSupply (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent) {s : PairedCover hβ₁ hβ₂ W₁ W₂}
    (hs : JointTraceSupply s) {nd : PairedCover hβ₁ hβ₂ W₁ W₂}
    (tr : PairedTrace s nd) (x : M₁) :
    ∃ (nd' : PairedCover hβ₁ hβ₂ W₁ W₂) (_ : PairedStep nd nd'),
      (∃ i : Fin nd'.arity, nd'.tuple₁ i = x) ∧ Nonempty (PairedTrace s nd') := by
  obtain ⟨k, f, t, T, t', T', h₁, hT, hx, h₂, hT', hred⟩ := hs nd ⟨tr⟩ x
  exact ⟨⟨k, t, t', T, T', hT, hT', hred⟩, PairedStep.ofEmb hW₁c hW₂c f h₁ h₂, hx,
    ⟨tr.step (PairedStep.ofEmb hW₁c hW₂c f h₁ h₂)⟩⟩

/-- **Exactness of the weakening**: the joint supply holds IFF every traced node and every
scheduled fresh left point admits a paired appended trace node containing the point — the
joint-choice residual is EQUIVALENT to the absorption lemma, neither an over-ask nor an
under-ask. -/
theorem jointTraceSupply_iff_absorb (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent) (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    JointTraceSupply s ↔
      ∀ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) → ∀ x : M₁,
        ∃ (nd' : PairedCover hβ₁ hβ₂ W₁ W₂) (_ : PairedStep nd nd'),
          (∃ i : Fin nd'.arity, nd'.tuple₁ i = x) ∧ Nonempty (PairedTrace s nd') := by
  constructor
  · intro hs nd htr x
    obtain ⟨tr⟩ := htr
    exact pairedTrace_absorb_of_jointSupply hW₁c hW₂c hs tr x
  · intro h nd htr x
    obtain ⟨nd', st, hx, -⟩ := h nd htr x
    exact ⟨nd'.arity, st.emb, nd'.tuple₁, nd'.type₁, nd'.tuple₂, nd'.type₂,
      st.trans₁, nd'.eval₁, hx, st.trans₂, nd'.eval₂, nd'.red_eq⟩

/-! ### The menu-intersection form: the residual is source-to-source -/

/-- **THE FINAL COMPILED RESIDUAL** (the terminal theorem of the provenance/Karp
classification route — see the module docstring): for every paired construction trace and
prescribed fresh point on either side — the mirrored side is this Prop at `s.swap` — the
two source-realized menus contain a common reduced labelled extension.  Equal to the joint
supply (`menuIntersection_iff_jointSupply`) through the literal reduct links, so the
residual is a source-to-source common-labelled-extension question with existential freedom
on BOTH sides — the irreducible cross-model content of the classification. -/
def MenuIntersectionSupply (R₁ : KnightRealization (blockStage 0) M₁)
    (R₂ : KnightRealization (blockStage 0) M₂) (s : PairedCover hβ₁ hβ₂ W₁ W₂) : Prop :=
  ∀ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) → ∀ x : M₁,
    ∃ (k : ℕ) (f : Fin nd.arity ↪ Fin k),
      (sourceMenuAt R₁ nd.tuple₁ x f ∩ sourceMenu R₂ nd.tuple₂ f).Nonempty

/-- **The lift loses nothing**: the menu-intersection property of the SOURCES is exactly
the joint supply of the WITNESSES — up through `eval_reduct_eq_some` (both lifted labels
reduce to the common menu element), down through `reduct_eval`. -/
theorem menuIntersection_iff_jointSupply (hred₁ : W₁.reduct hβ₁ = R₁)
    (hred₂ : W₂.reduct hβ₂ = R₂) (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    MenuIntersectionSupply R₁ R₂ s ↔ JointTraceSupply s := by
  constructor
  · intro hs nd htr x
    obtain ⟨k, f, σ, ⟨t, h₁, hx, ht⟩, t', h₂, ht'⟩ := hs nd htr x
    have ht₁ : (W₁.reduct hβ₁).eval t = some σ := by rw [hred₁]; exact ht
    obtain ⟨T, hT, hTred⟩ := eval_reduct_eq_some hβ₁ ht₁
    have ht₂ : (W₂.reduct hβ₂).eval t' = some σ := by rw [hred₂]; exact ht'
    obtain ⟨T', hT', hT'red⟩ := eval_reduct_eq_some hβ₂ ht₂
    exact ⟨k, f, t, T, t', T', h₁, hT, hx, h₂, hT', hTred.trans hT'red.symm⟩
  · intro hs nd htr x
    obtain ⟨k, f, t, T, t', T', h₁, hT, hx, h₂, hT', hred⟩ := hs nd htr x
    refine ⟨k, f, reduceType (blockStage 0).2 hβ₁ T, ⟨t, h₁, hx, ?_⟩, t', h₂, ?_⟩
    · rw [← hred₁, Realization.reduct_eval, hT]; rfl
    · rw [hred, ← hred₂, Realization.reduct_eval, hT']; rfl

/-! ### The trace-generated chart family and the conditional pipeline

The minimal compiled cone of the boundary record: the σ-projections of traced nodes form
exactly the family the mainline Karp bridge consumes, with forth/back one appended producer
transition under the joint supply.  Only the JOINT versions are re-homed — the
independent-supply duplicates stay on `origin/e7/based-karp` (they follow from these via
`jointTraceSupply_of_traceExtensionSupply`). -/

/-- **The trace-generated chart family** — the σ-projections of traced nodes: exactly the
membership shape `HasCommonChart` and the Karp bridge consume.  State = the paired
construction provenance (the traced node with its projection). -/
def traceFamily (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    Set (Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) :=
  {x | ∃ nd : PairedCover hβ₁ hβ₂ W₁ W₂, Nonempty (PairedTrace s nd) ∧
    ∃ σ : Fin x.1 → Fin nd.arity, nd.tuple₁ ∘ σ = x.2.1 ∧ nd.tuple₂ ∘ σ = x.2.2}

/-- The empty pair is a projection of the seed. -/
theorem traceFamily_empty_mem (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ traceFamily s :=
  ⟨s, ⟨.refl⟩, fun i => i.elim0, funext fun i => i.elim0, funext fun i => i.elim0⟩

/-- Every family member carries a common projected chart of the SOURCES — the shared
source label of its traced node, through the literal reduct links. -/
theorem traceFamily_commonChart (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} :
    ∀ x ∈ traceFamily s, HasCommonChart R₁ R₂ x.2.1 x.2.2 := by
  rintro x ⟨nd, -, σ, hσ₁, hσ₂⟩
  exact ⟨nd.arity, nd.tuple₁, nd.tuple₂, σ, nd.sourceType,
    nd.source_eval₁ hred₁, nd.source_eval₂ hred₂, hσ₁, hσ₂⟩

/-- Mirroring the family: back is symmetry. -/
theorem traceFamily_swap_mem {s : PairedCover hβ₁ hβ₂ W₁ W₂}
    {x : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)} (hx : x ∈ traceFamily s) :
    (⟨x.1, x.2.2, x.2.1⟩ : Σ n : ℕ, (Fin n → M₂) × (Fin n → M₁)) ∈ traceFamily s.swap := by
  obtain ⟨nd, ⟨tr⟩, σ, hσ₁, hσ₂⟩ := hx
  exact ⟨nd.swap, ⟨tr.swap⟩, σ, hσ₂, hσ₁⟩

/-- Forth under the joint supply: one appended jointly chosen producer event extends any
family member by the scheduled fresh left point and its produced right partner. -/
theorem traceFamily_forth_of_jointSupply (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} (hs : JointTraceSupply s) :
    ∀ x ∈ traceFamily s, ∀ m : M₁, ∃ n' : M₂,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ traceFamily s := by
  rintro ⟨k, a, b⟩ ⟨nd, ⟨tr⟩, σ, hσ₁, hσ₂⟩ m
  obtain ⟨nd', st, ⟨i, hi⟩, ⟨tr'⟩⟩ := pairedTrace_absorb_of_jointSupply hW₁c hW₂c hs tr m
  refine ⟨nd'.tuple₂ i, nd', ⟨tr'⟩, Fin.snoc (fun j => st.emb (σ j)) i,
    funext fun j => ?_, funext fun j => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
      exact hi
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (DFunLike.congr_fun st.trans₁ (σ j)).trans (congrFun hσ₁ j)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (DFunLike.congr_fun st.trans₂ (σ j)).trans (congrFun hσ₂ j)

/-- Back under the mirrored joint supply: symmetry of the construction. -/
theorem traceFamily_back_of_jointSupply (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} (hs : JointTraceSupply s.swap) :
    ∀ x ∈ traceFamily s, ∀ n' : M₂, ∃ m : M₁,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ traceFamily s := by
  intro x hx n'
  obtain ⟨m, hm⟩ :=
    traceFamily_forth_of_jointSupply hW₂c hW₁c hs _ (traceFamily_swap_mem hx) n'
  exact ⟨m, traceFamily_swap_mem hm⟩

/-- **The conditional headline under the joint supply**: code-matched stopped witnesses
with a paired seed and the TWO-SIDED joint supply yield an isomorphism of the sources —
the trace family fed to the mainline Karp bridge (`nonempty_iso_of_commonCharts`; the
alternating enumeration and formula induction live in `InfinitaryLogic`).  Conditional:
the two supply hypotheses are the open residual, not proved anywhere. -/
theorem nonempty_iso_of_jointTraceSupply [Countable M₁] [Countable M₂]
    (hW₁ : W₁.IsModel) (hW₂ : W₂.IsModel)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂)
    (s : PairedCover hβ₁ hβ₂ W₁ W₂)
    (hforth : JointTraceSupply s) (hback : JointTraceSupply s.swap) :
    Nonempty (R₁.Iso R₂) := by
  have hR₁c : R₁.IsExactParentConsistent := hred₁ ▸ hW₁.consistent.reduct hβ₁
  have hR₂c : R₂.IsExactParentConsistent := hred₂ ▸ hW₂.consistent.reduct hβ₂
  exact nonempty_iso_of_commonCharts hR₁c hR₂c (traceFamily s)
    (traceFamily_empty_mem s) (traceFamily_commonChart hred₁ hred₂)
    (traceFamily_forth_of_jointSupply hW₁.consistent hW₂.consistent hforth)
    (traceFamily_back_of_jointSupply hW₁.consistent hW₂.consistent hback)

end KnightRealization
end VaughtConjecture.Knight
