/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockGeometry
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.ChartLanguage

/-! # The paired provenance trace (#57/#47 terminal boundary — vocabulary)

The pairing vocabulary of the based-Karp extension experiment, graduated to main: the
construction-private relation between two code-matched stopped witnesses whose members are
concrete per-node data — never `HasCommonChart` certificates.  This implements the #178
correction: *provenance constructs the relation; `HasCommonChart` is only a projection*
(`PairedCover.hasCommonChart_sources`).

Provenance: re-homed verbatim (minus the quarantined `HighCandidate` context) from
`VaughtConjecture/Knight/BasedKarp.lean` on `origin/e7/based-karp` (PR #195); the
`exactParent_typeMap` spelling is re-proved from mainline material (it was a one-line
unfolding in `PartialDensity.lean` on `origin/e7/high-candidate`, PR #194).  The supplies
and the compiled equivalence over this vocabulary are `Knight/TraceBoundary.lean`.

## The pairing objects

* `PairedCover` — one node: a common finite arity, one labelled cover of each witness
  (`W₁.LabelledExt` / `W₂.LabelledExt` data, unbundled to share the arity), and the single
  cross-model field `red_eq`: the two labels have EQUAL source reductions (a carrier-free
  stage type at `blockStage 0`).  Target-stage labels are NOT compared — only their
  reductions enter the chart projection, and the witnesses may sit at different stages.
* `PairedStep` — one trace letter: ONE shared embedding under which both covers restrict to
  the previous node, tuples and labels.  The label restrictions are DERIVED data:
  `PairedStep.ofEmb` shows exact parent consistency of the two witnesses reconstructs them
  from the tuple restrictions alone, so the genuine step datum is the shared embedding.
* `PairedTrace` — the construction-private provenance word: the reflexive-transitive
  data-carrying closure of `PairedStep` from a seed node.  `PairedTrace.seed_le` projects the
  composite shared embedding (every traced node carries the seed as a matched face);
  `PairedTrace.swap` mirrors a trace (back = symmetry, as the producer-word design demands).
* Seeding (`exists_pairedSeed_of_code_matched`): two stopped receipts with EQUAL COMPLETE
  codes (`StopCode`: run level, cutoff, both source labels, `⊤`-witness) seed the relation —
  the receipt face pair and copy pair, matched by code equality through the literal
  `reduct_base` links, with the shared embedding `Fin.castSuccEmb` between them.  Membership
  is by construction only; no `HasCommonChart` premise anywhere.

## The unconditional transfer content

`red_agree_on_base`: for ANY evaluated right cover extending a node's right occurrence along
the shared embedding, its source reduction agrees with the left cover's on EVERY base-face
cell — exact parent consistency of both witnesses plus the node's `red_eq`.  Whatever
residual transfer question is asked of a paired trace (`Knight/TraceBoundary.lean`) is
therefore confined to the label cells meeting the FRESH coordinates.

**Mainline placement**: this module is deliberately NOT root-exported (the
`TopProduction`/`StoppedReceipt` precedent): it is construction-facing vocabulary, imported
by `Knight/TraceBoundary.lean`.  It imports only mainline modules. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

/-- Exact parent consistency, `typeMap`-spelled (the tower's `pull` is `typeMap`,
definitionally).  Re-proved from the mainline definition; the original one-liner is
`PartialDensity.lean` on `origin/e7/high-candidate` (PR #194). -/
theorem exactParent_typeMap {γ : LimitStage} {M : Type w} {B : KnightRealization γ M}
    (hB : B.IsExactParentConsistent) {n k : ℕ} (t : Fin n ↪ M) (q : S γ.1 n)
    (f : Fin k ↪ Fin n) (hq : B.eval t = some q) : B.eval (f.trans t) = typeMap f q :=
  hB t q f hq

/-! ### The paired node: two labelled covers with equal source reductions -/

/-- **One node of the paired provenance trace**: a labelled cover of each witness at one
common finite arity, whose labels have EQUAL source reductions — the single cross-model
field, a carrier-free stage type at the base stage.  Target-stage labels are never compared
(the witnesses may even sit at different stages); everything the chart projection consumes
is the shared reduction.  Membership in the pairing relation is by construction
(`PairedTrace`), never by `HasCommonChart` — the chart certificate is the PROJECTION
`hasCommonChart_sources`. -/
structure PairedCover {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
    (hβ₁ : blockStage 0 ≤ β₁) (hβ₂ : blockStage 0 ≤ β₂)
    (W₁ : KnightRealization β₁ M₁) (W₂ : KnightRealization β₂ M₂) where
  /-- The common finite arity of the two covers. -/
  arity : ℕ
  /-- The left occurrence. -/
  tuple₁ : Fin arity ↪ M₁
  /-- The right occurrence. -/
  tuple₂ : Fin arity ↪ M₂
  /-- The left target-stage label. -/
  type₁ : S β₁.1 arity
  /-- The right target-stage label. -/
  type₂ : S β₂.1 arity
  /-- The left cover is actually evaluated in the left witness. -/
  eval₁ : W₁.eval tuple₁ = some type₁
  /-- The right cover is actually evaluated in the right witness. -/
  eval₂ : W₂.eval tuple₂ = some type₂
  /-- **The matching field**: the two labels have equal source reductions. -/
  red_eq : reduceType (blockStage 0).2 hβ₁ type₁ = reduceType (blockStage 0).2 hβ₂ type₂

namespace PairedCover

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁} {R₂ : KnightRealization (blockStage 0) M₂}

/-- The left cover, as a labelled cover of the left witness. -/
def left (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : W₁.LabelledExt :=
  ⟨nd.arity, nd.tuple₁, nd.type₁, nd.eval₁⟩

/-- The right cover, as a labelled cover of the right witness. -/
def right (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : W₂.LabelledExt :=
  ⟨nd.arity, nd.tuple₂, nd.type₂, nd.eval₂⟩

/-- The shared source label of the node — the common reduction. -/
noncomputable def sourceType (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : S (blockStage 0).1 nd.arity :=
  reduceType (blockStage 0).2 hβ₁ nd.type₁

/-- The shared source label read from the right side. -/
theorem sourceType_eq_right (nd : PairedCover hβ₁ hβ₂ W₁ W₂) :
    nd.sourceType = reduceType (blockStage 0).2 hβ₂ nd.type₂ :=
  nd.red_eq

/-- The left source realizes the shared source label over the left occurrence — read
through the literal reduct link. -/
theorem source_eval₁ (nd : PairedCover hβ₁ hβ₂ W₁ W₂) (hred₁ : W₁.reduct hβ₁ = R₁) :
    R₁.eval nd.tuple₁ = some nd.sourceType := by
  rw [← hred₁, Realization.reduct_eval, nd.eval₁]; rfl

/-- The right source realizes the SAME shared source label over the right occurrence. -/
theorem source_eval₂ (nd : PairedCover hβ₁ hβ₂ W₁ W₂) (hred₂ : W₂.reduct hβ₂ = R₂) :
    R₂.eval nd.tuple₂ = some nd.sourceType := by
  rw [← hred₂, Realization.reduct_eval, nd.eval₂, sourceType_eq_right]; rfl

/-- **The chart projection** — a theorem about paired nodes, never a premise: the two
source occurrences carry one common full chart, the shared source label. -/
theorem hasCommonChart_sources (nd : PairedCover hβ₁ hβ₂ W₁ W₂)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂) :
    HasCommonChart R₁ R₂ nd.tuple₁ nd.tuple₂ :=
  hasCommonChart_of_eval_eq_some (nd.source_eval₁ hred₁) (nd.source_eval₂ hred₂)

/-- The mirrored node: back is symmetry. -/
def swap (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : PairedCover hβ₂ hβ₁ W₂ W₁ :=
  ⟨nd.arity, nd.tuple₂, nd.tuple₁, nd.type₂, nd.type₁, nd.eval₂, nd.eval₁, nd.red_eq.symm⟩

@[simp] theorem swap_swap (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : nd.swap.swap = nd := rfl

@[simp] theorem swap_arity (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : nd.swap.arity = nd.arity := rfl

@[simp] theorem swap_tuple₁ (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : nd.swap.tuple₁ = nd.tuple₂ :=
  rfl

@[simp] theorem swap_tuple₂ (nd : PairedCover hβ₁ hβ₂ W₁ W₂) : nd.swap.tuple₂ = nd.tuple₁ :=
  rfl

end PairedCover

/-! ### The paired step and the provenance trace -/

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁} {R₂ : KnightRealization (blockStage 0) M₂}

/-- **One trace letter**: both covers of the new node restrict to the old node under ONE
shared embedding — tuples and labels.  The genuine datum is the shared embedding: the label
restrictions are reconstructed from the tuple restrictions by exact parent consistency
(`ofEmb`), and each side separately is the labelled-cover order of its witness (`left_le` /
`right_le`). -/
structure PairedStep (nd nd' : PairedCover hβ₁ hβ₂ W₁ W₂) where
  /-- The shared embedding of the old node into the new. -/
  emb : Fin nd.arity ↪ Fin nd'.arity
  /-- The left tuples restrict. -/
  trans₁ : emb.trans nd'.tuple₁ = nd.tuple₁
  /-- The left labels restrict. -/
  map₁ : typeMap emb nd'.type₁ = some nd.type₁
  /-- The right tuples restrict — along the SAME embedding. -/
  trans₂ : emb.trans nd'.tuple₂ = nd.tuple₂
  /-- The right labels restrict — along the SAME embedding. -/
  map₂ : typeMap emb nd'.type₂ = some nd.type₂

namespace PairedStep

variable {nd nd' : PairedCover hβ₁ hβ₂ W₁ W₂}

/-- The left projection of a step is the labelled-cover order of the left witness. -/
theorem left_le (st : PairedStep nd nd') : nd.left ≤ nd'.left :=
  ⟨st.emb, st.trans₁, st.map₁⟩

/-- The right projection of a step is the labelled-cover order of the right witness. -/
theorem right_le (st : PairedStep nd nd') : nd.right ≤ nd'.right :=
  ⟨st.emb, st.trans₂, st.map₂⟩

/-- **The label restrictions are derived data**: exact parent consistency of the two
witnesses reconstructs `map₁`/`map₂` from the tuple restrictions alone — the genuine step
datum is the shared embedding.  (In particular target-stage label MATCHING is never a step
obligation.) -/
def ofEmb (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent)
    (emb : Fin nd.arity ↪ Fin nd'.arity) (h₁ : emb.trans nd'.tuple₁ = nd.tuple₁)
    (h₂ : emb.trans nd'.tuple₂ = nd.tuple₂) : PairedStep nd nd' where
  emb := emb
  trans₁ := h₁
  map₁ := by
    have h := exactParent_typeMap hW₁c nd'.tuple₁ nd'.type₁ emb nd'.eval₁
    rw [h₁, nd.eval₁] at h
    exact h.symm
  trans₂ := h₂
  map₂ := by
    have h := exactParent_typeMap hW₂c nd'.tuple₂ nd'.type₂ emb nd'.eval₂
    rw [h₂, nd.eval₂] at h
    exact h.symm

/-- The mirrored step. -/
def swap (st : PairedStep nd nd') : PairedStep nd.swap nd'.swap :=
  ⟨st.emb, st.trans₂, st.map₂, st.trans₁, st.map₁⟩

end PairedStep

/-- **The provenance trace** — the construction-private pairing relation, data-carrying:
the reflexive-transitive closure of `PairedStep` from a seed node.  Each letter records the
appended node and its shared embedding; nothing existential is stored, so the trace survives
elimination and is exactly the State a producer-word/`ExtensionPresentation` packaging
consumes.  Membership is by construction only. -/
inductive PairedTrace (s : PairedCover hβ₁ hβ₂ W₁ W₂) :
    PairedCover hβ₁ hβ₂ W₁ W₂ → Type (max 1 w) where
  /-- The seed is traced. -/
  | refl : PairedTrace s s
  /-- Append one paired step. -/
  | step {a b : PairedCover hβ₁ hβ₂ W₁ W₂} :
      PairedTrace s a → PairedStep a b → PairedTrace s b

namespace PairedTrace

variable {s : PairedCover hβ₁ hβ₂ W₁ W₂}

/-- The mirrored trace: back is symmetry of the construction. -/
def swap : ∀ {nd : PairedCover hβ₁ hβ₂ W₁ W₂},
    PairedTrace s nd → PairedTrace s.swap nd.swap
  | _, .refl => .refl
  | _, .step tr st => .step tr.swap st.swap

/-- **Provenance projection**: every traced node carries the seed as a matched face under
ONE composite shared embedding — tuples and labels, both sides. -/
theorem seed_le {nd : PairedCover hβ₁ hβ₂ W₁ W₂} (tr : PairedTrace s nd) :
    ∃ f : Fin s.arity ↪ Fin nd.arity,
      f.trans nd.tuple₁ = s.tuple₁ ∧ f.trans nd.tuple₂ = s.tuple₂ ∧
      typeMap f nd.type₁ = some s.type₁ ∧ typeMap f nd.type₂ = some s.type₂ := by
  induction tr with
  | refl =>
    exact ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, typeMap_refl _, typeMap_refl _⟩
  | step tr st ih =>
    obtain ⟨f, hf₁, hf₂, hm₁, hm₂⟩ := ih
    refine ⟨f.trans st.emb, ?_, ?_, ?_, ?_⟩
    · rw [Function.Embedding.trans_assoc, st.trans₁]; exact hf₁
    · rw [Function.Embedding.trans_assoc, st.trans₂]; exact hf₂
    · rw [← typeMap_trans f st.emb _ _ st.map₁]; exact hm₁
    · rw [← typeMap_trans f st.emb _ _ st.map₂]; exact hm₂

end PairedTrace

/-! ### Base-face pinning: the unconditional half of any transfer -/

/-- **Base-face pinning, unconditional**: for ANY evaluated right cover extending the
node's right occurrence along the shared embedding, its source reduction agrees with the
left cover's on EVERY base-face cell (`typeMap` along the shared embedding) — exact parent
consistency of both witnesses plus the node's `red_eq`.  Any residual transfer question over
a paired trace (`Knight/TraceBoundary.lean`) is therefore confined to the cells meeting the
fresh coordinates. -/
theorem red_agree_on_base (hW₁c : W₁.IsExactParentConsistent)
    (hW₂c : W₂.IsExactParentConsistent) (nd : PairedCover hβ₁ hβ₂ W₁ W₂) {k : ℕ}
    {f : Fin nd.arity ↪ Fin k} {t : Fin k ↪ M₁} {T : S β₁.1 k}
    (h₁ : f.trans t = nd.tuple₁) (hT : W₁.eval t = some T)
    {t' : Fin k ↪ M₂} {T' : S β₂.1 k}
    (h₂ : f.trans t' = nd.tuple₂) (hT' : W₂.eval t' = some T') :
    typeMap f (reduceType (blockStage 0).2 hβ₂ T')
      = typeMap f (reduceType (blockStage 0).2 hβ₁ T) := by
  have hm₁ : typeMap f T = some nd.type₁ := by
    have h := exactParent_typeMap hW₁c t T f hT
    rw [h₁, nd.eval₁] at h
    exact h.symm
  have hm₂ : typeMap f T' = some nd.type₂ := by
    have h := exactParent_typeMap hW₂c t' T' f hT'
    rw [h₂, nd.eval₂] at h
    exact h.symm
  calc typeMap f (reduceType (blockStage 0).2 hβ₂ T')
      = (typeMap f T').map (reduceType (blockStage 0).2 hβ₂) :=
        typeMap_reduceType_comm (blockStage 0).2 hβ₂ f T'
    _ = some (reduceType (blockStage 0).2 hβ₂ nd.type₂) := by rw [hm₂]; rfl
    _ = some (reduceType (blockStage 0).2 hβ₁ nd.type₁) := congrArg some nd.red_eq.symm
    _ = (typeMap f T).map (reduceType (blockStage 0).2 hβ₁) := by rw [hm₁]; rfl
    _ = typeMap f (reduceType (blockStage 0).2 hβ₁ T) :=
        (typeMap_reduceType_comm (blockStage 0).2 hβ₁ f T).symm

end KnightRealization
end VaughtConjecture.Knight
