module

public import VaughtConjecture.Knight.FairPairedChain
public import VaughtConjecture.Knight.EmptySeedBoundary
public import VaughtConjecture.Knight.CommonChartSupply
public import VaughtConjecture.Knight.SelectedCommonCharts

/-! # The source-level common-chart chain: the lowest classification consumer

**Review-directed graduation, queue item 3** (2026-08-31; scratch-compiled by the
reviewer across two rounds, adapted with credit; graduation review verified the
acceptance test: THE ISOMORPHISM PROOF CONSUMES NO CONSECUTIVE LABEL-MAP
COMPATIBILITY — `FairCommonChartChain` carries only tuple-restriction laws, each family
member's chart certificate uses only its own node's shared source type, and forth/back
are coordinate bookkeeping).

* `CommonChartNode` / `FairCommonChartChain` — one common full source chart per node (no
  higher-stage witness attached); a monotone exhaustive chain with unrelated consecutive
  labels; `nonempty_iso_of_fairCommonChartChain` gives the source isomorphism.
* `CommonChartStepSupply` / `RestrictedCommonChartStepSupply Good` — forcing-lite local
  density (Rasiowa–Sikorski without set-theoretic machinery), and its
  construction-selected restriction: `RestrictedCommonChartStepSupply Good` is THE
  LOWEST CLASSIFICATION PRODUCER; `nonempty_iso_of_commonChartStepSupply_of_isModel` is
  the final boundary with the empty seed from model covering.
* `HeightFlexibleCommonChartExtension` and its adapters — each scheduled step may
  independently choose convenient higher stages and fresh linked witnesses, prove one
  finite paired occurrence, and forget all high data after projecting the next common
  source chart: NO compatibility between successive high witnesses is consumed, so
  persistent high recurrence is off the classification route.
* The paired-occurrence/`ScheduledPairedRun` layer and
  `FairPairedChain.toFairCommonChartChain` — the merged high-witness chain FORGETS onto
  this quotient: its inter-node label maps are certification scaffolding, not consumed
  classification data.

`CommonChartNode` and the step-supply vocabulary live in `Knight/CommonChartSupply.lean`
(re-exported here, names unchanged). The `Nonempty` classification cashouts below go through the
direct selected-chart consumer (`Knight/SelectedCommonCharts.lean`) and build no chain; the chain
constructors remain for applications that want an actual chain.

Not root-exported, like the boundary vocabulary it serves. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower
open Value

universe w

namespace KnightRealization

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁}
variable {R₂ : KnightRealization (blockStage 0) M₂}

/-- The occurrence data before the one genuinely cross-source equation is supplied.
This is the most literal interface a Knight-VC producer can return. -/
structure PairedOccurrences where
  arity : ℕ
  tuple₁ : Fin arity ↪ M₁
  tuple₂ : Fin arity ↪ M₂
  type₁ : S β₁.1 arity
  type₂ : S β₂.1 arity
  eval₁ : W₁.eval tuple₁ = some type₁
  eval₂ : W₂.eval tuple₂ = some type₂

namespace PairedOccurrences

/-- To match two high occurrences, one does not need their high labels to
agree.  The paired consumer asks only for the same owned row scheme and the
same labels after strict reduction to the source stage. -/
theorem reduced_eq_of_scheme_and_truncatedLabels
    (d : PairedOccurrences (W₁ := W₁) (W₂ := W₂))
    (hScheme : d.type₁.scheme = d.type₂.scheme)
    (hLabel : HEq
      (fun c : Cell d.type₁.scheme.scheme =>
        truncExt (blockStage 0).1 (d.type₁.label c))
      (fun c : Cell d.type₂.scheme.scheme =>
        truncExt (blockStage 0).1 (d.type₂.label c))) :
    reduceType (blockStage 0).2 hβ₁ d.type₁ =
      reduceType (blockStage 0).2 hβ₂ d.type₂ :=
  StageType.ext hScheme hLabel

/-- Equality of source reductions is the only cross-source field needed to turn
two evaluated occurrences into a paired cover. -/
def toPairedCover (d : PairedOccurrences (W₁ := W₁) (W₂ := W₂))
    (hred : reduceType (blockStage 0).2 hβ₁ d.type₁ =
      reduceType (blockStage 0).2 hβ₂ d.type₂) :
    PairedCover hβ₁ hβ₂ W₁ W₂ where
  arity := d.arity
  tuple₁ := d.tuple₁
  tuple₂ := d.tuple₂
  type₁ := d.type₁
  type₂ := d.type₂
  eval₁ := d.eval₁
  eval₂ := d.eval₂
  red_eq := hred

/-- The retained-face portion of the source-reduction equation is automatic.
It uses only the old paired cover, the shared embedding, and exact parent
consistency.  Thus a producer's new semantic work is confined to fresh cells. -/
theorem reductions_agree_on_retainedFace
    (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent)
    (nd : PairedCover hβ₁ hβ₂ W₁ W₂)
    (d : PairedOccurrences (W₁ := W₁) (W₂ := W₂))
    (f : Fin nd.arity ↪ Fin d.arity)
    (h₁ : f.trans d.tuple₁ = nd.tuple₁) (h₂ : f.trans d.tuple₂ = nd.tuple₂) :
    typeMap f (reduceType (blockStage 0).2 hβ₂ d.type₂) =
      typeMap f (reduceType (blockStage 0).2 hβ₁ d.type₁) :=
  red_agree_on_base hW₁c hW₂c nd h₁ d.eval₁ h₂ d.eval₂

end PairedOccurrences

/-- The exact construction-facing datum for one successor of a paired node.
The target-label face equations are deliberately absent: exact parent consistency
reconstructs them from the two tuple equations. -/
structure PairedExtensionData
    (nd : PairedCover hβ₁ hβ₂ W₁ W₂) where
  next : PairedCover hβ₁ hβ₂ W₁ W₂
  emb : Fin nd.arity ↪ Fin next.arity
  trans₁ : emb.trans next.tuple₁ = nd.tuple₁
  trans₂ : emb.trans next.tuple₂ = nd.tuple₂

namespace PairedExtensionData

/-- Exact consistency supplies all label-restriction plumbing. -/
def toStep {nd : PairedCover hβ₁ hβ₂ W₁ W₂}
    (d : PairedExtensionData nd)
    (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent) :
    PairedStep nd d.next :=
  PairedStep.ofEmb hW₁c hW₂c d.emb d.trans₁ d.trans₂

end PairedExtensionData

/-- A synchronized run only records what a producer naturally proves at each
scheduled step.  Global coverage is not an input. -/
structure ScheduledPairedRun
    (s : PairedCover hβ₁ hβ₂ W₁ W₂)
    (e : ℕ → M₁ ⊕ M₂) where
  node : ℕ → PairedCover hβ₁ hβ₂ W₁ W₂
  node_zero : node 0 = s
  step : ∀ k, PairedStep (node k) (node (k + 1))
  serves_left : ∀ k x, e k = Sum.inl x →
    ∃ i : Fin (node (k + 1)).arity, (node (k + 1)).tuple₁ i = x
  serves_right : ∀ k y, e k = Sum.inr y →
    ∃ i : Fin (node (k + 1)).arity, (node (k + 1)).tuple₂ i = y

namespace ScheduledPairedRun

/-- Alternating fair scheduling is the entire remaining recursion cashout. -/
def toFair {s : PairedCover hβ₁ hβ₂ W₁ W₂} {e : ℕ → M₁ ⊕ M₂}
    (r : ScheduledPairedRun s e) (he : Function.Surjective e) :
    FairPairedChain s where
  node := r.node
  node_zero := r.node_zero
  step := r.step
  covers_left := by
    intro x
    obtain ⟨k, hk⟩ := he (Sum.inl x)
    obtain ⟨i, hi⟩ := r.serves_left k x hk
    exact ⟨k + 1, i, hi⟩
  covers_right := by
    intro y
    obtain ⟨k, hk⟩ := he (Sum.inr y)
    obtain ⟨i, hi⟩ := r.serves_right k y hk
    exact ⟨k + 1, i, hi⟩

end ScheduledPairedRun

/-- Backward cashout: the scheduled-run interface already reaches the merged
classification theorem; no WAP, menu, or transcript datum appears. -/
theorem nonempty_iso_of_scheduledPairedRun [Countable M₁] [Countable M₂]
    (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} {e : ℕ → M₁ ⊕ M₂}
    (r : ScheduledPairedRun s e) (he : Function.Surjective e) :
    Nonempty (R₁.Iso R₂) :=
  nonempty_iso_of_fairPairedChain hW₁c hW₂c hred₁ hred₂ (r.toFair he)

/-! ## A still smaller, source-level consumer

The proof of `nonempty_iso_of_fairPairedChain` does not consume the label-map
fields of `PairedStep`.  It only consumes a monotone sequence of common source
charts.  The following direct formulation makes that quotient explicit; its nodes
are the `CommonChartNode`s of `Knight/CommonChartSupply.lean`. -/

variable {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- A monotone exhaustive chain of common source charts.  Consecutive chart
labels need not be related: only their tuple coordinates are retained. -/
structure FairCommonChartChain where
  node : ℕ → CommonChartNode (A₁ := A₁) (A₂ := A₂)
  emb : ∀ k, Fin (node k).arity ↪ Fin (node (k + 1)).arity
  trans₁ : ∀ k, (emb k).trans (node (k + 1)).tuple₁ = (node k).tuple₁
  trans₂ : ∀ k, (emb k).trans (node (k + 1)).tuple₂ = (node k).tuple₂
  covers_left : ∀ x : M₁, ∃ (k : ℕ) (i : Fin (node k).arity), (node k).tuple₁ i = x
  covers_right : ∀ y : M₂, ∃ (k : ℕ) (i : Fin (node k).arity), (node k).tuple₂ i = y

/-! ## Height-flexible certification scaffolding

The source-level consumer never compares the higher witnesses used at two
successive construction steps.  A producer may therefore choose fresh stages
and fresh linked witnesses for each scheduled requirement, prove one paired
occurrence there, and immediately forget them after projecting its common
source chart.  This is strictly an adapter statement: it does not construct
the paired occurrence. -/

/-- A literal reduct link automatically supplies the source evaluation field
used below.  It is included in the structure only to avoid dependent transport
noise, not as additional producer mathematics. -/
theorem sourceEval_of_linked {A B : LimitStage} {N : Type w}
    {R : KnightRealization A N} {W : KnightRealization B N}
    (h : A ≤ B) (hred : W.reduct h = R) {n : ℕ} {t : Fin n ↪ N}
    {q : S B.1 n} (hq : W.eval t = some q) :
    R.eval t = some (reduceType A.2 h q) := by
  have hfun : (W.reduct h).eval t = R.eval t :=
    congrArg (fun X : KnightRealization A N => X.eval t) hred
  rw [← hfun, Realization.reduct_eval, hq]
  rfl

/-- One common-chart extension certified at arbitrary convenient higher
stages.  The stages and witnesses are existential scaffolding local to this
single step. -/
structure HeightFlexibleCommonChartExtension
    (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (z : M₁ ⊕ M₂) where
  β₁ : LimitStage
  β₂ : LimitStage
  hβ₁ : α ≤ β₁
  hβ₂ : α ≤ β₂
  W₁ : KnightRealization β₁ M₁
  W₂ : KnightRealization β₂ M₂
  reduct₁ : W₁.reduct hβ₁ = A₁
  reduct₂ : W₂.reduct hβ₂ = A₂
  arity : ℕ
  tuple₁ : Fin arity ↪ M₁
  tuple₂ : Fin arity ↪ M₂
  type₁ : S β₁.1 arity
  type₂ : S β₂.1 arity
  eval₁ : W₁.eval tuple₁ = some type₁
  eval₂ : W₂.eval tuple₂ = some type₂
  reduced_eq :
    reduceType α.2 hβ₁ type₁ = reduceType α.2 hβ₂ type₂
  source_eval₁ : A₁.eval tuple₁ = some (reduceType α.2 hβ₁ type₁)
  source_eval₂ : A₂.eval tuple₂ = some (reduceType α.2 hβ₂ type₂)
  emb : Fin nd.arity ↪ Fin arity
  trans₁ : emb.trans tuple₁ = nd.tuple₁
  trans₂ : emb.trans tuple₂ = nd.tuple₂
  serves_left : ∀ x, z = Sum.inl x → ∃ i, tuple₁ i = x
  serves_right : ∀ y, z = Sum.inr y → ∃ i, tuple₂ i = y

namespace HeightFlexibleCommonChartExtension

/-- **The smart constructor**: the source evaluations are DERIVED from the reduct links
(`sourceEval_of_linked`) — a producer supplies only the linked witnesses, the finite
occurrence, its reduced-label equality, the restriction, and the served point; the
`source_eval` fields are never independent obligations. -/
noncomputable def ofLinked {nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)} {z : M₁ ⊕ M₂}
    (β₁ β₂ : LimitStage) (hβ₁ : α ≤ β₁) (hβ₂ : α ≤ β₂)
    (W₁ : KnightRealization β₁ M₁) (W₂ : KnightRealization β₂ M₂)
    (reduct₁ : W₁.reduct hβ₁ = A₁) (reduct₂ : W₂.reduct hβ₂ = A₂)
    (arity : ℕ) (tuple₁ : Fin arity ↪ M₁) (tuple₂ : Fin arity ↪ M₂)
    (type₁ : S β₁.1 arity) (type₂ : S β₂.1 arity)
    (eval₁ : W₁.eval tuple₁ = some type₁) (eval₂ : W₂.eval tuple₂ = some type₂)
    (reduced_eq : reduceType α.2 hβ₁ type₁ = reduceType α.2 hβ₂ type₂)
    (emb : Fin nd.arity ↪ Fin arity)
    (trans₁ : emb.trans tuple₁ = nd.tuple₁) (trans₂ : emb.trans tuple₂ = nd.tuple₂)
    (serves_left : ∀ x, z = Sum.inl x → ∃ i, tuple₁ i = x)
    (serves_right : ∀ y, z = Sum.inr y → ∃ i, tuple₂ i = y) :
    HeightFlexibleCommonChartExtension nd z :=
  { β₁ := β₁, β₂ := β₂, hβ₁ := hβ₁, hβ₂ := hβ₂, W₁ := W₁, W₂ := W₂
    reduct₁ := reduct₁, reduct₂ := reduct₂
    arity := arity, tuple₁ := tuple₁, tuple₂ := tuple₂
    type₁ := type₁, type₂ := type₂, eval₁ := eval₁, eval₂ := eval₂
    reduced_eq := reduced_eq
    source_eval₁ := sourceEval_of_linked hβ₁ reduct₁ eval₁
    source_eval₂ := sourceEval_of_linked hβ₂ reduct₂ eval₂
    emb := emb, trans₁ := trans₁, trans₂ := trans₂
    serves_left := serves_left, serves_right := serves_right }

/-- Forget the per-step higher stages and witnesses. -/
noncomputable def toCommonChartExtension
    {nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)} {z : M₁ ⊕ M₂}
    (d : HeightFlexibleCommonChartExtension nd z) : CommonChartExtension nd z := by
  exact {
    next := {
      arity := d.arity
      tuple₁ := d.tuple₁
      tuple₂ := d.tuple₂
      type := reduceType α.2 d.hβ₁ d.type₁
      eval₁ := d.source_eval₁
      eval₂ := by rw [d.reduced_eq]; exact d.source_eval₂ }
    emb := d.emb
    trans₁ := d.trans₁
    trans₂ := d.trans₂
    serves_left := d.serves_left
    serves_right := d.serves_right }

end HeightFlexibleCommonChartExtension

/-- A per-request high-occurrence theorem, allowed to rebuild its higher
certification scaffolding independently at every call. -/
def HeightFlexibleCommonChartStepSupply : Prop :=
  ∀ (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)) (z : M₁ ⊕ M₂),
    Nonempty (HeightFlexibleCommonChartExtension nd z)

/-- Height-flexible certification supplies the source-level density theorem;
no compatibility between the chosen stages or higher witnesses is consumed. -/
theorem commonChartStepSupply_of_heightFlexible
    (h : HeightFlexibleCommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    CommonChartStepSupply (A₁ := A₁) (A₂ := A₂) := by
  intro nd z
  exact ⟨(h nd z).some.toCommonChartExtension⟩

/-- Construction-relative version: the projected next source chart must
preserve the selected invariant, but the higher scaffolding remains local. -/
def RestrictedHeightFlexibleCommonChartStepSupply
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) : Prop :=
  ∀ (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)), Good nd →
    ∀ z : M₁ ⊕ M₂,
      ∃ d : HeightFlexibleCommonChartExtension nd z,
        Good d.toCommonChartExtension.next

/-- Restricted height-flexible certification feeds the selected closed
subcategory consumer. -/
theorem restrictedCommonChartStepSupply_of_heightFlexible
    {Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop}
    (h : RestrictedHeightFlexibleCommonChartStepSupply
      (A₁ := A₁) (A₂ := A₂) Good) :
    RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good := by
  intro nd hnd z
  obtain ⟨d, hd⟩ := h nd hnd z
  exact ⟨⟨d.toCommonChartExtension, hd⟩⟩

namespace FairCommonChartChain

noncomputable def compositeEmb (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂))
    {j k : ℕ} (h : j ≤ k) : Fin (c.node j).arity ↪ Fin (c.node k).arity :=
  Nat.leRecOn h (fun {i} e => e.trans (c.emb i)) (Function.Embedding.refl _)

theorem compositeEmb_self (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂))
    {j : ℕ} (h : j ≤ j) : c.compositeEmb h = Function.Embedding.refl _ :=
  Nat.leRecOn_self _

theorem compositeEmb_succ (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂))
    {j k : ℕ} (h1 : j ≤ k) (h2 : j ≤ k + 1) :
    c.compositeEmb h2 = (c.compositeEmb h1).trans (c.emb k) :=
  Nat.leRecOn_succ h1 _

theorem compositeEmb_tuple₁ (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) {j : ℕ} :
    ∀ {k : ℕ} (h : j ≤ k) (i : Fin (c.node j).arity),
      (c.node k).tuple₁ (c.compositeEmb h i) = (c.node j).tuple₁ i := by
  intro k h
  induction k, h using Nat.le_induction with
  | base => intro i; rw [compositeEmb_self]; rfl
  | succ k hk ih =>
    intro i
    rw [c.compositeEmb_succ hk, Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun (c.trans₁ k) (c.compositeEmb hk i)).trans (ih i)

theorem compositeEmb_tuple₂ (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) {j : ℕ} :
    ∀ {k : ℕ} (h : j ≤ k) (i : Fin (c.node j).arity),
      (c.node k).tuple₂ (c.compositeEmb h i) = (c.node j).tuple₂ i := by
  intro k h
  induction k, h using Nat.le_induction with
  | base => intro i; rw [compositeEmb_self]; rfl
  | succ k hk ih =>
    intro i
    rw [c.compositeEmb_succ hk, Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun (c.trans₂ k) (c.compositeEmb hk i)).trans (ih i)

def family (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :
    Set (Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) :=
  {x | ∃ (k : ℕ) (σ : Fin x.1 → Fin (c.node k).arity),
    (c.node k).tuple₁ ∘ σ = x.2.1 ∧ (c.node k).tuple₂ ∘ σ = x.2.2}

theorem family_empty_mem (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :
    (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family :=
  ⟨0, fun i => i.elim0, funext fun i => i.elim0, funext fun i => i.elim0⟩

theorem family_commonChart (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :
    ∀ x ∈ c.family, HasCommonChart A₁ A₂ x.2.1 x.2.2 := by
  rintro x ⟨k, σ, hσ₁, hσ₂⟩
  exact ⟨(c.node k).arity, (c.node k).tuple₁, (c.node k).tuple₂, σ,
    (c.node k).type, (c.node k).eval₁, (c.node k).eval₂, hσ₁, hσ₂⟩

theorem family_forth (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :
    ∀ x ∈ c.family, ∀ m : M₁, ∃ n' : M₂,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family := by
  rintro ⟨a0, a, b⟩ ⟨k, σ, hσ₁, hσ₂⟩ m
  obtain ⟨k', i, hi⟩ := c.covers_left m
  refine ⟨(c.node (max k k')).tuple₂ (c.compositeEmb (le_max_right k k') i),
    max k k', Fin.snoc (fun j => c.compositeEmb (le_max_left k k') (σ j))
      (c.compositeEmb (le_max_right k k') i), funext fun j => ?_, funext fun j => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
      exact (c.compositeEmb_tuple₁ (le_max_right k k') i).trans hi
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.compositeEmb_tuple₁ (le_max_left k k') (σ j)).trans (congrFun hσ₁ j)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.compositeEmb_tuple₂ (le_max_left k k') (σ j)).trans (congrFun hσ₂ j)

theorem family_back (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :
    ∀ x ∈ c.family, ∀ n' : M₂, ∃ m : M₁,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family := by
  rintro ⟨a0, a, b⟩ ⟨k, σ, hσ₁, hσ₂⟩ n'
  obtain ⟨k', i, hi⟩ := c.covers_right n'
  refine ⟨(c.node (max k k')).tuple₁ (c.compositeEmb (le_max_right k k') i),
    max k k', Fin.snoc (fun j => c.compositeEmb (le_max_left k k') (σ j))
      (c.compositeEmb (le_max_right k k') i), funext fun j => ?_, funext fun j => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.compositeEmb_tuple₁ (le_max_left k k') (σ j)).trans (congrFun hσ₁ j)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
      exact (c.compositeEmb_tuple₂ (le_max_right k k') i).trans hi
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.compositeEmb_tuple₂ (le_max_left k k') (σ j)).trans (congrFun hσ₂ j)

end FairCommonChartChain

open Classical in
/-- Rasiowa--Sikorski without set-theoretic machinery: one local density
theorem plus a surjective schedule produces the exhaustive chain, and the chain
starts at the seed. -/
theorem exists_fairCommonChartChain_of_stepSupply'
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    ∃ c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂), c.node 0 = seed := by
  obtain ⟨e, he⟩ := exists_surjective_nat (M₁ ⊕ M₂)
  let node : ℕ → CommonChartNode (A₁ := A₁) (A₂ := A₂) :=
    Nat.rec seed (fun k nd => (supply nd (e k)).some.next)
  let ext (k : ℕ) : CommonChartExtension (node k) (e k) :=
    (supply (node k) (e k)).some
  have node_succ (k : ℕ) : node (k + 1) = (ext k).next := rfl
  refine ⟨{
    node := node
    emb := fun k => (node_succ k) ▸ (ext k).emb
    trans₁ := fun k => ?_
    trans₂ := fun k => ?_
    covers_left := fun x => ?_
    covers_right := fun y => ?_ }, rfl⟩
  · simpa only [node_succ k] using (ext k).trans₁
  · simpa only [node_succ k] using (ext k).trans₂
  · obtain ⟨k, hk⟩ := he (Sum.inl x)
    obtain ⟨i, hi⟩ := (ext k).serves_left x hk
    exact ⟨k + 1, (node_succ k) ▸ i, by simpa only [node_succ k] using hi⟩
  · obtain ⟨k, hk⟩ := he (Sum.inr y)
    obtain ⟨i, hi⟩ := (ext k).serves_right y hk
    exact ⟨k + 1, (node_succ k) ▸ i, by simpa only [node_succ k] using hi⟩

/-- The exhaustive chain, in its original interface (the seed is forgotten). -/
theorem exists_fairCommonChartChain_of_stepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    Nonempty (FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :=
  let ⟨c, _⟩ := exists_fairCommonChartChain_of_stepSupply' seed supply
  ⟨c⟩

open Classical in
/-- Restricted Rasiowa--Sikorski cashout.  A good seed and density preserving
`Good` suffice; the ambient class of all common charts need not amalgamate.  The
chain starts at the seed. -/
theorem exists_fairCommonChartChain_of_restrictedStepSupply'
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    ∃ c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂), c.node 0 = seed := by
  obtain ⟨e, he⟩ := exists_surjective_nat (M₁ ⊕ M₂)
  let selected (nd : { nd : CommonChartNode (A₁ := A₁) (A₂ := A₂) // Good nd })
      (z : M₁ ⊕ M₂) : GoodCommonChartExtension Good nd.1 z :=
    (supply nd.1 nd.2 z).some
  let state : ℕ → { nd : CommonChartNode (A₁ := A₁) (A₂ := A₂) // Good nd } :=
    Nat.rec ⟨seed, seed_good⟩ fun k nd =>
      ⟨(selected nd (e k)).extension.next, (selected nd (e k)).good_next⟩
  let node (k : ℕ) : CommonChartNode (A₁ := A₁) (A₂ := A₂) := (state k).1
  let ext (k : ℕ) : CommonChartExtension (node k) (e k) :=
    (selected (state k) (e k)).extension
  have node_succ (k : ℕ) : node (k + 1) = (ext k).next := rfl
  refine ⟨{
    node := node
    emb := fun k => (node_succ k) ▸ (ext k).emb
    trans₁ := fun k => ?_
    trans₂ := fun k => ?_
    covers_left := fun x => ?_
    covers_right := fun y => ?_ }, rfl⟩
  · simpa only [node_succ k] using (ext k).trans₁
  · simpa only [node_succ k] using (ext k).trans₂
  · obtain ⟨k, hk⟩ := he (Sum.inl x)
    obtain ⟨i, hi⟩ := (ext k).serves_left x hk
    exact ⟨k + 1, (node_succ k) ▸ i, by simpa only [node_succ k] using hi⟩
  · obtain ⟨k, hk⟩ := he (Sum.inr y)
    obtain ⟨i, hi⟩ := (ext k).serves_right y hk
    exact ⟨k + 1, (node_succ k) ▸ i, by simpa only [node_succ k] using hi⟩

/-- The restricted chain, in its original interface (the seed is forgotten). -/
theorem exists_fairCommonChartChain_of_restrictedStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    Nonempty (FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) :=
  let ⟨c, _⟩ := exists_fairCommonChartChain_of_restrictedStepSupply' Good seed seed_good supply
  ⟨c⟩

/-- Every node's tuple pair belongs to the chain's extension family. -/
theorem FairCommonChartChain.node_mem_family
    (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) (k : ℕ) :
    (⟨(c.node k).arity, ⇑(c.node k).tuple₁, ⇑(c.node k).tuple₂⟩ :
      Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family :=
  ⟨k, id, rfl, rfl⟩

/-- Backward-minimal classification cashout: an exhaustive monotone sequence
of common source charts already gives the isomorphism. -/
theorem nonempty_iso_of_fairCommonChartChain [Countable M₁] [Countable M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (c : FairCommonChartChain (A₁ := A₁) (A₂ := A₂)) : Nonempty (A₁.Iso A₂) :=
  nonempty_iso_of_commonCharts hA₁ hA₂ c.family c.family_empty_mem
    c.family_commonChart c.family_forth c.family_back

/-- Complete one-step-density cashout: the local common-chart extension
theorem alone yields the source isomorphism.  Proved by the direct selected-chart
consumer with every chart good; the `Nonempty` instances are no longer used. -/
theorem nonempty_iso_of_commonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :
    Nonempty (A₁.Iso A₂) :=
  let ⟨e, _⟩ := exists_iso_of_selectedCommonCharts hA₁ hA₂ (fun _ => True) seed trivial
    (restrictedCommonChartStepSupply_true supply)
  ⟨e⟩

/-- The same classification cashout on a construction-selected closed
subcategory.  This is the direct consumer for a weak-ready-arrow invariant; it is
proved by `exists_iso_of_selectedCommonCharts`, and the `Nonempty` instances are no
longer used. -/
theorem nonempty_iso_of_restrictedCommonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (seed : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :
    Nonempty (A₁.Iso A₂) :=
  let ⟨e, _⟩ := exists_iso_of_selectedCommonCharts hA₁ hA₂ Good seed seed_good supply
  ⟨e⟩

/-- Final forcing-lite boundary: for two countable models, local density of
common source charts is the only open hypothesis.  The seed is the empty
common chart supplied by model covering. -/
theorem nonempty_iso_of_commonChartStepSupply_of_isModel
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    {B₁ : KnightRealization (blockStage 0) M₁}
    {B₂ : KnightRealization (blockStage 0) M₂}
    (hB₁ : B₁.IsModel) (hB₂ : B₂.IsModel)
    (supply : CommonChartStepSupply (A₁ := B₁) (A₂ := B₂)) :
    Nonempty (B₁.Iso B₂) := by
  obtain ⟨p₁, hp₁⟩ := exists_eval_empty hB₁
  obtain ⟨p₂, hp₂⟩ := exists_eval_empty hB₂
  have hp : p₁ = p₂ := Subsingleton.elim _ _
  subst p₂
  let seed : CommonChartNode (A₁ := B₁) (A₂ := B₂) := {
    arity := 0
    tuple₁ := Function.Embedding.ofIsEmpty
    tuple₂ := Function.Embedding.ofIsEmpty
    type := p₁
    eval₁ := hp₁
    eval₂ := hp₂ }
  exact nonempty_iso_of_commonChartStepSupply hB₁.consistent hB₂.consistent seed supply

/-- The merged high-witness fair chain forgets to the source-level quotient.
In particular its inter-node label-map fields are certification scaffolding,
not data consumed by classification. -/
noncomputable def FairPairedChain.toFairCommonChartChain
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} (c : FairPairedChain s)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂) :
    FairCommonChartChain (A₁ := R₁) (A₂ := R₂) where
  node k := {
    arity := (c.node k).arity
    tuple₁ := (c.node k).tuple₁
    tuple₂ := (c.node k).tuple₂
    type := (c.node k).sourceType
    eval₁ := (c.node k).source_eval₁ hred₁
    eval₂ := (c.node k).source_eval₂ hred₂ }
  emb k := (c.step k).emb
  trans₁ k := (c.step k).trans₁
  trans₂ k := (c.step k).trans₂
  covers_left := c.covers_left
  covers_right := c.covers_right

end KnightRealization

end VaughtConjecture.Knight
