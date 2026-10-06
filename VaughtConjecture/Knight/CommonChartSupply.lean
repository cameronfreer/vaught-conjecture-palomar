/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Common source charts and their one-step supply

The small vocabulary shared by the direct selected-chart consumer
(`Knight/SelectedCommonCharts.lean`) and the historical fair-chain consumer
(`Knight/CommonChartChain.lean`), placed below both so that the direct consumer does not import
the chain module.

* `CommonChartNode` — one common full source chart, with no higher-stage witness attached;
* `CommonChartExtension` / `CommonChartStepSupply` — one density witness absorbing a requested
  point, and forcing-lite local density of all common charts;
* `GoodCommonChartExtension` / `RestrictedCommonChartStepSupply Good` — the
  construction-selected restriction: density is required only below good charts, and the
  extension stays good.

The declarations were moved verbatim from `Knight/CommonChartChain.lean`, which re-exports this
module; their names and signatures are unchanged. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {M₁ M₂ : Type w}
variable {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-- One common full source chart, with no higher-stage witness attached. -/
structure CommonChartNode where
  arity : ℕ
  tuple₁ : Fin arity ↪ M₁
  tuple₂ : Fin arity ↪ M₂
  type : S α.1 arity
  eval₁ : A₁.eval tuple₁ = some type
  eval₂ : A₂.eval tuple₂ = some type

/-- One density witness below a common chart: extend both coordinate tuples
and absorb whichever side's point is currently scheduled. -/
structure CommonChartExtension
    (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (z : M₁ ⊕ M₂) where
  next : CommonChartNode (A₁ := A₁) (A₂ := A₂)
  emb : Fin nd.arity ↪ Fin next.arity
  trans₁ : emb.trans next.tuple₁ = nd.tuple₁
  trans₂ : emb.trans next.tuple₂ = nd.tuple₂
  serves_left : ∀ x, z = Sum.inl x → ∃ i, next.tuple₁ i = x
  serves_right : ∀ y, z = Sum.inr y → ∃ i, next.tuple₂ i = y

/-- Forcing-lite producer interface: every finite common chart has an
extension meeting either next carrier requirement. -/
def CommonChartStepSupply : Prop :=
  ∀ (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)) (z : M₁ ⊕ M₂),
    Nonempty (CommonChartExtension nd z)

/-- A density witness which stays inside a declared construction-reached
subclass.  This is the useful weak-amalgamation shape: no claim is made about
arbitrary common charts outside `Good`. -/
structure GoodCommonChartExtension
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop)
    (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (z : M₁ ⊕ M₂) where
  extension : CommonChartExtension nd z
  good_next : Good extension.next

/-- Construction-relative forcing interface.  Density is required only below
nodes satisfying the invariant which defines the selected closed subcategory. -/
def RestrictedCommonChartStepSupply
    (Good : CommonChartNode (A₁ := A₁) (A₂ := A₂) → Prop) : Prop :=
  ∀ (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂)), Good nd →
    ∀ z : M₁ ⊕ M₂, Nonempty (GoodCommonChartExtension Good nd z)

end KnightRealization

end VaughtConjecture.Knight
