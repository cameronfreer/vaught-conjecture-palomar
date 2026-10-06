/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinalGateCompletion
public import VaughtConjecture.Knight.FinalGateTransport
public import VaughtConjecture.Knight.MaximalFullLayer
public import VaughtConjecture.Knight.FullScopeZeroExtension

/-! # A mute apex above the final active gate layer

The only new occurrence has grade N+1 on a scope of size N+1. Every final-gate
row and occurrence remains literal; all proper faces are unchanged. A lawful
grade-N display extends by bottom and retains its stage bound. Consistency,
coding and completeness are constructed from the explicit predecessor
receipts. Bountifulness consumes the final-gate pair theorem, separately.

This uses the mute base of `MaximalFullLayer`, not its active-apex operation.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.FinalGateApex
open Transform Value ExtOrd AmalgamationPlan
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ}
variable (F : FinalGateLayer.Input D N X Q)
variable (hD : ∀ d : Cell D, D.grade d ≤ N) (hcard : A.card = N + 1)

abbrev scheme := MaximalFullLayer.scheme F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
abbrev old := MaximalFullLayer.old F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
abbrev apex := MaximalFullLayer.apex F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
abbrev rows := MaximalFullLayer.base F.carrier F.rows N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge
abbrev ownerEquiv := MaximalFullLayer.ownerEquiv F.carrier N (N + 1) (F.grade_bound hD)
  (Nat.lt_succ_self N) hcard.ge

theorem old_index (d : Cell F.carrier) : (scheme F hcard).cell (old F hcard d) =
    F.carrier.cell d := MaximalFullLayer.old_index _ _ _ _ _ _

theorem apex_index : (scheme F hcard).cell (apex F hcard) = (A, N + 1) :=
  MaximalFullLayer.apex_index _ _ _ _ _

theorem old_order : StrictMono (old F hcard) := SourceLayerCarrier.old_order _ _ _ _ _

theorem old_row (c : Cell F.carrier) (d : F.carrier.below (F.carrier.cell c)) :
    (rows F hD hcard).E (old F hcard c) (ownerEquiv F hD hcard c d) = F.rows.E c d :=
  MaximalFullLayer.inherited_row _ _ _ _ _ _ _ c d

theorem complete (seed : Q)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.2 ≤ N → J ≠ (A, N) → ∃ d, D.cell d = J) :
    (scheme F hcard).IsComplete := by
  apply MaximalFullLayer.complete F.carrier N (N + 1) (Nat.lt_succ_self N) hcard.ge
  intro J hJ hne
  apply F.complete_through seed hc J hJ
  obtain ⟨hmem, _, hj⟩ := Plan.mem_gradedPlan.mp hJ
  have hs := F.carrier.isPlan.subset_of_mem hmem
  have hc' := Finset.card_le_card hs
  by_contra hn
  have hsz : J.1.card = A.card := by rw [hcard] at hc' ⊢; omega
  have he : J.1 = A := Finset.eq_of_subset_of_card_le hs hsz.ge
  apply hne
  apply Prod.ext he
  rw [hcard] at hc'
  omega

theorem consistent (hc : F.sem.IsConsistent) : (rows F hD hcard).IsConsistent :=
  MaximalFullLayer.consistent _ _ _ _ _ _ _ (F.consistent hc)

theorem coded (hc : F.rows.IsCoded) : (rows F hD hcard).IsCoded :=
  MaximalFullLayer.coded _ _ _ _ _ _ _ hc

/-- The final-layer pair theorem is consumed here, not assumed in a scope
operator or hidden in the selected display. -/
theorem bountiful (hb : F.rows.IsBountiful) : (rows F hD hcard).IsBountiful :=
  MaximalFullLayer.bountiful _ _ _ _ _ _ _ F.positive hb

abbrev lowerEquiv : F.carrier.below (A, N) ≃ (scheme F hcard).below (A, N) :=
  HighLayerBountiful.equiv F.carrier Unit (N + 1) (by omega) hcard.ge (A, N)
    (fun h => (Nat.not_succ_le_self N) h.2)

def display (p : F.carrier.below (A, N) → ExtOrd) : Cell (scheme F hcard) → ExtOrd :=
  CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm)

theorem display_old (p : F.carrier.below (A, N) → ExtOrd) (d : F.carrier.below (A, N)) :
    display F hcard p (old F hcard d.1) = p d := by
  change CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm)
    ((lowerEquiv F hcard) d).1 = p d
  rw [CellScheme.zeroAbove_low]
  exact congrArg p ((lowerEquiv F hcard).symm_apply_apply d)

theorem display_apex (p : F.carrier.below (A, N) → ExtOrd) :
    display F hcard p (apex F hcard) = ⊥ := by
  apply CellScheme.zeroAbove_high
  change ¬ ((scheme F hcard).cell (apex F hcard)).2 ≤ N
  rw [apex_index]
  exact Nat.not_succ_le_self N

theorem display_lawful {p : F.carrier.below (A, N) → ExtOrd}
    (hp : RespectsSemanticsBelow F.rows (A, N) p) :
    RespectsSemantics (rows F hD hcard) (display F hcard p) := by
  apply RespectsSemanticsBelow.zeroAbove
  exact (HighLayerBountiful.respects_iff F.carrier Unit (N + 1) (by omega) hcard.ge N
    (F.grade_bound hD) (Nat.lt_succ_self N) F.rows (rows F hD hcard)
    (old_row F hD hcard) (A, N) (fun h => (Nat.not_succ_le_self N) h.2) p).mp hp

/-- Any lawful whole section restricts to the actual final active layer.
This applies to arbitrary ambients, not only constructed displays. -/
theorem restrict_lawful {q : Cell (scheme F hcard) → ExtOrd}
    (hq : RespectsSemantics (rows F hD hcard) q) :
    RespectsSemanticsBelow F.rows (A, N) (fun d => q (old F hcard d.1)) := by
  exact HighLayerBountiful.pullback_respects F.carrier Unit (N + 1) (by omega) hcard.ge N
    (F.grade_bound hD) (Nat.lt_succ_self N) F.rows (rows F hD hcard)
    (old_row F hD hcard) (fun h => (Nat.not_succ_le_self N) h.2) (hq.toBelow (A, N))

theorem display_bound {α : Ordinal.{0}} {p : F.carrier.below (A, N) → ExtOrd}
    (hp : ∀ d, p d < ofOrd α ∨ p d = ⊤) :
    ∀ d, display F hcard p d < ofOrd α ∨ display F hcard p d = ⊤ := by
  intro d
  by_cases hd : (scheme F hcard).grade d ≤ N
  · let d' : (scheme F hcard).below (A, N) :=
      ⟨d, (scheme F hcard).isPlan.subset_of_mem ((scheme F hcard).scope_mem_plan d), hd⟩
    change CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm) d'.1 < ofOrd α ∨
      CellScheme.zeroAbove (p ∘ (lowerEquiv F hcard).symm) d'.1 = ⊤
    rw [CellScheme.zeroAbove_low]
    exact hp ((lowerEquiv F hcard).symm d')
  · rw [display, CellScheme.zeroAbove_high _ hd]
    exact Or.inl (bot_lt_ofOrd _)

/-- Any proper original face survives the apex with every row and occurrence. -/
def properFace {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : ¬ A ⊆ S) (E : ExactSemanticFace sem₀ F.rows) :
    ExactSemanticFace sem₀ (rows F hD hcard) where
  map := ⟨old F hcard ∘ E.map, (old_order F hcard).injective.comp E.map.injective⟩
  index d := (old_index F hcard _).trans (E.index d)
  exhaustive z hz := by
    have hn : (scheme F hcard).cell z ≠ (A, N + 1) := fun he => hS (by
      change ((scheme F hcard).cell z).1 ⊆ S at hz
      simpa only [he] using hz)
    obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence F.carrier Unit (N + 1)
      (by omega) hcard.ge z hn
    have hs : F.carrier.scope x ⊆ S := by
      change ((scheme F hcard).cell z).1 ⊆ S at hz
      rw [hx, old_index] at hz
      exact hz
    obtain ⟨d, hd⟩ := E.exhaustive x hs
    exact ⟨d, (congrArg (old F hcard) hd).trans hx.symm⟩
  row c d := (old_row F hD hcard (E.map c) (E.belowMap c d)).trans (E.row c d)

theorem properFace_order {S : Finset ι} {D₀ : CellScheme S} {sem₀ : Semantics D₀}
    (hS : ¬ A ⊆ S) (E : ExactSemanticFace sem₀ F.rows) (hE : StrictMono E.map) :
    StrictMono (properFace F hD hcard hS E).map := (old_order F hcard).comp hE

end
end VaughtConjecture.Knight.FinalGateApex
