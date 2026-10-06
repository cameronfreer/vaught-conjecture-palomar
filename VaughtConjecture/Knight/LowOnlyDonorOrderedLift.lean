/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyDonorGradeOneLift
public import VaughtConjecture.Knight.LowOnlyGradeOneSupply

/-! # All-cap donor lifting on the actual ordered LOW ladder

The literal left-face occurrence map supplies donor readback. The original
ordered-boundary lawfulness theorem discharges the physical source premise.
Positive-cap lifting consumes the donor fibre; bottom supply is independent.
No LOW symmetry, replacement admission, or output lawfulness is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyOrderedLadder
open Transform Value ExtOrd CappedDonor LowOnly RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)

theorem field_donor (S : State I.left I.right) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.u d :=
  (field_read I S (I.leftFace.map d)).trans (I.paste_left S.u S.v d)

include hroot in
/-- Positive-cap donor lifting from arbitrary lawful inputs on these installed
rows. All semantic producer premises are derived from the original inputs. -/
theorem donor_positive_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p : I.left.scheme.below (effC n 1) → ExtOrd}
    {q : (carrier I.boundary hA
      (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (Family.donorAt F I.boundary hA (donorIncl I) d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) w ∧
      (∀ d, w (Family.donorAt F I.boundary hA (donorIncl I) d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ :=
  Family.donor_positive_lift F I.boundary I.rows hA (field I) (proper I hB hC)
    (boundary_lawful I F hroot) (donorIncl I)
    (fun S _ d => field_donor I S d.1) hp hq hγ hpos hag

include hroot in
/-- All permitted grade-one original caps, with literal donor retention and an
individual cap equation at every actual target occurrence. -/
theorem donor_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p : I.left.scheme.below (effC n 1) → ExtOrd}
    {q : (carrier I.boundary hA
      (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (Family.donorAt F I.boundary hA (donorIncl I) d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) w ∧
      (∀ d, w (Family.donorAt F I.boundary hA (donorIncl I) d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := donor_bottom_supply I F hroot hA hB hC hp
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
  · exact donor_positive_lift I F hroot hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) hag

end
end VaughtConjecture.Knight.LowOnlyOrderedLadder
