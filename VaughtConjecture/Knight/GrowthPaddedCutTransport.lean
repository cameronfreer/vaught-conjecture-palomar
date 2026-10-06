/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedOriginalInduction
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Actual lower domains on a fixed installed growth carrier

Only occurrences and literal rows are transported. Independently selected
renderings at different grades are not identified.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedCutTransport
open Transform Value ExtOrd Growth
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedStepRows
open CoatomBoundaryExtension
noncomputable section
section Local
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- No added owner lies below a strictly lower cutoff. -/
def stepEquiv (U : Finset ι × ℕ) (hu : U.2 ≤ k) :
    P.carrier.below U ≃ (successor P hk hnext).carrier.below U :=
  HighLayerBountiful.equiv P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext U (fun h => by have := h.2; omega)

theorem step_index (U : Finset ι × ℕ) (hu : U.2 ≤ k) (d : P.carrier.below U) :
    (successor P hk hnext).carrier.cell (stepEquiv P hk hnext U hu d).1 =
      P.carrier.cell d.1 :=
  HighLayerBountiful.equiv_cell _ _ _ _ _ _ _ d

theorem step_respects_iff (U : Finset ι × ℕ) (hu : U.2 ≤ k)
    (p : P.carrier.below U → ExtOrd) :
    RespectsSemanticsBelow P.rows U p ↔
      RespectsSemanticsBelow (successor P hk hnext).rows U
        (p ∘ (stepEquiv P hk hnext U hu).symm) :=
  SeparatedLayerFace.respects_iff P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I X T hA hB hC (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) U
    (fun h => by have := h.2; omega) p

theorem step_lift {U V : Finset ι × ℕ} (h : GradedLe U V) (hv : V.2 ≤ k)
    (hl : CappedLift P.rows h) : CappedLift (successor P hk hnext).rows h :=
  SeparatedLayerFace.lift P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I X T hA hB hC (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) h
    (fun h => by have := h.2; omega) hl

/-- Grade one is exactly the retained padded base, on every installed layer. -/
def baseEquiv : (base I X T hA hB hC).below (A, 1) ≃ P.carrier.below (A, 1) :=
  Equiv.ofBijective
    (fun d => ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (P.base_mono.injective (congrArg Subtype.val h)), by
      intro d
      rcases P.cases d.1 with ⟨b, hb⟩ | ⟨_, hg, _⟩
      · have hbm : GradedLe ((base I X T hA hB hC).cell b) (A, 1) := by
          simpa only [hb, P.base_index] using d.2
        exact ⟨⟨b, hbm⟩, Subtype.ext hb.symm⟩
      · have := d.2.2
        change 2 ≤ (P.carrier.cell d.1).2 at hg
        omega⟩

theorem base_index (d : (base I X T hA hB hC).below (A, 1)) :
    P.carrier.cell (baseEquiv P d).1 = (base I X T hA hB hC).cell d.1 :=
  P.base_index d.1

theorem baseEquiv_val (d : (base I X T hA hB hC).below (A, 1)) :
    (baseEquiv P d).1 = P.baseMap d.1 := rfl

theorem base_respects_iff (p : (base I X T hA hB hC).below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) p ↔
      RespectsSemanticsBelow P.rows (A, 1) (p ∘ (baseEquiv P).symm) := by
  apply respects_iff_of_equiv (baseEquiv P)
    (fun d => (congrArg Prod.snd (base_index P d)).symm)
    (fun d e => ?_) (fun c d _ => (P.base_row c.1 d).symm) p
  simp only [CellScheme.scope, base_index]

end Local

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- The literal occurrence embedding through a finite suffix of installations. -/
def advanceMap (s : ℕ) (hs : s + 2 ≤ A.card) :
    (u : ℕ) → (hu : s + u + 2 ≤ A.card) →
      Cell (build I X T hA hB hC s hs).carrier →
      Cell (build I X T hA hB hC (s + u) hu).carrier
  | 0, _, d => d
  | u + 1, hu, d => old (build I X T hA hB hC (s + u) (by omega)) (by omega)
      (advanceMap s hs u (by omega) d)

theorem advance_index (s : ℕ) (hs : s + 2 ≤ A.card)
    (u : ℕ) (hu : s + u + 2 ≤ A.card) (d : Cell (build I X T hA hB hC s hs).carrier) :
    (build I X T hA hB hC (s + u) hu).carrier.cell
      (advanceMap I X T hA hB hC s hs u hu d) =
        (build I X T hA hB hC s hs).carrier.cell d := by
  induction u with
  | zero => rfl
  | succ u ih =>
    exact (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (ih (by omega))

theorem advance_order (s : ℕ) (hs : s + 2 ≤ A.card)
    (u : ℕ) (hu : s + u + 2 ≤ A.card) :
    StrictMono (advanceMap I X T hA hB hC s hs u hu) := by
  induction u with
  | zero => exact strictMono_id
  | succ u ih => exact (SourceLayerCarrier.old_order _ _ _ _ _).comp (ih (by omega))

/-- The occurrence of every retained rung, shadow and original is the one
already named by the final carrier's base map. -/
theorem advance_baseMap (s : ℕ) (hs : s + 2 ≤ A.card)
    (u : ℕ) (hu : s + u + 2 ≤ A.card) (d : Cell (base I X T hA hB hC)) :
    advanceMap I X T hA hB hC s hs u hu
      ((build I X T hA hB hC s hs).baseMap d) =
        (build I X T hA hB hC (s + u) hu).baseMap d := by
  induction u with
  | zero => rfl
  | succ u ih => exact congrArg (old _ _) (ih (by omega))

/-- Entire inherited rows, including inherited high proper owners, remain literal. -/
theorem advance_row (s : ℕ) (hs : s + 2 ≤ A.card)
    (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC s hs).carrier)
    (d : (build I X T hA hB hC s hs).carrier.below
      ((build I X T hA hB hC s hs).carrier.cell c)) :
    (build I X T hA hB hC (s + u) hu).rows.E
      (advanceMap I X T hA hB hC s hs u hu c)
      ⟨advanceMap I X T hA hB hC s hs u hu d.1, by
        rw [advance_index, advance_index]; exact d.2⟩ =
      (build I X T hA hB hC s hs).rows.E c d := by
  induction u with
  | zero => rfl
  | succ u ih =>
    exact (inherited_row (build I X T hA hB hC (s + u) (by omega))
      (by omega) (by omega) (advanceMap I X T hA hB hC s hs u (by omega) c)
      ⟨advanceMap I X T hA hB hC s hs u (by omega) d.1, by
        rw [advance_index, advance_index]; exact d.2⟩).trans (ih (by omega))

/-- Exact lower domain of an earlier layer inside one fixed later carrier. -/
def advanceEquiv (s : ℕ) (hs : s + 2 ≤ A.card)
    (U : Finset ι × ℕ) (hU : U.2 ≤ s + 2) :
    (u : ℕ) → (hu : s + u + 2 ≤ A.card) →
      (build I X T hA hB hC s hs).carrier.below U ≃
      (build I X T hA hB hC (s + u) hu).carrier.below U
  | 0, _ => Equiv.refl _
  | u + 1, hu => (advanceEquiv s hs U hU u (by omega)).trans
      (stepEquiv (build I X T hA hB hC (s + u) (by omega)) (by omega)
        (by omega) U (by omega))

theorem advanceEquiv_val (s : ℕ) (hs : s + 2 ≤ A.card)
    (U : Finset ι × ℕ) (hU : U.2 ≤ s + 2) (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (d : (build I X T hA hB hC s hs).carrier.below U) :
    (advanceEquiv I X T hA hB hC s hs U hU u hu d).1 =
      advanceMap I X T hA hB hC s hs u hu d.1 := by
  induction u with
  | zero => rfl
  | succ u ih => exact congrArg (old _ _) (ih (by omega))

theorem advance_respects_iff (s : ℕ) (hs : s + 2 ≤ A.card)
    (U : Finset ι × ℕ) (hU : U.2 ≤ s + 2) (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (p : (build I X T hA hB hC s hs).carrier.below U → ExtOrd) :
    RespectsSemanticsBelow (build I X T hA hB hC s hs).rows U p ↔
      RespectsSemanticsBelow (build I X T hA hB hC (s + u) hu).rows U
        (p ∘ (advanceEquiv I X T hA hB hC s hs U hU u hu).symm) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    exact (ih (by omega)).trans
      (step_respects_iff (build I X T hA hB hC (s + u) (by omega))
        (by omega) (by omega) U (by omega) _)

/-- Literal rows on the exact lower-domain equivalence, not just equivalent
lawfulness or equality of selected numerical readings. -/
theorem advanceEquiv_row (s : ℕ) (hs : s + 2 ≤ A.card)
    (U : Finset ι × ℕ) (hU : U.2 ≤ s + 2) (u : ℕ) (hu : s + u + 2 ≤ A.card)
    (c : (build I X T hA hB hC s hs).carrier.below U)
    (d : (build I X T hA hB hC s hs).carrier.below
      ((build I X T hA hB hC s hs).carrier.cell c.1))
    (hd : GradedLe
      ((build I X T hA hB hC (s + u) hu).carrier.cell
        (advanceEquiv I X T hA hB hC s hs U hU u hu ⟨d.1, d.2.trans c.2⟩).1)
      ((build I X T hA hB hC (s + u) hu).carrier.cell
        (advanceEquiv I X T hA hB hC s hs U hU u hu c).1)) :
    (build I X T hA hB hC (s + u) hu).rows.E
      (advanceEquiv I X T hA hB hC s hs U hU u hu c).1
      ⟨(advanceEquiv I X T hA hB hC s hs U hU u hu ⟨d.1, d.2.trans c.2⟩).1, hd⟩ =
      (build I X T hA hB hC s hs).rows.E c.1 d :=
  ((build I X T hA hB hC (s + u) hu).rows.E_congr'
    (advanceEquiv_val I X T hA hB hC s hs U hU u hu c)
    (advanceEquiv_val I X T hA hB hC s hs U hU u hu ⟨d.1, d.2.trans c.2⟩)).trans
    (advance_row I X T hA hB hC s hs u hu c.1 d)

/-- Direct earlier-to-final producer. At cutoff j ≥ 2, choose s = j-2.
Grade one is supplied separately by baseEquiv on the same final layer. -/
theorem exists_earlier_transport (s t : ℕ) (ht : t + 2 ≤ A.card) (hst : s ≤ t)
    (U : Finset ι × ℕ) (hU : U.2 ≤ s + 2) :
    ∃ e : (build I X T hA hB hC s (by omega)).carrier.below U ≃
        (build I X T hA hB hC t ht).carrier.below U,
      (∀ d, (build I X T hA hB hC t ht).carrier.cell (e d).1 =
        (build I X T hA hB hC s (by omega)).carrier.cell d.1) ∧
      (∀ p, RespectsSemanticsBelow (build I X T hA hB hC s (by omega)).rows U p ↔
        RespectsSemanticsBelow (build I X T hA hB hC t ht).rows U (p ∘ e.symm)) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hst
  refine ⟨advanceEquiv I X T hA hB hC s (by omega) U hU u ht, ?_, ?_⟩
  · intro d
    rw [advanceEquiv_val, advance_index]
  · exact advance_respects_iff I X T hA hB hC s (by omega) U hU u ht

end
end VaughtConjecture.Knight.GrowthPaddedCutTransport
