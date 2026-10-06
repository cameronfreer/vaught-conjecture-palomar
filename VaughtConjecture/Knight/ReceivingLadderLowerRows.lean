/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderCarrier

/-! # Physical lower rows and extraction on the mixed receiving carrier

The inherited rows are retained on their entire actual domains. Each new
grade-one rung or shadow reads every present original field, the request,
and both eligible ladder copies using the explicit long-rung formula.
These are coded orderly rows, not a supplied lawfulness interface.

On any semantics installing these rows, an arbitrary lawful section of an
actual lower set restricts to the full ladder table. Thus the faithful scalar
chart and the long-rung zero implications apply to physical occurrences.
Upper rows, consistency of the complete scheme, and lifting are separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "T" => SupportLadderRows.Point L X Q

/-- Literal old rows with no enlarged domain. -/
noncomputable def inheritedRow (sem : Semantics C) (c : Cell C)
    (d : (D).below ((D).cell (old C hC c))) : ExtOrd :=
  sem.E c (oldArg C hC c d)

theorem inheritedRow_old (sem : Semantics C) (c : Cell C) (d : C.below (C.cell c)) :
    inheritedRow (L := L) (X := X) (Q := Q) (U := U) C hC sem c
      (oldBelow C hC c d) = sem.E c d := by simp only [inheritedRow, oldArg_oldBelow]

theorem inheritedRow_orderly (sem : Semantics C) (c : Cell C) :
    IsOrderly (fun d : (D).below ((D).cell (old C hC c)) => (D).grade d.1)
      (inheritedRow C hC sem c) := by
  intro d
  dsimp only
  rw [← oldArg_grade C hC c d]
  exact sem.orderly c (oldArg C hC c d)

theorem inheritedRow_coded (sem : Semantics C) (hc : sem.IsCoded) (c : Cell C)
    (d : (D).below ((D).cell (old C hC c))) :
    IsCodedLabel ((D).grade (old C hC c)) (inheritedRow C hC sem c d) := by
  rw [show (D).grade (old C hC c) = C.grade c from
    congrArg Prod.snd (old_index C hC c)]
  exact hc c _

variable (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

/-- A totalized index for row formulas. Upper occurrences never lie below
a grade-one owner, so their default zero is not a semantic constraint. -/
noncomputable def lowerIndex (a : Q) (d : Cell D) : ℕ :=
  match view C hC d with
  | .inl c => profile a (field c)
  | .inr .request => profile a request
  | .inr (.ladder _ v) => SupportLadderRows.index profile a v
  | .inr (.upper _ _ _) => 0
  | .inr .apex => 0

noncomputable def ladderRow (c : T) (d : Cell D) : ExtOrd :=
  SupportLadderRows.source (SupportLadderRows.ceiling profile c)
    (lowerIndex C hC field request profile (SupportLadderRows.parent c) d)

@[simp] theorem ladderRow_old (c : T) (d : Cell C) :
    ladderRow (U := U) C hC field request profile c (old C hC d) =
      SupportLadderRows.source (SupportLadderRows.ceiling profile c)
        (profile (SupportLadderRows.parent c) (field d)) := by
  simp only [ladderRow, lowerIndex, view_old]

@[simp] theorem ladderRow_request (c : T) :
    ladderRow (U := U) C hC field request profile c (added C hC .request) =
      SupportLadderRows.source (SupportLadderRows.ceiling profile c)
        (profile (SupportLadderRows.parent c) request) := by
  simp only [ladderRow, lowerIndex, view_added]

@[simp] theorem ladderRow_ladder (c v : T) (b : Bool) :
    ladderRow (U := U) C hC field request profile c (added C hC (.ladder b v)) =
      SupportLadderRows.row profile c v := by
  simp only [ladderRow, lowerIndex, view_added, SupportLadderRows.row]

theorem ladderRow_coded (c : T) (d : Cell D) :
    IsCodedLabel 1 (ladderRow C hC field request profile c d) :=
  SupportLadderRows.source_coded _ _

theorem ladderRow_orderly (b : Bool) (c : T) :
    IsOrderly (fun d : (D).below ((D).cell (added C hC (.ladder b c))) => (D).grade d.1)
      (fun d => ladderRow C hC field request profile c d.1) := by
  intro d
  dsimp only
  rw [below_ladder_grade C hC b c d]
  exact (SupportLadderRows.source_visible _ _).symm

/-- Every inherited field has an actual parent shadow with the same source,
for every serving owner, not just for a selected display. -/
theorem ladderRow_old_shadow (hb : ∀ a x, profile a x ≤ L) (c : T)
    (d : Cell C) (b : Bool) :
    ladderRow (U := U) C hC field request profile c (old C hC d) =
      ladderRow (U := U) C hC field request profile c
        (added C hC (.ladder b (SupportLadderRows.shadow (SupportLadderRows.parent c)
          (field d)))) := by
  rw [ladderRow_old, ladderRow_ladder]
  simp only [SupportLadderRows.row, SupportLadderRows.index, SupportLadderRows.shadow,
    SupportLadderRows.parent, SupportLadderRows.ceiling, FiniteProfileControllers.cut_refl]
  rw [min_eq_right (hb _ _)]

theorem ladderRow_request_shadow (hb : ∀ a x, profile a x ≤ L) (c : T) (b : Bool) :
    ladderRow (U := U) C hC field request profile c (added C hC .request) =
      ladderRow (U := U) C hC field request profile c
        (added C hC (.ladder b (SupportLadderRows.shadow (SupportLadderRows.parent c)
          request))) := by
  rw [ladderRow_request, ladderRow_ladder]
  simp only [SupportLadderRows.row, SupportLadderRows.index, SupportLadderRows.shadow,
    SupportLadderRows.parent, SupportLadderRows.ceiling, FiniteProfileControllers.cut_refl]
  rw [min_eq_right (hb _ _)]

/-- Prefix agreement reaches original fields and the request as well as
every separate rung/shadow occurrence at both scopes. -/
theorem lowerIndex_agreement (a a' : Q) (d : Cell D) :
    min (lowerIndex C hC field request profile a d)
        (FiniteProfileControllers.cut L (profile a) (profile a')) =
      min (lowerIndex C hC field request profile a' d)
        (FiniteProfileControllers.cut L (profile a) (profile a')) := by
  cases hv : view C hC d with
  | inl c =>
      simpa only [lowerIndex, hv] using
        FiniteProfileControllers.agree_cut L (profile a) (profile a') (field c)
  | inr x =>
      cases x with
      | request =>
          simpa only [lowerIndex, hv] using
            FiniteProfileControllers.agree_cut L (profile a) (profile a') request
      | ladder b v =>
          simpa only [lowerIndex, hv] using
            SupportLadderRows.index_agreement (profile := profile) a a' v
      | upper _ _ _ => simp only [lowerIndex, hv]
      | apex => simp only [lowerIndex, hv]

noncomputable def lowerImage (a : Q) (f : ℕ → ExtOrd) (d : Cell D) : ExtOrd :=
  f (lowerIndex C hC field request profile a d)

/-- Original-cap receipts for the complete lower vector, including unused
rungs, all shadows, both mixed copies, and original fields. Only capped
agreement is required below the rank cut. The zero defaults above grade one
are not claims about upper numerical labels. -/
theorem lowerImage_cap_agreement (a a' : Q) {k : ℕ}
    (hk : k ≤ FiniteProfileControllers.cut L (profile a) (profile a'))
    (f g : ℕ → ExtOrd) (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγf : γ ≤ f k) (hγg : γ ≤ g k)
    (hfg : ∀ i, i < k → min (f i) γ = min (g i) γ) (d : Cell D) :
    min (lowerImage C hC field request profile a f d) γ =
      min (lowerImage C hC field request profile a' g d) γ := by
  have he := congrArg (fun z => min z k)
    (lowerIndex_agreement C hC field request profile a a' d)
  simp only [min_assoc, min_eq_right hk] at he
  change min (f (lowerIndex C hC field request profile a d)) γ =
    min (g (lowerIndex C hC field request profile a' d)) γ
  by_cases ha : lowerIndex C hC field request profile a d < k
  · have heq : lowerIndex C hC field request profile a' d =
        lowerIndex C hC field request profile a d := by omega
    rw [heq]
    exact hfg _ ha
  · have ha' : k ≤ lowerIndex C hC field request profile a d := by omega
    have hb' : k ≤ lowerIndex C hC field request profile a' d := by omega
    rw [min_eq_right (hγf.trans (hf ha')), min_eq_right (hγg.trans (hg hb'))]

/-- The exact installed-row equation; it imposes no assumption about lawful
sections, availability, lifting, or any upper source catalogue. -/
def HasLadderRows (sem : Semantics D) : Prop :=
  ∀ (b : Bool) (c : T) (d : (D).below ((D).cell (added C hC (.ladder b c)))),
    sem.E (added C hC (.ladder b c)) d = ladderRow C hC field request profile c d.1

variable {BJ : Finset (Fin 3) × ℕ} (b : Bool) (hb : GradedLe (scope b, 1) BJ)

/-- Include every rung and shadow at a present mixed index. -/
noncomputable def tableAt (v : T) : (D).below BJ :=
  ⟨added C hC (.ladder b v), by rw [added_index]; exact hb⟩

/-- Arbitrary target-local lawful inputs recover the faithful table law.
No whole ambient extension or normalization assumption is used. -/
theorem lawful_tableBelow (sem : Semantics D) (hrows : HasLadderRows C hC field request profile sem)
    (p : (D).below BJ → ExtOrd) (hp : RespectsSemanticsBelow sem BJ p) :
    SupportLadderRows.Lawful profile (fun v => p (tableAt C hC b hb v)) := by
  constructor
  · intro v
    have hv := hp.orderly (tableAt C hC b hb v)
    dsimp only at hv
    rw [show (D).grade (tableAt C hC b hb v).1 = 1 from ladder_grade C hC b v] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (tableAt C hC b hb c)).reindex (ladderBelow C hC b c)
    dsimp only [HasLadderRows] at hrows
    have hr : sem.E (tableAt C hC b hb c).1 ∘ ladderBelow C hC b c =
        SupportLadderRows.row profile c := by
      funext v
      exact (hrows b c (ladderBelow C hC b c v)).trans
        (ladderRow_ladder C hC field request profile c v b)
    rw [hr] at ht
    simpa only [Function.comp_def, ladderBelow, tableAt, CellScheme.below.incl,
      ladder_grade] using ht

/-- Recover a maximal serving leaf and its scalar chart from all actual
rung and shadow values, at either mixed scope. -/
theorem exists_shapeBelow [Nonempty Q] (hL : 0 < L) (hbound : ∀ a x, profile a x ≤ L)
    (sem : Semantics D) (hrows : HasLadderRows C hC field request profile sem)
    (p : (D).below BJ → ExtOrd) (hp : RespectsSemanticsBelow sem BJ p) :
    ∃ a f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ v, p (tableAt C hC b hb v) = SupportLadderRows.image profile a f v :=
  (lawful_tableBelow C hC field request profile b hb sem hrows p hp).exists_shape hbound hL

/-- Physical long rungs prohibit partial erasure even at unused ranks. -/
theorem predecessor_botBelow (sem : Semantics D)
    (hrows : HasLadderRows C hC field request profile sem)
    (p : (D).below BJ → ExtOrd) (hp : RespectsSemanticsBelow sem BJ p)
    (a : Q) {i : ℕ} (hi : 0 < i) (hiL : i < L)
    (hz : p (tableAt C hC b hb (SupportLadderRows.rung a ⟨i - 1, by omega⟩)) = ⊥) :
    p (tableAt C hC b hb (SupportLadderRows.rung a ⟨i, hiL⟩)) = ⊥ :=
  (lawful_tableBelow C hC field request profile b hb sem hrows p hp).predecessor_bot a hi hiL hz

/-- A present inherited field and its actual parent shadow have the same
reading below this owner's cap in every lawful local section. This is derived
from that owner's faithful witness, not from a decoded maximum. -/
theorem old_shadow_receiptBelow (hbound : ∀ a x, profile a x ≤ L)
    (sem : Semantics D) (hrows : HasLadderRows C hC field request profile sem)
    (p : (D).below BJ → ExtOrd) (hp : RespectsSemanticsBelow sem BJ p)
    (c : T) (d : Cell C)
    (hd : GradedLe ((D).cell (old C hC d)) ((D).cell (added C hC (.ladder b c)))) :
    min (p ⟨old C hC d, hd.trans (tableAt C hC b hb c).2⟩)
        (p (tableAt C hC b hb c)) =
      min (p (tableAt C hC b hb
        (SupportLadderRows.shadow (SupportLadderRows.parent c) (field d))))
        (p (tableAt C hC b hb c)) := by
  let x : (D).below ((D).cell (added C hC (.ladder b c))) := ⟨old C hC d, hd⟩
  let y := ladderBelow (U := U) C hC b c
    (SupportLadderRows.shadow (SupportLadderRows.parent c) (field d))
  have he : sem.E (added C hC (.ladder b c)) x =
      sem.E (added C hC (.ladder b c)) y :=
    (hrows b c x).trans ((ladderRow_old_shadow C hC field request profile hbound c d b).trans
      (hrows b c y).symm)
  obtain ⟨g, σ, _, _, _, _, _, hr⟩ := hp.locality (tableAt C hC b hb c)
  have hx := hr x
  have hy := hr y
  change min (p _) (p _) = min (σ (sem.E _ x)) (g ((D).grade x.1)) at hx
  change min (p _) (p _) = min (σ (sem.E _ y)) (g ((D).grade y.1)) at hy
  rw [below_ladder_grade C hC b c x, he] at hx
  rw [below_ladder_grade C hC b c y] at hy
  exact hx.trans hy.symm

end VaughtConjecture.Knight.ReceivingLadderCarrier
