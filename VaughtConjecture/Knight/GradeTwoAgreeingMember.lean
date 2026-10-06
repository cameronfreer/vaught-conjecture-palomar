/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoInvariant

/-! # The two-level tower: constructing the agreeing retained member

`lift_of_agreeing_member` (`Knight/GradeTwoBountifulTest.lean`) lifts a prescribed input over the
row of a retained member `m` at `m`'s cap once a retained member `m'` extends the input literally
and agrees with `m` on the **full decoded vector** under `m`'s cap.  This module constructs `m'`
for the coded inputs that `Member` actually represents — the prescribed labelling is the row of a
retained member `mp` restricted to `D⟨C,2⟩` — from an explicit base obligation, and isolates the
one clause of full-vector agreement that the counted recoding must supply.

* **The base obligation** `CodedBountiful sem₀ I`: bountifulness of the base at the pair
  `⟨C,2⟩ ≺ ⟨A,2⟩` with alphabet-valued inputs and output, under alphabet caps.  It is derived
  from ordinary bountifulness of the base in `Knight/GradeTwoCodedBountiful.lean`
  (`codedBountiful_of_isBountiful`).
* **The member** `agreeingMember`: the base output, capped at the larger of the two caps; it is
  alphabet-valued, respects the base, is retained whenever the family predicate depends only on
  the cells under `C` (`hPC`), extends `mp` literally under `C`, and agrees with `m` under `m.γ`
  at every base cell (`agreeingMember_agree`).
* **Full-vector agreement** (`levelCap_eq_of_agree`): base agreement together with agreement of
  the **level-one readings** under `m.γ` gives `levelCap m m' = m.γ`, the hypothesis of the lift.
* **The level-one clause** `ReadOneStable m`: a member agreeing with `m` under `m.γ` at every base
  cell, with at least `m`'s cap, has its decoded level-one readings agree with `m`'s under `m.γ`.
  It holds trivially when the grade-`≤ 1` parts coincide (`readOne_agree_of_low_eq`: the witnesses
  are then the same member and the decoder differs only at its cap, `shift_min_of_le`), and in
  general by the stability of the counted recoding under the cap
  (`Knight/GradeTwoReadOneStable.lean`, `readOneStable_of_member`).
* **The lift for coded inputs** (`lift_of_coded_input`): under the base obligation and
  `ReadOneStable m`, the literal clause instance at `⟨C,2⟩ ≺ ⟨A,2⟩` with ambient `memberRow m`,
  cap `m.γ` and prescribed input `memberRow mp ↾ D⟨C,2⟩` has a lift by controller change to
  `agreeingMember`; unconditionally in `Knight/GradeTwoReadOneStable.lean`
  (`lift_of_coded_input'`).

Arbitrary ambient labellings (not member rows) are not addressed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## The decoder under a larger cap -/

/-- The decoder with a larger cap agrees with the decoder under the smaller cap: the cap enters
only at the top and past the last block. -/
theorem shift_min_of_le {l : ℕ} {S : Finset Ordinal.{0}} {γ γ' : ExtOrd} (h : γ ≤ γ')
    (x : ExtOrd) : min (shift l S γ' x) γ = min (shift l S γ x) γ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot, shift_bot]
  · rw [shift_top, shift_top, min_eq_right h, min_self]
  · rw [shift_ofOrd, shift_ofOrd]
    split_ifs with hb
    · rw [min_eq_right h, min_self]
    · rfl

/-! ## The base obligation -/

/-- **Coded bountifulness of the base at a proper-to-full pair** (derived from ordinary
bountifulness in `Knight/GradeTwoCodedBountiful.lean`): for alphabet-valued base labellings `F`
(the ambient controller's) and
`G` (the prescribed input's) at grade two, respecting the base under caps `γ` and `δ`, agreeing
under `γ` on the cells under `C`, there is an alphabet-valued respecting `F'` under `max γ δ`
agreeing with `F` under `γ` everywhere and equal to `G` under `C`. -/
def CodedBountiful (sem₀ : Semantics D₀) (I : ℕ) : Prop :=
  ∀ (C : Finset ι), (C, 2) ∈ Plan.gradedPlan D₀.plan → C ≠ A →
    ∀ (F G : BaseCells D₀ 2 → ExtOrd) (γ δ : ExtOrd),
      (∀ d, F d ∈ alph 2 I) → RespectsBase sem₀ 2 F → (∀ d, F d ≤ γ) →
      (∀ d, G d ∈ alph 2 I) → RespectsBase sem₀ 2 G → (∀ d, G d ≤ δ) →
      γ ∈ alph 2 I → SelfVis 2 γ →
      (∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (G d) γ = min (F d) γ) →
      ∃ F' : BaseCells D₀ 2 → ExtOrd, (∀ d, F' d ∈ alph 2 I) ∧ RespectsBase sem₀ 2 F' ∧
        (∀ d, F' d ≤ max γ δ) ∧ (∀ d, min (F' d) γ = min (F d) γ) ∧
        ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → F' d = G d

/-! ## The member -/

section Construct

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}

/-- The agreeing retained member: the base output of `CodedBountiful` for the ambient controller
`m` and the coded input `mp`, capped at `max m.γ mp.γ`. -/
noncomputable def agreeingMember (hcb : CodedBountiful sem₀ I) (C : Finset ι)
    (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
    (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
    (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F') :
    Member sem₀ I 2 P :=
  let spec := hcb C hC hCA m.F mp.F m.γ mp.γ m.F_mem m.respects m.le_cap mp.F_mem mp.respects
    mp.le_cap m.γ_mem m.γ_vis hagree
  { F := Classical.choose spec
    γ := max m.γ mp.γ
    F_mem := (Classical.choose_spec spec).1
    γ_mem := by
      rcases le_total m.γ mp.γ with h | h
      · rw [max_eq_right h]; exact mp.γ_mem
      · rw [max_eq_left h]; exact m.γ_mem
    γ_vis := by
      rcases le_total m.γ mp.γ with h | h
      · rw [max_eq_right h]; exact mp.γ_vis
      · rw [max_eq_left h]; exact m.γ_vis
    le_cap := (Classical.choose_spec spec).2.2.1
    respects := (Classical.choose_spec spec).2.1
    sel := hPC mp.F _ (fun d hd => ((Classical.choose_spec spec).2.2.2.2 d hd).symm) mp.sel }

variable (hcb : CodedBountiful sem₀ I) (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan)
  (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
  (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
  (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F')

theorem agreeingMember_γ : (agreeingMember hcb C hC hCA m mp hagree hPC).γ = max m.γ mp.γ := rfl

theorem le_agreeingMember_γ : m.γ ≤ (agreeingMember hcb C hC hCA m mp hagree hPC).γ :=
  le_max_left _ _

/-- The member agrees with the ambient controller under its cap at every base cell. -/
theorem agreeingMember_agree (d : BaseCells D₀ 2) :
    min ((agreeingMember hcb C hC hCA m mp hagree hPC).F d) m.γ = min (m.F d) m.γ :=
  (Classical.choose_spec (hcb C hC hCA m.F mp.F m.γ mp.γ m.F_mem m.respects m.le_cap mp.F_mem
    mp.respects mp.le_cap m.γ_mem m.γ_vis hagree)).2.2.2.1 d

/-- The member extends the coded input literally under `C`. -/
theorem agreeingMember_F_of_scope (d : BaseCells D₀ 2) (hd : D₀.scope d.1 ⊆ C) :
    (agreeingMember hcb C hC hCA m mp hagree hPC).F d = mp.F d :=
  (Classical.choose_spec (hcb C hC hCA m.F mp.F m.γ mp.γ m.F_mem m.respects m.le_cap mp.F_mem
    mp.respects mp.le_cap m.γ_mem m.γ_vis hagree)).2.2.2.2 d hd

end Construct

/-! ## Full-vector agreement and the level-one clause -/

section Agreement

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
  (hI : Fintype.card (Cell D₀) + 2 ≤ I)

/-- **The level-one clause**: every member agreeing with `m` under `m.γ` at every base cell, with
at least `m`'s cap, has its decoded level-one readings agree with `m`'s under `m.γ`.  Proved for
every member in `Knight/GradeTwoReadOneStable.lean` (`readOneStable_of_member`); the same-low case
is `readOne_agree_of_low_eq`. -/
def ReadOneStable (m : Member sem₀ I 2 P) : Prop :=
  ∀ m' : Member sem₀ I 2 P, (∀ d, min (m'.F d) m.γ = min (m.F d) m.γ) → m.γ ≤ m'.γ →
    ∀ m₁ : Member₁ sem₀ I, min (readOne sem₀ I P hI m' m₁) m.γ = min (readOne sem₀ I P hI m m₁) m.γ

/-- Members with the same grade-`≤ 1` part have the same owned witness. -/
theorem Member.witness_eq_of_low_eq {m m' : Member sem₀ I 2 P} (h : m'.low = m.low) :
    m'.witness hI = m.witness hI :=
  Member.ext (funext fun d => by rw [Member.witness_F, Member.witness_F, h])
    (by rw [Member.witness_γ, Member.witness_γ, h])

/-- **The level-one clause in the same-low case**: when the grade-`≤ 1` parts coincide, the
witnesses coincide and the decoders differ only at their caps, so the readings agree under the
smaller cap. -/
theorem readOne_agree_of_low_eq {m m' : Member sem₀ I 2 P} (h : m'.low = m.low) (hγ : m.γ ≤ m'.γ)
    (m₁ : Member₁ sem₀ I) :
    min (readOne sem₀ I P hI m' m₁) m.γ = min (readOne sem₀ I P hI m m₁) m.γ := by
  unfold readOne Member.dec
  rw [Member.witness_eq_of_low_eq hI h, h]
  exact shift_min_of_le hγ _

/-- **Full-vector agreement**: base agreement and level-one agreement under `m.γ`, with at least
`m`'s cap, give `levelCap m m' = m.γ`. -/
theorem levelCap_eq_of_agree (m m' : Member sem₀ I 2 P)
    (hbase : ∀ d, min (m'.F d) m.γ = min (m.F d) m.γ)
    (hone : ∀ m₁ : Member₁ sem₀ I,
      min (readOne sem₀ I P hI m' m₁) m.γ = min (readOne sem₀ I P hI m m₁) m.γ)
    (hγ : m.γ ≤ m'.γ) :
    levelCap 2 I (fullVec sem₀ I P hI m) m.γ (fullVec sem₀ I P hI m') m'.γ = m.γ := by
  refine levelCap_eq_left_of m.γ_mem m.γ_vis (le_agreeCap_iff.mpr ?_) hγ
  rintro (b | m₁)
  · exact (hbase b).symm
  · exact (hone m₁).symm

end Agreement

/-! ## The lift for coded inputs -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

/-- **The lift for coded inputs, under the level-one clause.**  With the ambient the row of a
retained member `m` at its cap and the prescribed input the row of a retained member `mp`
restricted to `D⟨C,2⟩`, agreeing under `m.γ`, the base obligation and `ReadOneStable m` give a
lift by controller change to `agreeingMember`. -/
theorem lift_of_coded_input (hcb : CodedBountiful sem₀ I) (C : Finset ι)
    (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
    (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
    (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F')
    (hstable : ReadOneStable hI m) :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) m.γ = min (MROW m d) m.γ) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) =
        MROW mp (CellScheme.below.mono (gradedLe_full_two hC) d) := by
  refine lift_of_agreeing_member sem₀ I M P hAk hI hproper C hC hCA _ m
    (agreeingMember hcb C hC hCA m mp hagree hPC) ?_ ?_
  · exact levelCap_eq_of_agree hI m _ (agreeingMember_agree hcb C hC hCA m mp hagree hPC)
      (hstable _ (agreeingMember_agree hcb C hC hCA m mp hagree hPC)
        (le_agreeingMember_γ hcb C hC hCA m mp hagree hPC))
      (le_agreeingMember_γ hcb C hC hCA m mp hagree hPC)
  · intro b hb hg
    rw [agreeingMember_F_of_scope hcb C hC hCA m mp hagree hPC ⟨b, hg⟩ hb]
    exact (memberRow_old sem₀ I M P hAk hI hproper mp b hg _).symm

/-- **The lift for coded inputs, unconditionally, in the same-low case**: when the constructed
member has the grade-`≤ 1` part of the ambient controller. -/
theorem lift_of_coded_input_of_low_eq (hcb : CodedBountiful sem₀ I) (C : Finset ι)
    (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
    (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
    (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F')
    (hlow : (agreeingMember hcb C hC hCA m mp hagree hPC).low = m.low) :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) m.γ = min (MROW m d) m.γ) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) =
        MROW mp (CellScheme.below.mono (gradedLe_full_two hC) d) := by
  refine lift_of_agreeing_member sem₀ I M P hAk hI hproper C hC hCA _ m
    (agreeingMember hcb C hC hCA m mp hagree hPC) ?_ ?_
  · exact levelCap_eq_of_agree hI m _ (agreeingMember_agree hcb C hC hCA m mp hagree hPC)
      (readOne_agree_of_low_eq hI hlow (le_agreeingMember_γ hcb C hC hCA m mp hagree hPC))
      (le_agreeingMember_γ hcb C hC hCA m mp hagree hPC)
  · intro b hb hg
    rw [agreeingMember_F_of_scope hcb C hC hCA m mp hagree hPC ⟨b, hg⟩ hb]
    exact (memberRow_old sem₀ I M P hAk hI hproper mp b hg _).symm

end VaughtConjecture.Knight
