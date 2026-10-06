/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ThreePointSlotBoundary
public import VaughtConjecture.Knight.FiniteProfileControllers

/-! # A finite controller family covering every lawful three-point boundary

Profiles code all nine proper-face occurrences, including the two mute zeros,
and are normalized by occurrence rank rather than allowing arbitrary code gaps.
Every lawful boundary has an order- and bottom-preserving profile in this
fixed finite family, and therefore a whole joint row-layer section. No old
source order is chosen uniformly across inputs. Normalization here supplies
sections, not original-cap lifting for the new full-scope controllers.

This is a row-family construction. The two mute coordinates are zero
coordinates in the grade-one layer; an actual full-scope scheme and its
higher-grade lower domains still have to be installed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ThreePointSlotProfiles

open Transform Value ExtOrd SlotControllerFamily ThreePointSlotBoundary

/-- In this particular two-point domain, a bottom-preserving change of the
finite output order preserves respect. The witness is reconstructed directly
from the selected source table, not by composing faithful transformations. -/
theorem respects_of_order {p q : Fin 5 → ExtOrd}
    (hp : RespectsSemantics TwoPointSlots.rows p)
    (hv : ∀ d, SelfVis 1 (q d)) (hb : ∀ d, p d = ⊥ → q d = ⊥)
    (hm : ∀ d e, p d ≤ p e → q d ≤ q e) : RespectsSemantics TwoPointSlots.rows q := by
  have hj := TwoPointSlots.joint_of_respects (by decide : 1 ≤ 2)
    (hp.toBelow (Finset.univ, 2))
  obtain ⟨c, f, hf, h0, _, he⟩ := hj.exists_shape
  change ∀ d, p (TwoPointSlots.embed d) =
    f (SlotControllerFamily.index c (DonorSlotAssembly.position TwoPointSlots.source d)) at he
  have hjq : DonorSlotAssembly.Joint TwoPointSlots.source
      (fun d => q (TwoPointSlots.embed d)) := by
    apply DonorSlotAssembly.ordered_joint TwoPointSlots.source c
    · exact fun d => hv _
    · intro d hd
      apply hb
      have hz : SlotControllerFamily.index c
          (DonorSlotAssembly.position TwoPointSlots.source d) = 0 := by
        have hh := (value_le_iff _ 0).mp (le_of_eq hd)
        exact Nat.eq_zero_of_le_zero hh
      rw [he d, hz, h0]
    · intro d e hde
      have hi := (value_le_iff _ _).mp hde
      apply hm
      rw [he d, he e]
      exact hf hi
  have hq := TwoPointSlots.extend_respects hjq
  have hext : TwoPointSlots.extend (fun d => q (TwoPointSlots.embed d)) = q := by
    funext d
    by_cases hd : d = 4
    · subst d
      change ⊥ = q 4
      apply (hb 4 ?_).symm
      exact TwoPointSlots.mute_label (hp.toBelow (Finset.univ, 2)) (by
        unfold GradedLe
        decide)
    · simp only [TwoPointSlots.extend, hd, ↓reduceIte, TwoPointSlots.embed_project d hd]
  rwa [hext] at hq

theorem lawful_of_order {p q : Fin 9 → ExtOrd} (hp : Lawful p)
    (hv : ∀ d, SelfVis 1 (q d)) (hb : ∀ d, p d = ⊥ → q d = ⊥)
    (hm : ∀ d e, p d ≤ p e → q d ≤ q e) : Lawful q := by
  constructor
  · exact respects_of_order hp.1 (fun d => hv _) (fun d => hb _) (fun d e => hm _ _)
  · exact respects_of_order hp.2 (fun d => hv _) (fun d => hb _) (fun d e => hm _ _)

open Classical in
noncomputable def code (p : Fin 9 → ExtOrd) (d : Fin 9) : ℕ :=
  if p d = ⊥ then 0 else FreshSourceSlots.rank p d + 1

theorem code_le (p : Fin 9 → ExtOrd) (d : Fin 9) : code p d ≤ 9 := by
  classical
  have hr := FreshSourceSlots.rank_lt_card p d
  simp only [Fintype.card_fin] at hr
  unfold code
  split_ifs <;> omega

theorem code_zero (p : Fin 9 → ExtOrd) (d : Fin 9) : code p d = 0 ↔ p d = ⊥ := by
  classical
  simp [code]

theorem code_order (p : Fin 9 → ExtOrd) (d e : Fin 9) :
    code p d ≤ code p e ↔ p d ≤ p e := by
  classical
  by_cases hd : p d = ⊥
  · simp [code, hd]
  by_cases he : p e = ⊥
  · simp [code, hd, he]
  simp only [code, hd, he, ↓reduceIte, Nat.add_le_add_iff_right]
  exact FreshSourceSlots.rank_le_iff p d e

theorem encoded_lawful {p : Fin 9 → ExtOrd} (hp : Lawful p) :
    Lawful (fun d => value (code p d)) := by
  apply lawful_of_order hp
  · exact fun d => value_visible _
  · intro d hd
    rw [(code_zero p d).mpr hd]
    rfl
  · intro d e hde
    exact value_mono ((code_order p d e).mpr hde)

theorem value_code_bot (p : Fin 9 → ExtOrd) (d : Fin 9) :
    value (code p d) = ⊥ ↔ p d = ⊥ := by
  rw [← le_bot_iff, show (⊥ : ExtOrd) = value 0 from rfl, value_le_iff,
    Nat.le_zero, code_zero]
  rfl

theorem rank_encoded (p : Fin 9 → ExtOrd) (d : Fin 9) :
    FreshSourceSlots.rank (fun e => value (code p e)) d = FreshSourceSlots.rank p d := by
  classical
  unfold FreshSourceSlots.rank
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_not_ge,
    value_le_iff, code_order]

theorem code_idempotent (p : Fin 9 → ExtOrd) (d : Fin 9) :
    code (fun e => value (code p e)) d = code p d := by
  classical
  change (if value (code p d) = ⊥ then 0 else
    FreshSourceSlots.rank (fun e => value (code p e)) d + 1) = code p d
  simp only [value_code_bot, rank_encoded]
  rfl

/-- This family is fixed before prescribing any boundary labels. The rank
condition excludes extraneous gaps, without assuming a common source order. -/
def Profile := {p : Fin 9 → Fin 10 // Lawful (fun d => value (p d).val) ∧
  ∀ d, code (fun e => value (p e).val) d = (p d).val}

instance : Finite Profile := by unfold Profile; infer_instance

def profile (q : Profile) (d : Fin 9) : ℕ := (q.val d).val

theorem profile_bound (q : Profile) (d : Fin 9) : profile q d ≤ 9 :=
  Nat.le_of_lt_succ (q.val d).isLt

noncomputable def encode {p : Fin 9 → ExtOrd} (hp : Lawful p) : Profile :=
  ⟨fun d => ⟨code p d, Nat.lt_succ_of_le (code_le p d)⟩,
    encoded_lawful hp, code_idempotent p⟩

theorem encoding_transforms {p : Fin 9 → ExtOrd} (hp : Lawful p) :
    TransformsTo (fun _ : Fin 9 => 1) (fun d => value (profile (encode hp) d)) p := by
  apply transforms_of_table
  · exact hp.visible
  · intro d hd
    exact (code_zero p d).mp hd
  · intro d e hde
    exact (code_order p d e).mp hde

/-- Every actual proper-face input extends over all full-index profile
controllers at once. The two proper faces, including all four old controller
labels and both mute zeros, are retained literally. -/
theorem boundary_section {p : Fin 9 → ExtOrd} (hp : Lawful p) :
    ∃ r : Fin 9 ⊕ Profile → ExtOrd,
      FiniteProfileControllers.Joint 9 profile r ∧ (∀ d, r (.inl d) = p d) :=
  FiniteProfileControllers.section_of_transform profile_bound (encode hp)
    (encoding_transforms hp)

/-- Each controller's old restriction is lawful on both literal faces, and
all new/new localities hold at the row's actual controller readings. -/
theorem profile_consistency (q : Profile) :
    Lawful (fun d => FiniteProfileControllers.row 9 profile q (.inl d)) ∧
      FiniteProfileControllers.Joint 9 profile (FiniteProfileControllers.row 9 profile q) :=
  ⟨q.property.1, FiniteProfileControllers.rows_joint profile_bound q⟩

/-- No additional proper-face localities have been hidden in a hypothesis:
every joint labelling of this family restricts to two lawful literal faces. -/
theorem joint_lawful_boundary {r : Fin 9 ⊕ Profile → ExtOrd}
    (hr : FiniteProfileControllers.Joint 9 profile r) : Lawful (fun d => r (.inl d)) := by
  obtain ⟨q₀, _⟩ := hr.2.2 (.inl 0)
  let : Nonempty Profile := ⟨q₀⟩
  obtain ⟨q, f, hf, h0, _, he⟩ := hr.exists_shape
  apply lawful_of_order q.property.1
  · exact fun d => hr.1 _
  · intro d hd
    have hz : profile q d = 0 := Nat.eq_zero_of_le_zero ((value_le_iff _ 0).mp (le_of_eq hd))
    rw [he]
    change f (profile q d) = ⊥
    rw [hz, h0]
  · intro d e hde
    rw [he, he]
    exact hf ((value_le_iff _ _).mp hde)

/-- Exact section supply for the whole proper boundary, including all old
auxiliaries. This is not capped lifting against full-controller ambients. -/
theorem boundary_section_iff (p : Fin 9 → ExtOrd) :
    (∃ r : Fin 9 ⊕ Profile → ExtOrd,
      FiniteProfileControllers.Joint 9 profile r ∧ (∀ d, r (.inl d) = p d)) ↔ Lawful p := by
  refine ⟨?_, boundary_section⟩
  rintro ⟨r, hr, he⟩
  have hp := joint_lawful_boundary hr
  have hh : (fun d => r (.inl d)) = p := funext he
  rwa [hh] at hp

/-- A second extension step at the row-family level: retain the entire
previous two-point labelling, including both competing controllers, and
prescribe the third singleton independently. No unique-donor input is used. -/
theorem next_section {p : Fin 5 → ExtOrd} (hp : RespectsSemantics TwoPointSlots.rows p)
    {v : ExtOrd} (hv : SelfVis 1 v) :
    ∃ r : Fin 9 ⊕ Profile → ExtOrd, FiniteProfileControllers.Joint 9 profile r ∧
      Lawful (fun d => r (.inl d)) ∧
      (∀ d, r (.inl (left d)) = p d) ∧ r (.inl 2) = v := by
  obtain ⟨b, hb, hl, hvb⟩ := extend_face hp hv
  obtain ⟨r, hr, he⟩ := boundary_section hb
  exact ⟨r, hr, joint_lawful_boundary hr, fun d => (he _).trans (hl d),
    (he _).trans hvb⟩

/-- Regression: even this next boundary has no common scalar source order
that accommodates all lawful inputs. The family really retains branching. -/
theorem no_common_boundary_order :
    ¬ ∃ E : Fin 9 → ExtOrd, ∀ p : Fin 9 → ExtOrd,
      Lawful p → ∀ d e, E d ≤ E e → p d ≤ p e := by
  rintro ⟨E, hE⟩
  apply TwoPointSlots.no_common_source_order
  refine ⟨E ∘ left, ?_⟩
  intro p hp d e hde
  obtain ⟨r, hr, hl, _⟩ := extend_face hp (selfVis_bot 1)
  have hh := hE r hr (left d) (left e) hde
  rwa [hl d, hl e] at hh

end VaughtConjecture.Knight.ThreePointSlotProfiles
