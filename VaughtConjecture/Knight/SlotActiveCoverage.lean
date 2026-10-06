/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DonorSlotAssembly
public import VaughtConjecture.Knight.FullRowCoverage

/-! # An ambient-active slot covering the complete prescribed base

Among the slots fitting the new old/fresh prescription, choose one nearest
the ambient's actual branch. If it were inactive, moving one step toward that
branch would still fit: below the cap all prescribed readings are pinned.
Thus the whole-face coverage test succeeds for every row-layer ambient.

This is not yet capped lifting: inactive auxiliary controller readings must
also be retained by a whole section, and that is not asserted here.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SlotActiveCoverage

open Transform Value ExtOrd FreshSourceSlots DonorSlotAssembly

variable {X : Type*} [Fintype X]

def Fits (E p : X → ExtOrd) (v : ExtOrd) (j : Fin (Fintype.card X + 1)) : Prop :=
  ∀ d, E d ≠ ⊥ → (rank E d < j.val → p d ≤ v) ∧ (j.val ≤ rank E d → v ≤ p d)

theorem exists_fits (E p : X → ExtOrd) (v : ExtOrd)
    (horder : ∀ d e, E d ≤ E e → p d ≤ p e) : ∃ j, Fits E p v j := by
  refine ⟨⟨chooseSlot E p v, Nat.lt_succ_of_le (chooseSlot_le E p v)⟩, ?_⟩
  intro d hd
  exact ⟨fun h => before_slot horder h, fun h => after_slot hd h⟩

theorem old_index (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) (d : X)
    (hd : E d ≠ ⊥) :
    SlotControllerFamily.index q (position E (old d)) = 2 * rank E d + 2 := by
  simp only [position, old, ite_eq_right hd, SlotControllerFamily.old,
    SlotControllerFamily.index]

/-- A nearest fitting slot is ambient-active whenever the prescription reaches
the cap. Every old occurrence and the fresh occurrence participate in agreement. -/
theorem exists_active_fits {E p : X → ExtOrd} {v γ : ExtOrd} {a : Occ X → ExtOrd}
    (ha : Joint E a) (horder : ∀ d e, E d ≤ E e → p d ≤ p e)
    (hcap : ∀ d : Option X, min (a (.inl d)) γ = min (FreeDiagonal.append p v d) γ)
    (hreaches : ∃ d : Option X, γ ≤ FreeDiagonal.append p v d) :
    ∃ j, Fits E p v j ∧ γ ≤ a (controller j) := by
  classical
  obtain ⟨q, f, hm, _, _, hf⟩ := ha.exists_shape
  let S := Finset.univ.filter (Fits E p v)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := exists_fits E p v horder
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨j, hjS, hjmin⟩ := Finset.exists_min_image S
    (fun j => (j.val - q.val) + (q.val - j.val)) hS
  have hj : Fits E p v j := (Finset.mem_filter.mp hjS).2
  refine ⟨j, hj, ?_⟩
  by_contra hn
  have hlow : a (controller j) < γ := not_le.mp hn
  rcases lt_trichotomy j q with hjq | heq | hqj
  · let k : Fin (Fintype.card X + 1) := ⟨j.val + 1, by have hq := q.isLt; omega⟩
    have hk : Fits E p v k := by
      intro d hd
      refine ⟨?_, fun h => (hj d hd).2 (by dsimp [k] at h; omega)⟩
      intro hdk
      by_cases hdj : rank E d < j.val
      · exact (hj d hd).1 hdj
      have hdj : rank E d = j.val := by dsimp [k] at hdk; omega
      have he : a (old d) = a (controller j) := by
        rw [hf (old d), hf (controller j), old_index E q d hd]
        simp only [controller, position, SlotControllerFamily.controller,
          SlotControllerFamily.index, SlotControllerFamily.cross,
          ite_eq_right (ne_of_gt hjq), ite_eq_left hjq, hdj]
      have hdf : a (old d) ≤ a fresh := by
        rw [hf (old d), hf fresh, old_index E q d hd]
        apply hm
        change 2 * rank E d + 2 ≤ 2 * q.val + 1
        have hval : j.val < q.val := hjq
        omega
      have hpfix : p d = a (old d) :=
        ((FullRowLifting.cap_eq_iff_profile _ _ _).mp (hcap (some d)).symm).1
          (he.trans_lt hlow)
      rw [hpfix]
      calc
        a (old d) = min (a (old d)) γ := (min_eq_left (he.trans_lt hlow).le).symm
        _ ≤ min (a fresh) γ := min_le_min_right _ hdf
        _ = min v γ := hcap none
        _ ≤ v := min_le_left _ _
    have hcloser := hjmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    have hval : j.val < q.val := hjq
    dsimp [k] at hcloser
    omega
  · subst j
    obtain ⟨d, hd⟩ := hreaches
    have hact : γ ≤ a (.inl d) := by
      have he := hcap d
      rw [min_eq_right hd] at he
      exact min_eq_right_iff.mp he
    have hdom : a (.inl d) ≤ a (controller q) := by
      rw [hf (.inl d), hf (controller q)]
      change f (SlotControllerFamily.index q (position E (.inl d))) ≤
        f (SlotControllerFamily.index q (SlotControllerFamily.controller q))
      rw [SlotControllerFamily.index_diagonal]
      exact hm (SlotControllerFamily.index_le_height q _)
    exact (not_le_of_gt hlow) (hact.trans hdom)
  · let k : Fin (Fintype.card X + 1) := ⟨j.val - 1, by have hj' := j.isLt; omega⟩
    have hk : Fits E p v k := by
      intro d hd
      refine ⟨fun h => (hj d hd).1 (by dsimp [k] at h; omega), ?_⟩
      intro hkd
      by_cases hjd : j.val ≤ rank E d
      · exact (hj d hd).2 hjd
      have hdj : rank E d = j.val - 1 := by dsimp [k] at hkd; omega
      have he : a fresh = a (controller j) := by
        rw [hf fresh, hf (controller j)]
        simp only [fresh, controller, position, SlotControllerFamily.fresh,
          SlotControllerFamily.controller,
          SlotControllerFamily.index, SlotControllerFamily.cross,
          ite_eq_right (ne_of_lt hqj), ite_eq_right (not_lt_of_gt hqj)]
      have hfd : a fresh ≤ a (old d) := by
        rw [hf fresh, hf (old d), old_index E q d hd]
        apply hm
        change 2 * q.val + 1 ≤ 2 * rank E d + 2
        have hval : q.val < j.val := hqj
        omega
      have hvfix : v = a fresh :=
        ((FullRowLifting.cap_eq_iff_profile _ _ _).mp (hcap none).symm).1
          (he.trans_lt hlow)
      rw [hvfix]
      calc
        a fresh = min (a fresh) γ := (min_eq_left (he.trans_lt hlow).le).symm
        _ ≤ min (a (old d)) γ := min_le_min_right _ hfd
        _ = min (p d) γ := hcap (some d)
        _ ≤ p d := min_le_left _ _
    have hcloser := hjmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    have hval : q.val < j.val := hqj
    dsimp [k] at hcloser
    omega

/-- Fitting has the literal faithful whole-face consequence, not merely
pairwise separation. The old bottom pattern remains explicit. -/
theorem fits_transforms {E p : X → ExtOrd} {v : ExtOrd}
    (j : Fin (Fintype.card X + 1)) (hj : Fits E p v j)
    (hp : ∀ d, SelfVis 1 (p d)) (hv : SelfVis 1 v)
    (horder : ∀ d e, E d ≤ E e → p d ≤ p e) (hbot : ∀ d, E d = ⊥ → p d = ⊥) :
    TransformsTo (fun _ : Option X => 1) (fun d => DonorSlotAssembly.row E j (.inl d))
      (FreeDiagonal.append p v) := by
  classical
  have hvisible : ∀ d : Option X, SelfVis 1 (FreeDiagonal.append p v d) := by
    rintro (_ | d)
    · exact hv
    · exact hp d
  have hb : ∀ d : Option X, blocks E j.val d = none → FreeDiagonal.append p v d = ⊥ := by
    rintro (_ | d) h
    · cases h
    · by_cases hd : E d = ⊥
      · exact hbot d hd
      · simp only [blocks, oldBlock, ite_eq_right hd, Option.some_ne_none] at h
  have ho : ∀ d e : Option X, source (blocks E j.val d) ≤ source (blocks E j.val e) →
      FreeDiagonal.append p v d ≤ FreeDiagonal.append p v e := by
    intro d e h
    cases d with
    | none =>
      cases e with
      | none => exact le_rfl
      | some e =>
        by_cases he : E e = ⊥
        · have hh : SeparatedGradeOne.band (2 * j.val + 1) ≤ ⊥ := by
            simpa only [blocks, oldBlock, ite_eq_left he, source] using h
          exact False.elim ((not_ofOrd_le_bot _) hh)
        · have hh : 2 * j.val + 1 ≤ 2 * rank E e + 2 := by
            apply (band_le_iff _ _).mp
            simpa only [blocks, oldBlock, ite_eq_right he, source] using h
          exact (hj e he).2 (by omega)
    | some d =>
      cases e with
      | none =>
        by_cases hd : E d = ⊥
        · change p d ≤ v
          rw [hbot d hd]
          exact bot_le
        · have hh : 2 * rank E d + 2 ≤ 2 * j.val + 1 := by
            apply (band_le_iff _ _).mp
            simpa only [blocks, oldBlock, ite_eq_right hd, source] using h
          exact (hj d hd).1 (by omega)
      | some e => exact horder d e ((oldSource_le_iff E d e).mp h)
  apply (decoder_witness (blocks E j.val) (FreeDiagonal.append p v) hvisible).transformsTo
  intro d
  rw [base_reading, gTop_of_le le_rfl, min_top_right]
  exact (decoder_read _ _ ho hb d).symm

/-- The entire old/fresh prescription is covered by one ambient-active row.
This proves the coverage acceptance test, not preservation of auxiliary caps. -/
theorem active_whole_face_coverage {E p : X → ExtOrd} {v γ : ExtOrd}
    {a : Occ X → ExtOrd} (ha : Joint E a)
    (hp : ∀ d, SelfVis 1 (p d)) (hv : SelfVis 1 v)
    (horder : ∀ d e, E d ≤ E e → p d ≤ p e) (hbot : ∀ d, E d = ⊥ → p d = ⊥)
    (hcap : ∀ d : Option X, min (a (.inl d)) γ = min (FreeDiagonal.append p v d) γ)
    (hreaches : ∃ d : Option X, γ ≤ FreeDiagonal.append p v d) :
    ∃ j, γ ≤ a (controller j) ∧
      TransformsTo (fun _ : Option X => 1) (fun d => DonorSlotAssembly.row E j (.inl d))
        (FreeDiagonal.append p v) := by
  obtain ⟨j, hj, hact⟩ := exists_active_fits ha horder hcap hreaches
  exact ⟨j, hact, fits_transforms j hj hp hv horder hbot⟩

end VaughtConjecture.Knight.SlotActiveCoverage
