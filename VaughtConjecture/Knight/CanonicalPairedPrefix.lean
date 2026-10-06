/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedEncoding
public import VaughtConjecture.Knight.PairedSlotComparison

/-! # Relative prefix room for canonical paired inventories

A complete field inventory is normalized at once. Literal low-prefix stability
is only half the assertion: new upper groups must not enter below the old cut.
The canonical fixed-point hypothesis supplies exactly this relative slot bound.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalPairedPrefix
open Transform Value ExtOrd PairedSlotEncoding CanonicalPairedEncoding
noncomputable section

def lowerGroups (j : ℕ) (S : Finset Ordinal.{0}) (h : Ordinal.{0}) : ℕ :=
  ((PairedSlotEncoding.keys j S).filter (· < h)).card

/-- If a canonical field reaches a grid cut, the unchanged lower groups leave
enough room for a new point group at or above that cut. -/
theorem cut_le_next_slot {j B : ℕ} {S : Finset Ordinal.{0}}
    (hc : ∀ a ∈ S, encode j S a = ofOrd a)
    (hu : ∃ a ∈ S, Ordinal.omega0 * B + j ≤ a) :
    (Ordinal.omega0 : Ordinal.{0}) * B + j ≤
      Ordinal.omega0 * (2 * lowerGroups j S (Ordinal.omega0 * B + j) + 1 : ℕ) + j := by
  classical
  let h := Ordinal.omega0 * B + j
  let U := S.filter (fun a => h ≤ a)
  have hU : U.Nonempty := by
    obtain ⟨a, ha, hh⟩ := hu
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hh⟩⟩
  obtain ⟨a, haU, hmin⟩ := U.exists_min_image id hU
  have ha := (Finset.mem_filter.mp haU).1
  have hha : h ≤ a := (Finset.mem_filter.mp haU).2
  have he : a = codeOrd j S a := (ofOrd_inj.mp (hc a ha)).symm
  by_cases hk : key j S a < h
  · have hr : PairedSlotEncoding.rank j S a < lowerGroups j S h := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (fun x hx =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2.trans hk⟩)).mpr
      exact ⟨key j S a, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha, hk⟩,
        by simp⟩
    have hb : block j S a ≤ 2 * lowerGroups j S h + 1 := by
      unfold block
      split_ifs <;> omega
    apply hha.trans
    rw [he]
    exact add_le_add (by gcongr) (Nat.cast_le.mpr (offset_le j S a))
  · have hf : (PairedSlotEncoding.keys j S).filter (· < key j S a) =
        (PairedSlotEncoding.keys j S).filter (· < h) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxa⟩
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        have hba : b < a := by
          by_contra hn
          exact hxa.not_ge (key_mono j S (not_lt.mp hn))
        have hbh : b < h := by
          by_contra hn
          exact hba.not_ge (hmin b (Finset.mem_filter.mpr ⟨hb, not_lt.mp hn⟩))
        exact ⟨Finset.mem_image_of_mem _ hb, (key_le j S b).trans_lt hbh⟩
      · rintro ⟨hx, hxh⟩
        exact ⟨hx, hxh.trans_le (not_lt.mp hk)⟩
    have hr : PairedSlotEncoding.rank j S a = lowerGroups j S h := congrArg Finset.card hf
    by_cases ho : Orbit j S a
    · obtain ⟨b, hb, hbj, hba⟩ := ho.2
      have hhb : h ≤ b := by
        apply (not_lt.mp hk).trans
        simpa only [key, ite_eq_left ho, ← hba] using limitPart_le b
      have hab := hmin b (Finset.mem_filter.mpr ⟨hb, hhb⟩)
      have haj : finitePart a < j :=
        (finitePart_le_of_le_of_limitPart_eq hab hba.symm).trans_lt hbj
      have hB : B ≤ 2 * lowerGroups j S h + 1 := by
        by_contra hn
        have hblock : block j S a ≤ B := by
          simp only [block, ite_eq_left ho, hr]
          omega
        have hsmall : a < h := by
          rw [he]
          apply lt_of_lt_of_le
            ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr
              (show offset j S a < j by simpa only [offset, ite_eq_left ho] using haj)))
          exact add_le_add (by gcongr) le_rfl
        exact hsmall.not_ge hha
      exact add_le_add (by gcongr) le_rfl
    · have hh : codeOrd j S a =
          Ordinal.omega0 * (2 * lowerGroups j S h + 1 : ℕ) + j := by
        simp only [codeOrd, block, offset, ite_eq_right ho, hr]
      exact hha.trans_eq (he.trans hh)

section Profile
variable {X : Type*} [Fintype X]

theorem fixed_values {j : ℕ} {p : X → ExtOrd}
    (hc : normalize j p = p) : ∀ a ∈ values p, encode j (values p) a = ofOrd a := by
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  exact (normalize_ofOrd hd).symm.trans ((congrFun hc d).trans hd)

theorem normalize_upper {j B : ℕ} {p q : X → ExtOrd}
    (hc : normalize j p = p) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (q d) (ofOrd (Ordinal.omega0 * B + j)))
    (d : X) (hd : ofOrd (Ordinal.omega0 * B + j) ≤ q d) :
    ofOrd (Ordinal.omega0 * B + j) ≤ normalize j q d := by
  classical
  let h := Ordinal.omega0 * B + j
  have hv : j ≤ finitePart h := by simp only [h, finitePart_mul_add, le_refl]
  have hpref := keys_prefix hv (values_prefix hag)
  have hl : lowerGroups j (values p) h = lowerGroups j (values q) h :=
    congrArg Finset.card hpref
  have hpd : ofOrd h ≤ p d := by
    have he := hag d
    rw [min_eq_right hd] at he
    exact (min_eq_right_iff.mp he)
  have hu : ∃ a ∈ values p, h ≤ a := by
    rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
    · exact (ofOrd_ne_bot h (le_bot_iff.mp (hb ▸ hpd))).elim
    · exact (hp d ht).elim
    · exact ⟨a, mem_values.mpr ⟨d, ha⟩, ofOrd_le_ofOrd.mp (ha ▸ hpd)⟩
  have hbound := cut_le_next_slot (B := B) (fixed_values hc) hu
  rw [hl] at hbound
  rcases ExtOrd.cases (q d) with hb | ht | ⟨a, ha⟩
  · exact (ofOrd_ne_bot h (le_bot_iff.mp (hb ▸ hd))).elim
  · simp only [PairedSlotEncoding.normalize, ht, le_top]
  · have haS : a ∈ values q := mem_values.mpr ⟨d, ha⟩
    have hha : h ≤ a := ofOrd_le_ofOrd.mp (ha ▸ hd)
    by_cases hk : key j (values q) a < h
    · have ho : Orbit j (values q) a := by
        by_contra hn
        simp only [key, ite_eq_right hn] at hk
        exact hk.not_ge hha
      obtain ⟨b, hbS, hbj, hba⟩ := ho.2
      have hbh : b < h := invisible_lt_cut hbj hv (by
        simpa only [key, ite_eq_left ho, ← hba] using hk)
      obtain ⟨e, he⟩ := mem_values.mp hbS
      have hlow : normalize j q e = q e := by
        have heqOld : p e = q e :=
          (eq_of_cap_eq_lt (hag e).symm (he ▸ ofOrd_lt_ofOrd.mpr hbh)).symm
        have hpe : p e < ofOrd h := heqOld ▸ he ▸ ofOrd_lt_ofOrd.mpr hbh
        calc
          normalize j q e = normalize j p e := (normalize_prefix hv hag e hpe).symm
          _ = p e := congrFun hc e
          _ = q e := heqOld
      have haround : ofOrd a ≤ extVisibilityReplace (ofOrd b) j j := by
        rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hbj,
          ordinalReplace, hba]
        apply ofOrd_le_ofOrd.mpr
        calc
          a = limitPart a + finitePart a := (limitPart_add_finitePart a).symm
          _ ≤ limitPart a + j := add_le_add_right (Nat.cast_le.mpr ho.1) _
      have hround : extVisibilityReplace (ofOrd b) j j = ofOrd h := by
        apply le_antisymm
        · exact (evr_mono (ofOrd_lt_ofOrd.mpr hbh).le (le_refl j)).trans_eq
            (selfVis_ofOrd_iff.mpr hv)
        · exact (ofOrd_le_ofOrd.mpr hha).trans haround
      have heq : ofOrd a = ofOrd h := le_antisymm
        (haround.trans_eq hround) (ofOrd_le_ofOrd.mpr hha)
      have hw := (PairedSlotIncoming.encoder_bounded j (values q)).comm
        (ofOrd b) j j le_rfl le_rfl
      rw [hround, ← heq, PairedSlotIncoming.encoder_at haS,
        ← he, PairedSlotIncoming.encoder_profile, hlow, he, hround] at hw
      rw [normalize_ofOrd ha, hw]
    · have hr : lowerGroups j (values q) h ≤ PairedSlotEncoding.rank j (values q) a :=
        Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans_le (not_lt.mp hk)⟩)
      rw [normalize_ofOrd ha]
      apply ofOrd_le_ofOrd.mpr
      apply hbound.trans
      by_cases ho : Orbit j (values q) a
      · have hb : 2 * lowerGroups j (values q) h + 1 < block j (values q) a := by
          simp only [block, ite_eq_left ho]
          omega
        exact (code_add_lt_mul (Nat.cast_lt.mpr hb) j).le.trans le_self_add
      · have hb : 2 * lowerGroups j (values q) h + 1 ≤ block j (values q) a := by
          simp only [block, ite_eq_right ho]
          omega
        exact add_le_add (by gcongr) (by simp only [offset, ite_eq_right ho, le_refl])

/-- Relative normalization retains the entire original cut, not only the
coordinates strictly below it. The ambient must be a proper canonical fixed point. -/
theorem normalize_cap {j B : ℕ} {p q : X → ExtOrd}
    (hc : normalize j p = p) (hp : ∀ d, p d ≠ ⊤)
    (hag : ∀ d, min (p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (q d) (ofOrd (Ordinal.omega0 * B + j))) (d : X) :
    min (normalize j q d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (p d) (ofOrd (Ordinal.omega0 * B + j)) := by
  by_cases hd : p d < ofOrd (Ordinal.omega0 * B + j)
  · rw [← normalize_prefix (by simp only [finitePart_mul_add, le_refl]) hag d hd, hc]
  · have hqd : ofOrd (Ordinal.omega0 * B + j) ≤ q d := by
      have he := hag d
      rw [min_eq_right (not_lt.mp hd)] at he
      exact min_eq_right_iff.mp he.symm
    rw [min_eq_right (normalize_upper hc hp hag d hqd), min_eq_right (not_lt.mp hd)]

end Profile
end
end VaughtConjecture.Knight.CanonicalPairedPrefix
