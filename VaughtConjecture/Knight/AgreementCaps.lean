/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

/-! # Agreement caps: the meet of two capped labellings in a coded alphabet

The full-scope families of the one-reference tower are labellings of a lower set together with a
cap; two members read one another at the **largest cap below which they agree**.  This module
supplies the value-level algebra:

* the **coded alphabet** `alph l I` at grade `l` with block bound `I` — `⊥` and the ordinals
  `ω·i + j` with `i < I`, `j ≤ l + 1` — a finite set of coded labels (`isCodedLabel_of_mem_alph`);
* **rounding down** `roundDown l I x`: the largest self-visible alphabet value below `x`; it is
  monotone, fixes self-visible alphabet values, and commutes with capping by a self-visible
  alphabet value (`roundDown_min_right`);
* the **agreement cap** `agreeCap F G` of two labellings of a finite index type: the largest `e`
  with `min (F z) e = min (G z) e` for every `z` (`le_agreeCap_iff`), `⊤` when `F = G`;
* the **ultrametric identity** `min_agreeCap_eq`: if `F` and `G` agree below `e`, then
  `agreeCap F H` and `agreeCap G H` agree below `e` for every `H`;
* the **level cap** `levelCap l I F γ G δ = roundDown l I (min (agreeCap F G) (min γ δ))` of
  two capped labellings — below both caps and below their agreement, self-visible, in the
  alphabet, equal to `γ` on the diagonal (`levelCap_self`), and satisfying the capped
  ultrametric identity `min_levelCap_eq`, which is the sibling locality of a family whose rows
  read one another by level caps.

Nothing here mentions cell schemes; the tower instantiates `Z` with a lower set.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

/-! ## The coded alphabet -/

/-- The **coded alphabet** at grade `l` with block bound `I`: `⊥` and `ω·i + j`, `i < I`,
`j ≤ l + 1`. -/
noncomputable def alph (l I : ℕ) : Finset ExtOrd :=
  insert ⊥ ((Finset.univ : Finset (Fin I × Fin (l + 2))).image
    fun ij => ofOrd (Ordinal.omega0 * ((ij.1 : ℕ) : Ordinal) + ((ij.2 : ℕ) : Ordinal)))

theorem bot_mem_alph (l I : ℕ) : (⊥ : ExtOrd) ∈ alph l I := Finset.mem_insert_self _ _

theorem mem_alph_iff {l I : ℕ} {x : ExtOrd} :
    x ∈ alph l I ↔ x = ⊥ ∨ ∃ i j : ℕ, i < I ∧ j ≤ l + 1 ∧
      x = ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)) := by
  simp only [alph, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro (h | ⟨i, j, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, j, i.2, Nat.lt_succ_iff.mp j.2, h.symm⟩
  · rintro (h | ⟨i, j, hi, hj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨i, hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩, h.symm⟩

theorem isCodedLabel_of_mem_alph {l I : ℕ} {x : ExtOrd} (h : x ∈ alph l I) : IsCodedLabel l x := by
  rcases mem_alph_iff.mp h with rfl | ⟨i, j, -, hj, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, j, hj, rfl⟩

theorem ne_top_of_mem_alph {l I : ℕ} {x : ExtOrd} (h : x ∈ alph l I) : x ≠ ⊤ := by
  rcases mem_alph_iff.mp h with rfl | ⟨i, j, -, -, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

/-! ## Rounding down to a self-visible alphabet value -/

open Classical in
/-- **Rounding down**: the largest self-visible value of the alphabet below `x` (`⊥` at worst). -/
noncomputable def roundDown (l I : ℕ) (x : ExtOrd) : ExtOrd :=
  ((alph l I).filter fun a => SelfVis l a ∧ a ≤ x).max'
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph l I, selfVis_bot l, bot_le⟩⟩

theorem roundDown_spec (l I : ℕ) (x : ExtOrd) :
    roundDown l I x ∈ alph l I ∧ SelfVis l (roundDown l I x) ∧ roundDown l I x ≤ x := by
  classical
  have h := Finset.max'_mem ((alph l I).filter fun a => SelfVis l a ∧ a ≤ x)
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph l I, selfVis_bot l, bot_le⟩⟩
  rw [Finset.mem_filter] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem roundDown_mem (l I : ℕ) (x : ExtOrd) : roundDown l I x ∈ alph l I :=
  (roundDown_spec l I x).1

theorem roundDown_selfVis (l I : ℕ) (x : ExtOrd) : SelfVis l (roundDown l I x) :=
  (roundDown_spec l I x).2.1

theorem roundDown_le (l I : ℕ) (x : ExtOrd) : roundDown l I x ≤ x :=
  (roundDown_spec l I x).2.2

theorem le_roundDown {l I : ℕ} {a x : ExtOrd} (ha : a ∈ alph l I) (hs : SelfVis l a)
    (hax : a ≤ x) : a ≤ roundDown l I x := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨ha, hs, hax⟩)

theorem roundDown_eq_self {l I : ℕ} {x : ExtOrd} (hx : x ∈ alph l I) (hs : SelfVis l x) :
    roundDown l I x = x :=
  le_antisymm (roundDown_le l I x) (le_roundDown hx hs le_rfl)

theorem roundDown_mono {l I : ℕ} {x y : ExtOrd} (hxy : x ≤ y) :
    roundDown l I x ≤ roundDown l I y :=
  le_roundDown (roundDown_mem l I x) (roundDown_selfVis l I x) ((roundDown_le l I x).trans hxy)

theorem roundDown_bot (l I : ℕ) : roundDown l I ⊥ = ⊥ :=
  le_bot_iff.mp (roundDown_le l I ⊥)

/-- Rounding commutes with capping by a self-visible alphabet value. -/
theorem roundDown_min_right {l I : ℕ} {e : ExtOrd} (he : e ∈ alph l I) (hs : SelfVis l e)
    (x : ExtOrd) : min (roundDown l I x) e = roundDown l I (min x e) := by
  rcases le_total e x with h | h
  · rw [min_eq_right h, min_eq_right (le_roundDown he hs h), roundDown_eq_self he hs]
  · rw [min_eq_left h, min_eq_left ((roundDown_le l I x).trans h)]

/-! ## Agreement caps -/

section Agreement

variable {Z : Type*} [Fintype Z]

open Classical in
/-- The **agreement cap** of two labellings: the largest value below which they agree —
the infimum, over the cells where they differ, of the smaller of the two labels (`⊤` if they
agree everywhere). -/
noncomputable def agreeCap (F G : Z → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun z => F z ≠ G z).inf fun z => min (F z) (G z)

/-- `e` is below the agreement cap exactly when the two labellings agree below `e`. -/
theorem le_agreeCap_iff {F G : Z → ExtOrd} {e : ExtOrd} :
    e ≤ agreeCap F G ↔ ∀ z, min (F z) e = min (G z) e := by
  classical
  unfold agreeCap
  rw [Finset.le_inf_iff]
  constructor
  · intro h z
    by_cases hz : F z = G z
    · rw [hz]
    · have := h z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      rw [le_min_iff] at this
      rw [min_eq_right this.1, min_eq_right this.2]
  · intro h z hz
    have hne : F z ≠ G z := (Finset.mem_filter.mp hz).2
    by_contra hlt
    rw [not_le, min_lt_iff] at hlt
    have hz' := h z
    rcases hlt with hF | hG
    · rw [min_eq_left hF.le] at hz'
      rcases le_total (G z) e with hGe | hGe
      · rw [min_eq_left hGe] at hz'; exact hne hz'
      · rw [min_eq_right hGe] at hz'; exact absurd hz' hF.ne
    · rw [min_eq_left hG.le] at hz'
      rcases le_total (F z) e with hFe | hFe
      · rw [min_eq_left hFe] at hz'; exact hne hz'
      · rw [min_eq_right hFe] at hz'; exact absurd hz'.symm hG.ne

theorem min_eq_of_le_agreeCap {F G : Z → ExtOrd} {e : ExtOrd} (he : e ≤ agreeCap F G) (z : Z) :
    min (F z) e = min (G z) e :=
  le_agreeCap_iff.mp he z

theorem min_eq_of_le_agreeCap_of_le {F G : Z → ExtOrd} {e x : ExtOrd} (he : e ≤ agreeCap F G)
    (hx : x ≤ e) (z : Z) : min (F z) x = min (G z) x := by
  calc min (F z) x = min (min (F z) e) x := by rw [min_assoc, min_eq_right hx]
    _ = min (min (G z) e) x := by rw [min_eq_of_le_agreeCap he z]
    _ = min (G z) x := by rw [min_assoc, min_eq_right hx]

theorem agreeCap_comm (F G : Z → ExtOrd) : agreeCap F G = agreeCap G F := by
  classical
  unfold agreeCap
  refine Finset.inf_congr ?_ fun z _ => min_comm _ _
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

theorem agreeCap_self (F : Z → ExtOrd) : agreeCap F F = ⊤ := by
  classical
  unfold agreeCap
  rw [Finset.filter_eq_empty_iff.mpr (fun z _ => not_not.mpr rfl), Finset.inf_empty]

/-- **The ultrametric identity**: labellings agreeing below `e` have agreement caps with any third
labelling that agree below `e`. -/
theorem min_agreeCap_eq {F G : Z → ExtOrd} {e : ExtOrd} (he : e ≤ agreeCap F G) (H : Z → ExtOrd) :
    min (agreeCap F H) e = min (agreeCap G H) e := by
  have key : ∀ x, x ≤ min (agreeCap F H) e ↔ x ≤ min (agreeCap G H) e := by
    intro x
    simp only [le_min_iff, le_agreeCap_iff]
    constructor
    · rintro ⟨h1, hx⟩
      exact ⟨fun z => by rw [← min_eq_of_le_agreeCap_of_le he hx z]; exact h1 z, hx⟩
    · rintro ⟨h1, hx⟩
      exact ⟨fun z => by rw [min_eq_of_le_agreeCap_of_le he hx z]; exact h1 z, hx⟩
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

/-! ## Level caps -/

/-- The **level cap** between two capped labellings: the agreement cap, capped by both caps,
rounded down to a self-visible alphabet value at grade `l`. -/
noncomputable def levelCap (l I : ℕ) (F : Z → ExtOrd) (γ : ExtOrd) (G : Z → ExtOrd) (δ : ExtOrd) :
    ExtOrd :=
  roundDown l I (min (agreeCap F G) (min γ δ))

variable (l I : ℕ) (F : Z → ExtOrd) (γ : ExtOrd) (G : Z → ExtOrd) (δ : ExtOrd)

theorem levelCap_mem : levelCap l I F γ G δ ∈ alph l I := roundDown_mem _ _ _

theorem levelCap_selfVis : SelfVis l (levelCap l I F γ G δ) := roundDown_selfVis _ _ _

theorem levelCap_le_agreeCap : levelCap l I F γ G δ ≤ agreeCap F G :=
  (roundDown_le _ _ _).trans (min_le_left _ _)

theorem levelCap_le_left : levelCap l I F γ G δ ≤ γ :=
  (roundDown_le _ _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem levelCap_le_right : levelCap l I F γ G δ ≤ δ :=
  (roundDown_le _ _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem levelCap_comm : levelCap l I F γ G δ = levelCap l I G δ F γ := by
  unfold levelCap
  rw [agreeCap_comm, min_comm γ δ]

/-- On the diagonal the level cap is the cap itself. -/
theorem levelCap_self (hγ : γ ∈ alph l I) (hs : SelfVis l γ) : levelCap l I F γ F γ = γ := by
  unfold levelCap
  rw [agreeCap_self, min_self, min_eq_right le_top, roundDown_eq_self hγ hs]

/-- The two labellings agree below their level cap. -/
theorem min_eq_of_levelCap (z : Z) :
    min (F z) (levelCap l I F γ G δ) = min (G z) (levelCap l I F γ G δ) :=
  min_eq_of_le_agreeCap (levelCap_le_agreeCap l I F γ G δ) z

/-- **The capped ultrametric identity**: below the level cap of `F` and `G`, the level caps of
`F` and of `G` with any third capped labelling agree. -/
theorem min_levelCap_eq (H : Z → ExtOrd) (ζ : ExtOrd) :
    min (levelCap l I F γ H ζ) (levelCap l I F γ G δ) =
      min (levelCap l I G δ H ζ) (levelCap l I F γ G δ) := by
  set e := levelCap l I F γ G δ with he
  have hem := levelCap_mem l I F γ G δ
  have hes := levelCap_selfVis l I F γ G δ
  unfold levelCap
  rw [roundDown_min_right hem hes, roundDown_min_right hem hes]
  congr 1
  have key : ∀ x, x ≤ min (min (agreeCap F H) (min γ ζ)) e ↔
      x ≤ min (min (agreeCap G H) (min δ ζ)) e := by
    intro x
    simp only [le_min_iff]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, hx⟩
      refine ⟨⟨?_, hx.trans (levelCap_le_right l I F γ G δ), h3⟩, hx⟩
      have := min_agreeCap_eq (levelCap_le_agreeCap l I F γ G δ) H
      exact (le_min_iff.mp (this ▸ le_min h1 hx)).1
    · rintro ⟨⟨h1, -, h3⟩, hx⟩
      refine ⟨⟨?_, hx.trans (levelCap_le_left l I F γ G δ), h3⟩, hx⟩
      have := min_agreeCap_eq (levelCap_le_agreeCap l I F γ G δ) H
      exact (le_min_iff.mp (this.symm ▸ le_min h1 hx)).1
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end Agreement

end VaughtConjecture.Knight
