/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungOnlyLadder
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Exact decoding of the complete rung table

The numerical table is defined at every retained anchor and every rung, even
when the input profile has no chosen anchor in the catalogue. Prefix agreement
does not need catalogue coverage. Lawfulness is asserted only when an actual
anchor has the input's rank profile.

Decoding a normalized table recovers its entire ceiling-filled table, not just
the represented field values. This is the base identity used by the recursive
renderer; it does not assert exact restriction between construction grades.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RungTableRendering
open Transform Value ExtOrd LadderScalarRendering
noncomputable section
variable {X B : Type*} [Fintype X] {H : ℕ}

/-- A monotone finite round trip transports every occupied and unused level. -/
theorem level_decode (p : X → ExtOrd) {f g : ExtOrd → ExtOrd}
    (hf : Monotone f) (hg : Monotone g) (hfbot : f ⊥ = ⊥) (hgbot : g ⊥ = ⊥)
    (hinv : ∀ d, g (f (p d)) = p d) (C : ExtOrd) (i : ℕ) :
    g (LadderScalarRendering.level (values (fun d => f (p d))) C i) =
      LadderScalarRendering.level (values p) (g C) i := by
  classical
  have hpos (d : X) : f (p d) ≠ ⊥ ↔ p d ≠ ⊥ := by
    constructor
    · intro h he; exact h (he ▸ hfbot)
    · intro h he
      exact h ((hinv d).symm.trans ((congrArg g he).trans hgbot))
  have himage : values (fun d => f (p d)) = (values p).image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy, d, rfl⟩ := mem_values.mp hy
      exact Finset.mem_image.mpr ⟨p d, mem_values.mpr ⟨(hpos d).mp hy, d, rfl⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hx, d, rfl⟩ := mem_values.mp hx
      exact mem_values.mpr ⟨(hpos d).mpr hx, d, rfl⟩
  have hcard : (values (fun d => f (p d))).card = (values p).card := by
    rw [himage]
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    obtain ⟨_, d, rfl⟩ := mem_values.mp hx
    obtain ⟨_, e, rfl⟩ := mem_values.mp hy
    simpa only [hinv] using congrArg g he
  have hr := ReceivingCatalogueRanks.fieldRank_of_leftInverse p hf hg hfbot hgbot hinv
  unfold LadderScalarRendering.level
  rw [hcard]
  split_ifs with hi
  · rfl
  · apply le_antisymm
    · by_cases hn : ((values (fun d => f (p d))).filter
          (fun x => rank (values (fun d => f (p d))) x ≤ i)).Nonempty
      · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
        rw [← he]
        obtain ⟨hxv, hxi⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx, d, rfl⟩ := mem_values.mp hxv
        simp only [id_eq, hinv]
        apply Finset.le_sup (f := id)
        refine Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos d).mp hx, d, rfl⟩, ?_⟩
        change fieldRank p d ≤ i
        change fieldRank (fun e => f (p e)) d ≤ i at hxi
        rwa [hr d] at hxi
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty, hgbot]
        exact bot_le
    · apply Finset.sup_le
      intro x hx
      obtain ⟨hxv, hxi⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx, d, rfl⟩ := mem_values.mp hxv
      rw [← hinv d]
      apply hg
      apply Finset.le_sup (f := id)
      refine Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos d).mpr hx, d, rfl⟩, ?_⟩
      change fieldRank (fun e => f (p e)) d ≤ i
      rw [hr d]
      exact hxi

/-- The full rank table, including foreign anchors and the unused ceiling tail. -/
def render (ranks : B → X → ℕ) (p : X → ExtOrd) (C : ExtOrd)
    (v : RungOnlyLadder.Point H B) : ExtOrd :=
  LadderScalarRendering.level (values p) C
    (min (FiniteProfileControllers.cut H (fieldRank p) (ranks v.1)) (v.2.val + 1))

theorem render_eq_image (ranks : B → X → ℕ) (a : B) (p : X → ExtOrd) (C : ExtOrd)
    (ha : ranks a = fieldRank p) (v : RungOnlyLadder.Point H B) :
    render ranks p C v =
      RungOnlyLadder.image ranks a (LadderScalarRendering.level (values p) C) v := by
  simp only [render, RungOnlyLadder.image, RungOnlyLadder.toFull,
    SupportLadderRows.image, SupportLadderRows.index, SupportLadderRows.rung,
    SupportLadderRows.parent, SupportLadderRows.ceiling, ha]

theorem render_lawful [Finite B] (ranks : B → X → ℕ) (a : B)
    {p : X → ExtOrd} {C : ExtOrd} (ha : ranks a = fieldRank p)
    (hp : ∀ d, SelfVis 1 (p d)) (hC : SelfVis 1 C) (hb : ∀ d, p d ≤ C) :
    RungOnlyLadder.Lawful (H := H) ranks (render ranks p C) := by
  have he : render (H := H) ranks p C =
      RungOnlyLadder.restrict (LadderScalarRendering.render ranks a p C) := by
    funext v
    exact render_eq_image ranks a p C ha v
  rw [he]
  exact RungOnlyLadder.Lawful.restrict (LadderScalarRendering.render_lawful ranks a hp hC hb)

/-- No anchor realizing either input is required for the numerical prefix theorem. -/
theorem render_agreement (ranks : B → X → ℕ) {p q : X → ExtOrd} {C h : ExtOrd}
    (hH : Fintype.card X + 1 ≤ H) (hp : ∀ d, p d ≤ C) (hq : ∀ d, q d ≤ C)
    (hC : h ≤ C) (hag : SourcePrefixRows.Agree p q h) :
    SourcePrefixRows.Agree (render (H := H) ranks p C) (render ranks q C) h := by
  let extended : B ⊕ Bool → X → ℕ := Sum.elim ranks
    (fun b => if b then fieldRank p else fieldRank q)
  intro v
  exact LadderScalarRendering.render_cap_agreement extended
    (a := .inr true) (b := .inr false) hH (fun _ => rfl) (fun _ => rfl)
    hp hq hC hag (.inl v.1, .inl v.2)

theorem render_bound (ranks : B → X → ℕ) {p : X → ExtOrd} {C : ExtOrd}
    (hb : ∀ d, p d ≤ C) (v : RungOnlyLadder.Point H B) : render ranks p C v ≤ C :=
  level_le (values_bound hb) _

theorem render_supported (ranks : B → X → ℕ) (p : X → ExtOrd) (C : ExtOrd)
    (v : RungOnlyLadder.Point H B) :
    render ranks p C v = ⊥ ∨ (∃ d, render ranks p C v = p d) ∨ render ranks p C v = C := by
  rcases level_supported (values p) C _ with hb | hv | hc
  · exact Or.inl hb
  · obtain ⟨_, d, hd⟩ := mem_values.mp hv
    exact Or.inr (Or.inl ⟨d, hd.symm⟩)
  · exact Or.inr (Or.inr hc)

/-- Exact whole-base decoding, with no omission of unused ranks or spare tips. -/
theorem decode_normalized (ranks : B → X → ℕ) (j : ℕ) (p : X → ExtOrd)
    (hp : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {C D : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hD : PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G C D = C)
    (v : RungOnlyLadder.Point H B) :
    PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G C
      (render ranks (PairedSlotEncoding.normalize j p) D v) = render ranks p C v := by
  let f := PairedSlotIncoming.encoder j (PairedSlotEncoding.values p)
  let g := PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G C
  have hf := PairedSlotIncoming.encoder_bounded j (PairedSlotEncoding.values p)
  have hg : Witness (gTop j) g := PairedSlotDecoder.decode_witness hG hC
  have hinv (d : X) : g (f (p d)) = p d := by
    dsimp only [f, g]
    rw [PairedSlotIncoming.encoder_profile]
    exact PairedSlotDecoder.decode_normalize hG hC hp d
  have hr : fieldRank (PairedSlotEncoding.normalize j p) = fieldRank p :=
    funext (ReceivingCatalogueRanks.fieldRank_normalize j p hp)
  unfold render
  rw [hr]
  have he := level_decode p hf.mono hg.mono hf.bot hg.bot hinv D
    (min (FiniteProfileControllers.cut H (fieldRank p) (ranks v.1)) (v.2.val + 1))
  simpa only [f, g, PairedSlotIncoming.encoder_profile, hD] using he

end
end VaughtConjecture.Knight.RungTableRendering
