/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ContextSourceRowRespect

/-! # The cross-grade recoding transformation

The reviewer's assignment (2026-09-15): the faithful transformation between two new rows that
recode the same labels at two grades — retaining actual occurrences, controller caps and
literal top; a triangle identity for codes is not by itself that transformation.

**The statement.**  On any family of cells of grade `≤ l'` labelled in `S ∪ {⊥, ⊤}`, the
counted encoding at `l'` transforms (Def. 2.3.9, faithful, unguarded clause 5) to the counted
encoding at any `l ≥ l'`, capped at any `ρ` self-visible at `l'` (`crossGrade_transformsTo`);
in the literal-top form used by the actual rows, where `⊤` is coded as the cap code, the
capped encodings transform likewise (`crossGrade_transformsTo_capped`).  **The witness** is
explicit: the shifter decodes at `l'` and re-encodes at `l` (`encT l S ∘ shift l' S ⊤`, capped
at the cap code in the literal-top form), the suppressor is `ρ` through grade `l'` and `⊥`
above.  No transitivity of `⇒` is used: every clause is verified on the composite directly —
the decoder's outputs are keyed at every higher level (`keyed_shift`), so the encoding is
monotone on them; clause 5 at thresholds `≤ l'` is the decoder's and the encoder's commutation
with replacement, and above `l'` the suppressor is `⊥` and the decoder propagates `⊥`; the
composite recovers the higher encoding on the value set (`encT_shift_encT`).

**On the actual context** (`ContextSourceRow.crossGrade_actual`): the candidate rows over the
receiver's reference context at two grades `l' ≤ l` — the actual labels and the requested
value recoded at each grade (`codeLabelAt`, which at grade `N` is the candidate controller row,
`codeLabelAt_N`) — satisfy the locality a lower new cell owes a higher one, with the higher row's
own value at the lower cell as the cap.  This discharges obligation (2) of the mixed-cell
isolation in `Knight/ContextSourceRow.lean`'s successor record for rows that recode the actual
labels; the own values of new cells (1) and bountifulness at the mixed pairs (3) are untouched.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section CrossGrade

variable (l l' : ℕ) (S : Finset Ordinal.{0})

/-- **The decoder's outputs are keyed at every higher level**: a decoded value is `⊥`, `⊤`
(the cap), a block key plus an offset `≤ l'`, or a large key — all keyed at `l ≥ l'`. -/
theorem keyed_shift (hll' : l' ≤ l) (x : ExtOrd) : Keyed l S (shift l' S ⊤ x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]
    exact keyed_bot l S
  · rw [shift_top]
    exact keyed_top l S
  · rw [shift_ofOrd]
    split_ifs with h
    · exact keyed_top l S
    · rcases hk : keyAt l' S (blockIdx α) with _ | κ
      · exact keyed_bot l S
      · obtain ⟨v, hv, hvκ⟩ := Finset.mem_image.mp (keyAt_mem l' S hk)
        change Keyed l S (ofOrd (decodeIn l' κ (finitePart α)))
        unfold decodeIn
        split_ifs with h0
        · have hfp : finitePart v ≤ l' := by
            by_contra hfp
            rw [← hvκ] at h0
            unfold keyOrd at h0
            rw [ite_eq_right hfp] at h0
            exact hfp (h0 ▸ Nat.zero_le _)
          have hκlp : κ = limitPart v := by
            rw [← hvκ]
            unfold keyOrd
            rw [ite_eq_left hfp]
          subst hκlp
          refine Or.inr (Or.inr ⟨_, rfl, ?_⟩)
          have hkey : keyOrd l (limitPart v + ((min (finitePart α) l' : ℕ) : Ordinal)) =
              limitPart v := by
            unfold keyOrd
            rw [finitePart_limitPart_add_nat, ite_eq_left ((min_le_right _ _).trans hll'),
              limitPart_limitPart_add_nat]
          rw [hkey]
          refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
          unfold keyOrd
          rw [ite_eq_left (hfp.trans hll')]
        · have hκv : κ = v := by
            rw [← hvκ]
            unfold keyOrd
            split_ifs with hfp
            · exfalso
              apply h0
              rw [← hvκ]
              unfold keyOrd
              rw [ite_eq_left hfp]
              exact finitePart_limitPart v
            · rfl
          subst hκv
          exact Or.inr (Or.inr ⟨_, rfl, keyOrd_mem_keys l S hv⟩)

/-- Decoding at `l'` and re-encoding at `l` recovers the encoding at `l` on `S`-valued labels. -/
theorem encT_shift_encT {x : ExtOrd} (hx : x = ⊥ ∨ x = ⊤ ∨ ∃ v ∈ S, x = ofOrd v) :
    encT l S (shift l' S ⊤ (encT l' S x)) = encT l S x := by
  rcases hx with rfl | rfl | ⟨v, hv, rfl⟩
  · rfl
  · rfl
  · rw [encT_ofOrd l' S, encOrdK_eq_code, shift_code l' S ⊤ hv]

/-- **The cross-grade recoding transformation**: on cells of grade `≤ l'` labelled in
`S ∪ {⊥, ⊤}`, the encoding at `l'` transforms to the encoding at `l ≥ l'` capped at any `ρ`
self-visible at `l'`.  Witness: decode at `l'`, re-encode at `l`; suppressor `ρ` through `l'`. -/
theorem crossGrade_transformsTo {D : Type*} (grade : D → ℕ) (hll' : l' ≤ l)
    (hgr : ∀ d, grade d ≤ l') (p : D → ExtOrd)
    (hp : ∀ d, p d = ⊥ ∨ p d = ⊤ ∨ ∃ v ∈ S, p d = ofOrd v) {ρ : ExtOrd} (hρ : SelfVis l' ρ) :
    TransformsTo grade (fun d => encT l' S (p d)) (fun d => min (encT l S (p d)) ρ) := by
  refine ⟨fun k => if k ≤ l' then ρ else ⊥, fun x => encT l S (shift l' S ⊤ x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro k
    dsimp only
    split_ifs with h
    · exact (hρ.mono h).symm
    · exact (extVisibilityReplace_bot _ _).symm
  · change encT l S (shift l' S ⊤ ⊥) = ⊥
    rw [shift_bot]
    rfl
  · intro x y hxy
    exact encT_le_keyed l S (keyed_shift l l' S hll' x) (keyed_shift l l' S hll' y)
      (shift_mono l' S ⊤ (extVisibilityReplace_top _ _) (fun _ _ => le_top) hxy)
  · intro x k hle i hi
    dsimp only at hle ⊢
    by_cases hk : k ≤ l'
    · rw [shift_evr_of_le l' S ⊤ (extVisibilityReplace_top _ _) hk x hi,
        encT_evr_of_le l S (hk.trans hll') _ hi]
    · rw [ite_eq_right hk] at hle
      have hbot : encT l S (shift l' S ⊤ x) = ⊥ := le_bot_iff.mp hle
      have hbot' := (encT_eq_bot_iff l S _).mp hbot
      rw [shift_evr_of_bot l' S ⊤ x k i hbot', hbot, encT_bot, extVisibilityReplace_bot]
  · intro d
    dsimp only
    rw [ite_eq_left (hgr d), encT_shift_encT l l' S (hp d)]

/-- **The literal-top form**: with `⊤` coded as the cap code at each grade, the capped encoding
at `l'` transforms to the capped encoding at `l ≥ l'`, capped at `ρ`.  Witness: decode at
`l'`, re-encode at `l`, cap at the cap code of `l`. -/
theorem crossGrade_transformsTo_capped {D : Type*} (grade : D → ℕ) (hll' : l' ≤ l)
    (hgr : ∀ d, grade d ≤ l') (p : D → ExtOrd)
    (hp : ∀ d, p d = ⊥ ∨ p d = ⊤ ∨ ∃ v ∈ S, p d = ofOrd v) {ρ : ExtOrd} (hρ : SelfVis l' ρ) :
    TransformsTo grade (fun d => min (encT l' S (p d)) (ofOrd (capCode l' S)))
      (fun d => min (min (encT l S (p d)) (ofOrd (capCode l S))) ρ) := by
  have hcapvis : ∀ k, k ≤ l' → SelfVis k (ofOrd (capCode l S)) :=
    fun k hk => (capCode_selfVis l S).mono (hk.trans hll')
  have hmono : Monotone (fun x => encT l S (shift l' S ⊤ x)) := fun x y hxy =>
    encT_le_keyed l S (keyed_shift l l' S hll' x) (keyed_shift l l' S hll' y)
      (shift_mono l' S ⊤ (extVisibilityReplace_top _ _) (fun _ _ => le_top) hxy)
  refine ⟨fun k => if k ≤ l' then ρ else ⊥,
    fun x => min (encT l S (shift l' S ⊤ x)) (ofOrd (capCode l S)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro k
    dsimp only
    split_ifs with h
    · exact (hρ.mono h).symm
    · exact (extVisibilityReplace_bot _ _).symm
  · change min (encT l S (shift l' S ⊤ ⊥)) _ = ⊥
    rw [shift_bot, encT_bot]
    exact min_eq_left bot_le
  · exact hmono.min monotone_const
  · intro x k hle i hi
    dsimp only at hle ⊢
    by_cases hk : k ≤ l'
    · rw [shift_evr_of_le l' S ⊤ (extVisibilityReplace_top _ _) hk x hi,
        encT_evr_of_le l S (hk.trans hll') _ hi,
        (extVisibilityReplace_mono k i hi).map_min,
        evr_eq_self_of_selfVis (hcapvis k hk) i]
    · rw [ite_eq_right hk] at hle
      have hbot : min (encT l S (shift l' S ⊤ x)) (ofOrd (capCode l S)) = ⊥ := le_bot_iff.mp hle
      rcases min_eq_bot.mp hbot with hb | hb
      · have hbot' := (encT_eq_bot_iff l S _).mp hb
        rw [shift_evr_of_bot l' S ⊤ x k i hbot', hbot, encT_bot, extVisibilityReplace_bot]
        exact min_eq_left bot_le
      · exact absurd hb (ofOrd_ne_bot _)
  · intro d
    dsimp only
    rw [ite_eq_left (hgr d)]
    rcases hp d with h | h | ⟨v, hv, h⟩ <;> rw [h]
    · simp only [encT_bot, shift_bot, min_eq_left bot_le]
    · simp only [encT_top, min_eq_right le_top, shift_capCode]
    · rw [encT_ofOrd l' S, encOrdK_eq_code,
        min_eq_left (ofOrd_le_ofOrd.mpr (code_le_capCode l' S v)), shift_code l' S ⊤ hv]

end CrossGrade

/-! ## On the actual context -/

namespace ContextSourceRow

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {r : BlockRequest} (C : ReferenceContext R t [r])

/-- The recoding of a label at grade `l` over the context's values, `⊤` as the cap code. -/
noncomputable def codeLabelAt (l : ℕ) (x : ExtOrd) : ExtOrd :=
  min (encT l (vals C) x) (ofOrd (capCode l (vals C)))

/-- At the threshold `N` this is the candidate controller row's recoding. -/
theorem codeLabelAt_N (x : ExtOrd) : codeLabelAt C C.N x = codeLabel C x :=
  (codeLabel_eq_cap C x).symm

/-- The actual labels lie in the context's values, `⊥` or `⊤`. -/
theorem actual_mem (c : cellType C) :
    actual C c = ⊥ ∨ actual C c = ⊤ ∨ ∃ v ∈ vals C, actual C c = ofOrd v := by
  rcases c with d | u
  · change C.p₀.label d.1 = ⊥ ∨ C.p₀.label d.1 = ⊤ ∨ ∃ v ∈ vals C, C.p₀.label d.1 = ofOrd v
    rcases ExtOrd.cases (C.p₀.label d.1) with h | h | ⟨v, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨v, mem_vals_of_label C h, h⟩)
  · exact Or.inr (Or.inr ⟨r.value, value_mem_vals C, rfl⟩)

/-- **Cross-grade locality between two candidate rows over the actual context**: on the cells
of grade `≤ l'`, the recoding at `l'` of the actual labels transforms to the recoding at
`l ≥ l'`, capped at any `ρ` self-visible at `l'` — in particular at the higher row's own value
at the lower cell. -/
theorem crossGrade_actual {l l' : ℕ} (hll' : l' ≤ l) {ρ : ExtOrd} (hρ : SelfVis l' ρ) :
    TransformsTo (fun c : {c : cellType C // grade C c ≤ l'} => grade C c.1)
      (fun c => codeLabelAt C l' (actual C c.1))
      (fun c => min (codeLabelAt C l (actual C c.1)) ρ) :=
  crossGrade_transformsTo_capped l l' (vals C) _ hll'
    (fun c : {c : cellType C // grade C c ≤ l'} => c.2)
    (fun c : {c : cellType C // grade C c ≤ l'} => actual C c.1)
    (fun c : {c : cellType C // grade C c ≤ l'} => actual_mem C c.1) hρ

end ContextSourceRow

end VaughtConjecture.Knight
