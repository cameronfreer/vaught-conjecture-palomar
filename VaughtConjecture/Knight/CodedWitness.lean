/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AgreementCaps
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.RowFactorization
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Base labellings, their counted recoding, and the decoder

The full-scope families of the one-reference tower are built from **base labellings**: labellings
of the base cells of grade `≤ k` that respect the base semantics (`RespectsBase`: orderly, local at
every base controller, available among the base cells).  Restriction to a lower grade preserves
respect (`RespectsBase.restrict`).

A level-two member owns, at level one, the **counted recoding** of its grade-`≤ 1` part
(`Knight/CountedRecoding.lean`, `Knight/CountedEncoding.lean`): the coded labelling
`encT 1 S ∘ F` respects the base semantics again (`RespectsBase.encode`) — locality by the
capped-locality recoding theorem `coded_locality_S` with the encoding's monotonicity on keyed
values, orderliness by `code_selfVis`, availability by `encT_le_keyed` — and takes coded values
with blocks bounded by the number of base cells (`encT_mem_alph`).  The decoder `shift 1 S γ` is a
`Decoder 1 c` for every cap (`shiftDecoder`): it fixes `⊥`, is monotone, its `⊥` outputs are stable
under visibility replacement, and it commutes with replacement at threshold `≤ 1`
(`shift_evr_of_le`).  Its outputs at self-visible inputs are self-visible at grade one
(`shift_selfVis_one`) and, for a value set coded at grade two, coded at grade two
(`shift_isCoded_two`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## Base labellings -/

/-- The base cells of grade at most `k`. -/
abbrev BaseCells (D₀ : CellScheme A) (k : ℕ) : Type := {d : Cell D₀ // D₀.grade d ≤ k}

/-- A labelling of the base cells of grade `≤ k` **respects the base semantics**: orderly, local at
every base controller of grade `≤ k`, available among the base cells. -/
structure RespectsBase (sem₀ : Semantics D₀) (k : ℕ) (F : BaseCells D₀ k → ExtOrd) : Prop where
  /-- Each label is self-visible at its cell's grade. -/
  orderly : ∀ d, SelfVis (D₀.grade d.1) (F d)
  /-- Locality at every base controller. -/
  locality : ∀ y : BaseCells D₀ k,
    TransformsTo (fun d : D₀.below (D₀.cell y.1) => D₀.grade d.1) (sem₀.E y.1)
      (fun d => min (F ⟨d.1, (d.2.2 : D₀.grade d.1 ≤ D₀.grade y.1).trans y.2⟩) (F y))
  /-- Availability among the base cells. -/
  availability : ∀ Sig Xi₀ : BaseCells D₀ k, D₀.scope Sig.1 ⊆ D₀.scope Xi₀.1 →
    D₀.grade Sig.1 = D₀.grade Xi₀.1 →
    ∃ Xi : BaseCells D₀ k, D₀.cell Xi.1 = D₀.cell Xi₀.1 ∧ F Sig ≤ F Xi

variable {sem₀ : Semantics D₀}

/-- Restriction of a base labelling to a lower grade. -/
def BaseCells.restrict {j k : ℕ} (hjk : j ≤ k) (F : BaseCells D₀ k → ExtOrd) :
    BaseCells D₀ j → ExtOrd :=
  fun d => F ⟨d.1, d.2.trans hjk⟩

/-- Restriction preserves respect. -/
theorem RespectsBase.restrict {k : ℕ} {F : BaseCells D₀ k → ExtOrd} (h : RespectsBase sem₀ k F)
    {j : ℕ} (hjk : j ≤ k) : RespectsBase sem₀ j (BaseCells.restrict hjk F) where
  orderly d := h.orderly ⟨d.1, d.2.trans hjk⟩
  locality y := h.locality ⟨y.1, y.2.trans hjk⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hXi, hle⟩ := h.availability ⟨Sig.1, Sig.2.trans hjk⟩ ⟨Xi₀.1, Xi₀.2.trans hjk⟩ hs hg
    refine ⟨⟨Xi.1, ?_⟩, hXi, hle⟩
    unfold CellScheme.grade
    rw [hXi]
    exact Xi₀.2

/-- The constantly-`⊥` labelling respects the base semantics. -/
theorem respectsBase_bot (sem₀ : Semantics D₀) (k : ℕ) :
    RespectsBase sem₀ k (fun _ : BaseCells D₀ k => ⊥) where
  orderly d := (extVisibilityReplace_bot (D₀.grade d.1) (D₀.grade d.1)).symm
  locality y :=
    ⟨fun _ => ⊤, fun _ => ⊥, fun _ _ _ => le_refl ⊤, fun _ => rfl, rfl, monotone_const,
      fun _ _ _ _ _ => (extVisibilityReplace_bot _ _).symm, fun _ => by simp⟩
  availability Sig Xi₀ _ _ := ⟨Xi₀, rfl, le_rfl⟩

/-! ## The counted recoding of a base labelling -/

section Encode

variable {l : ℕ} {F : BaseCells D₀ l → ExtOrd}

/-- The value set of a base labelling: its ordinal values. -/
noncomputable def baseRange (F : BaseCells D₀ l → ExtOrd) : Finset Ordinal.{0} := primRange F

theorem keyed_baseRange (F : BaseCells D₀ l → ExtOrd) (d : BaseCells D₀ l) :
    Keyed l (baseRange F) (F d) :=
  keyed_target l F d

/-- **The counted recoding respects the base semantics.** -/
theorem RespectsBase.encode (h : RespectsBase sem₀ l F) :
    RespectsBase sem₀ l (fun d => encT l (baseRange F) (F d)) where
  orderly d := by
    rcases ExtOrd.cases (F d) with hb | ht | ⟨v, hv⟩
    · rw [hb, encT_bot]; exact selfVis_bot _
    · rw [ht, encT_top]; exact extVisibilityReplace_top _ _
    · rw [hv, encT_ofOrd, encOrdK_eq_code]
      have ho := h.orderly d
      rw [hv, selfVis_ofOrd_iff] at ho
      exact code_selfVis _ _ ho d.2
  locality y := by
    let _ : Fintype (D₀.below (D₀.cell y.1)) := Fintype.ofFinite _
    have key := coded_locality_S (fun d : D₀.below (D₀.cell y.1) => D₀.grade d.1) (sem₀.E y.1)
      (fun d => F ⟨d.1, (d.2.2 : D₀.grade d.1 ≤ D₀.grade y.1).trans y.2⟩)
      ⟨y.1, GradedLe.refl _⟩ (fun d => d.2.2) (fun d => h.orderly _) (h.locality y) y.2
      (baseRange F) (fun d => keyed_min _ _ (keyed_baseRange F _) (keyed_baseRange F _))
    convert key using 1
    funext d
    exact (encT_min_keyed _ _ (keyed_baseRange F _) (keyed_baseRange F _)).symm
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hXi, hle⟩ := h.availability Sig Xi₀ hs hg
    exact ⟨Xi, hXi, encT_le_keyed _ _ (keyed_baseRange F _) (keyed_baseRange F _) hle⟩

/-- The number of keys is at most the number of base cells. -/
theorem card_keys_baseRange_le (F : BaseCells D₀ l → ExtOrd) :
    (keys l (baseRange F)).card ≤ Fintype.card (BaseCells D₀ l) := by
  classical
  calc (keys l (baseRange F)).card ≤ (baseRange F).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (BaseCells D₀ l)).card := by
        unfold baseRange primRange
        calc (Finset.univ.biUnion fun d : BaseCells D₀ l =>
              match F d with | some (some v) => ({v} : Finset Ordinal.{0}) | _ => ∅).card
            ≤ ∑ d : BaseCells D₀ l,
                (match F d with | some (some v) => ({v} : Finset Ordinal.{0}) | _ => ∅).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _d : BaseCells D₀ l, 1 := by
              refine Finset.sum_le_sum fun d _ => ?_
              rcases ExtOrd.cases (F d) with hb | ht | ⟨v, hv⟩
              · rw [hb]; exact zero_le_one
              · rw [ht]; exact zero_le_one
              · rw [hv]; exact le_rfl
          _ = (Finset.univ : Finset (BaseCells D₀ l)).card := by simp
    _ = Fintype.card (BaseCells D₀ l) := Finset.card_univ

/-- The coded values lie in the alphabet at grade `l` once the block bound exceeds the number of
base cells by two. -/
theorem encT_mem_alph {I : ℕ} (hI : Fintype.card (BaseCells D₀ l) + 2 ≤ I)
    (F : BaseCells D₀ l → ExtOrd) (d : BaseCells D₀ l) (hne : F d ≠ ⊤) :
    encT l (baseRange F) (F d) ∈ alph l I := by
  rcases ExtOrd.cases (F d) with hb | ht | ⟨v, hv⟩
  · rw [hb, encT_bot]; exact bot_mem_alph _ _
  · exact absurd ht hne
  · rw [hv, encT_ofOrd, encOrdK_eq_code]
    refine mem_alph_iff.mpr (Or.inr ⟨blockOf l (baseRange F) v, min (finitePart v) l, ?_, ?_, rfl⟩)
    · have h1 := blockOfKey_le l (baseRange F) (keyOrd l v)
      have h2 := card_keys_baseRange_le F
      unfold blockOf
      omega
    · omega

/-- The cap code lies in the alphabet. -/
theorem capCode_mem_alph {I : ℕ} (hI : Fintype.card (BaseCells D₀ l) + 2 ≤ I)
    (F : BaseCells D₀ l → ExtOrd) : ofOrd (capCode l (baseRange F)) ∈ alph l I := by
  refine mem_alph_iff.mpr (Or.inr ⟨(keys l (baseRange F)).card + 1, l, ?_, by omega, rfl⟩)
  have := card_keys_baseRange_le F
  omega

end Encode

/-! ## The decoder -/

section Decode

variable (S : Finset Ordinal.{0}) {γ : ExtOrd}

/-- **The counted decoder is a decoder** at grade one under every cap. -/
noncomputable def shiftDecoder (hγ : SelfVis 1 γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) (c : ExtOrd) :
    Decoder 1 c where
  toFun := shift 1 S γ
  bot := shift_bot 1 S γ
  mono := shift_mono 1 S γ hγ hS
  bot_evr a k i h := shift_evr_of_bot 1 S γ a k i h
  comm a _ hk _ _ hi := shift_evr_of_le 1 S γ hγ hk a hi

/-- A key with nonzero finite part has finite part above the grade. -/
theorem one_lt_finitePart_of_mem_keys {κ : Ordinal.{0}} (hκ : κ ∈ keys 1 S)
    (h0 : finitePart κ ≠ 0) : 1 < finitePart κ := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  rcases finitePart_keyOrd 1 v with h | h
  · exact absurd h h0
  · exact h

/-- A key with zero finite part is its own limit part. -/
theorem limitPart_eq_of_finitePart_eq_zero {κ : Ordinal.{0}} (h0 : finitePart κ = 0) :
    limitPart κ = κ := by
  have := limitPart_add_finitePart κ
  rw [h0, Nat.cast_zero, add_zero] at this
  exact this

/-- **Decoder outputs are self-visible at grade one** when the input is. -/
theorem shift_selfVis_one (hγ : SelfVis 1 γ) {x : ExtOrd} (hx : SelfVis 1 x) :
    SelfVis 1 (shift 1 S γ x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]; exact selfVis_bot _
  · rw [shift_top]; exact hγ
  · rw [shift_ofOrd]
    split_ifs with h
    · exact hγ
    · rcases hκ : keyAt 1 S (blockIdx α) with _ | κ
      · exact selfVis_bot _
      · have hmem := keyAt_mem 1 S hκ
        rw [selfVis_ofOrd_iff]
        unfold decodeIn
        split_ifs with h0
        · rw [selfVis_ofOrd_iff] at hx
          have hlp := limitPart_eq_of_finitePart_eq_zero h0
          rw [← hlp, finitePart_limitPart_add_nat]
          omega
        · exact (one_lt_finitePart_of_mem_keys S hmem h0).le

/-- **Decoder outputs are coded at grade two** when the cap is and every value is. -/
theorem shift_isCoded_two (hγ : IsCodedLabel 2 γ) (hS : ∀ v ∈ S, IsCodedLabel 2 (ofOrd v))
    (x : ExtOrd) : IsCodedLabel 2 (shift 1 S γ x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]; exact Or.inl rfl
  · rw [shift_top]; exact hγ
  · rw [shift_ofOrd]
    split_ifs with h
    · exact hγ
    · rcases hκ : keyAt 1 S (blockIdx α) with _ | κ
      · exact Or.inl rfl
      · have hmem := keyAt_mem 1 S hκ
        obtain ⟨v, hv, hκv⟩ := Finset.mem_image.mp hmem
        rcases hS v hv with hb | ⟨i, j, hj, hij⟩
        · exact absurd hb (ofOrd_ne_bot v)
        · have hvij : v = Ordinal.omega0 * i + j := ofOrd_inj.mp hij
          dsimp only
          unfold decodeIn
          split_ifs with h0
          · refine Or.inr ⟨i, min (finitePart α) 1, by omega, ?_⟩
            have hlp := limitPart_eq_of_finitePart_eq_zero h0
            rw [← hκv, hvij, limitPart_keyOrd, limitPart_mul_add] at hlp
            rw [← hκv, hvij, ← hlp]
          · refine Or.inr ⟨i, j, hj, ?_⟩
            unfold keyOrd at hκv
            split_ifs at hκv with hle
            · exfalso
              apply h0
              rw [← hκv, finitePart_limitPart]
            · rw [← hκv, hvij]

end Decode

end VaughtConjecture.Knight
