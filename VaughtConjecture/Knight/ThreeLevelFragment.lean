/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.RecodingTriangle

/-! # The three-level semantic-tree fragment (`3 → 2 → 1`): a regression module

**What this certifies.**  Over an abstract proper part (cells with positive grades) and the
stratified alphabets `codedAlphabet k T`, the fixed three-level fragment of the construction-time
sharp-coded semantic tree has every property the arbitrary-depth recursion will need from its
lower strata, proved from the counted recoding (`Knight/CountedRecoding.lean`) and its
canonicality under iteration (`Knight/RecodingTriangle.lean`, including the global decoder
equality `compShift_eq_shift`):

* **level-one rows** `Row1`, **cores** `Core k V` (values in `V` at grade-`≤ k` proper cells, `⊥`
  above), level-one meets `meet₁` (ultrametric), the packaged grade-one witness `witness1`, the
  grade-one decoder `dec1`, the directed value `dirVal1` (decoder at the meet with the owned
  witness; the cap at the witness), and clause 4 at a proper cell (`clause4_1`);
* **level-two cells** `Core2` with owned witness `Core2.wit` and sharply coded directed values
  `Core2.rho`; level-two meets on the full lower row (`meet₂`);
* **the level-three core** with its owned level-two witness `Core3.wit2` (a level-two cell built
  from the grade-two witness row and cap), decoder `Core3.dec2`, and directed values `Core3.rho2`
  (to level-two cells) and `Core3.rho1` (to level-one cells, *directly*);
* **acceptance**: `valuesAt_spec` (the grade-two value set is exactly the nonbottom proper range,
  no caps), `Core3.wit2_wit` (the level-two witness's level-one witness is the direct one),
  `Core3.rho1_eq_dec2_rho` (the grade-two chart decodes the level-one-directed values: derived
  directed values lie in the decoder image of already represented lower-stratum values, so the
  key set needs only the primitive lower-grade range), `Core3.rho2_mem`/`Core3.rho1_mem` (sharp
  codedness at grade three), `Core3.availability` (both lower grades, at the owned witnesses),
  `Core3.mixed_square` (the mixed `3 → 2 → 1` locality square — triangle canonicality and
  level-two meet agreement on the level-one stratum), `Core3.cross31`/`Core3.cross32` (cross-level
  locality as `TransformsTo` witnesses toward both predecessor levels, the level-one stratum of
  `cross32` being the mixed square), and `Core3.same3` (same-level meet locality on the complete
  lower row, identity shifter); all directed values are self-visible at the lower grade
  (`shift_selfVis_of_selfVis`).

**Not here**: the proper-part clauses against an ambient semantics, truncations, finiteness of
the fibres beyond the alphabet bound, and assembly into a `CellScheme`/`SemScheme` — the next
scout; and full-scope bountifulness (§§9.4–9.6), open.

Construction-private (not root-exported).  Reviewer scout (2026-09-06), graduated as a
regression module. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Part B — alphabets, level-one rows, level-two cores, and their meets -/

section Alphabets

/-- A grade-`k` alphabet: coded at `k`, containing `⊥`, `min`-closed. -/
structure Alph (k : ℕ) (V : Finset ExtOrd) : Prop where
  coded : ∀ v ∈ V, IsCodedLabel k v
  bot : (⊥ : ExtOrd) ∈ V
  min_mem : ∀ a ∈ V, ∀ b ∈ V, min a b ∈ V

/-- The concrete alphabet: `⊥` and `ω·t + j`, `t ≤ T`, `j ≤ k + 1`. -/
noncomputable def codedAlphabet (k T : ℕ) : Finset ExtOrd :=
  insert ⊥ (((Finset.range (T + 1)) ×ˢ (Finset.range (k + 2))).image
    fun tj : ℕ × ℕ => ofOrd (Ordinal.omega0 * tj.1 + tj.2))

theorem mem_codedAlphabet_of {k T t j : ℕ} (ht : t ≤ T) (hj : j ≤ k + 1) :
    ofOrd (Ordinal.omega0 * t + j) ∈ codedAlphabet k T := by
  unfold codedAlphabet
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(t, j), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, rfl⟩

theorem bot_mem_codedAlphabet (k T : ℕ) : (⊥ : ExtOrd) ∈ codedAlphabet k T :=
  Finset.mem_insert_self _ _

theorem codedAlphabet_isAlph (k T : ℕ) : Alph k (codedAlphabet k T) where
  coded v hv := by
    unfold codedAlphabet at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl rfl
    · obtain ⟨⟨t, j⟩, hm, rfl⟩ := Finset.mem_image.mp hv
      have hj := (Finset.mem_product.mp hm).2
      rw [Finset.mem_range] at hj
      exact Or.inr ⟨t, j, by omega, rfl⟩
  bot := bot_mem_codedAlphabet k T
  min_mem a ha b hb := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]; exact ha
    · rw [min_eq_right h]; exact hb

/-- An ordinal value lies in the alphabet iff its block is `≤ T` and its finite part `≤ k + 1`. -/
theorem ofOrd_mem_codedAlphabet_iff {k T : ℕ} {v : Ordinal.{0}} :
    ofOrd v ∈ codedAlphabet k T ↔ blockIdx v ≤ T ∧ finitePart v ≤ k + 1 := by
  constructor
  · intro h
    unfold codedAlphabet at h
    rcases Finset.mem_insert.mp h with h | h
    · exact absurd h (ofOrd_ne_bot v)
    · obtain ⟨⟨t, j⟩, hm, he⟩ := Finset.mem_image.mp h
      rw [ofOrd_inj] at he
      subst he
      have := Finset.mem_product.mp hm
      rw [Finset.mem_range, Finset.mem_range] at this
      rw [blockIdx_mul_add, finitePart_mul_add]
      exact ⟨by exact_mod_cast (by omega : t ≤ T), by omega⟩
  · rintro ⟨hb, hf⟩
    obtain ⟨t, ht⟩ : ∃ t : ℕ, blockIdx v = t :=
      Ordinal.lt_omega0.mp (hb.trans_lt (Ordinal.natCast_lt_omega0 T))
    have hv : v = Ordinal.omega0 * t + finitePart v := by
      conv_lhs => rw [← limitPart_add_finitePart v]
      rw [limitPart_eq_mul_blockIdx, ht]
    rw [hv]
    exact mem_codedAlphabet_of (by rw [ht] at hb; exact_mod_cast hb) hf

/-- The values of a decoder over a value set inside the alphabet, with cap in the alphabet, lie
in the alphabet of any grade `k ≥ l - 1`. -/
theorem shift_mem_codedAlphabet {l k T : ℕ} (hlk : l ≤ k + 1) {S : Finset Ordinal.{0}}
    (hS : ∀ v ∈ S, ofOrd v ∈ codedAlphabet k T) {γ : ExtOrd} (hγ : γ ∈ codedAlphabet k T)
    (x : ExtOrd) : shift l S γ x ∈ codedAlphabet k T := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]; exact bot_mem_codedAlphabet k T
  · rw [shift_top]; exact hγ
  · rw [shift_ofOrd]
    split_ifs with h
    · exact hγ
    · rcases hk : keyAt l S (blockIdx α) with _ | κ
      · exact bot_mem_codedAlphabet k T
      · simp only
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (keyAt_mem l S hk)
        have hvA := (ofOrd_mem_codedAlphabet_iff).mp (hS v hv)
        rw [ofOrd_mem_codedAlphabet_iff]
        rcases finitePart_keyOrd l v with h0 | hl
        · rw [decodeIn_of_fp_zero l h0]
          have e : keyOrd l v = limitPart v := by
            conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v)]
            rw [h0, limitPart_keyOrd]; simp
          rw [e]
          have hb : blockIdx (limitPart v + ((min (finitePart α) l : ℕ) : Ordinal)) = blockIdx v := by
            rw [limitPart_eq_mul_blockIdx]
            unfold blockIdx
            rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
              Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 _), add_zero]
          rw [hb, finitePart_limitPart_add_nat]
          exact ⟨hvA.1, by omega⟩
        · rw [decodeIn_of_fp_ne l (by omega)]
          unfold keyOrd at hl ⊢
          split_ifs at hl ⊢ with hfp
          · rw [finitePart_limitPart] at hl; omega
          · exact hvA

end Alphabets

section Fragment

variable {P : Type*} [Fintype P] [DecidableEq P] (gradeP : P → ℕ) (T : ℕ)

local notation "V₁" => codedAlphabet 1 T
local notation "V₂" => codedAlphabet 2 T
local notation "V₃" => codedAlphabet 3 T

/-- **A level-one row**. -/
structure Row1 where
  G : P → ExtOrd
  δ : ExtOrd
  G_mem : ∀ c, gradeP c ≤ 1 → G c ∈ V₁
  δ_mem : δ ∈ V₁
  δ_vis : SelfVis 1 δ
  G_le : ∀ c, G c ≤ δ
  G_orderly : ∀ c, gradeP c ≤ 1 → SelfVis (gradeP c) (G c)

/-- **A level-`k` core** (used at `k = 2, 3`): values in `V_k` at the grade-`≤ k` proper cells,
orderly there, bounded by `γ ∈ V_k` self-visible at `k`; `⊥` above grade `k`. -/
structure Core (k : ℕ) (V : Finset ExtOrd) where
  F : P → ExtOrd
  γ : ExtOrd
  F_mem : ∀ c, gradeP c ≤ k → F c ∈ V
  F_bot : ∀ c, k < gradeP c → F c = ⊥
  γ_mem : γ ∈ V
  γ_vis : SelfVis k γ
  F_le : ∀ c, F c ≤ γ
  F_orderly : ∀ c, gradeP c ≤ k → SelfVis (gradeP c) (F c)

variable {gradeP T}

theorem Core.orderlyRow (hg : ∀ c, 1 ≤ gradeP c) {k : ℕ} {V : Finset ExtOrd} (hV : Alph k V)
    (s : Core gradeP k V) : OrderlyRow gradeP s.F where
  pos := hg
  vis c := by
    by_cases hc : gradeP c ≤ k
    · exact s.F_orderly c hc
    · rw [s.F_bot c (by omega)]; exact selfVis_bot _
  ne_top c := by
    by_cases hc : gradeP c ≤ k
    · exact (hV.coded _ (s.F_mem c hc)).ne_top
    · rw [s.F_bot c (by omega)]; exact bot_ne_top

/-! ### Level-one meets -/

def agree₁ (H H' : Row1 gradeP T) (η : ExtOrd) : Prop :=
  ∀ c, gradeP c ≤ 1 → min (H.G c) η = min (H'.G c) η

theorem agree₁_symm {H H' : Row1 gradeP T} {η : ExtOrd} (h : agree₁ H H' η) : agree₁ H' H η :=
  fun c hc => (h c hc).symm

theorem agree₁_of_le {H H' : Row1 gradeP T} {η η' : ExtOrd} (h : agree₁ H H' η) (hle : η' ≤ η) :
    agree₁ H H' η' := by
  intro c hc
  rw [← min_eq_right hle, ← min_assoc, h c hc, min_assoc]

theorem agree₁_trans {H H' H'' : Row1 gradeP T} {η : ExtOrd} (h : agree₁ H H' η)
    (h' : agree₁ H' H'' η) : agree₁ H H'' η :=
  fun c hc => (h c hc).trans (h' c hc)

open Classical in
noncomputable def agreeSet₁ (H H' : Row1 gradeP T) : Finset ExtOrd :=
  (codedAlphabet 1 T).filter fun η => η ≤ min H.δ H'.δ ∧ SelfVis 1 η ∧ agree₁ H H' η

theorem mem_agreeSet₁ {H H' : Row1 gradeP T} {η : ExtOrd} :
    η ∈ agreeSet₁ H H' ↔ η ∈ V₁ ∧ η ≤ min H.δ H'.δ ∧ SelfVis 1 η ∧ agree₁ H H' η := by
  classical
  unfold agreeSet₁; simp only [Finset.mem_filter]

theorem bot_mem_agreeSet₁ (H H' : Row1 gradeP T) : (⊥ : ExtOrd) ∈ agreeSet₁ H H' :=
  mem_agreeSet₁.mpr ⟨bot_mem_codedAlphabet 1 T, bot_le, selfVis_bot 1, fun _ _ => by simp⟩

noncomputable def meet₁ (H H' : Row1 gradeP T) : ExtOrd :=
  (agreeSet₁ H H').max' ⟨⊥, bot_mem_agreeSet₁ H H'⟩

theorem meet₁_mem (H H' : Row1 gradeP T) : meet₁ H H' ∈ agreeSet₁ H H' := Finset.max'_mem _ _
theorem le_meet₁ {H H' : Row1 gradeP T} {η : ExtOrd} (h : η ∈ agreeSet₁ H H') : η ≤ meet₁ H H' :=
  Finset.le_max' _ _ h
theorem meet₁_le (H H' : Row1 gradeP T) : meet₁ H H' ≤ min H.δ H'.δ :=
  (mem_agreeSet₁.mp (meet₁_mem H H')).2.1
theorem meet₁_selfVis (H H' : Row1 gradeP T) : SelfVis 1 (meet₁ H H') :=
  (mem_agreeSet₁.mp (meet₁_mem H H')).2.2.1
theorem meet₁_agree (H H' : Row1 gradeP T) : agree₁ H H' (meet₁ H H') :=
  (mem_agreeSet₁.mp (meet₁_mem H H')).2.2.2
theorem meet₁_mem_V (H H' : Row1 gradeP T) : meet₁ H H' ∈ V₁ :=
  (mem_agreeSet₁.mp (meet₁_mem H H')).1

theorem meet₁_comm (H H' : Row1 gradeP T) : meet₁ H H' = meet₁ H' H := by
  apply le_antisymm
  · refine le_meet₁ (mem_agreeSet₁.mpr ⟨meet₁_mem_V H H', ?_, meet₁_selfVis H H',
      agree₁_symm (meet₁_agree H H')⟩)
    rw [min_comm]; exact meet₁_le H H'
  · refine le_meet₁ (mem_agreeSet₁.mpr ⟨meet₁_mem_V H' H, ?_, meet₁_selfVis H' H,
      agree₁_symm (meet₁_agree H' H)⟩)
    rw [min_comm]; exact meet₁_le H' H

theorem meet₁_self (H : Row1 gradeP T) : meet₁ H H = H.δ := by
  apply le_antisymm
  · exact (meet₁_le H H).trans (min_le_left _ _)
  · exact le_meet₁ (mem_agreeSet₁.mpr ⟨H.δ_mem, by simp, H.δ_vis, fun _ _ => rfl⟩)

theorem ultra_identity {β : Type*} [LinearOrder β] {a b c : β} (h1 : min a b ≤ c)
    (h2 : min b c ≤ a) (h3 : min a c ≤ b) : min b a = min c a := by
  rcases le_total a b with hab | hba
  · rw [min_eq_right hab, min_eq_left hab] at *
    rw [min_eq_right h1]
  · rw [min_eq_left hba]
    rw [min_eq_right hba] at h1
    rcases le_total c a with hca | hac
    · rw [min_eq_right hca] at h3
      rw [min_eq_left hca]
      exact le_antisymm h1 h3
    · rw [min_eq_left hac] at h3
      rw [min_eq_right hac]
      exact le_antisymm hba h3

theorem min_meet₁_le (w H H' : Row1 gradeP T) : min (meet₁ w H) (meet₁ w H') ≤ meet₁ H H' := by
  refine le_meet₁ (mem_agreeSet₁.mpr ⟨(codedAlphabet_isAlph 1 T).min_mem _ (meet₁_mem_V w H)
    _ (meet₁_mem_V w H'), ?_, selfVis_min (meet₁_selfVis w H) (meet₁_selfVis w H'), ?_⟩)
  · exact le_min ((min_le_left _ _).trans ((meet₁_le w H).trans (min_le_right _ _)))
      ((min_le_right _ _).trans ((meet₁_le w H').trans (min_le_right _ _)))
  · exact agree₁_trans (agree₁_symm (agree₁_of_le (meet₁_agree w H) (min_le_left _ _)))
      (agree₁_of_le (meet₁_agree w H') (min_le_right _ _))

theorem meet₁_ultra (w H H' : Row1 gradeP T) :
    min (meet₁ w H') (meet₁ w H) = min (meet₁ H H') (meet₁ w H) := by
  have h1 := min_meet₁_le w H H'
  have h2 := min_meet₁_le H' w H
  have h3 := min_meet₁_le H w H'
  rw [meet₁_comm H' w, meet₁_comm H' H] at h2
  rw [meet₁_comm H w] at h3
  exact ultra_identity h1 h2 h3

/-! ### Level-two cells: a core, its owned level-one witness, its decoder, its directed values -/

/-- The grade-one witness row of any orderly row, packaged as a level-one row. -/
noncomputable def witness1 (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd)
    (hF : OrderlyRow gradeP F) : Row1 gradeP T where
  G := witnessRow gradeP F 1 (valuesAt gradeP F 1)
  δ := ofOrd (capCode 1 (valuesAt gradeP F 1))
  G_mem c hc := by
    rcases hFc : F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc]; exact bot_mem_codedAlphabet 1 T
    · exact absurd hFc (hF.ne_top c)
    · rw [witnessRow_ofOrd gradeP hc (show F c = ofOrd α from hFc)]
      unfold code
      apply mem_codedAlphabet_of
      · have h1 : blockOf 1 (valuesAt gradeP F 1) α ≤ (keys 1 (valuesAt gradeP F 1)).card :=
          blockOfKey_le _ _ _
        have h2 : (keys 1 (valuesAt gradeP F 1)).card ≤ Fintype.card P :=
          Finset.card_image_le.trans (Finset.card_image_le.trans
            (Finset.card_le_card (Finset.filter_subset _ _) |>.trans
              (Finset.card_image_le.trans (Finset.card_le_univ _))))
        omega
      · omega
  δ_mem := by
    unfold capCode
    apply mem_codedAlphabet_of
    · have h2 : (keys 1 (valuesAt gradeP F 1)).card ≤ Fintype.card P :=
        Finset.card_image_le.trans (Finset.card_image_le.trans
          (Finset.card_le_card (Finset.filter_subset _ _) |>.trans
            (Finset.card_image_le.trans (Finset.card_le_univ _))))
      omega
    · omega
  δ_vis := capCode_selfVis 1 _
  G_le c := by
    by_cases hc : gradeP c ≤ 1
    · rcases hFc : F c with _ | _ | α
      · rw [witnessRow_bot gradeP hc hFc]; exact bot_le
      · exact absurd hFc (hF.ne_top c)
      · rw [witnessRow_ofOrd gradeP hc (show F c = ofOrd α from hFc), ofOrd_le_ofOrd]
        exact code_le_capCode 1 _ α
    · unfold witnessRow; rw [if_neg hc]; exact bot_le
  G_orderly c hc := by
    rcases hFc : F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc]; exact selfVis_bot _
    · exact absurd hFc (hF.ne_top c)
    · rw [witnessRow_ofOrd gradeP hc (show F c = ofOrd α from hFc)]
      have hv := hF.vis c
      rw [show F c = ofOrd α from hFc, selfVis_ofOrd_iff] at hv
      exact code_selfVis 1 _ hv hc

theorem witness1_G (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F) :
    (witness1 hT F hF).G = witnessRow gradeP F 1 (valuesAt gradeP F 1) := rfl
theorem witness1_δ (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F) :
    (witness1 hT F hF).δ = ofOrd (capCode 1 (valuesAt gradeP F 1)) := rfl

/-- The grade-one decoder of a row with cap `γ`. -/
noncomputable def dec1 (gradeP : P → ℕ) (F : P → ExtOrd) (γ : ExtOrd) : ExtOrd → ExtOrd :=
  shift 1 (valuesAt gradeP F 1) γ

/-- **Directed value of a row (with its cap) at a level-one cell**: the decoder at the meet of the
owned witness with the cell. -/
noncomputable def dirVal1 (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F)
    (γ : ExtOrd) (H : Row1 gradeP T) : ExtOrd :=
  dec1 gradeP F γ (meet₁ (witness1 hT F hF) H)

/-- The decoder decodes the witness row to the row. -/
theorem dec1_witness (F : P → ExtOrd) (hF : OrderlyRow gradeP F) (γ : ExtOrd) {c : P}
    (hc : gradeP c ≤ 1) : dec1 gradeP F γ (witnessRow gradeP F 1 (valuesAt gradeP F 1) c) = F c := by
  unfold dec1
  rcases hFc : F c with _ | _ | α
  · rw [witnessRow_bot gradeP hc hFc, shift_bot]; rfl
  · exact absurd hFc (hF.ne_top c)
  · rw [witnessRow_ofOrd gradeP hc (show F c = ofOrd α from hFc)]
    exact shift_code 1 _ γ ((mem_valuesAt gradeP).mpr ⟨c, hc, hFc⟩)

theorem dec1_mono (gradeP : P → ℕ) (F : P → ExtOrd) {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hFγ : ∀ c, F c ≤ γ) :
    Monotone (dec1 gradeP F γ) :=
  shift_mono 1 _ γ hγ fun v hv => by
    obtain ⟨c, -, hc⟩ := (mem_valuesAt gradeP).mp hv
    rw [← hc]; exact hFγ c

/-- **Directed value at the owned witness is the cap** (clause 6). -/
theorem dirVal1_witness (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F)
    (γ : ExtOrd) : dirVal1 hT F hF γ (witness1 hT F hF) = γ := by
  unfold dirVal1
  rw [meet₁_self, witness1_δ]
  exact shift_capCode 1 _ γ

theorem dirVal1_le (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hFγ : ∀ c, F c ≤ γ) (H : Row1 gradeP T) :
    dirVal1 hT F hF γ H ≤ γ := by
  unfold dirVal1
  have := dec1_mono gradeP F hγ hFγ (le_top : meet₁ (witness1 hT F hF) H ≤ ⊤)
  unfold dec1 at this
  rwa [shift_top] at this

/-- **Clause 4 at a proper cell** (grade one). -/
theorem clause4_1 (hT : Fintype.card P + 1 ≤ T) (F : P → ExtOrd) (hF : OrderlyRow gradeP F)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hFγ : ∀ c, F c ≤ γ) (H : Row1 gradeP T) {c : P}
    (hc : gradeP c ≤ 1) :
    min (dec1 gradeP F γ (H.G c)) (dirVal1 hT F hF γ H) = min (F c) (dirVal1 hT F hF γ H) := by
  set w := witness1 hT F hF with hw
  set η := meet₁ w H with hη
  have hagree : min (w.G c) η = min (H.G c) η := meet₁_agree w H c hc
  have hFc : F c = dec1 gradeP F γ (w.G c) := (dec1_witness F hF γ hc).symm
  have hmono := dec1_mono gradeP F hγ hFγ
  show min (dec1 gradeP F γ (H.G c)) (dec1 gradeP F γ η) = min (F c) (dec1 gradeP F γ η)
  rw [hFc]
  rcases lt_or_ge (H.G c) η with hlt | hge
  · rw [min_eq_left hlt.le] at hagree
    have hw' : w.G c = H.G c := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left (h.trans hlt).le] at hagree; exact hne hagree
      · have : η ≤ w.G c := by
          by_contra h'
          rw [min_eq_left (not_le.mp h').le] at hagree
          exact hne hagree
        rw [min_eq_right this] at hagree
        exact absurd hagree.symm (ne_of_lt hlt)
    rw [hw']
  · rw [min_eq_right hge] at hagree
    have hwge : η ≤ w.G c := by
      by_contra h'
      rw [min_eq_left (not_le.mp h').le] at hagree
      exact absurd hagree (ne_of_lt (not_le.mp h'))
    rw [min_eq_right (hmono hge), min_eq_right (hmono hwge)]


/-! ## Part C — level-two cells, the level-three core, and the fragment's acceptance tests -/

theorem Row1.ext' {H H' : Row1 gradeP T} (hG : H.G = H'.G) (hδ : H.δ = H'.δ) : H = H' := by
  cases H; cases H'
  simp only at hG hδ
  subst hG; subst hδ; rfl

/-- The fragment's setting: positive grades and an alphabet bound hosting every code. -/
structure Setting (gradeP : P → ℕ) (T : ℕ) : Prop where
  hg : ∀ c, 1 ≤ gradeP c
  hT : Fintype.card P + 1 ≤ T

/-- The level-two cells: cores at grade `2` over `V₂`. -/
abbrev Core2 := Core gradeP 2 (codedAlphabet 2 T)
/-- The level-three cores over `V₃`. -/
abbrev Core3 := Core gradeP 3 (codedAlphabet 3 T)

theorem Core2.orderly (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) : OrderlyRow gradeP s.F :=
  s.orderlyRow st.hg (codedAlphabet_isAlph 2 T)

theorem Core3.orderly (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) : OrderlyRow gradeP t.F :=
  t.orderlyRow st.hg (codedAlphabet_isAlph 3 T)

/-- The owned level-one witness of a level-two cell. -/
noncomputable def Core2.wit (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) : Row1 gradeP T :=
  witness1 st.hT s.F (s.orderly st)

/-- The directed value of a level-two cell at a level-one cell. -/
noncomputable def Core2.rho (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) : ExtOrd :=
  dirVal1 st.hT s.F (s.orderly st) s.γ H

theorem Core2.rho_def (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    s.rho st H = dec1 gradeP s.F s.γ (meet₁ (s.wit st) H) := rfl

theorem Core2.rho_mem (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    s.rho st H ∈ codedAlphabet 2 T := by
  unfold Core2.rho dirVal1 dec1
  refine shift_mem_codedAlphabet (by omega) ?_ s.γ_mem _
  intro v hv
  obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
  rw [← hFc]; exact s.F_mem c (by omega)

/-! ### Level-two meets, on the full lower row (proper values and directed values) -/

def agree₂ (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) (η : ExtOrd) : Prop :=
  (∀ c, gradeP c ≤ 2 → min (s.F c) η = min (s'.F c) η) ∧
  ∀ H : Row1 gradeP T, min (s.rho st H) η = min (s'.rho st H) η

theorem agree₂_symm (st : Setting gradeP T) {s s' : Core2 (gradeP := gradeP) (T := T)} {η : ExtOrd}
    (h : agree₂ st s s' η) : agree₂ st s' s η :=
  ⟨fun c hc => (h.1 c hc).symm, fun H => (h.2 H).symm⟩

theorem agree₂_of_le (st : Setting gradeP T) {s s' : Core2 (gradeP := gradeP) (T := T)} {η η' : ExtOrd}
    (h : agree₂ st s s' η) (hle : η' ≤ η) : agree₂ st s s' η' :=
  ⟨fun c hc => by rw [← min_eq_right hle, ← min_assoc, h.1 c hc, min_assoc],
   fun H => by rw [← min_eq_right hle, ← min_assoc, h.2 H, min_assoc]⟩

theorem agree₂_trans (st : Setting gradeP T) {s s' s'' : Core2 (gradeP := gradeP) (T := T)} {η : ExtOrd}
    (h : agree₂ st s s' η) (h' : agree₂ st s' s'' η) : agree₂ st s s'' η :=
  ⟨fun c hc => (h.1 c hc).trans (h'.1 c hc), fun H => (h.2 H).trans (h'.2 H)⟩

open Classical in
noncomputable def agreeSet₂ (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : Finset ExtOrd :=
  (codedAlphabet 2 T).filter fun η => η ≤ min s.γ s'.γ ∧ SelfVis 2 η ∧ agree₂ st s s' η

theorem mem_agreeSet₂ (st : Setting gradeP T) {s s' : Core2 (gradeP := gradeP) (T := T)} {η : ExtOrd} :
    η ∈ agreeSet₂ st s s' ↔
      η ∈ codedAlphabet 2 T ∧ η ≤ min s.γ s'.γ ∧ SelfVis 2 η ∧ agree₂ st s s' η := by
  classical
  unfold agreeSet₂; simp only [Finset.mem_filter]

theorem bot_mem_agreeSet₂ (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) :
    (⊥ : ExtOrd) ∈ agreeSet₂ st s s' :=
  (mem_agreeSet₂ st).mpr ⟨bot_mem_codedAlphabet 2 T, bot_le, selfVis_bot 2,
    ⟨fun _ _ => by simp, fun _ => by simp⟩⟩

noncomputable def meet₂ (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : ExtOrd :=
  (agreeSet₂ st s s').max' ⟨⊥, bot_mem_agreeSet₂ st s s'⟩

theorem meet₂_mem (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) :
    meet₂ st s s' ∈ agreeSet₂ st s s' := Finset.max'_mem _ _
theorem le_meet₂ (st : Setting gradeP T) {s s' : Core2 (gradeP := gradeP) (T := T)} {η : ExtOrd}
    (h : η ∈ agreeSet₂ st s s') : η ≤ meet₂ st s s' := Finset.le_max' _ _ h
theorem meet₂_le (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : meet₂ st s s' ≤ min s.γ s'.γ :=
  ((mem_agreeSet₂ st).mp (meet₂_mem st s s')).2.1
theorem meet₂_selfVis (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : SelfVis 2 (meet₂ st s s') :=
  ((mem_agreeSet₂ st).mp (meet₂_mem st s s')).2.2.1
theorem meet₂_agree (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : agree₂ st s s' (meet₂ st s s') :=
  ((mem_agreeSet₂ st).mp (meet₂_mem st s s')).2.2.2
theorem meet₂_mem_V (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : meet₂ st s s' ∈ codedAlphabet 2 T :=
  ((mem_agreeSet₂ st).mp (meet₂_mem st s s')).1

theorem meet₂_comm (st : Setting gradeP T) (s s' : Core2 (gradeP := gradeP) (T := T)) : meet₂ st s s' = meet₂ st s' s := by
  apply le_antisymm
  · refine le_meet₂ st ((mem_agreeSet₂ st).mpr ⟨meet₂_mem_V st s s', ?_,
      meet₂_selfVis st s s', agree₂_symm st (meet₂_agree st s s')⟩)
    rw [min_comm]; exact meet₂_le st s s'
  · refine le_meet₂ st ((mem_agreeSet₂ st).mpr ⟨meet₂_mem_V st s' s, ?_,
      meet₂_selfVis st s' s, agree₂_symm st (meet₂_agree st s' s)⟩)
    rw [min_comm]; exact meet₂_le st s' s

theorem meet₂_self (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) : meet₂ st s s = s.γ := by
  apply le_antisymm
  · exact (meet₂_le st s s).trans (min_le_left _ _)
  · exact le_meet₂ st ((mem_agreeSet₂ st).mpr ⟨s.γ_mem, by simp, s.γ_vis,
      ⟨fun _ _ => rfl, fun _ => rfl⟩⟩)

theorem min_meet₂_le (st : Setting gradeP T) (w s s' : Core2 (gradeP := gradeP) (T := T)) :
    min (meet₂ st w s) (meet₂ st w s') ≤ meet₂ st s s' := by
  refine le_meet₂ st ((mem_agreeSet₂ st).mpr ⟨(codedAlphabet_isAlph 2 T).min_mem _
    (meet₂_mem_V st w s) _ (meet₂_mem_V st w s'), ?_,
    selfVis_min (meet₂_selfVis st w s) (meet₂_selfVis st w s'), ?_⟩)
  · exact le_min ((min_le_left _ _).trans ((meet₂_le st w s).trans (min_le_right _ _)))
      ((min_le_right _ _).trans ((meet₂_le st w s').trans (min_le_right _ _)))
  · exact agree₂_trans st
      (agree₂_symm st (agree₂_of_le st (meet₂_agree st w s) (min_le_left _ _)))
      (agree₂_of_le st (meet₂_agree st w s') (min_le_right _ _))

theorem meet₂_ultra (st : Setting gradeP T) (w s s' : Core2 (gradeP := gradeP) (T := T)) :
    min (meet₂ st w s') (meet₂ st w s) = min (meet₂ st s s') (meet₂ st w s) := by
  have h1 := min_meet₂_le st w s s'
  have h2 := min_meet₂_le st s' w s
  have h3 := min_meet₂_le st s w s'
  rw [meet₂_comm st s' w, meet₂_comm st s' s] at h2
  rw [meet₂_comm st s w] at h3
  exact ultra_identity h1 h2 h3

/-! ### The level-three core: its level-two witness, decoder, and directed values -/

theorem card_keys_le (gradeP : P → ℕ) (F : P → ExtOrd) (l : ℕ) :
    (keys l (valuesAt gradeP F l)).card ≤ Fintype.card P :=
  Finset.card_image_le.trans (Finset.card_image_le.trans
    (Finset.card_le_card (Finset.filter_subset _ _) |>.trans
      (Finset.card_image_le.trans (Finset.card_le_univ _))))

/-- **The owned level-two witness** of a level-three core: the grade-two witness row with the
grade-two cap, as a level-two cell. -/
noncomputable def Core3.wit2 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) : Core2 (gradeP := gradeP) (T := T) where
  F := witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2)
  γ := ofOrd (capCode 2 (valuesAt gradeP t.F 2))
  F_mem c hc := by
    rcases hFc : t.F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc]; exact bot_mem_codedAlphabet 2 T
    · exact absurd hFc ((t.orderly st).ne_top c)
    · rw [witnessRow_ofOrd gradeP hc (show t.F c = ofOrd α from hFc)]
      unfold code
      apply mem_codedAlphabet_of
      · have h1 : blockOf 2 (valuesAt gradeP t.F 2) α ≤ (keys 2 (valuesAt gradeP t.F 2)).card :=
          blockOfKey_le _ _ _
        have h2 := card_keys_le gradeP t.F 2
        have h3 := st.hT
        omega
      · omega
  F_bot c hc := by unfold witnessRow; rw [if_neg (by omega)]
  γ_mem := by
    unfold capCode
    apply mem_codedAlphabet_of
    · have h2 := card_keys_le gradeP t.F 2; have h3 := st.hT; omega
    · omega
  γ_vis := capCode_selfVis 2 _
  F_le c := by
    by_cases hc : gradeP c ≤ 2
    · rcases hFc : t.F c with _ | _ | α
      · rw [witnessRow_bot gradeP hc hFc]; exact bot_le
      · exact absurd hFc ((t.orderly st).ne_top c)
      · rw [witnessRow_ofOrd gradeP hc (show t.F c = ofOrd α from hFc), ofOrd_le_ofOrd]
        exact code_le_capCode 2 _ α
    · unfold witnessRow; rw [if_neg hc]; exact bot_le
  F_orderly c hc := by
    rcases hFc : t.F c with _ | _ | α
    · rw [witnessRow_bot gradeP hc hFc]; exact selfVis_bot _
    · exact absurd hFc ((t.orderly st).ne_top c)
    · rw [witnessRow_ofOrd gradeP hc (show t.F c = ofOrd α from hFc)]
      have hv := (t.orderly st).vis c
      rw [show t.F c = ofOrd α from hFc, selfVis_ofOrd_iff] at hv
      exact code_selfVis 2 _ hv hc

/-- The grade-two decoder of the level-three core. -/
noncomputable def Core3.dec2 (t : Core3 (gradeP := gradeP) (T := T)) : ExtOrd → ExtOrd :=
  shift 2 (valuesAt gradeP t.F 2) t.γ

/-- **Directed value at a level-two cell**: the grade-two decoder at the level-two meet with the
owned witness. -/
noncomputable def Core3.rho2 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (s : Core2 (gradeP := gradeP) (T := T)) : ExtOrd :=
  t.dec2 (meet₂ st (t.wit2 st) s)

/-- **Directed value at a level-one cell**, defined directly (grade-one decoder, direct witness). -/
noncomputable def Core3.rho1 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) : ExtOrd :=
  dirVal1 st.hT t.F (t.orderly st) t.γ H

theorem Core3.dec2_mono (t : Core3 (gradeP := gradeP) (T := T)) : Monotone t.dec2 :=
  shift_mono 2 _ t.γ (t.γ_vis.mono (by omega)) fun v hv => by
    obtain ⟨c, -, hc⟩ := (mem_valuesAt gradeP).mp hv
    rw [← hc]; exact t.F_le c

theorem Core3.dec2_witness (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) {c : P} (hc : gradeP c ≤ 2) :
    t.dec2 ((t.wit2 st).F c) = t.F c := by
  show shift 2 _ t.γ (witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2) c) = t.F c
  rcases hFc : t.F c with _ | _ | α
  · rw [witnessRow_bot gradeP hc hFc, shift_bot]; rfl
  · exact absurd hFc ((t.orderly st).ne_top c)
  · rw [witnessRow_ofOrd gradeP hc (show t.F c = ofOrd α from hFc)]
    exact shift_code 2 _ t.γ ((mem_valuesAt gradeP).mpr ⟨c, hc, hFc⟩)

/-! ### Acceptance: the value set, the witness of the witness, sharp codedness -/

/-- **The grade-two value set is the actual proper range** (nonbottom values at grade-`≤ 2` proper
cells), with no cap values. -/
theorem valuesAt_spec (t : Core3 (gradeP := gradeP) (T := T)) (v : Ordinal.{0}) :
    v ∈ valuesAt gradeP t.F 2 ↔ ∃ c, gradeP c ≤ 2 ∧ t.F c = ofOrd v :=
  mem_valuesAt gradeP

/-- **The level-two witness's level-one witness is the direct level-one witness.** -/
theorem Core3.wit2_wit (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    (t.wit2 st).wit st = witness1 st.hT t.F (t.orderly st) := by
  apply Row1.ext'
  · show witnessRow gradeP (witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2)) 1
      (valuesAt gradeP (witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2)) 1) =
      witnessRow gradeP t.F 1 (valuesAt gradeP t.F 1)
    exact witness_comp_eq (t.orderly st)
  · show ofOrd (capCode 1 (valuesAt gradeP (witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2)) 1)) =
      ofOrd (capCode 1 (valuesAt gradeP t.F 1))
    rw [valuesAt_witness, capCode_comp_eq (t.orderly st)]

/-- **The grade-two chart decodes the level-one-directed values**: the level-three row's directed
value at a level-one cell is the grade-two decoder applied to the witness's directed value —
so the level-one-directed range needs no separate entry in the grade-two value set. -/
theorem Core3.rho1_eq_dec2_rho (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    t.rho1 st H = t.dec2 ((t.wit2 st).rho st H) := by
  rw [Core2.rho_def, Core3.wit2_wit]
  show dirVal1 st.hT t.F (t.orderly st) t.γ H =
    shift 2 (valuesAt gradeP t.F 2) t.γ
      (shift 1 (valuesAt gradeP (witnessRow gradeP t.F 2 (valuesAt gradeP t.F 2)) 1)
        (ofOrd (capCode 2 (valuesAt gradeP t.F 2))) (meet₁ (witness1 st.hT t.F (t.orderly st)) H))
  rw [valuesAt_witness]
  exact (compShift_eq_shift (t.orderly st) t.γ _).symm

theorem Core3.rho2_mem (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (s : Core2 (gradeP := gradeP) (T := T)) :
    t.rho2 st s ∈ codedAlphabet 3 T := by
  unfold Core3.rho2 Core3.dec2
  refine shift_mem_codedAlphabet (by omega) ?_ t.γ_mem _
  intro v hv
  obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
  rw [← hFc]; exact t.F_mem c (by omega)

theorem Core3.rho1_mem (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    t.rho1 st H ∈ codedAlphabet 3 T := by
  unfold Core3.rho1 dirVal1 dec1
  refine shift_mem_codedAlphabet (by omega) ?_ t.γ_mem _
  intro v hv
  obtain ⟨c, hc, hFc⟩ := (mem_valuesAt gradeP).mp hv
  rw [← hFc]; exact t.F_mem c (by omega)

/-! ### Acceptance: availability at both lower grades from the owned witnesses -/

theorem Core3.rho2_wit2 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) : t.rho2 st (t.wit2 st) = t.γ := by
  unfold Core3.rho2
  rw [meet₂_self]
  exact shift_capCode 2 _ t.γ

theorem Core3.rho1_wit1 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    t.rho1 st (witness1 st.hT t.F (t.orderly st)) = t.γ :=
  dirVal1_witness st.hT t.F (t.orderly st) t.γ

theorem Core3.rho2_le (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (s : Core2 (gradeP := gradeP) (T := T)) :
    t.rho2 st s ≤ t.γ := by
  unfold Core3.rho2
  have := t.dec2_mono (le_top : meet₂ st (t.wit2 st) s ≤ ⊤)
  unfold Core3.dec2 at this
  rwa [shift_top] at this

theorem Core3.rho1_le (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    t.rho1 st H ≤ t.γ :=
  dirVal1_le st.hT t.F (t.orderly st) (t.γ_vis.mono (by omega)) t.F_le H

/-- **Availability of the level-three row at grades one and two**: every value at a grade-one or
grade-two cell of its lower set is dominated by `γ`, attained at the owned witnesses. -/
theorem Core3.availability (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    (∀ H : Row1 gradeP T, t.rho1 st H ≤ t.rho1 st (witness1 st.hT t.F (t.orderly st))) ∧
    (∀ s : Core2 (gradeP := gradeP) (T := T), t.rho2 st s ≤ t.rho2 st (t.wit2 st)) ∧
    (∀ c, t.F c ≤ t.rho1 st (witness1 st.hT t.F (t.orderly st))) ∧
    (∀ c, t.F c ≤ t.rho2 st (t.wit2 st)) := by
  rw [t.rho1_wit1, t.rho2_wit2]
  exact ⟨t.rho1_le st, t.rho2_le st, t.F_le, t.F_le⟩


/-! ## Part D — the mixed square and the localities -/

/-- A decoder preserves self-visibility at its target grade (clause 5 at `k = i = l`). -/
theorem shift_selfVis_of_selfVis {l : ℕ} {S : Finset Ordinal.{0}} {γ : ExtOrd} (hγ : SelfVis l γ)
    {x : ExtOrd} (hx : SelfVis l x) : SelfVis l (shift l S γ x) := by
  have h := shift_evr_of_le l S γ hγ (le_refl l) x (le_refl l)
  unfold SelfVis at hx
  rw [hx] at h
  exact h.symm

/-- The level-three row's directed values are self-visible at the lower grade. -/
theorem Core3.rho1_selfVis (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (H : Row1 gradeP T) : SelfVis 1 (t.rho1 st H) :=
  shift_selfVis_of_selfVis (t.γ_vis.mono (by omega)) (meet₁_selfVis _ H)

theorem Core3.rho2_selfVis (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (s : Core2 (gradeP := gradeP) (T := T)) : SelfVis 2 (t.rho2 st s) :=
  shift_selfVis_of_selfVis (t.γ_vis.mono (by omega)) (meet₂_selfVis st _ s)

/-- **The mixed locality square**: for an arbitrary level-two cell `s`, its directed value at a
level-one cell `H`, decoded by the level-three chart and capped at `ρ₂ s`, is the level-three
row's directly constructed directed value at `H`, capped the same way.  Triangle canonicality
(`wit2_wit`, `rho1_eq_dec2_rho`) and level-two meet agreement on the level-one stratum are what
make it close. -/
theorem Core3.mixed_square (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (s : Core2 (gradeP := gradeP) (T := T)) (H : Row1 gradeP T) :
    min (t.dec2 (s.rho st H)) (t.rho2 st s) = min (t.rho1 st H) (t.rho2 st s) := by
  have hag := (meet₂_agree st (t.wit2 st) s).2 H
  have hmono := t.dec2_mono
  have := congrArg t.dec2 hag
  rw [Monotone.map_min hmono, Monotone.map_min hmono] at this
  rw [Core3.rho1_eq_dec2_rho st t H]
  show min (t.dec2 (s.rho st H)) (t.dec2 (meet₂ st (t.wit2 st) s)) =
    min (t.dec2 ((t.wit2 st).rho st H)) (t.dec2 (meet₂ st (t.wit2 st) s))
  exact this.symm

/-- **Clause 4 at a proper cell** (grade two). -/
theorem Core3.clause4_2 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (s : Core2 (gradeP := gradeP) (T := T)) {c : P} (hc : gradeP c ≤ 2) :
    min (t.dec2 (s.F c)) (t.rho2 st s) = min (t.F c) (t.rho2 st s) := by
  set w := t.wit2 st with hw
  set η := meet₂ st w s with hη
  have hagree : min (w.F c) η = min (s.F c) η := (meet₂_agree st w s).1 c hc
  have hFc : t.F c = t.dec2 (w.F c) := (t.dec2_witness st hc).symm
  have hmono := t.dec2_mono
  show min (t.dec2 (s.F c)) (t.dec2 η) = min (t.F c) (t.dec2 η)
  rw [hFc]
  rcases lt_or_ge (s.F c) η with hlt | hge
  · rw [min_eq_left hlt.le] at hagree
    have hw' : w.F c = s.F c := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left (h.trans hlt).le] at hagree; exact hne hagree
      · have : η ≤ w.F c := by
          by_contra h'
          rw [min_eq_left (not_le.mp h').le] at hagree
          exact hne hagree
        rw [min_eq_right this] at hagree
        exact absurd hagree.symm (ne_of_lt hlt)
    rw [hw']
  · rw [min_eq_right hge] at hagree
    have hwge : η ≤ w.F c := by
      by_contra h'
      rw [min_eq_left (not_le.mp h').le] at hagree
      exact absurd hagree (ne_of_lt (not_le.mp h'))
    rw [min_eq_right (hmono hge), min_eq_right (hmono hwge)]

/-! ### Lower sets and rows -/

abbrev Low1 (gradeP : P → ℕ) (T : ℕ) := {c : P // gradeP c ≤ 1} ⊕ Row1 gradeP T
abbrev Low2 (gradeP : P → ℕ) (T : ℕ) :=
  {c : P // gradeP c ≤ 2} ⊕ Row1 gradeP T ⊕ Core2 (gradeP := gradeP) (T := T)
abbrev Low3 (gradeP : P → ℕ) (T : ℕ) :=
  {c : P // gradeP c ≤ 3} ⊕ Row1 gradeP T ⊕ Core2 (gradeP := gradeP) (T := T) ⊕
    Core3 (gradeP := gradeP) (T := T)

def Low1.grade : Low1 gradeP T → ℕ
  | Sum.inl c => gradeP c.1
  | Sum.inr _ => 1
def Low2.grade : Low2 gradeP T → ℕ
  | Sum.inl c => gradeP c.1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2
def Low3.grade : Low3 gradeP T → ℕ
  | Sum.inl c => gradeP c.1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

noncomputable def Row1.row (H : Row1 gradeP T) : Low1 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => H.G c.1
  | Sum.inr H' => meet₁ H H'

noncomputable def Core2.row (st : Setting gradeP T) (s : Core2 (gradeP := gradeP) (T := T)) :
    Low2 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => s.F c.1
  | Sum.inr (Sum.inl H) => s.rho st H
  | Sum.inr (Sum.inr s') => meet₂ st s s'

noncomputable def Core3.rowOn1 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    Low1 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => t.F c.1
  | Sum.inr H => t.rho1 st H

noncomputable def Core3.rowOn2 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    Low2 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => t.F c.1
  | Sum.inr (Sum.inl H) => t.rho1 st H
  | Sum.inr (Sum.inr s) => t.rho2 st s

/-- **Cross-level locality `3 → 1`**: the row of a level-one cell transforms to the level-three row
capped at the directed value, with the grade-one decoder as shifter. -/
theorem Core3.cross31 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (H : Row1 gradeP T) :
    TransformsTo Low1.grade H.row (fun d => min (t.rowOn1 st d) (t.rho1 st H)) := by
  have hγ : SelfVis 1 t.γ := t.γ_vis.mono (by omega)
  have hS : ∀ v ∈ valuesAt gradeP t.F 1, ofOrd v ≤ t.γ := fun v hv => by
    obtain ⟨c, -, hc⟩ := (mem_valuesAt gradeP).mp hv
    rw [← hc]; exact t.F_le c
  have h := transformsTo_of_shift 1 (valuesAt gradeP t.F 1) t.γ Low1.grade hγ hS H.row
    (t.rho1_selfVis st H)
  have e : (fun d => min (shift 1 (valuesAt gradeP t.F 1) t.γ (H.row d))
      (if Low1.grade d ≤ 1 then t.rho1 st H else ⊥)) =
      fun d => min (t.rowOn1 st d) (t.rho1 st H) := by
    funext d
    rcases d with c | H'
    · show min (dec1 gradeP t.F t.γ (H.G c.1)) (if gradeP c.1 ≤ 1 then t.rho1 st H else ⊥) =
        min (t.F c.1) (t.rho1 st H)
      rw [if_pos c.2]
      exact clause4_1 st.hT t.F (t.orderly st) hγ t.F_le H c.2
    · show min (dec1 gradeP t.F t.γ (meet₁ H H')) (if (1 : ℕ) ≤ 1 then t.rho1 st H else ⊥) =
        min (t.rho1 st H') (t.rho1 st H)
      rw [if_pos (le_refl 1)]
      have hmono := dec1_mono gradeP t.F hγ t.F_le
      show min (dec1 gradeP t.F t.γ (meet₁ H H')) (dec1 gradeP t.F t.γ (meet₁ (witness1 st.hT t.F (t.orderly st)) H)) =
        min (dec1 gradeP t.F t.γ (meet₁ (witness1 st.hT t.F (t.orderly st)) H'))
          (dec1 gradeP t.F t.γ (meet₁ (witness1 st.hT t.F (t.orderly st)) H))
      rw [← Monotone.map_min hmono, ← Monotone.map_min hmono, meet₁_ultra]
  rw [e] at h
  exact h

/-- **Cross-level locality `3 → 2`**, including the mixed square at the level-one stratum. -/
theorem Core3.cross32 (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T))
    (s : Core2 (gradeP := gradeP) (T := T)) :
    TransformsTo Low2.grade (s.row st) (fun d => min (t.rowOn2 st d) (t.rho2 st s)) := by
  have hγ : SelfVis 2 t.γ := t.γ_vis.mono (by omega)
  have hS : ∀ v ∈ valuesAt gradeP t.F 2, ofOrd v ≤ t.γ := fun v hv => by
    obtain ⟨c, -, hc⟩ := (mem_valuesAt gradeP).mp hv
    rw [← hc]; exact t.F_le c
  have h := transformsTo_of_shift 2 (valuesAt gradeP t.F 2) t.γ Low2.grade hγ hS (s.row st)
    (t.rho2_selfVis st s)
  have e : (fun d => min (shift 2 (valuesAt gradeP t.F 2) t.γ (s.row st d))
      (if Low2.grade d ≤ 2 then t.rho2 st s else ⊥)) =
      fun d => min (t.rowOn2 st d) (t.rho2 st s) := by
    funext d
    rcases d with c | H | s'
    · show min (t.dec2 (s.F c.1)) (if gradeP c.1 ≤ 2 then t.rho2 st s else ⊥) =
        min (t.F c.1) (t.rho2 st s)
      rw [if_pos c.2]
      exact t.clause4_2 st s c.2
    · show min (t.dec2 (s.rho st H)) (if (1 : ℕ) ≤ 2 then t.rho2 st s else ⊥) =
        min (t.rho1 st H) (t.rho2 st s)
      rw [if_pos (by omega)]
      exact t.mixed_square st s H
    · show min (t.dec2 (meet₂ st s s')) (if (2 : ℕ) ≤ 2 then t.rho2 st s else ⊥) =
        min (t.rho2 st s') (t.rho2 st s)
      rw [if_pos (le_refl 2)]
      have hmono := t.dec2_mono
      show min (t.dec2 (meet₂ st s s')) (t.dec2 (meet₂ st (t.wit2 st) s)) =
        min (t.dec2 (meet₂ st (t.wit2 st) s')) (t.dec2 (meet₂ st (t.wit2 st) s))
      rw [← Monotone.map_min hmono, ← Monotone.map_min hmono, meet₂_ultra]
  rw [e] at h
  exact h

/-! ### Same-level meets at level three, on the complete lower row -/

def agree₃ (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) (η : ExtOrd) : Prop :=
  (∀ c, gradeP c ≤ 3 → min (t.F c) η = min (t'.F c) η) ∧
  (∀ H : Row1 gradeP T, min (t.rho1 st H) η = min (t'.rho1 st H) η) ∧
  ∀ s : Core2 (gradeP := gradeP) (T := T), min (t.rho2 st s) η = min (t'.rho2 st s) η

theorem agree₃_symm (st : Setting gradeP T) {t t' : Core3 (gradeP := gradeP) (T := T)} {η : ExtOrd}
    (h : agree₃ st t t' η) : agree₃ st t' t η :=
  ⟨fun c hc => (h.1 c hc).symm, fun H => (h.2.1 H).symm, fun s => (h.2.2 s).symm⟩

theorem agree₃_of_le (st : Setting gradeP T) {t t' : Core3 (gradeP := gradeP) (T := T)} {η η' : ExtOrd}
    (h : agree₃ st t t' η) (hle : η' ≤ η) : agree₃ st t t' η' :=
  ⟨fun c hc => by rw [← min_eq_right hle, ← min_assoc, h.1 c hc, min_assoc],
   fun H => by rw [← min_eq_right hle, ← min_assoc, h.2.1 H, min_assoc],
   fun s => by rw [← min_eq_right hle, ← min_assoc, h.2.2 s, min_assoc]⟩

theorem agree₃_trans (st : Setting gradeP T) {t t' t'' : Core3 (gradeP := gradeP) (T := T)}
    {η : ExtOrd} (h : agree₃ st t t' η) (h' : agree₃ st t' t'' η) : agree₃ st t t'' η :=
  ⟨fun c hc => (h.1 c hc).trans (h'.1 c hc), fun H => (h.2.1 H).trans (h'.2.1 H),
   fun s => (h.2.2 s).trans (h'.2.2 s)⟩

open Classical in
noncomputable def agreeSet₃ (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    Finset ExtOrd :=
  (codedAlphabet 3 T).filter fun η => η ≤ min t.γ t'.γ ∧ SelfVis 3 η ∧ agree₃ st t t' η

theorem mem_agreeSet₃ (st : Setting gradeP T) {t t' : Core3 (gradeP := gradeP) (T := T)} {η : ExtOrd} :
    η ∈ agreeSet₃ st t t' ↔
      η ∈ codedAlphabet 3 T ∧ η ≤ min t.γ t'.γ ∧ SelfVis 3 η ∧ agree₃ st t t' η := by
  classical
  unfold agreeSet₃; simp only [Finset.mem_filter]

theorem bot_mem_agreeSet₃ (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    (⊥ : ExtOrd) ∈ agreeSet₃ st t t' :=
  (mem_agreeSet₃ st).mpr ⟨bot_mem_codedAlphabet 3 T, bot_le, selfVis_bot 3,
    ⟨fun _ _ => by simp, fun _ => by simp, fun _ => by simp⟩⟩

noncomputable def meet₃ (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) : ExtOrd :=
  (agreeSet₃ st t t').max' ⟨⊥, bot_mem_agreeSet₃ st t t'⟩

theorem meet₃_mem (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    meet₃ st t t' ∈ agreeSet₃ st t t' := Finset.max'_mem _ _
theorem le_meet₃ (st : Setting gradeP T) {t t' : Core3 (gradeP := gradeP) (T := T)} {η : ExtOrd}
    (h : η ∈ agreeSet₃ st t t') : η ≤ meet₃ st t t' := Finset.le_max' _ _ h
theorem meet₃_le (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    meet₃ st t t' ≤ min t.γ t'.γ := ((mem_agreeSet₃ st).mp (meet₃_mem st t t')).2.1
theorem meet₃_selfVis (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    SelfVis 3 (meet₃ st t t') := ((mem_agreeSet₃ st).mp (meet₃_mem st t t')).2.2.1
theorem meet₃_agree (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    agree₃ st t t' (meet₃ st t t') := ((mem_agreeSet₃ st).mp (meet₃_mem st t t')).2.2.2
theorem meet₃_mem_V (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    meet₃ st t t' ∈ codedAlphabet 3 T := ((mem_agreeSet₃ st).mp (meet₃_mem st t t')).1

theorem meet₃_comm (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    meet₃ st t t' = meet₃ st t' t := by
  apply le_antisymm
  · refine le_meet₃ st ((mem_agreeSet₃ st).mpr ⟨meet₃_mem_V st t t', ?_, meet₃_selfVis st t t',
      agree₃_symm st (meet₃_agree st t t')⟩)
    rw [min_comm]; exact meet₃_le st t t'
  · refine le_meet₃ st ((mem_agreeSet₃ st).mpr ⟨meet₃_mem_V st t' t, ?_, meet₃_selfVis st t' t,
      agree₃_symm st (meet₃_agree st t' t)⟩)
    rw [min_comm]; exact meet₃_le st t' t

theorem min_meet₃_le (st : Setting gradeP T) (w t t' : Core3 (gradeP := gradeP) (T := T)) :
    min (meet₃ st w t) (meet₃ st w t') ≤ meet₃ st t t' := by
  refine le_meet₃ st ((mem_agreeSet₃ st).mpr ⟨(codedAlphabet_isAlph 3 T).min_mem _
    (meet₃_mem_V st w t) _ (meet₃_mem_V st w t'), ?_,
    selfVis_min (meet₃_selfVis st w t) (meet₃_selfVis st w t'), ?_⟩)
  · exact le_min ((min_le_left _ _).trans ((meet₃_le st w t).trans (min_le_right _ _)))
      ((min_le_right _ _).trans ((meet₃_le st w t').trans (min_le_right _ _)))
  · exact agree₃_trans st
      (agree₃_symm st (agree₃_of_le st (meet₃_agree st w t) (min_le_left _ _)))
      (agree₃_of_le st (meet₃_agree st w t') (min_le_right _ _))

theorem meet₃_ultra (st : Setting gradeP T) (w t t' : Core3 (gradeP := gradeP) (T := T)) :
    min (meet₃ st w t') (meet₃ st w t) = min (meet₃ st t t') (meet₃ st w t) := by
  have h1 := min_meet₃_le st w t t'
  have h2 := min_meet₃_le st t' w t
  have h3 := min_meet₃_le st t w t'
  rw [meet₃_comm st t' w, meet₃_comm st t' t] at h2
  rw [meet₃_comm st t w] at h3
  exact ultra_identity h1 h2 h3

noncomputable def Core3.row (st : Setting gradeP T) (t : Core3 (gradeP := gradeP) (T := T)) :
    Low3 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => t.F c.1
  | Sum.inr (Sum.inl H) => t.rho1 st H
  | Sum.inr (Sum.inr (Sum.inl s)) => t.rho2 st s
  | Sum.inr (Sum.inr (Sum.inr t')) => meet₃ st t t'

/-- **Same-level meet locality at level three**, on the complete lower row (proper values, level-one
directed values, level-two directed values, level-three meets). -/
theorem Core3.same3 (st : Setting gradeP T) (t t' : Core3 (gradeP := gradeP) (T := T)) :
    TransformsTo Low3.grade (t.row st) (fun d => min (t'.row st d) (meet₃ st t' t)) := by
  set m := meet₃ st t' t with hm
  refine ⟨fun k => if k ≤ 3 then m else ⊥, id, ?_, ?_, rfl, fun _ _ h => h,
    fun _ _ _ _ _ => rfl, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro n
    dsimp only
    split_ifs with h
    · exact ((meet₃_selfVis st t' t).mono h).symm
    · simp
  · intro d
    have hag := meet₃_agree st t' t
    rcases d with c | H | s | t''
    · show min (t'.F c.1) m = min (id (t.F c.1)) (if gradeP c.1 ≤ 3 then m else ⊥)
      rw [if_pos c.2]; exact hag.1 c.1 c.2
    · show min (t'.rho1 st H) m = min (id (t.rho1 st H)) (if (1 : ℕ) ≤ 3 then m else ⊥)
      rw [if_pos (by omega)]; exact hag.2.1 H
    · show min (t'.rho2 st s) m = min (id (t.rho2 st s)) (if (2 : ℕ) ≤ 3 then m else ⊥)
      rw [if_pos (by omega)]; exact hag.2.2 s
    · show min (meet₃ st t' t'') m = min (id (meet₃ st t t'')) (if (3 : ℕ) ≤ 3 then m else ⊥)
      rw [if_pos (le_refl 3)]
      simp only [id]
      rw [hm, meet₃_ultra st t' t t'', meet₃_comm st t t'']


end Fragment

end VaughtConjecture.Knight
