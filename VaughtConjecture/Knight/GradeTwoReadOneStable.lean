/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoAgreeingMember

/-! # The level-one clause: decoded readings are stable under capped agreement

`ReadOneStable m` (`Knight/GradeTwoAgreeingMember.lean`) asks that every member `m'` agreeing
with `m` under `m`'s cap `γ = ofOrd g` at every base cell, with at least that cap, has its decoded
level-one readings agree with `m`'s under `γ`.  This module proves it for every member
(`readOneStable_of_member`), through the counted recoding:

* **Keys under the cap are stable** (`mem_keys_iff_of_lt`): the value sets `S` of `m.low` and
  `S'` of `m'.low` have the same keys below `g` — a value of `S` is at most `g`, and a value at
  least `g` has key at least `g` (`le_keyOrd_of_le`, since `g` is self-visible at grade two).
  Hence blocks and codes of values below `g` coincide (`blockOfKey_eq_of_lt`, `code_eq_of_lt`),
  and every key at least `g` has block beyond the low keys (`le_blockOfKey_of_ge`).
* **The witness vectors agree under the code cap** `c₀ = ω·(n+1) + 1`, `n` the number of low
  keys (`witness_agree`): at a cell where `m.low` is below `g` the codes are equal; where it is
  `g` the code is `c₀` and `m'`'s code is at least `c₀` (its value is at least `g`, its finite
  part at least one by orderliness).
* **The level caps with any level-one member agree under `c₀`** (`levelCap_min_eq`): the
  capped ultrametric identity for agreement caps and rounding commuting with capping.
* **The decoders agree under `γ`** (`shift_min_eq_of_agree`): an input below `c₀` is common to
  both and decodes through the same hosted key (`keyAt_eq_of_le_lowCount`); an input at least
  `c₀` decodes on both sides to at least `γ` (`ofOrd_le_shift_of_lowCount_lt`).

With it, `lift_of_coded_input` holds unconditionally for coded inputs
(`lift_of_coded_input'`): the agreeing retained member agrees with the ambient controller on the
full decoded vector, level-one readings included.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Value ExtOrd

/-! ## Keys under a cap -/

section Keys

variable (g : Ordinal.{0})

/-- The keys of a value set below the cap. -/
noncomputable def lowKeys (T : Finset Ordinal.{0}) : Finset Ordinal.{0} :=
  (keys 1 T).filter fun κ => κ < g

theorem lowKeys_card_le (T : Finset Ordinal.{0}) : (lowKeys g T).card ≤ (keys 1 T).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

variable {g}

/-- A cap self-visible at grade two is its own key at grade one. -/
theorem keyOrd_one_eq_self (hg : 2 ≤ finitePart g) : keyOrd 1 g = g := by
  unfold keyOrd
  split_ifs with h
  · omega
  · rfl

/-- A value at least a cap self-visible at grade two has key at least the cap. -/
theorem le_keyOrd_of_le (hg : 2 ≤ finitePart g) {v : Ordinal.{0}} (hv : g ≤ v) :
    g ≤ keyOrd 1 v := by
  unfold keyOrd
  split_ifs with h
  · rcases lt_or_eq_of_le (limitPart_mono hv) with hlt | heq
    · have := limitPart_add_nat_le_of_lt hlt (finitePart g)
      rw [limitPart_add_finitePart] at this
      exact this
    · have := finitePart_le_of_le_of_limitPart_eq hv heq
      omega
  · exact hv

/-- **Capped agreement of two value sets under the cut `g`**: the two have the same values below
`g`, and the second has finite parts at least one.  (No bound on the first set: the cut may be
interior to both.) -/
structure LowAgree (g : Ordinal.{0}) (S S' : Finset Ordinal.{0}) : Prop where
  /-- The two sets have the same values below the cut. -/
  low : ∀ v, v < g → (v ∈ S ↔ v ∈ S')
  /-- Values of the second set have finite part at least one. -/
  fp : ∀ v ∈ S', 1 ≤ finitePart v

variable {S S' : Finset Ordinal.{0}}

theorem mem_keys_iff_of_lt (hg : 2 ≤ finitePart g) (h : LowAgree g S S') {κ : Ordinal.{0}}
    (hκ : κ < g) : κ ∈ keys 1 S ↔ κ ∈ keys 1 S' := by
  constructor
  · intro hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    have hvg : v < g := by
      by_contra hge
      exact absurd hκ (not_lt.mpr (le_keyOrd_of_le hg (not_lt.mp hge)))
    exact Finset.mem_image.mpr ⟨v, (h.low v hvg).mp hv, rfl⟩
  · intro hk
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
    have hvg : v < g := by
      by_contra hge
      exact absurd hκ (not_lt.mpr (le_keyOrd_of_le hg (not_lt.mp hge)))
    exact Finset.mem_image.mpr ⟨v, (h.low v hvg).mpr hv, rfl⟩

theorem lowKeys_eq (hg : 2 ≤ finitePart g) (h : LowAgree g S S') : lowKeys g S = lowKeys g S' := by
  ext κ
  simp only [lowKeys, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hκ⟩
    exact ⟨(mem_keys_iff_of_lt hg h hκ).mp hk, hκ⟩
  · rintro ⟨hk, hκ⟩
    exact ⟨(mem_keys_iff_of_lt hg h hκ).mpr hk, hκ⟩

theorem blockOfKey_eq_of_lt (hg : 2 ≤ finitePart g) (h : LowAgree g S S') {κ : Ordinal.{0}}
    (hκ : κ < g) : blockOfKey 1 S κ = blockOfKey 1 S' κ := by
  unfold blockOfKey
  congr 1
  ext κ'
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hk, hle⟩
    exact ⟨(mem_keys_iff_of_lt hg h (hle.trans_lt hκ)).mp hk, hle⟩
  · rintro ⟨hk, hle⟩
    exact ⟨(mem_keys_iff_of_lt hg h (hle.trans_lt hκ)).mpr hk, hle⟩

theorem code_eq_of_lt (hg : 2 ≤ finitePart g) (h : LowAgree g S S') {v : Ordinal.{0}}
    (hv : v < g) : code 1 S v = code 1 S' v := by
  unfold code blockOf
  rw [blockOfKey_eq_of_lt hg h ((keyOrd_le 1 v).trans_lt hv)]

/-- A key at least the cap has block beyond the low keys. -/
theorem le_blockOfKey_of_ge (T : Finset Ordinal.{0}) {κ : Ordinal.{0}} (hκ : κ ∈ keys 1 T)
    (hgκ : g ≤ κ) : (lowKeys g T).card + 1 ≤ blockOfKey 1 T κ := by
  unfold blockOfKey
  have hnot : κ ∉ lowKeys g T := by
    simp only [lowKeys, Finset.mem_filter, not_and, not_lt]
    exact fun _ => hgκ
  have hsub : insert κ (lowKeys g T) ⊆ (keys 1 T).filter fun κ' => κ' ≤ κ := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | hx
    · exact ⟨hκ, le_rfl⟩
    · simp only [lowKeys, Finset.mem_filter] at hx
      exact ⟨hx.1, hx.2.le.trans hgκ⟩
  calc (lowKeys g T).card + 1 = (insert κ (lowKeys g T)).card :=
        (Finset.card_insert_of_notMem hnot).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- A key below the cap has block within the low keys. -/
theorem blockOfKey_le_lowCount_of_lt (T : Finset Ordinal.{0}) {κ : Ordinal.{0}} (hκ : κ < g) :
    blockOfKey 1 T κ ≤ (lowKeys g T).card := by
  unfold blockOfKey
  apply Finset.card_le_card
  intro x hx
  simp only [lowKeys, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans_lt hκ⟩

/-- The cap, when it is a value, has block one past the low keys. -/
theorem blockOfKey_g (hg : 2 ≤ finitePart g) {T : Finset Ordinal.{0}} (hgT : g ∈ T) :
    blockOfKey 1 T g = (lowKeys g T).card + 1 := by
  have hmem : g ∈ keys 1 T := Finset.mem_image.mpr ⟨g, hgT, keyOrd_one_eq_self hg⟩
  have hnot : g ∉ lowKeys g T := by
    simp only [lowKeys, Finset.mem_filter, not_and, not_lt]
    exact fun _ => le_rfl
  have hfil : ((keys 1 T).filter fun κ => κ ≤ g) = insert g (lowKeys g T) := by
    ext x
    simp only [lowKeys, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hle⟩
      rcases hle.lt_or_eq with hlt | rfl
      · exact Or.inr ⟨hx, hlt⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hmem, le_rfl⟩
      · exact ⟨hx, hlt.le⟩
  unfold blockOfKey
  rw [hfil, Finset.card_insert_of_notMem hnot]

/-- The hosted keys on the low blocks coincide. -/
theorem keyAt_eq_of_le_lowCount (hg : 2 ≤ finitePart g) (h : LowAgree g S S') {i : ℕ}
    (hi : i ≤ (lowKeys g S).card) : keyAt 1 S i = keyAt 1 S' i := by
  unfold keyAt
  congr 1
  ext κ
  simp only [Finset.mem_filter]
  have hn := lowKeys_eq hg h
  constructor
  · rintro ⟨hk, hb⟩
    have hb' : blockOfKey 1 S κ ≤ i := by exact_mod_cast hb
    have hκ : κ < g := by
      by_contra hge
      have := le_blockOfKey_of_ge S hk (not_lt.mp hge)
      omega
    refine ⟨(mem_keys_iff_of_lt hg h hκ).mp hk, ?_⟩
    rw [← blockOfKey_eq_of_lt hg h hκ]
    exact hb
  · rintro ⟨hk, hb⟩
    have hb' : blockOfKey 1 S' κ ≤ i := by exact_mod_cast hb
    have hκ : κ < g := by
      by_contra hge
      have := le_blockOfKey_of_ge S' hk (not_lt.mp hge)
      rw [← hn] at this
      omega
    refine ⟨(mem_keys_iff_of_lt hg h hκ).mpr hk, ?_⟩
    rw [blockOfKey_eq_of_lt hg h hκ]
    exact hb

/-- Decoding an input on a block beyond the low keys gives at least the cap. -/
theorem ofOrd_le_shift_of_lowCount_lt (T : Finset Ordinal.{0}) {γT : ExtOrd}
    (hγT : ofOrd g ≤ γT) {i j : ℕ} (hi : (lowKeys g T).card + 1 ≤ i) :
    ofOrd g ≤ shift 1 T γT (ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal))) := by
  rw [shift_ofOrd, blockIdx_mul_add, finitePart_mul_add]
  split_ifs with hc
  · exact hγT
  · have hc' : i ≤ (keys 1 T).card := by
      have : ¬ ((keys 1 T).card + 1 ≤ i) := fun h => hc (by exact_mod_cast h)
      omega
    obtain ⟨κ, hκ, hκi, hb⟩ := keyAt_nat_eq_some 1 T (by omega) hc'
    rw [hκi]
    have hgκ : g ≤ κ := by
      by_contra hlt
      have := blockOfKey_le_lowCount_of_lt T (not_le.mp hlt)
      omega
    exact ofOrd_le_ofOrd.mpr (hgκ.trans (decodeIn_ge 1 κ j))

/-- An input in a block within the low keys, with positive finite part, lies below the code cap. -/
theorem omega_mul_add_lt_of_le {i j n : ℕ} (hi : i ≤ n) :
    Ordinal.omega0 * (i : Ordinal) + (j : Ordinal) <
      Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal) := by
  have h1 : Ordinal.omega0 * (i : Ordinal) + (j : Ordinal) <
      Ordinal.omega0 * (i : Ordinal) + Ordinal.omega0 :=
    (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 j)
  have h2 : Ordinal.omega0 * (i : Ordinal) + Ordinal.omega0 =
      Ordinal.omega0 * ((i + 1 : ℕ) : Ordinal) := by
    rw [Nat.cast_succ, mul_add_one]
  have h3 : ((i + 1 : ℕ) : Ordinal) ≤ ((n + 1 : ℕ) : Ordinal) := by
    exact_mod_cast Nat.succ_le_succ hi
  calc Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)
      < Ordinal.omega0 * ((i + 1 : ℕ) : Ordinal) := h2 ▸ h1
    _ ≤ Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal) := by gcongr
    _ ≤ Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal) := le_self_add

/-- **The decoders agree under the cap** on inputs agreeing under the code cap. -/
theorem shift_min_eq_of_agree {I : ℕ} (hg : 2 ≤ finitePart g) (h : LowAgree g S S')
    {γ γ' : ExtOrd} (hγ : ofOrd g ≤ γ) (hγ' : ofOrd g ≤ γ') {u u' : ExtOrd} (hu : u ∈ alph 1 I)
    (hus : SelfVis 1 u)
    (hu' : u' ∈ alph 1 I)
    (hagree : min u' (ofOrd (Ordinal.omega0 * (((lowKeys g S).card + 1 : ℕ) : Ordinal) +
      ((1 : ℕ) : Ordinal))) =
      min u (ofOrd (Ordinal.omega0 * (((lowKeys g S).card + 1 : ℕ) : Ordinal) +
        ((1 : ℕ) : Ordinal)))) :
    min (shift 1 S' γ' u') (ofOrd g) = min (shift 1 S γ u) (ofOrd g) := by
  set n := (lowKeys g S).card with hn
  set c₀ : ExtOrd := ofOrd (Ordinal.omega0 * ((n + 1 : ℕ) : Ordinal) + ((1 : ℕ) : Ordinal))
    with hc₀
  have hn' : (lowKeys g S').card = n := by rw [hn, lowKeys_eq hg h]
  rcases ExtOrd.cases u with rfl | rfl | ⟨α, rfl⟩
  · have hu'b : u' = ⊥ := by
      rw [min_eq_left bot_le] at hagree
      exact (min_eq_bot.mp hagree).resolve_right (ofOrd_ne_bot _)
    rw [hu'b, shift_bot, shift_bot]
  · exact absurd rfl (ne_top_of_mem_alph hu)
  · obtain ⟨i, j, -, hj2, hα⟩ := (mem_alph_iff.mp hu).resolve_left (ofOrd_ne_bot α)
    rw [ofOrd_inj] at hα
    subst hα
    have hj1 : 1 ≤ j := by
      rw [selfVis_ofOrd_iff, finitePart_mul_add] at hus
      exact hus
    rcases Nat.lt_or_ge i (n + 1) with hi | hi
    · -- below the code cap: common input, common hosted key
      have hlt : ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)) < c₀ :=
        ofOrd_lt_ofOrd.mpr (omega_mul_add_lt_of_le (Nat.lt_succ_iff.mp hi))
      have hu'e : u' = ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)) := by
        rw [min_eq_left hlt.le] at hagree
        rcases le_total u' c₀ with hle | hle
        · rw [min_eq_left hle] at hagree
          exact hagree
        · rw [min_eq_right hle] at hagree
          exact absurd hagree hlt.ne'
      rw [hu'e]
      congr 1
      rw [shift_ofOrd, shift_ofOrd, blockIdx_mul_add]
      have hiS : ¬ (((keys 1 S).card + 1 : ℕ) : Ordinal) ≤ (i : Ordinal) := by
        have := lowKeys_card_le g S
        intro hle
        have hle' : (keys 1 S).card + 1 ≤ i := by exact_mod_cast hle
        omega
      have hiS' : ¬ (((keys 1 S').card + 1 : ℕ) : Ordinal) ≤ (i : Ordinal) := by
        have := lowKeys_card_le g S'
        intro hle
        have hle' : (keys 1 S').card + 1 ≤ i := by exact_mod_cast hle
        omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hiS'), ite_eq_right_of_eq_false _ _ (eq_false hiS),
        keyAt_eq_of_le_lowCount hg h (Nat.lt_succ_iff.mp hi)]
    · -- at least the code cap: both decode to at least the cap
      have hge : c₀ ≤ ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)) := by
        rw [hc₀, ofOrd_le_ofOrd]
        have h1 : ((n + 1 : ℕ) : Ordinal) ≤ (i : Ordinal) := by exact_mod_cast hi
        have h2 : ((1 : ℕ) : Ordinal) ≤ (j : Ordinal) := by exact_mod_cast hj1
        gcongr
      have hge' : c₀ ≤ u' := by
        rw [min_eq_right hge] at hagree
        rw [← hagree]
        exact min_le_left _ _
      have h1 : ofOrd g ≤
          shift 1 S γ (ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal))) :=
        ofOrd_le_shift_of_lowCount_lt S hγ hi
      have h2 : ofOrd g ≤ shift 1 S' γ' u' := by
        rcases ExtOrd.cases u' with rfl | rfl | ⟨α', rfl⟩
        · exact absurd hge' (not_le.mpr (bot_lt_ofOrd _))
        · exact absurd rfl (ne_top_of_mem_alph hu')
        · obtain ⟨i', j', -, -, hα'⟩ := (mem_alph_iff.mp hu').resolve_left (ofOrd_ne_bot α')
          rw [ofOrd_inj] at hα'
          subst hα'
          have hi' : (lowKeys g S').card + 1 ≤ i' := by
            rw [hn']
            have := blockIdx_mono (ofOrd_le_ofOrd.mp hge')
            rw [blockIdx_mul_add, blockIdx_mul_add] at this
            exact_mod_cast this
          exact ofOrd_le_shift_of_lowCount_lt S' hγ' hi'
      rw [min_eq_right h1, min_eq_right h2]

end Keys

/-! ## Level caps under the code cap -/

theorem min_min_min_eq {α : Type*} [LinearOrder α] (a b x c : α) :
    min (min a (min b x)) c = min (min a c) (min (min b c) x) := by
  apply le_antisymm
  · exact le_min (le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _))
      (le_min (le_min ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        (min_le_right _ _)) ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  · exact le_min (le_min ((min_le_left _ _).trans (min_le_left _ _))
      (le_min ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
        ((min_le_right _ _).trans (min_le_right _ _)))) ((min_le_left _ _).trans (min_le_right _ _))

/-- **Level caps with a common partner agree under a cap** below the agreement of the two
labellings and below both their caps. -/
theorem levelCap_min_eq {Z : Type*} [Fintype Z] {I : ℕ} {W W' X : Z → ExtOrd}
    {Wγ W'γ Xγ c : ExtOrd} (hc : c ∈ alph 1 I) (hcs : SelfVis 1 c) (hW : c ≤ agreeCap W' W)
    (hWγ : c ≤ Wγ) (hW'γ : c ≤ W'γ) :
    min (levelCap 1 I W' W'γ X Xγ) c = min (levelCap 1 I W Wγ X Xγ) c := by
  unfold levelCap
  rw [roundDown_min_right hc hcs, roundDown_min_right hc hcs]
  congr 1
  have h1 := min_agreeCap_eq hW X
  rw [min_min_min_eq, min_min_min_eq, h1, min_eq_right hWγ, min_eq_right hW'γ]

/-! ## The members -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

section Members

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
  (hI : Fintype.card (Cell D₀) + 2 ≤ I)

/-- A member's grade-`≤ 1` values have finite part at least one (orderliness at positive grade). -/
theorem Member.one_le_finitePart_of_low (m : Member sem₀ I 2 P) {d : BaseCells D₀ 1}
    {v : Ordinal.{0}} (hv : m.low d = ofOrd v) : 1 ≤ finitePart v := by
  have h := m.respects.orderly ⟨d.1, d.2.trans (by omega)⟩
  rw [← Member.low_apply, hv] at h
  have h1 := SelfVis.mono h (D₀.grade_pos d.1)
  rw [selfVis_ofOrd_iff] at h1
  exact h1

section Stable

variable (m m' : Member sem₀ I 2 P) {g : Ordinal.{0}} (hg : m.γ = ofOrd g)
  (hbase : ∀ d, min (m'.F d) m.γ = min (m.F d) m.γ)

include hg hbase

omit hg in
theorem low_min_eq (d : BaseCells D₀ 1) : min (m'.low d) m.γ = min (m.low d) m.γ := by
  rw [Member.low_apply, Member.low_apply]
  exact hbase _

/-- The value sets of the two members agree under the cap. -/
theorem lowAgree_of_members : LowAgree g (baseRange m.low) (baseRange m'.low) where
  low v hv := by
    constructor
    · intro hS
      obtain ⟨d, hd⟩ := Member.exists_of_mem_baseRange hS
      have h := low_min_eq m m' hbase d
      rw [hd, hg, min_eq_left (ofOrd_le_ofOrd.mpr hv.le)] at h
      have hd' : m'.low d = ofOrd v := by
        rcases le_total (m'.low d) (ofOrd g) with hle | hle
        · rw [min_eq_left hle] at h
          exact h
        · rw [min_eq_right hle] at h
          exact absurd h (ofOrd_lt_ofOrd.mpr hv).ne'
      exact mem_primRange_of_eq hd'
    · intro hS'
      obtain ⟨d, hd⟩ := Member.exists_of_mem_baseRange hS'
      have h := low_min_eq m m' hbase d
      rw [hd, hg, min_eq_left (ofOrd_le_ofOrd.mpr hv.le)] at h
      have hd' : m.low d = ofOrd v := by
        rcases le_total (m.low d) (ofOrd g) with hle | hle
        · rw [min_eq_left hle] at h
          exact h.symm
        · rw [min_eq_right hle] at h
          exact absurd h.symm (ofOrd_lt_ofOrd.mpr hv).ne'
      exact mem_primRange_of_eq hd'
  fp v hv := by
    obtain ⟨d, hd⟩ := Member.exists_of_mem_baseRange hv
    exact m'.one_le_finitePart_of_low hd

omit hbase in
theorem two_le_finitePart_of_cap : 2 ≤ finitePart g := by
  have := m.γ_vis
  rw [hg, selfVis_ofOrd_iff] at this
  exact this

/-- The code cap of the first member. -/
noncomputable def codeCap : ExtOrd :=
  ofOrd (Ordinal.omega0 * (((lowKeys g (baseRange m.low)).card + 1 : ℕ) : Ordinal) +
    ((1 : ℕ) : Ordinal))

omit hg hbase in
include hI in
theorem codeCap_mem_alph : codeCap m (g := g) ∈ alph 1 I := by
  refine mem_alph_iff.mpr (Or.inr ⟨(lowKeys g (baseRange m.low)).card + 1, 1, ?_, by omega, rfl⟩)
  have h1 := lowKeys_card_le g (baseRange m.low)
  have h2 := card_keys_baseRange_le m.low
  have h3 := Member.card_baseCells_le (D₀ := D₀) 1
  omega

omit hg hbase in
theorem codeCap_selfVis : SelfVis 1 (codeCap m (g := g)) := by
  unfold codeCap
  rw [selfVis_ofOrd_iff, finitePart_mul_add]

omit hg hbase in
/-- The code cap is at most the witness cap of any member with the same number of low keys. -/
theorem codeCap_le_capCode {T : Finset Ordinal.{0}}
    (hT : (lowKeys g (baseRange m.low)).card ≤ (keys 1 T).card) :
    codeCap m (g := g) ≤ ofOrd (capCode 1 T) := by
  unfold codeCap capCode
  rw [ofOrd_le_ofOrd]
  have h1 : (((lowKeys g (baseRange m.low)).card + 1 : ℕ) : Ordinal) ≤
      (((keys 1 T).card + 1 : ℕ) : Ordinal) := by exact_mod_cast Nat.succ_le_succ hT
  gcongr

/-- **The witness vectors agree under the code cap.** -/
theorem witness_agree (d : BaseCells D₀ 1) :
    min ((m'.witness hI).F d) (codeCap m (g := g)) =
      min ((m.witness hI).F d) (codeCap m (g := g)) := by
  have hfp := two_le_finitePart_of_cap m hg
  have hL := lowAgree_of_members m m' hg hbase
  have hd := low_min_eq m m' hbase d
  rw [Member.witness_F, Member.witness_F]
  rcases ExtOrd.cases (m.low d) with h0 | h0 | ⟨v, hv⟩
  · have h1 : m'.low d = ⊥ := by
      rw [h0, min_eq_left bot_le] at hd
      exact (min_eq_bot.mp hd).resolve_right (by rw [hg]; exact ofOrd_ne_bot g)
    rw [h0, h1, encT_bot, encT_bot]
  · exact absurd h0 (m.low_ne_top d)
  · rcases lt_or_eq_of_le (ofOrd_le_ofOrd.mp
        (hg ▸ m.baseRange_le_cap v (mem_primRange_of_eq hv))) with hvg | rfl
    · have h1 : m'.low d = ofOrd v := by
        rw [hv, hg, min_eq_left (ofOrd_le_ofOrd.mpr hvg.le)] at hd
        rcases le_total (m'.low d) (ofOrd g) with hle | hle
        · rw [min_eq_left hle] at hd
          exact hd
        · rw [min_eq_right hle] at hd
          exact absurd hd (ofOrd_lt_ofOrd.mpr hvg).ne'
      rw [hv, h1, encT_ofOrd, encT_ofOrd, encOrdK_eq_code, encOrdK_eq_code,
        code_eq_of_lt hfp hL hvg]
    · -- the first member attains the cap: its code is the code cap, the second's is at least it
      have hcode : encT 1 (baseRange m.low) (m.low d) = codeCap m (g := v) := by
        rw [hv, encT_ofOrd, encOrdK_eq_code]
        unfold code blockOf codeCap
        rw [keyOrd_one_eq_self hfp,
          blockOfKey_g hfp (T := baseRange m.low) (mem_primRange_of_eq hv),
          min_eq_right (by omega : 1 ≤ finitePart v)]
      have hge : ofOrd v ≤ m'.low d := by
        rw [hv, hg, min_self] at hd
        rcases le_total (m'.low d) (ofOrd v) with hle | hle
        · rw [min_eq_left hle] at hd
          exact hd.ge
        · exact hle
      rcases ExtOrd.cases (m'.low d) with h0' | h0' | ⟨v', hv'⟩
      · exact absurd (h0' ▸ hge) (not_ofOrd_le_bot v)
      · exact absurd h0' (m'.low_ne_top d)
      · rw [hv'] at hge
        have hgv' : v ≤ v' := ofOrd_le_ofOrd.mp hge
        have hcode' : codeCap m (g := v) ≤ encT 1 (baseRange m'.low) (m'.low d) := by
          rw [hv', encT_ofOrd, encOrdK_eq_code]
          unfold code blockOf codeCap
          rw [ofOrd_le_ofOrd, min_eq_right (hL.fp v' (mem_primRange_of_eq hv'))]
          have hb := le_blockOfKey_of_ge (baseRange m'.low)
            (keyOrd_mem_keys 1 (baseRange m'.low) (mem_primRange_of_eq hv'))
            (le_keyOrd_of_le hfp hgv')
          rw [← lowKeys_eq hfp hL] at hb
          have h1 : (((lowKeys v (baseRange m.low)).card + 1 : ℕ) : Ordinal) ≤
              ((blockOfKey 1 (baseRange m'.low) (keyOrd 1 v') : ℕ) : Ordinal) := by
            exact_mod_cast hb
          gcongr
        rw [hcode, min_self, min_eq_right hcode']

/-- **The level-one readings agree under the cap.** -/
theorem readOne_min_eq (hγ : m.γ ≤ m'.γ) (m₁ : Member₁ sem₀ I) :
    min (readOne sem₀ I P hI m' m₁) m.γ = min (readOne sem₀ I P hI m m₁) m.γ := by
  have hfp := two_le_finitePart_of_cap m hg
  have hL := lowAgree_of_members m m' hg hbase
  unfold readOne Member.dec
  rw [hg]
  have hcap : min (levelCap 1 I (m'.witness hI).F (m'.witness hI).γ m₁.F m₁.γ)
        (codeCap m (g := g)) =
      min (levelCap 1 I (m.witness hI).F (m.witness hI).γ m₁.F m₁.γ) (codeCap m (g := g)) := by
    refine levelCap_min_eq (codeCap_mem_alph hI m) (codeCap_selfVis m)
      (le_agreeCap_iff.mpr fun d => witness_agree hI m m' hg hbase d) ?_ ?_
    · rw [Member.witness_γ]
      exact codeCap_le_capCode m (lowKeys_card_le g _)
    · rw [Member.witness_γ]
      refine codeCap_le_capCode m ?_
      rw [lowKeys_eq hfp hL]
      exact lowKeys_card_le g _
  exact shift_min_eq_of_agree hfp hL le_rfl (hg ▸ hγ) (roundDown_mem _ _ _)
    (roundDown_selfVis _ _ _)
    (roundDown_mem _ _ _) hcap

end Stable

/-- **The level-one clause holds for every member.** -/
theorem readOneStable_of_member (m : Member sem₀ I 2 P) : ReadOneStable hI m := by
  intro m' hbase hγ m₁
  rcases ExtOrd.cases m.γ with hb | ht | ⟨g, hg⟩
  · rw [hb, min_eq_right bot_le, min_eq_right bot_le]
  · exact absurd ht (ne_top_of_mem_alph m.γ_mem)
  · exact readOne_min_eq hI m m' hg hbase hγ m₁

end Members

/-! ## The lift for coded inputs, unconditionally -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

/-- **The lift for coded inputs**, with the ambient a retained member's row at its cap and the
prescribed input a retained member's row restricted to `D⟨C,2⟩`: under the base obligation
alone, the lift by controller change to the agreeing retained member exists, agreeing with the
ambient on the full decoded vector under its cap. -/
theorem lift_of_coded_input' (hcb : CodedBountiful sem₀ I) (C : Finset ι)
    (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan) (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
    (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
    (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F') :
    ∃ q' : Tbelow (A, 2) → ExtOrd,
      RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2) q' ∧
      (∀ d, min (q' d) m.γ = min (MROW m d) m.γ) ∧
      ∀ d : Tbelow (C, 2), q' (CellScheme.below.mono (gradedLe_full_two hC) d) =
        MROW mp (CellScheme.below.mono (gradedLe_full_two hC) d) :=
  lift_of_coded_input sem₀ I M P hAk hI hproper hcb C hC hCA m mp hagree hPC
    (readOneStable_of_member hI m)

end VaughtConjecture.Knight
