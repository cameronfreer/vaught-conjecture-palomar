/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.Repair
public import VaughtConjecture.Knight.NormalForm
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

/-! # The counted recoding of a finite row at a target grade

**The one-step interface of construction-time sharp coding.**  Given a finite set `S` of ordinal
values (the nonbottom values of a row), a cap `γ` self-visible at the target grade `l ≥ 1` and
dominating `S`, this module codes each `v ∈ S` at grade `l` and builds the decoder `σ` that is
the Def. 2.3.9 shifter of the clause-4 witness `G ⇒ (F ↾ dom G) ∧ F(G)` of Knight's stacks
(Def. 4.3.5): `transformsTo_of_shift` is the packaged `TransformsTo` witness with the step
suppressor at a cap `ρ` up to grade `l`.

**Why the code has this shape.**  Def. 2.3.9 clause 5 is unguarded: for every `α` with
`σ α ≤ g k` and every `i ≤ k`, `σ (α ⊔⁺_k i) = σ α ⊔⁺_k i`.  At `k = l` this forces the decoder,
on the code block hosting a value `v`, to be `j ↦ v ⊔⁺_l (min j l)`; so the code must carry `v`'s
finite part up to `l`, values of one `ω`-block with finite part `≤ l` share a code block, and a
value with larger finite part needs its own constant block.  (A value-counted code `ω·cnt v + l`
with a block-constant decoder fails clause 5 exactly on values whose finite part is below `l`,
which every row with cells of grade `< l` contains.)  Hence:

* the **key** of `v = lp + fp` is `lp` if `fp ≤ l`, else `v` (`keyOrd`);
* the **block** of `v` is the number of keys of `S` at most its key (`blockOf`) — a count, so
  no enumeration is chosen;
* the **code** is `ω·blockOf v + min (fp v) l` (`code`): coded at `l` (`code_isCoded`),
  self-visible at every cell grade `a ≤ fp v`, `a ≤ l` (`code_selfVis`);
* the **decoder** `shift`: on the block of an `ω`-block key `κ`, `j ↦ κ + min j l`; on the block
  of a large key, constantly that key; `⊥` on block `0`; `γ` on every block past the last key;
  `⊥ ↦ ⊥`, `⊤ ↦ γ`.

**Proved**: `shift_mono` (across blocks a key's block never reaches the next key,
`key_add_le_next`, through the block-key bijection `exists_key_of_block`), `shift_code` (exact
decoding), `shift_capCode` (the cap code `ω·(|keys| + 1) + l` decodes to `γ`),
`shift_evr_of_le` (clause 5 for every `k ≤ l`, unguarded) and `shift_evr_of_bot` (for `k > l`
under `σ α = ⊥`), and `transformsTo_of_shift`.

**Integration notes.**  Positive cell grades come from graded-plan membership
(`CellScheme.grade_pos`), and coded labels are never `⊤` (`IsCodedLabel.ne_top`); neither is a
construction hypothesis.  The value set fed to the recoding is the **primitive** lower-grade range of
the row (its nonbottom values at proper cells of grade at most the target), and nothing else:
auxiliary cap values must not enter it, since they would change the key count; and the derived
directed values a recursive construction introduces should need no keys of their own, because
each should lie in the decoder image of an already represented lower-stratum value.  That
decoder-image invariant is **proved at three levels** (`Knight/ThreeLevelFragment.lean`,
`Core3.rho1_eq_dec2_rho`); an arbitrary-depth recursion must preserve it level by level — it is
not yet a compiled general theorem.

Construction-private (not root-exported).  Reviewer scout (2026-09-05), graduated: the algebra
has passed unguarded clause 5 above grade one and the `3 → 2 → 1` coherence triangle
(`Knight/RecodingTriangle.lean`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Value lemmas -/

/-- The block index `α / ω`. -/
noncomputable def blockIdx (α : Ordinal.{0}) : Ordinal.{0} := α / Ordinal.omega0

theorem blockIdx_mul_add (t : ℕ) (j : ℕ) : blockIdx (Ordinal.omega0 * t + j) = t := by
  unfold blockIdx
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 j), add_zero]

theorem blockIdx_mono {α β : Ordinal.{0}} (h : α ≤ β) : blockIdx α ≤ blockIdx β := by
  unfold blockIdx
  exact (Ordinal.mul_le_iff_le_div Ordinal.omega0_ne_zero).mp
    ((Ordinal.mul_div_le α Ordinal.omega0).trans h)

theorem limitPart_eq_mul_blockIdx (α : Ordinal.{0}) :
    limitPart α = Ordinal.omega0 * blockIdx α := rfl

theorem blockIdx_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    blockIdx (visibilityReplace α k i) = blockIdx α := by
  unfold visibilityReplace
  split_ifs with h
  · unfold ordinalReplace
    rw [limitPart_eq_mul_blockIdx]
    unfold blockIdx
    rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 i), add_zero]
  · rfl

theorem finitePart_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    finitePart (visibilityReplace α k i) = if finitePart α < k then i else finitePart α := by
  unfold visibilityReplace
  split_ifs with h
  · unfold ordinalReplace; exact finitePart_limitPart_add_nat _ _
  · rfl

theorem limitPart_mul_nat (t : ℕ) : limitPart (Ordinal.omega0 * t) = Ordinal.omega0 * t := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel _ Ordinal.omega0_ne_zero]

theorem finitePart_mul_add (t j : ℕ) : finitePart (Ordinal.omega0 * t + j) = j := by
  have := finitePart_limitPart_add_nat (Ordinal.omega0 * t) j
  rwa [limitPart_mul_nat] at this

theorem limitPart_mul_add (t j : ℕ) : limitPart (Ordinal.omega0 * t + j) = Ordinal.omega0 * t := by
  have := limitPart_limitPart_add_nat (Ordinal.omega0 * t) j
  rwa [limitPart_mul_nat] at this

theorem selfVis_ofOrd_iff {α : Ordinal.{0}} {k : ℕ} : SelfVis k (ofOrd α) ↔ k ≤ finitePart α := by
  unfold SelfVis
  rw [extVisibilityReplace_ofOrd, ofOrd_inj]
  unfold visibilityReplace
  constructor
  · intro h
    by_contra hlt
    rw [if_pos (not_le.mp hlt)] at h
    unfold ordinalReplace at h
    have := congrArg finitePart h
    rw [finitePart_limitPart_add_nat] at this
    omega
  · intro h
    rw [if_neg (not_lt.mpr h)]

/-- The limit part of a limit part is itself. -/
theorem limitPart_idem (α : Ordinal.{0}) : limitPart (limitPart α) = limitPart α := by
  have := limitPart_limitPart_add_nat α 0
  simpa using this

/-- Two ordinals with the same limit part compare by their finite parts. -/
theorem le_of_finitePart_le {α β : Ordinal.{0}} (hl : limitPart α = limitPart β)
    (hf : finitePart α ≤ finitePart β) : α ≤ β := by
  rw [← limitPart_add_finitePart α, ← limitPart_add_finitePart β, hl]
  exact add_le_add le_rfl (by exact_mod_cast hf)

/-- A larger limit part dominates any finite offset. -/
theorem limitPart_add_nat_le_of_lt {α β : Ordinal.{0}} (h : limitPart α < limitPart β) (j : ℕ) :
    limitPart α + j ≤ limitPart β := by
  rw [limitPart_eq_mul_blockIdx, limitPart_eq_mul_blockIdx] at *
  have hb : blockIdx α < blockIdx β := by
    by_contra hle
    exact absurd h (not_lt.mpr (by gcongr; exact not_lt.mp hle))
  calc Ordinal.omega0 * blockIdx α + j ≤ Ordinal.omega0 * blockIdx α + Ordinal.omega0 :=
        add_le_add le_rfl (Ordinal.natCast_lt_omega0 j).le
    _ = Ordinal.omega0 * (blockIdx α + 1) := by rw [mul_add, mul_one]
    _ ≤ Ordinal.omega0 * blockIdx β := by gcongr; exact Order.add_one_le_of_lt hb

/-! ## Keys, blocks, codes -/

section Recoding

variable (l : ℕ) (S : Finset Ordinal.{0}) (γ : ExtOrd)

/-- The key of a value: its `ω`-block when the finite part is `≤ l`, itself otherwise. -/
noncomputable def keyOrd (v : Ordinal.{0}) : Ordinal.{0} :=
  if finitePart v ≤ l then limitPart v else v

theorem keyOrd_le (v : Ordinal.{0}) : keyOrd l v ≤ v := by
  unfold keyOrd; split_ifs
  · exact limitPart_le v
  · exact le_rfl

theorem limitPart_keyOrd (v : Ordinal.{0}) : limitPart (keyOrd l v) = limitPart v := by
  unfold keyOrd; split_ifs
  · exact limitPart_idem v
  · rfl

/-- A key is an `ω`-block key (finite part `0`) or a large value (finite part `> l`). -/
theorem finitePart_keyOrd (v : Ordinal.{0}) :
    finitePart (keyOrd l v) = 0 ∨ l < finitePart (keyOrd l v) := by
  unfold keyOrd; split_ifs with h
  · exact Or.inl (finitePart_limitPart v)
  · exact Or.inr (not_le.mp h)

/-- The key set of the row. -/
noncomputable def keys : Finset Ordinal.{0} := S.image (keyOrd l)

/-- The block of a key: the number of keys at most it. -/
noncomputable def blockOfKey (κ : Ordinal.{0}) : ℕ := ((keys l S).filter fun κ' => κ' ≤ κ).card

/-- The block of a value. -/
noncomputable def blockOf (v : Ordinal.{0}) : ℕ := blockOfKey l S (keyOrd l v)

theorem blockOfKey_le (κ : Ordinal.{0}) : blockOfKey l S κ ≤ (keys l S).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem blockOfKey_mono {κ κ' : Ordinal.{0}} (h : κ ≤ κ') : blockOfKey l S κ ≤ blockOfKey l S κ' := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem blockOfKey_lt {κ κ' : Ordinal.{0}} (hκ' : κ' ∈ keys l S) (h : κ < κ') :
    blockOfKey l S κ < blockOfKey l S κ' := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h.le⟩
  · have := hsub (Finset.mem_filter.mpr ⟨hκ', le_rfl⟩)
    exact absurd (Finset.mem_filter.mp this).2 (not_le.mpr h)

theorem blockOfKey_pos {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) : 0 < blockOfKey l S κ :=
  Finset.card_pos.mpr ⟨κ, Finset.mem_filter.mpr ⟨hκ, le_rfl⟩⟩

theorem keyOrd_mem_keys {v : Ordinal.{0}} (hv : v ∈ S) : keyOrd l v ∈ keys l S :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- **The code** of a value: `ω·block + min (fp v) l`. -/
noncomputable def code (v : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)

theorem code_isCoded (v : Ordinal.{0}) : IsCodedLabel l (ofOrd (code l S v)) :=
  Or.inr ⟨blockOf l S v, min (finitePart v) l, by omega, rfl⟩

theorem code_selfVis {v : Ordinal.{0}} {a : ℕ} (ha : a ≤ finitePart v) (hal : a ≤ l) :
    SelfVis a (ofOrd (code l S v)) := by
  rw [selfVis_ofOrd_iff]
  unfold code
  rw [finitePart_mul_add]
  exact le_min ha hal

/-- The cap code: one block past every key, finite part `l`. -/
noncomputable def capCode : Ordinal.{0} := Ordinal.omega0 * (((keys l S).card + 1 : ℕ) : Ordinal) + l

theorem capCode_selfVis : SelfVis l (ofOrd (capCode l S)) := by
  rw [selfVis_ofOrd_iff]; unfold capCode; rw [finitePart_mul_add]

theorem capCode_isCoded : IsCodedLabel l (ofOrd (capCode l S)) :=
  Or.inr ⟨(keys l S).card + 1, l, by omega, rfl⟩

theorem code_le_capCode (v : Ordinal.{0}) : code l S v ≤ capCode l S := by
  unfold code capCode
  have h1 : (blockOf l S v : Ordinal) ≤ (((keys l S).card + 1 : ℕ) : Ordinal) := by
    exact_mod_cast (by have := blockOfKey_le l S (keyOrd l v); unfold blockOf; omega :
      blockOf l S v ≤ (keys l S).card + 1)
  have h2 : ((min (finitePart v) l : ℕ) : Ordinal) ≤ (l : Ordinal) := by
    exact_mod_cast min_le_right _ _
  calc Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)
      ≤ Ordinal.omega0 * (blockOf l S v : ℕ) + (l : Ordinal) := add_le_add le_rfl h2
    _ ≤ Ordinal.omega0 * (((keys l S).card + 1 : ℕ) : Ordinal) + l := by gcongr

/-! ## The decoder -/

/-- The key hosted on block `t`: the largest key with block `≤ t` (`⊥` if none). -/
noncomputable def keyAt (t : Ordinal.{0}) : WithBot Ordinal.{0} :=
  ((keys l S).filter fun κ => ((blockOfKey l S κ : ℕ) : Ordinal) ≤ t).max

/-- Decoding on the block of a key `κ` at finite offset `j`. -/
noncomputable def decodeIn (κ : Ordinal.{0}) (j : ℕ) : Ordinal.{0} :=
  if finitePart κ = 0 then κ + (min j l : ℕ) else κ

/-- **The decoder.** -/
noncomputable def shift : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => γ
  | some (some α) =>
      if (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt l S (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α))

theorem shift_bot : shift l S γ ⊥ = ⊥ := rfl
theorem shift_top : shift l S γ ⊤ = γ := rfl
theorem shift_ofOrd (α : Ordinal.{0}) :
    shift l S γ (ofOrd α) =
      if (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α then γ
      else match keyAt l S (blockIdx α) with
        | ⊥ => ⊥
        | some κ => ofOrd (decodeIn l κ (finitePart α)) := rfl

theorem keyAt_eq_of_mem {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) :
    keyAt l S (blockOfKey l S κ) = some κ := by
  unfold keyAt
  apply le_antisymm
  · apply Finset.max_le
    intro κ' hκ'
    have h := (Finset.mem_filter.mp hκ').2
    have h' : blockOfKey l S κ' ≤ blockOfKey l S κ := by exact_mod_cast h
    by_contra hlt
    have hlt' : κ < κ' := by
      rcases lt_or_ge κ κ' with hh | hh
      · exact hh
      · exact absurd (WithBot.coe_le_coe.mpr hh) hlt
    exact absurd h' (not_le.mpr (blockOfKey_lt l S (Finset.mem_filter.mp hκ').1 hlt'))
  · exact Finset.le_max (Finset.mem_filter.mpr ⟨hκ, le_rfl⟩)

theorem keyAt_zero : keyAt l S 0 = ⊥ := by
  unfold keyAt
  apply Finset.max_eq_bot.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro κ hκ h
  have : ((blockOfKey l S κ : ℕ) : Ordinal) = 0 := le_antisymm h zero_le
  have h0 : blockOfKey l S κ = 0 := by exact_mod_cast this
  exact absurd h0 (Nat.pos_iff_ne_zero.mp (blockOfKey_pos l S hκ))

/-- **Exact decoding**: the code of a member of `S` decodes to it. -/
theorem shift_code {v : Ordinal.{0}} (hv : v ∈ S) : shift l S γ (ofOrd (code l S v)) = ofOrd v := by
  rw [shift_ofOrd]
  unfold code
  rw [blockIdx_mul_add, finitePart_mul_add]
  have hb : blockOf l S v ≤ (keys l S).card := blockOfKey_le l S _
  rw [if_neg (by
    intro h
    have : (keys l S).card + 1 ≤ blockOf l S v := by exact_mod_cast h
    omega)]
  unfold blockOf
  rw [keyAt_eq_of_mem l S (keyOrd_mem_keys l S hv)]
  simp only
  congr 1
  unfold decodeIn
  rcases finitePart_keyOrd l v with h0 | hl
  · rw [if_pos h0]
    unfold keyOrd at h0 ⊢
    split_ifs at h0 ⊢ with hfp
    · have hm : min (min (finitePart v) l) l = finitePart v := by
        rw [min_eq_left hfp, min_eq_left hfp]
      rw [hm]; exact limitPart_add_finitePart v
    · exfalso
      have := finitePart_keyOrd l v
      unfold keyOrd at this
      rw [if_neg hfp] at this
      rcases this with h | h
      · exact hfp (by omega)
      · omega
  · rw [if_neg (by omega)]
    unfold keyOrd at hl ⊢
    split_ifs at hl ⊢ with hfp
    · rw [finitePart_limitPart] at hl; omega
    · rfl

/-- **Cap decoding**: the cap code decodes to `γ`. -/
theorem shift_capCode : shift l S γ (ofOrd (capCode l S)) = γ := by
  rw [shift_ofOrd]
  unfold capCode
  rw [blockIdx_mul_add, if_pos le_rfl]

/-! ### Monotonicity -/

/-- The values decoded on the block of a key `κ` lie in `[κ, κ + l]`. -/
theorem decodeIn_ge (κ : Ordinal.{0}) (j : ℕ) : κ ≤ decodeIn l κ j := by
  unfold decodeIn; split_ifs
  · exact le_self_add
  · exact le_rfl

theorem decodeIn_le (κ : Ordinal.{0}) (j : ℕ) : decodeIn l κ j ≤ κ + l := by
  unfold decodeIn; split_ifs
  · exact add_le_add le_rfl (by exact_mod_cast min_le_right _ _)
  · exact le_self_add

theorem decodeIn_mono (κ : Ordinal.{0}) {j j' : ℕ} (h : j ≤ j') :
    decodeIn l κ j ≤ decodeIn l κ j' := by
  unfold decodeIn; split_ifs
  · exact add_le_add le_rfl (by exact_mod_cast min_le_min_right l h)
  · exact le_rfl

/-- **A key's block never reaches the next key**: for keys `κ < κ'`, `κ + l ≤ κ'`. -/
theorem key_add_le_next {κ κ' : Ordinal.{0}} (hκ : κ ∈ keys l S) (hκ' : κ' ∈ keys l S)
    (h : κ < κ') (h0 : finitePart κ = 0) : κ + l ≤ κ' := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hκ'
  rcases lt_or_ge (limitPart (keyOrd l v)) (limitPart (keyOrd l v')) with hlt | hge
  · -- a later `ω`-block dominates any finite offset
    have h1 : keyOrd l v = limitPart (keyOrd l v) := by
      conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v)]
      rw [h0]; simp
    rw [h1]
    exact (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le _)
  · -- same `ω`-block: `κ'` is a large value, `κ` the block key
    have heq : limitPart (keyOrd l v) = limitPart (keyOrd l v') :=
      le_antisymm (limitPart_mono h.le) hge
    rcases finitePart_keyOrd l v' with h0' | hl'
    · exfalso
      -- both are block keys of the same block: equal
      have e1 : keyOrd l v = limitPart (keyOrd l v) := by
        conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v)]; rw [h0]; simp
      have e2 : keyOrd l v' = limitPart (keyOrd l v') := by
        conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v')]; rw [h0']; simp
      rw [e1, e2, heq] at h
      exact lt_irrefl _ h
    · have e1 : keyOrd l v = limitPart (keyOrd l v) := by
        conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v)]; rw [h0]; simp
      rw [e1, heq]
      conv_rhs => rw [← limitPart_add_finitePart (keyOrd l v')]
      exact add_le_add le_rfl (by exact_mod_cast hl'.le)

theorem keyAt_mono {t t' : Ordinal.{0}} (h : t ≤ t') : keyAt l S t ≤ keyAt l S t' := by
  unfold keyAt
  apply Finset.max_mono
  intro κ hκ
  rw [Finset.mem_filter] at hκ ⊢
  exact ⟨hκ.1, hκ.2.trans h⟩

theorem keyAt_mem {t : Ordinal.{0}} {κ : Ordinal.{0}} (h : keyAt l S t = some κ) : κ ∈ keys l S :=
  (Finset.mem_filter.mp (Finset.mem_of_max h)).1

/-- Below a cap `γ` self-visible at `l` that dominates the values, the key-block values
`κ + l` stay below `γ`. -/
theorem key_add_l_le {v : Ordinal.{0}} {g : Ordinal.{0}} (hv : v ≤ g) (hg : l ≤ finitePart g)
    (h0 : finitePart (keyOrd l v) = 0) : keyOrd l v + l ≤ g := by
  have e1 : keyOrd l v = limitPart v := by
    conv_lhs => rw [← limitPart_add_finitePart (keyOrd l v)]
    rw [h0, limitPart_keyOrd]; simp
  rw [e1]
  rcases lt_or_ge (limitPart v) (limitPart g) with hlt | hge
  · exact (limitPart_add_nat_le_of_lt hlt l).trans (limitPart_le g)
  · have heq : limitPart v = limitPart g := le_antisymm (limitPart_mono hv) hge
    rw [heq]
    conv_rhs => rw [← limitPart_add_finitePart g]
    exact add_le_add le_rfl (by exact_mod_cast hg)

theorem decodeIn_le_of_key {v : Ordinal.{0}} {g : Ordinal.{0}} (hv : v ≤ g)
    (hg : l ≤ finitePart g) (j : ℕ) : decodeIn l (keyOrd l v) j ≤ g := by
  unfold decodeIn
  split_ifs with h0
  · exact (add_le_add le_rfl (by exact_mod_cast min_le_right j l)).trans (key_add_l_le l hv hg h0)
  · exact (keyOrd_le l v).trans hv

theorem shift_ofOrd_le_γ (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) (α : Ordinal.{0}) :
    shift l S γ (ofOrd α) ≤ γ := by
  rw [shift_ofOrd]
  split_ifs with h
  · exact le_rfl
  · rcases hk : keyAt l S (blockIdx α) with _ | κ
    · exact bot_le
    · simp only
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (keyAt_mem l S hk)
      have hvγ := hS v hv
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · exact absurd hvγ (not_ofOrd_le_bot v)
      · exact le_top
      · rw [ofOrd_le_ofOrd] at hvγ ⊢
        exact decodeIn_le_of_key l hvγ (selfVis_ofOrd_iff.mp hγ) _

/-! ### The block-key bijection -/

theorem blockOfKey_injOn : Set.InjOn (blockOfKey l S) (keys l S) := by
  intro κ hκ κ' hκ' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd h (ne_of_lt (blockOfKey_lt l S hκ' hlt))
  · exact absurd h (ne_of_gt (blockOfKey_lt l S hκ hgt))

theorem blockOfKey_mem_Icc {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) :
    blockOfKey l S κ ∈ Finset.Icc 1 (keys l S).card :=
  Finset.mem_Icc.mpr ⟨blockOfKey_pos l S hκ, blockOfKey_le l S κ⟩

/-- Every block `1 … |keys|` is the block of exactly one key. -/
theorem exists_key_of_block {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ (keys l S).card) :
    ∃ κ ∈ keys l S, blockOfKey l S κ = n := by
  have himg : (keys l S).image (blockOfKey l S) = Finset.Icc 1 (keys l S).card := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hb
      exact blockOfKey_mem_Icc l S hκ
    · rw [Finset.card_image_of_injOn (blockOfKey_injOn l S), Nat.card_Icc]
      omega
  have : n ∈ (keys l S).image (blockOfKey l S) := by
    rw [himg]; exact Finset.mem_Icc.mpr ⟨h1, hn⟩
  obtain ⟨κ, hκ, hb⟩ := Finset.mem_image.mp this
  exact ⟨κ, hκ, hb⟩

/-- On a block `t ≤ |keys|`, the hosted key has block exactly `t`. -/
theorem blockOfKey_of_keyAt {t : ℕ} (ht : t ≤ (keys l S).card) {κ : Ordinal.{0}}
    (h : keyAt l S t = some κ) : blockOfKey l S κ = t := by
  have hκ := keyAt_mem l S h
  have hle : blockOfKey l S κ ≤ t := by
    have := (Finset.mem_filter.mp (Finset.mem_of_max h)).2
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact absurd hle (not_le.mpr (blockOfKey_pos l S hκ))
  · obtain ⟨κ', hκ', hb⟩ := exists_key_of_block l S hpos ht
    -- `κ'` is in the filter, hence `≤ κ`, hence `t = block κ' ≤ block κ`
    have hmem : κ' ∈ (keys l S).filter fun κ'' => ((blockOfKey l S κ'' : ℕ) : Ordinal) ≤ t :=
      Finset.mem_filter.mpr ⟨hκ', by rw [hb]⟩
    have hle' : κ' ≤ κ := by
      have this : (κ' : WithBot Ordinal.{0}) ≤ keyAt l S t := Finset.le_max hmem
      rw [h] at this
      exact WithBot.coe_le_coe.mp this
    have := blockOfKey_mono l S hle'
    omega

theorem keyAt_nat_eq_some {t : ℕ} (h1 : 1 ≤ t) (ht : t ≤ (keys l S).card) :
    ∃ κ ∈ keys l S, keyAt l S t = some κ ∧ blockOfKey l S κ = t := by
  obtain ⟨κ, hκ, hb⟩ := exists_key_of_block l S h1 ht
  refine ⟨κ, hκ, ?_, hb⟩
  have := keyAt_eq_of_mem l S hκ
  rw [hb] at this
  exact this

/-- Block indices below `|keys| + 1` are naturals. -/
theorem exists_nat_of_lt_card {t : Ordinal.{0}} (h : t < (((keys l S).card + 1 : ℕ) : Ordinal)) :
    ∃ n : ℕ, t = n ∧ n ≤ (keys l S).card := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (h.trans_le (Ordinal.natCast_lt_omega0 _).le)
  rw [Nat.cast_succ] at h
  exact ⟨n, rfl, by exact_mod_cast Order.lt_add_one_iff.mp h⟩

/-! ### Monotonicity -/

theorem finitePart_le_of_le_of_limitPart_eq {α β : Ordinal.{0}} (h : α ≤ β)
    (hl : limitPart α = limitPart β) : finitePart α ≤ finitePart β := by
  by_contra hlt
  have := le_of_finitePart_le (α := β) (β := α) hl.symm (not_le.mp hlt).le
  have heq : α = β := le_antisymm h this
  subst heq
  exact hlt le_rfl

theorem shift_mono (hγ : SelfVis l γ) (hS : ∀ v ∈ S, ofOrd v ≤ γ) : Monotone (shift l S γ) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [shift_bot]; exact bot_le
  · have := top_le_iff.mp hxy; subst this; exact le_rfl
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · exact absurd hxy (not_ofOrd_le_bot α)
    · rw [shift_top]; exact shift_ofOrd_le_γ l S γ hγ hS α
    · have hαβ := ofOrd_le_ofOrd.mp hxy
      have hb := blockIdx_mono hαβ
      rw [shift_ofOrd, shift_ofOrd]
      by_cases h1 : (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx α
      · rw [if_pos h1, if_pos (h1.trans hb)]
      · rw [if_neg h1]
        by_cases h2 : (((keys l S).card + 1 : ℕ) : Ordinal) ≤ blockIdx β
        · rw [if_pos h2]
          have := shift_ofOrd_le_γ l S γ hγ hS α
          rw [shift_ofOrd, if_neg h1] at this
          exact this
        · rw [if_neg h2]
          obtain ⟨n, hn, hnle⟩ := exists_nat_of_lt_card l S (not_le.mp h1)
          obtain ⟨m, hm, hmle⟩ := exists_nat_of_lt_card l S (not_le.mp h2)
          rw [hn, hm]
          rw [hn, hm] at hb
          have hnm : n ≤ m := by exact_mod_cast hb
          rcases Nat.eq_zero_or_pos n with rfl | hnpos
          · rw [Nat.cast_zero, keyAt_zero]; exact bot_le
          · obtain ⟨κ, hκ, hk, hbκ⟩ := keyAt_nat_eq_some l S hnpos hnle
            obtain ⟨κ', hκ', hk', hbκ'⟩ := keyAt_nat_eq_some l S (hnpos.trans_le hnm) hmle
            rw [hk, hk']
            simp only
            rw [ofOrd_le_ofOrd]
            rcases Nat.eq_or_lt_of_le hnm with heq | hlt
            · -- same block: same key, compare finite parts
              subst heq
              have : κ = κ' := blockOfKey_injOn l S hκ hκ' (hbκ.trans hbκ'.symm)
              subst this
              have hlp : limitPart α = limitPart β := by
                rw [limitPart_eq_mul_blockIdx, limitPart_eq_mul_blockIdx, hn, hm]
              exact decodeIn_mono l κ (finitePart_le_of_le_of_limitPart_eq hαβ hlp)
            · -- different blocks: `κ < κ'`, and the block of `κ` never reaches `κ'`
              have hκlt : κ < κ' := by
                by_contra hge
                have := blockOfKey_mono l S (not_lt.mp hge)
                omega
              rcases Nat.eq_zero_or_pos (finitePart κ) with h0 | hpos
              · exact (decodeIn_le l κ _).trans
                  ((key_add_le_next l S hκ hκ' hκlt h0).trans (decodeIn_ge l κ' _))
              · have e : decodeIn l κ (finitePart α) = κ := by
                  unfold decodeIn; rw [if_neg (by omega)]
                rw [e]; exact hκlt.le.trans (decodeIn_ge l κ' _)

/-! ### Clause 5 -/

theorem limitPart_mul (μ : Ordinal.{0}) : limitPart (Ordinal.omega0 * μ) = Ordinal.omega0 * μ := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel _ Ordinal.omega0_ne_zero]

theorem finitePart_mul_add' (μ : Ordinal.{0}) (m : ℕ) :
    finitePart (Ordinal.omega0 * μ + m) = m := by
  have := finitePart_limitPart_add_nat (Ordinal.omega0 * μ) m
  rwa [limitPart_mul] at this

theorem limitPart_mul_add' (μ : Ordinal.{0}) (m : ℕ) :
    limitPart (Ordinal.omega0 * μ + m) = Ordinal.omega0 * μ := by
  have := limitPart_limitPart_add_nat (Ordinal.omega0 * μ) m
  rwa [limitPart_mul] at this

theorem finitePart_mul (μ : Ordinal.{0}) : finitePart (Ordinal.omega0 * μ) = 0 := by
  rw [← limitPart_mul μ]
  exact finitePart_limitPart _

theorem key_finitePart {κ : Ordinal.{0}} (hκ : κ ∈ keys l S) : finitePart κ = 0 ∨ l < finitePart κ := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hκ
  exact finitePart_keyOrd l v

/-- **Clause 5 below the target grade, unguarded**: for `k ≤ l`, the decoder commutes with
visibility replacement at threshold `k`. -/
theorem shift_evr_of_le (hγ : SelfVis l γ) {k : ℕ} (hk : k ≤ l) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    shift l S γ (extVisibilityReplace x k i) = extVisibilityReplace (shift l S γ x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp [shift_bot]
  · rw [extVisibilityReplace_top, shift_top]
    exact (evr_eq_self_of_selfVis (hγ.mono hk) i).symm
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    split_ifs with h
    · exact (evr_eq_self_of_selfVis (hγ.mono hk) i).symm
    · rcases hkA : keyAt l S (blockIdx α) with _ | κ
      · simp
      · simp only
        rw [extVisibilityReplace_ofOrd, ofOrd_inj, finitePart_visibilityReplace]
        have hκ := keyAt_mem l S hkA
        rcases key_finitePart l S hκ with h0 | hl
        · -- an `ω`-block key: `κ = ω·μ`
          obtain ⟨μ, rfl⟩ : ∃ μ, κ = Ordinal.omega0 * μ :=
            ⟨blockIdx κ, by
              rw [← limitPart_eq_mul_blockIdx]
              conv_lhs => rw [← limitPart_add_finitePart κ]
              rw [h0]; simp⟩
          unfold decodeIn
          rw [if_pos (finitePart_mul μ), if_pos (finitePart_mul μ)]
          unfold visibilityReplace
          rw [finitePart_mul_add']
          by_cases hfp : finitePart α < k
          · rw [if_pos hfp, if_pos (lt_of_le_of_lt (min_le_left _ _) hfp)]
            unfold ordinalReplace
            rw [limitPart_mul_add', min_eq_left (hi.trans hk)]
          · rw [if_neg hfp, if_neg (by
              intro hlt
              apply hfp
              rcases min_choice (finitePart α) l with e | e
              · rw [e] at hlt; exact hlt
              · rw [e] at hlt; omega)]
        · -- a large key: constant block, finite part `> l ≥ k`
          unfold decodeIn
          rw [if_neg (by omega), if_neg (by omega)]
          unfold visibilityReplace
          rw [if_neg (by omega)]

/-- **Clause 5 above the target grade**: a `⊥` value stays `⊥` under replacement. -/
theorem shift_evr_of_bot (x : ExtOrd) (k i : ℕ) (h : shift l S γ x = ⊥) :
    shift l S γ (extVisibilityReplace x k i) = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp [shift_bot]
  · rw [extVisibilityReplace_top]; exact h
  · rw [extVisibilityReplace_ofOrd, shift_ofOrd, blockIdx_visibilityReplace]
    rw [shift_ofOrd] at h
    split_ifs at h ⊢ with h1
    · exact h
    · rcases hkA : keyAt l S (blockIdx α) with _ | κ
      · rfl
      · rw [hkA] at h
        simp only at h
        exact absurd h (ofOrd_ne_bot _)

/-- **The packaged transformation witness**: any row `G` transforms to its decoding capped at a
self-visible `ρ` up to grade `l`. -/
theorem transformsTo_of_shift {D : Type*} (grade : D → ℕ) (hγ : SelfVis l γ)
    (hS : ∀ v ∈ S, ofOrd v ≤ γ) (G : D → ExtOrd) {ρ : ExtOrd} (hρ : SelfVis l ρ) :
    TransformsTo grade G (fun d => min (shift l S γ (G d)) (if grade d ≤ l then ρ else ⊥)) := by
  refine ⟨fun k => if k ≤ l then ρ else ⊥, shift l S γ, ?_, ?_, shift_bot l S γ,
    shift_mono l S γ hγ hS, ?_, fun _ => rfl⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro n
    dsimp only
    split_ifs with h
    · exact (hρ.mono h).symm
    · simp
  · intro α k hle i hi
    by_cases hk : k ≤ l
    · exact shift_evr_of_le l S γ hγ hk α hi
    · dsimp only at hle
      rw [if_neg hk] at hle
      have h0 : shift l S γ α = ⊥ := le_bot_iff.mp hle
      rw [shift_evr_of_bot l S γ α k i h0, h0]
      simp

end Recoding

/-! ## Integration bridges: nothing here is a construction hypothesis -/

/-- A coded label is never `⊤`. -/
theorem ExtOrd.IsCodedLabel.ne_top {k : ℕ} {x : ExtOrd} (h : IsCodedLabel k x) : x ≠ ⊤ := by
  rcases h with rfl | ⟨i, j, -, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

/-- Cell grades of a scheme are positive (graded-plan membership). -/
theorem CellScheme.one_le_grade {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
    (d : Cell D) : 1 ≤ D.grade d :=
  D.grade_pos d

end VaughtConjecture.Knight
