/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteBlockBridge
public import VaughtConjecture.Knight.VisibilityAlgebra

/-! # The counted encoding on keyed values, and transport of finite certificates

The counted encoding `encT l S` (the counted code `code l S` of `Knight/CountedRecoding.lean`,
extended to every label by counting the keys of `S` at or below the label's key) is **strictly
monotone on keyed values** — `⊥`, `⊤`, and the ordinals whose key is a key of `S`, which include
every value of `S` and every replacement image of one at a threshold `≤ l` — preserves minima and
finite suprema there, and commutes with replacement at every threshold `≤ l`
(`encT_evr_of_le`).  Consequently a finite block-bridge certificate
(`Knight/FiniteBlockBridge.lean`)
for a target with a keyed table **transports field by field** to a certificate for the encoded
target (`FiniteBlockBridgeCertificate.encode`), so the coded locality holds whenever the uncoded
one has a keyed certificate (`transformsTo_encode`), with no normalization hypothesis.  The
collapses seen on foreign-keyed junk values (e.g. `ω·4` over `{ω·3 + 1}`) are exactly what
keyedness excludes.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Replacement below a self-visible bound -/

/-! ## The encoding on keyed values -/

section Keyed

variable (l : ℕ) (S : Finset Ordinal.{0})

/-- The counted code of an ordinal, on all ordinals (`code l S` of
`Knight/CountedRecoding.lean`). -/
noncomputable def encOrdK (v : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)

theorem encOrdK_eq_code (v : Ordinal.{0}) : encOrdK l S v = code l S v := rfl

/-- The counted encoding on labels: `⊥`, `⊤` fixed, ordinals coded. -/
noncomputable def encT : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some α) => ofOrd (encOrdK l S α)

theorem encT_bot : encT l S ⊥ = ⊥ := rfl
theorem encT_top : encT l S ⊤ = ⊤ := rfl
theorem encT_ofOrd (α : Ordinal.{0}) : encT l S (ofOrd α) = ofOrd (encOrdK l S α) := rfl

/-- **Keyed values**: `⊥`, `⊤`, and ordinals whose key is a key of `S`. -/
def Keyed (x : ExtOrd) : Prop := x = ⊥ ∨ x = ⊤ ∨ ∃ α, x = ofOrd α ∧ keyOrd l α ∈ keys l S

theorem keyed_bot : Keyed l S ⊥ := Or.inl rfl
theorem keyed_top : Keyed l S ⊤ := Or.inr (Or.inl rfl)
theorem keyed_of_mem {v : Ordinal.{0}} (hv : v ∈ S) : Keyed l S (ofOrd v) :=
  Or.inr (Or.inr ⟨v, rfl, keyOrd_mem_keys l S hv⟩)

/-- Replacement at a threshold `≤ l` preserves the key. -/
theorem keyOrd_visibilityReplace {k : ℕ} (hk : k ≤ l) (α : Ordinal.{0}) {i : ℕ} (hi : i ≤ k) :
    keyOrd l (visibilityReplace α k i) = keyOrd l α := by
  unfold visibilityReplace
  split_ifs with hfp
  · unfold ordinalReplace keyOrd
    rw [finitePart_limitPart_add_nat, limitPart_limitPart_add_nat, ite_eq_left (by omega),
      ite_eq_left (by omega)]
  · rfl

/-- Replacement images of keyed values at thresholds `≤ l` are keyed. -/
theorem keyed_evr {k : ℕ} (hk : k ≤ l) {x : ExtOrd} (hx : Keyed l S x) {i : ℕ} (hi : i ≤ k) :
    Keyed l S (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨α, rfl, hα⟩
  · exact keyed_bot l S
  · exact keyed_top l S
  · rw [extVisibilityReplace_ofOrd]
    exact Or.inr (Or.inr ⟨_, rfl, by rw [keyOrd_visibilityReplace l hk α hi]; exact hα⟩)

theorem keyed_min {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) : Keyed l S (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact hx
  · rw [min_eq_right h]; exact hy

/-- **The encoder's clause 5 at thresholds `≤ l`**, on all values. -/
theorem encOrdK_evr_of_le {k : ℕ} (hk : k ≤ l) (α : Ordinal.{0}) {i : ℕ} (hi : i ≤ k) :
    encOrdK l S (visibilityReplace α k i) = visibilityReplace (encOrdK l S α) k i := by
  unfold encOrdK
  have hkey := keyOrd_visibilityReplace l hk α hi
  unfold blockOf
  rw [hkey]
  unfold visibilityReplace
  by_cases hfp : finitePart α < k
  · rw [ite_eq_left hfp]
    unfold ordinalReplace
    rw [finitePart_limitPart_add_nat, finitePart_mul_add, ite_eq_left (by omega), limitPart_mul_add,
      min_eq_left (by omega : i ≤ l)]
  · rw [ite_eq_right hfp, finitePart_mul_add, ite_eq_right (by
      intro h
      have := min_le_left (finitePart α) l
      omega)]

theorem encT_evr_of_le {k : ℕ} (hk : k ≤ l) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    encT l S (extVisibilityReplace x k i) = extVisibilityReplace (encT l S x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rfl
  · rfl
  · rw [extVisibilityReplace_ofOrd, encT_ofOrd, encT_ofOrd, extVisibilityReplace_ofOrd,
      encOrdK_evr_of_le l S hk α hi]

theorem keyOrd_mono_of_le {v v' : Ordinal.{0}} (h : v ≤ v') : keyOrd l v ≤ keyOrd l v' := by
  unfold keyOrd
  split_ifs with h1 h2 h2
  · exact limitPart_mono h
  · exact (limitPart_le v).trans h
  · rcases lt_or_ge (limitPart v) (limitPart v') with hlt | hge
    · rw [← limitPart_add_finitePart v]
      exact limitPart_add_nat_le_of_lt hlt _
    · have heq : limitPart v = limitPart v' := le_antisymm (limitPart_mono h) hge
      have := finitePart_le_of_le_of_limitPart_eq h heq
      omega
  · exact h

/-- **Strict monotonicity of the encoding on keyed ordinals.** -/
theorem encOrdK_lt_keyed {v v' : Ordinal.{0}} (hv : keyOrd l v ∈ keys l S)
    (hv' : keyOrd l v' ∈ keys l S) (h : v < v') : encOrdK l S v < encOrdK l S v' := by
  unfold encOrdK
  have hb : blockOf l S v ≤ blockOf l S v' := blockOfKey_mono l S (keyOrd_mono_of_le l h.le)
  rcases Nat.lt_or_ge (blockOf l S v) (blockOf l S v') with hlt | hge
  · calc Ordinal.omega0 * (blockOf l S v : ℕ) + (min (finitePart v) l : ℕ)
        < Ordinal.omega0 * (blockOf l S v : ℕ) + Ordinal.omega0 :=
          (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
      _ = Ordinal.omega0 * ((blockOf l S v + 1 : ℕ) : Ordinal) := by
          rw [Nat.cast_succ, mul_add, mul_one]
      _ ≤ Ordinal.omega0 * (blockOf l S v' : ℕ) := by gcongr; exact_mod_cast hlt
      _ ≤ _ := le_self_add
  · have heq : blockOf l S v = blockOf l S v' := le_antisymm hb hge
    rw [heq]
    apply (add_lt_add_iff_left _).mpr
    have hk : keyOrd l v = keyOrd l v' := blockOfKey_injOn l S hv hv' heq
    unfold keyOrd at hk
    split_ifs at hk with h1 h2 h2
    · have hfp : finitePart v < finitePart v' := by
        by_contra hc
        exact absurd h (not_lt.mpr (le_of_finitePart_le hk.symm (not_lt.mp hc)))
      exact_mod_cast (show min (finitePart v) l < min (finitePart v') l by omega)
    · exfalso; have := congrArg finitePart hk; rw [finitePart_limitPart] at this; omega
    · exfalso; have := congrArg finitePart hk; rw [finitePart_limitPart] at this; omega
    · exact absurd hk h.ne

theorem encT_lt_keyed {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) (h : x < y) :
    encT l S x < encT l S y := by
  rcases hy with rfl | rfl | ⟨v', rfl, hv'⟩
  · exact absurd h not_lt_bot
  · rcases hx with rfl | rfl | ⟨v, rfl, hv⟩
    · rw [encT_bot, encT_top]; exact bot_lt_top
    · exact absurd h (lt_irrefl _)
    · rw [encT_ofOrd, encT_top]; exact ofOrd_lt_top _
  · rcases hx with rfl | rfl | ⟨v, rfl, hv⟩
    · rw [encT_bot, encT_ofOrd]; exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
    · exact absurd h (not_lt.mpr le_top)
    · rw [encT_ofOrd, encT_ofOrd]
      have hvv' : v < v' := by
        by_contra hc; exact absurd h (not_lt.mpr (ofOrd_le_ofOrd.mpr (not_lt.mp hc)))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (encOrdK_lt_keyed l S hv hv' hvv'))

theorem encT_le_keyed {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) (h : x ≤ y) :
    encT l S x ≤ encT l S y := by
  rcases h.lt_or_eq with hlt | rfl
  · exact (encT_lt_keyed l S hx hy hlt).le
  · exact le_rfl

theorem encT_le_iff_keyed {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) :
    encT l S x ≤ encT l S y ↔ x ≤ y := by
  refine ⟨fun h => ?_, encT_le_keyed l S hx hy⟩
  by_contra hc
  exact absurd h (not_le.mpr (encT_lt_keyed l S hy hx (not_le.mp hc)))

theorem encT_min_keyed {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) :
    encT l S (min x y) = min (encT l S x) (encT l S y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (encT_le_keyed l S hx hy h)]
  · rw [min_eq_right h, min_eq_right (encT_le_keyed l S hy hx h)]

theorem encT_eq_bot_iff (x : ExtOrd) : encT l S x = ⊥ ↔ x = ⊥ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp [encT_bot]
  · simp [encT_top]
  · rw [encT_ofOrd]; simp

/-- The encoding of a finite supremum of keyed values is the supremum of the encodings. -/
theorem encT_finsetSup {ι : Type*} (s : Finset ι) (f : ι → ExtOrd) (hf : ∀ i ∈ s, Keyed l S (f i)) :
    encT l S (s.sup f) = s.sup fun i => encT l S (f i) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp [encT_bot]
  · obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup s hne f
    apply le_antisymm
    · rw [hsup]; exact Finset.le_sup (f := fun i => encT l S (f i)) hi₀
    · apply Finset.sup_le
      intro i hi
      exact encT_le_keyed l S (hf i hi) (hsup ▸ hf i₀ hi₀) (hsup ▸ Finset.le_sup (f := f) hi)

end Keyed

/-! ## Transport of certificates -/

section Transport

variable (l : ℕ) (S : Finset Ordinal.{0}) {D : Type*} [Finite D] (grade : D → ℕ)
  (source target : D → ExtOrd)

theorem finiteTargetSuppressor_eq (k : ℕ) :
    finiteTargetSuppressor grade target k =
      (@Finset.univ D (Fintype.ofFinite D)).sup fun d => if k ≤ grade d then target d else ⊥ := rfl

/-- The canonical suppressor of the encoded target is the encoded canonical suppressor. -/
theorem finiteTargetSuppressor_encode (ht : ∀ d, Keyed l S (target d)) (k : ℕ) :
    finiteTargetSuppressor grade (fun d => encT l S (target d)) k =
      encT l S (finiteTargetSuppressor grade target k) := by
  classical
  rw [finiteTargetSuppressor_eq, finiteTargetSuppressor_eq]
  rw [encT_finsetSup l S _ _ (fun d _ => by
    split_ifs
    · exact ht d
    · exact keyed_bot l S)]
  congr 1
  funext d
  split_ifs <;> rfl

theorem finiteTargetSuppressor_keyed (ht : ∀ d, Keyed l S (target d)) (k : ℕ) :
    Keyed l S (finiteTargetSuppressor grade target k) := by
  classical
  rw [finiteTargetSuppressor_eq]
  rcases Finset.eq_empty_or_nonempty (@Finset.univ D (Fintype.ofFinite D)) with he | hne
  · rw [he]; exact keyed_bot l S
  · obtain ⟨d, -, hsup⟩ := Finset.exists_mem_eq_sup _ hne
      fun d => if k ≤ grade d then target d else ⊥
    rw [hsup]
    split_ifs
    · exact ht d
    · exact keyed_bot l S

/-- The encoded lower envelope is the lower envelope of the encoded table. -/
theorem finiteLowerEnvelope_encode (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hs : ∀ y ∈ s, Keyed l S (table y)) (x : ExtOrd) :
    finiteLowerEnvelope s (fun y => encT l S (table y)) x =
      encT l S (finiteLowerEnvelope s table x) := by
  unfold finiteLowerEnvelope
  rw [encT_finsetSup l S s _ (fun y hy => by
    split_ifs
    · exact hs y hy
    · exact keyed_bot l S)]
  congr 1
  funext y
  split_ifs <;> rfl

variable {l S grade source target}

/-- **Transport of a keyed certificate along the counted encoding**, with the coding grade at
least every grade. -/
noncomputable def FiniteBlockBridgeCertificate.encode
    (C : FiniteBlockBridgeCertificate grade source target)
    (hl : ∀ d, grade d ≤ l) (ht : ∀ d, Keyed l S (target d))
    (hkeyed : ∀ y ∈ C.tableDomain, Keyed l S (C.table y)) :
    FiniteBlockBridgeCertificate grade source (fun d => encT l S (target d)) where
  tableDomain := C.tableDomain
  table := fun y => encT l S (C.table y)
  bottom := fun y hy hb => by rw [C.bottom y hy hb, encT_bot]
  monotone := fun a ha b hb hab =>
    encT_le_keyed l S (hkeyed a ha) (hkeyed b hb) (C.monotone a ha b hb hab)
  orbit := by
    intro x hx k i hi hact
    rw [finiteTargetSuppressor_encode l S grade target ht,
      encT_le_iff_keyed l S (hkeyed x hx)
        (finiteTargetSuppressor_keyed l S grade target ht k)] at hact
    dsimp only
    rcases C.orbit x hx k i hi hact with hbot | ⟨hmem, hcomm⟩
    · left; rw [hbot, encT_bot]
    · -- the threshold is at most `l`: above every grade the suppressor is `⊥`, forcing `⊥`
      by_cases hk : k ≤ l
      · right
        exact ⟨hmem, by rw [hcomm, encT_evr_of_le l S hk _ hi]⟩
      · left
        have := finiteTargetSuppressor_eq_bot_of_lt grade target hl (Nat.lt_of_not_ge hk)
        rw [this] at hact
        rw [le_bot_iff.mp hact, encT_bot]
  bridge := by
    intro x k hact i hi z hz hzx
    rw [finiteLowerEnvelope_encode l S C.tableDomain C.table hkeyed,
      finiteTargetSuppressor_encode l S grade target ht] at hact
    -- the envelope is keyed: a supremum of keyed values
    have henv : Keyed l S (finiteLowerEnvelope C.tableDomain C.table x) := by
      classical
      unfold finiteLowerEnvelope
      rcases Finset.eq_empty_or_nonempty C.tableDomain with he | hne
      · rw [he]; exact keyed_bot l S
      · obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup _ hne
          fun y => if y ≤ x then C.table y else ⊥
        rw [hsup]
        split_ifs
        · exact hkeyed y hy
        · exact keyed_bot l S
    rw [encT_le_iff_keyed l S henv (finiteTargetSuppressor_keyed l S grade target ht k)] at hact
    dsimp only
    rcases C.bridge x k hact i hi z hz hzx with hbot | ⟨y, hy, hyx, hzy⟩
    · left; rw [hbot, encT_bot]
    · right
      refine ⟨y, hy, hyx, ?_⟩
      by_cases hk : k ≤ l
      · rw [← encT_evr_of_le l S hk _ hi]
        exact encT_le_keyed l S (hkeyed z hz) (keyed_evr l S hk (hkeyed y hy) hi) hzy
      · -- above every grade the suppressor is `⊥`, so the envelope, hence the table at `z`, is `⊥`
        have := finiteTargetSuppressor_eq_bot_of_lt grade target hl (Nat.lt_of_not_ge hk)
        rw [this] at hact
        have hz0 : C.table z = ⊥ := by
          have h1 : C.table z ≤ finiteLowerEnvelope C.tableDomain C.table x := by
            -- `z ≤ x ⊔⁺ₖ i` does not give `z ≤ x`; use the bridge's own conclusion instead
            calc C.table z ≤ extVisibilityReplace (C.table y) k i := hzy
              _ = ⊥ := by
                have hy0 : C.table y ≤ finiteLowerEnvelope C.tableDomain C.table x := by
                  have hterm := Finset.le_sup (s := C.tableDomain)
                    (f := fun w => if w ≤ x then C.table w else ⊥) hy
                  simpa only [finiteLowerEnvelope, hyx, ite_true] using hterm
                rw [le_bot_iff.mp (hy0.trans hact), extVisibilityReplace_bot]
              _ ≤ _ := bot_le
          exact le_bot_iff.mp (h1.trans hact)
        rw [hz0, encT_bot]; exact bot_le
  source_mem := C.source_mem
  realizes := fun d => by
    rw [finiteTargetSuppressor_encode l S grade target ht, ← encT_min_keyed l S
      (hkeyed _ (C.source_mem d)) (finiteTargetSuppressor_keyed l S grade target ht _),
      ← C.realizes d]

/-- **The coded closure from a keyed certificate**: if the uncoded locality has a keyed finite
certificate and the coded target is orderly, the coded locality holds. -/
theorem transformsTo_encode (C : FiniteBlockBridgeCertificate grade source target)
    (hl : ∀ d, grade d ≤ l) (ht : ∀ d, Keyed l S (target d))
    (hkeyed : ∀ y ∈ C.tableDomain, Keyed l S (C.table y))
    (hord : IsOrderly grade fun d => encT l S (target d)) :
    TransformsTo grade source fun d => encT l S (target d) :=
  (C.encode hl ht hkeyed).transformsTo hord

omit [Finite D] in
/-- Orderliness of the coded target follows from orderliness of the target, since the encoding
commutes with the self-visibility replacement at grades `≤ l`. -/
theorem isOrderly_encode (hl : ∀ d, grade d ≤ l) (hord : IsOrderly grade target) :
    IsOrderly grade fun d => encT l S (target d) := by
  intro d
  show encT l S (target d) = extVisibilityReplace (encT l S (target d)) (grade d) (grade d)
  rw [← encT_evr_of_le l S (hl d) _ le_rfl, ← hord d]

end Transport



open Transform Value ExtOrd

end VaughtConjecture.Knight
