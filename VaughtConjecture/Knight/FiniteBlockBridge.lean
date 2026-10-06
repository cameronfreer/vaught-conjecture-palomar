/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

/-! # The finite block-bridge kernel: faithful locality from a finite shifter table

**What this proves.**  A faithful transformation `TransformsTo grade source target` (Def. 2.3.9,
unguarded clause 5) between finite rows can be certified by **finite data**: a table on a finite
domain of labels, extended to a total shifter by its lower envelope.  This is the repaired finite
lower-envelope machinery of the sibling Knight-VC development (its `PaperFinitePartialShifter
BlockBridge`/`WeakOrbit` files), ported to V-C's `TransformsTo`; the printed lower-envelope proof
of paper Lemma 2.3.10 is refuted there by a block-gap example, and the block bridge below is the
exact repair.

* `finiteTargetSuppressor` — the **canonical suppressor** of a finite target, `g k := ⨆ {target d
  | k ≤ grade d}`; antitone, self-visible for orderly targets, and **lossless**
  (`finiteTargetShifterData_nonempty_of_transformsTo`): any witness can be renormalized to it,
  keeping its shifter.
* `finiteLowerEnvelope` — the total extension of a finite table: monotone, bottom-preserving,
  and exact on a monotone table's domain.
* `FiniteShifterWeakOrbit` — the **bottom-aware orbit law**: at an active table point, either the
  value is `⊥` (contributing nothing to any envelope) or its replacement is in the domain with the
  commuted value.  For the canonical suppressor every obligation above the maximal grade closes
  through the bottom alternative (`FiniteShifterWeakOrbit.of_bounded`), so a producer solves the
  orbit law at the finitely many thresholds `≤ K` only.
* `FiniteShifterBlockBridge` — the **block-gap bridge**: every prescribed source visible below a
  replaced input is bottom-valued or controlled by a source below the original input.  It is
  the missing reverse inequality of the envelope's commutation and stays unrestricted.
* `FiniteBlockBridgeCertificate.transformsTo` — the cashout: table + bottom + monotonicity +
  weak orbit + bridge + realization of the rows gives `TransformsTo`.

No normalization of the ambient witness's range, no global range restriction, and no
transitivity of transformations enter.  Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Value ExtOrd
open Transform

noncomputable section

/-- Greatest target label at a cell of grade at least `k`. -/
def finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (k : ℕ) : ExtOrd := by
  letI := Fintype.ofFinite D
  exact Finset.univ.sup fun d => if k ≤ grade d then target d else ⊥

theorem finiteTargetSuppressor_antitone
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) :
    ∀ n m, n < m → finiteTargetSuppressor grade target m ≤
      finiteTargetSuppressor grade target n := by
  classical
  letI := Fintype.ofFinite D
  intro n m hnm
  apply Finset.sup_le
  intro d hd
  by_cases hm : m ≤ grade d
  · have hn : n ≤ grade d := (Nat.le_of_lt hnm).trans hm
    have hterm := Finset.le_sup
      (s := (Finset.univ : Finset D))
      (f := fun e => if n ≤ grade e then target e else ⊥) hd
    simpa only [finiteTargetSuppressor, hm, hn, if_true] using hterm
  · simp only [finiteTargetSuppressor, hm, if_false]
    exact bot_le

private theorem max_selfVis {a b : ExtOrd} {k : ℕ}
    (ha : a = extVisibilityReplace a k k)
    (hb : b = extVisibilityReplace b k k) :
    max a b = extVisibilityReplace (max a b) k k := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact hb
  · rw [max_eq_left hba]
    exact ha

private theorem finset_sup_selfVis
    {A : Type*} (s : Finset A) (f : A → ExtOrd) (k : ℕ)
    (hf : ∀ a ∈ s, f a = extVisibilityReplace (f a) k k) :
    s.sup f = extVisibilityReplace (s.sup f) k k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sup_insert]
      apply max_selfVis
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)

theorem finiteTargetSuppressor_selfVis
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd)
    (hTarget : IsOrderly grade target) :
    ∀ k, finiteTargetSuppressor grade target k =
      extVisibilityReplace (finiteTargetSuppressor grade target k) k k := by
  classical
  letI := Fintype.ofFinite D
  intro k
  apply finset_sup_selfVis
  intro d _hd
  by_cases hk : k ≤ grade d
  · simp only [hk, if_true]
    have hd : extVisibilityReplace (target d) (grade d) (grade d) = target d :=
      (hTarget d).symm
    exact (selfVis_mono hd hk).symm
  · simp only [hk, if_false, extVisibilityReplace]

theorem target_le_finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (d : D) :
    target d ≤ finiteTargetSuppressor grade target (grade d) := by
  classical
  letI := Fintype.ofFinite D
  have hterm := Finset.le_sup
    (s := (Finset.univ : Finset D))
    (f := fun e => if grade d ≤ grade e then target e else ⊥)
    (Finset.mem_univ d)
  simpa only [finiteTargetSuppressor, le_refl, if_true] using hterm

theorem finiteTargetSuppressor_le
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd)
    (g : ℕ → ExtOrd)
    (hg : ∀ n m, n < m → g m ≤ g n)
    (hTarget : ∀ d, target d ≤ g (grade d)) (k : ℕ) :
    finiteTargetSuppressor grade target k ≤ g k := by
  classical
  letI := Fintype.ofFinite D
  apply Finset.sup_le
  intro d _hd
  by_cases hk : k ≤ grade d
  · have hgate : g (grade d) ≤ g k := by
      rcases eq_or_lt_of_le hk with hEq | hLt
      · exact hEq ▸ le_rfl
      · exact hg k (grade d) hLt
    simpa only [finiteTargetSuppressor, hk, if_true] using
      (hTarget d).trans hgate
  · simp only [finiteTargetSuppressor, hk, if_false]
    exact bot_le

/-- Once the finite target is fixed, its suppressor can be chosen
canonically and only the shifter remains. -/
structure FiniteTargetShifterData
    {D : Type*} [Finite D]
    (grade : D → ℕ) (source target : D → ExtOrd) where
  shifter : ExtOrd → ExtOrd
  bot : shifter ⊥ = ⊥
  mono : Monotone shifter
  commutes : ∀ x k, shifter x ≤ finiteTargetSuppressor grade target k →
    ∀ i, i ≤ k → shifter (extVisibilityReplace x k i) =
      extVisibilityReplace (shifter x) k i
  realizes : ∀ d, target d = min (shifter (source d))
    (finiteTargetSuppressor grade target (grade d))

theorem FiniteTargetShifterData.transformsTo
    {D : Type*} [Finite D]
    {grade : D → ℕ} {source target : D → ExtOrd}
    (S : FiniteTargetShifterData grade source target)
    (hTarget : IsOrderly grade target) :
    TransformsTo grade source target := by
  exact ⟨finiteTargetSuppressor grade target, S.shifter,
    finiteTargetSuppressor_antitone grade target,
    finiteTargetSuppressor_selfVis grade target hTarget,
    S.bot, S.mono, S.commutes, S.realizes⟩

/-- Canonical-suppressor normalization is lossless for a finite target. -/
theorem finiteTargetShifterData_nonempty_of_transformsTo
    {D : Type*} [Finite D]
    {grade : D → ℕ} {source target : D → ExtOrd}
    (h : TransformsTo grade source target) :
    Nonempty (FiniteTargetShifterData grade source target) := by
  classical
  obtain ⟨g, σ, hgDec, _hgSelf, hσBot, hσMono, hσComm, hEq⟩ := h
  have hTargetGate : ∀ d, target d ≤ g (grade d) := by
    intro d
    rw [hEq d]
    exact min_le_right _ _
  have hCanonical : ∀ k, finiteTargetSuppressor grade target k ≤ g k :=
    finiteTargetSuppressor_le grade target g hgDec hTargetGate
  refine ⟨{
    shifter := σ
    bot := hσBot
    mono := hσMono
    commutes := ?_
    realizes := ?_ }⟩
  · intro x k hActive i hi
    exact hσComm x k (hActive.trans (hCanonical k)) i hi
  · intro d
    have hTargetShifter : target d ≤ σ (source d) := by
      rw [hEq d]
      exact min_le_left _ _
    apply le_antisymm
    · exact le_min hTargetShifter (target_le_finiteTargetSuppressor grade target d)
    · calc
        min (σ (source d)) (finiteTargetSuppressor grade target (grade d)) ≤
            min (σ (source d)) (g (grade d)) :=
          min_le_min le_rfl (hCanonical (grade d))
        _ = target d := (hEq d).symm

private theorem isNonSuccessor_limitPart (δ : Ordinal) :
    IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Order.isSuccLimit_iff]
    refine ⟨by simpa using h0, (Ordinal.isSuccPrelimit_iff_omega0_dvd).2 ?_⟩
    exact ⟨δ / Ordinal.omega0, rfl⟩

private theorem add_omega0_le_of_nonsucc
    {μ ν : Ordinal} (hν : IsNonSuccessor ν) (hμν : μ < ν) :
    μ + Ordinal.omega0 ≤ ν := by
  rcases hν with rfl | hLimit
  · simp at hμν
  · have hFinite : ∀ k : ℕ, μ + (k : Ordinal) < ν := by
      intro k
      induction k with
      | zero => simpa using hμν
      | succ k ih =>
          have hStep : μ + ((k + 1 : ℕ) : Ordinal) =
              Order.succ (μ + (k : Ordinal)) := by
            push_cast
            rw [← add_assoc, ← Order.succ_eq_add_one]
          rw [hStep]
          exact hLimit.succ_lt ih
    rw [Ordinal.add_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0]
    intro b hb
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb
    exact (hFinite k).le

/-- Visibility replacement is monotone in its label argument. -/
theorem extVisibilityReplace_mono (k i : ℕ) (hi : i ≤ k) :
    Monotone (fun x : ExtOrd => extVisibilityReplace x k i) := by
  have hOrd : Monotone (fun δ : Ordinal => visibilityReplace δ k i) := by
    intro γ δ hγδ
    by_cases hγ : finitePart γ < k
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_true, ordinalReplace]
        exact add_le_add (limitPart_mono hγδ) le_rfl
      · calc
          visibilityReplace γ k i ≤ δ :=
            visReplace_le_of_le_selfVis hγδ (Nat.not_lt.mp hδ) hi
          _ = visibilityReplace δ k i := by
            simp only [visibilityReplace, hδ, if_false]
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_false, if_true, ordinalReplace]
        have hLimitLe : limitPart γ ≤ limitPart δ := limitPart_mono hγδ
        have hLimitNe : limitPart γ ≠ limitPart δ := by
          intro hEq
          have hFiniteLe : finitePart γ ≤ finitePart δ := by
            have hDecomp : limitPart γ + (finitePart γ : Ordinal) ≤
                limitPart γ + (finitePart δ : Ordinal) := by
              calc
                limitPart γ + (finitePart γ : Ordinal) = γ := decomposition γ
                _ ≤ δ := hγδ
                _ = limitPart δ + (finitePart δ : Ordinal) := (decomposition δ).symm
                _ = limitPart γ + (finitePart δ : Ordinal) := by rw [hEq]
            exact_mod_cast (add_le_add_iff_left (limitPart γ)).mp hDecomp
          exact hγ (lt_of_le_of_lt hFiniteLe hδ)
        have hLimitLt : limitPart γ < limitPart δ :=
          lt_of_le_of_ne hLimitLe hLimitNe
        have hBlockSep : limitPart γ + Ordinal.omega0 ≤ limitPart δ :=
          add_omega0_le_of_nonsucc (isNonSuccessor_limitPart δ) hLimitLt
        have hGammaLtBlock : γ < limitPart γ + Ordinal.omega0 := by
          calc
            γ = limitPart γ + (finitePart γ : Ordinal) := (decomposition γ).symm
            _ < limitPart γ + Ordinal.omega0 :=
              (add_lt_add_iff_left (limitPart γ)).2
                (Ordinal.natCast_lt_omega0 (finitePart γ))
        exact hGammaLtBlock.le.trans (hBlockSep.trans le_self_add)
      · simp only [visibilityReplace, hγ, hδ, if_false]
        exact hγδ
  intro x y hxy
  match x, y with
  | ⊥, _ => exact bot_le
  | some ⊤, ⊥ =>
      exact (not_le_of_gt (WithBot.bot_lt_coe (⊤ : WithTop Ordinal)) hxy).elim
  | some ⊤, some ⊤ => exact le_rfl
  | some ⊤, some (some δ) =>
      exact (not_le_of_gt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top δ)) hxy).elim
  | some (some γ), ⊥ =>
      exact (not_le_of_gt (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot γ)) hxy).elim
  | some (some γ), some ⊤ => exact le_top
  | some (some γ), some (some δ) =>
      exact WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <| hOrd <|
        WithTop.coe_le_coe.mp <| WithBot.coe_le_coe.mp hxy

/-- Greatest prescribed output at an input below `x`. -/
def finiteLowerEnvelope
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  s.sup fun y => if y ≤ x then table y else ⊥

theorem finiteLowerEnvelope_mono
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) :
    Monotone (finiteLowerEnvelope s table) := by
  intro x y hxy
  apply Finset.sup_le
  intro a ha
  by_cases hax : a ≤ x
  · have hay : a ≤ y := hax.trans hxy
    have hterm := Finset.le_sup
      (s := s) (f := fun z => if z ≤ y then table z else ⊥) ha
    simpa only [finiteLowerEnvelope, hax, hay, if_true] using hterm
  · simp only [finiteLowerEnvelope, hax, if_false]
    exact bot_le

theorem finiteLowerEnvelope_bot
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hBot : ∀ y ∈ s, y = ⊥ → table y = ⊥) :
    finiteLowerEnvelope s table ⊥ = ⊥ := by
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    by_cases hyBot : y ≤ (⊥ : ExtOrd)
    · have hyEq : y = ⊥ := le_bot_iff.mp hyBot
      simp only [finiteLowerEnvelope, hyBot, if_true, hBot y hy hyEq]
      exact le_rfl
    · simp only [finiteLowerEnvelope, hyBot, if_false]
      exact le_rfl
  · exact bot_le

theorem finiteLowerEnvelope_source
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hMono : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → table a ≤ table b)
    {x : ExtOrd} (hx : x ∈ s) :
    finiteLowerEnvelope s table x = table x := by
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    by_cases hyx : y ≤ x
    · simpa only [finiteLowerEnvelope, hyx, if_true] using hMono y hy x hx hyx
    · simp only [finiteLowerEnvelope, hyx, if_false]
      exact bot_le
  · have hterm := Finset.le_sup
      (s := s) (f := fun y => if y ≤ x then table y else ⊥) hx
    simpa only [finiteLowerEnvelope, le_refl, if_true] using hterm

/-- **The bottom-aware orbit law**: at an active table point, either the value is `⊥`, or its
replacement is in the domain with the commuted value. -/
def FiniteShifterWeakOrbit
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x ∈ s, ∀ k i, i ≤ k → table x ≤ g k →
    table x = ⊥ ∨
      (extVisibilityReplace x k i ∈ s ∧
        table (extVisibilityReplace x k i) = extVisibilityReplace (table x) k i)

/-- Every active point visible below a replaced input is controlled from
an old point below the original input.  This is the exact block-gap repair. -/
def FiniteShifterBlockBridge
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x k, finiteLowerEnvelope s table x ≤ g k →
    ∀ i, i ≤ k → ∀ z ∈ s,
      z ≤ extVisibilityReplace x k i →
        table z = ⊥ ∨
          ∃ y ∈ s, y ≤ x ∧
            table z ≤ extVisibilityReplace (table y) k i

theorem finiteLowerEnvelope_visibility_le
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hOrbit : FiniteShifterWeakOrbit s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    extVisibilityReplace (finiteLowerEnvelope s table x) k i ≤
      finiteLowerEnvelope s table (extVisibilityReplace x k i) := by
  unfold finiteLowerEnvelope
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder
    (fun z : ExtOrd => extVisibilityReplace z k i)
    (extVisibilityReplace_mono k i hi) rfl]
  apply Finset.sup_le
  intro y hy
  by_cases hyx : y ≤ x
  · have hfy : table y ≤ finiteLowerEnvelope s table x := by
      have hterm := Finset.le_sup
        (s := s) (f := fun z => if z ≤ x then table z else ⊥) hy
      simpa only [finiteLowerEnvelope, hyx, if_true] using hterm
    simp only [Function.comp_apply, hyx, if_true]
    change extVisibilityReplace (table y) k i ≤
      s.sup (fun z => if z ≤ extVisibilityReplace x k i then table z else ⊥)
    rcases hOrbit y hy k i hi (hfy.trans hActive) with hbot | ⟨hmem, hcomm⟩
    · rw [hbot, extVisibilityReplace_bot]
      exact bot_le
    · have hinput : extVisibilityReplace y k i ≤ extVisibilityReplace x k i :=
        extVisibilityReplace_mono k i hi hyx
      have hterm := Finset.le_sup
        (s := s)
        (f := fun z => if z ≤ extVisibilityReplace x k i then table z else ⊥) hmem
      rw [← hcomm]
      simpa only [hinput, if_true] using hterm
  · simp only [Function.comp_apply, hyx, if_false]
    exact bot_le

theorem finiteLowerEnvelope_le_visibility
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hBridge : FiniteShifterBlockBridge s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    finiteLowerEnvelope s table (extVisibilityReplace x k i) ≤
      extVisibilityReplace (finiteLowerEnvelope s table x) k i := by
  unfold finiteLowerEnvelope
  apply Finset.sup_le
  intro z hz
  by_cases hzNew : z ≤ extVisibilityReplace x k i
  · rcases hBridge x k hActive i hi z hz hzNew with
      hzBot | ⟨y, hy, hyx, hzy⟩
    · simp only [hzNew, if_true, hzBot]
      exact bot_le
    · have hterm := Finset.le_sup
        (s := s) (f := fun w => if w ≤ x then table w else ⊥) hy
      have hfy : table y ≤ s.sup (fun w => if w ≤ x then table w else ⊥) := by
        simpa only [hyx, if_true] using hterm
      simp only [hzNew, if_true]
      exact hzy.trans (extVisibilityReplace_mono k i hi hfy)
  · simp only [hzNew, if_false]
    exact bot_le

/-- **The envelope commutes with replacement at active inputs**, from the weak orbit law and
the bridge. -/
theorem finiteLowerEnvelope_visibility_eq
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hOrbit : FiniteShifterWeakOrbit s table g)
    (hBridge : FiniteShifterBlockBridge s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    finiteLowerEnvelope s table (extVisibilityReplace x k i) =
      extVisibilityReplace (finiteLowerEnvelope s table x) k i := by
  apply le_antisymm
  · exact finiteLowerEnvelope_le_visibility s table g hBridge x k i hi hActive
  · exact finiteLowerEnvelope_visibility_le s table g hOrbit x k i hi hActive

/-- The canonical suppressor vanishes above every grade. -/
theorem finiteTargetSuppressor_eq_bot_of_lt
    {D : Type*} [Finite D] (grade : D → ℕ) (target : D → ExtOrd) {K k : ℕ}
    (hK : ∀ d, grade d ≤ K) (hk : K < k) : finiteTargetSuppressor grade target k = ⊥ := by
  letI := Fintype.ofFinite D
  apply le_bot_iff.mp
  apply Finset.sup_le
  intro d _
  rw [if_neg (by have := hK d; omega)]

/-- **Only the thresholds up to the maximal grade need solving**: for the canonical suppressor,
the weak orbit law at thresholds `≤ K` gives it at every threshold, the rest closing through the
bottom alternative. -/
theorem FiniteShifterWeakOrbit.of_bounded
    {D : Type*} [Finite D] (grade : D → ℕ) (target : D → ExtOrd) {K : ℕ}
    (hK : ∀ d, grade d ≤ K)
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hbounded : ∀ x ∈ s, ∀ k i, k ≤ K → i ≤ k → table x ≤ finiteTargetSuppressor grade target k →
      table x = ⊥ ∨
        (extVisibilityReplace x k i ∈ s ∧
          table (extVisibilityReplace x k i) = extVisibilityReplace (table x) k i)) :
    FiniteShifterWeakOrbit s table (finiteTargetSuppressor grade target) := by
  intro x hx k i hi hActive
  by_cases hk : k ≤ K
  · exact hbounded x hx k i hk hi hActive
  · left
    rw [finiteTargetSuppressor_eq_bot_of_lt grade target hK (Nat.lt_of_not_ge hk)] at hActive
    exact le_bot_iff.mp hActive

/-- **A finite certificate for a faithful transformation.**  It has no global range-normalization
field: the orbit law is bottom-aware, and the bridge is the only condition on inputs outside the
domain. -/
structure FiniteBlockBridgeCertificate
    {D : Type*} [Finite D]
    (grade : D → ℕ) (source target : D → ExtOrd) where
  tableDomain : Finset ExtOrd
  table : ExtOrd → ExtOrd
  bottom : ∀ y ∈ tableDomain, y = ⊥ → table y = ⊥
  monotone : ∀ a ∈ tableDomain, ∀ b ∈ tableDomain,
    a ≤ b → table a ≤ table b
  orbit : FiniteShifterWeakOrbit tableDomain table
    (finiteTargetSuppressor grade target)
  bridge : FiniteShifterBlockBridge tableDomain table
    (finiteTargetSuppressor grade target)
  source_mem : ∀ d, source d ∈ tableDomain
  realizes : ∀ d, target d = min (table (source d))
    (finiteTargetSuppressor grade target (grade d))

/-- **The cashout**: a certificate for an orderly target is a faithful transformation, witnessed
by the canonical suppressor and the lower envelope of the table. -/
theorem FiniteBlockBridgeCertificate.transformsTo
    {D : Type*} [Finite D]
    {grade : D → ℕ} {source target : D → ExtOrd}
    (C : FiniteBlockBridgeCertificate grade source target)
    (hTarget : IsOrderly grade target) :
    TransformsTo grade source target := by
  refine ⟨finiteTargetSuppressor grade target,
    finiteLowerEnvelope C.tableDomain C.table,
    finiteTargetSuppressor_antitone grade target,
    finiteTargetSuppressor_selfVis grade target hTarget,
    finiteLowerEnvelope_bot C.tableDomain C.table C.bottom,
    finiteLowerEnvelope_mono C.tableDomain C.table, ?_, ?_⟩
  · intro x k hActive i hi
    exact finiteLowerEnvelope_visibility_eq
      C.tableDomain C.table (finiteTargetSuppressor grade target)
      C.orbit C.bridge x k i hi hActive
  · intro d
    rw [finiteLowerEnvelope_source C.tableDomain C.table C.monotone (C.source_mem d)]
    exact C.realizes d

end

end VaughtConjecture.Knight
