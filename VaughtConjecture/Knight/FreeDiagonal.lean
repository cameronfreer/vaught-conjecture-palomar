/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ControllerPrefixFamily
public import VaughtConjecture.Knight.WitnessAlgebra

/-! # A free diagonal beyond a finite source inventory

Normalize an actual maximal-grade controller locality to its capped shifter, then take
its maximum with a bottom-to-high step at a fresh limit block. This retains all old
capped targets literally and assigns any larger self-visible value to the new diagonal.
The old cap may be bottom; the new value may be top. Clause 5 holds at every threshold.

The new source is chosen from the finite coded source inventory before the labelling,
locality witness, or desired high value. This is a row extension only: it establishes
neither joint consistency with other controller rows nor availability or bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace FreeDiagonal

/-- Normalized witnesses are closed under pointwise minimum as well as maximum.
The normalization is essential to this proof: below `K` both guards are automatic;
above `K` a bottom output of either factor propagates through replacement. -/
theorem min_witness {σ τ : ExtOrd → ExtOrd} {K : ℕ}
    (hσ : Witness (gTop K) σ) (hτ : Witness (gTop K) τ) :
    Witness (gTop K) (fun x => min (σ x) (τ x)) where
  anti := hσ.anti
  vis := hσ.vis
  bot := by rw [hσ.bot, hτ.bot, min_self]
  mono := fun _ _ h => min_le_min (hσ.mono h) (hτ.mono h)
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ K
    · have hm : Monotone (fun a => extVisibilityReplace a k i) := fun _ _ h => evr_mono h hi
      rw [hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
        hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi, hm.map_min]
    · rw [gTop_of_gt (not_le.mp hk)] at hact
      have hzero := le_bot_iff.mp hact
      rw [hzero, extVisibilityReplace_bot]
      rcases le_total (σ x) (τ x) with h | h
      · have hσb : σ x = ⊥ := by rwa [min_eq_left h] at hzero
        rw [hσ.clause5 x k (by rw [hσb]; exact bot_le) i hi, hσb,
          extVisibilityReplace_bot, min_bot_left]
      · have hτb : τ x = ⊥ := by rwa [min_eq_right h] at hzero
        rw [hτ.clause5 x k (by rw [hτb]; exact bot_le) i hi, hτb,
          extVisibilityReplace_bot, min_bot_right]

/-- A small proof-producing grammar for witness synthesis. There is deliberately no
composition constructor: composition of faithful transformations is not assumed. -/
inductive Circuit (ι : Type*) where
  | atom : ι → Circuit ι
  | meet : Circuit ι → Circuit ι → Circuit ι
  | join : Circuit ι → Circuit ι → Circuit ι

/-- Interpret a circuit as a pointwise minimum/maximum formula in the chosen shifters. -/
noncomputable def Circuit.eval {ι : Type*} (f : ι → ExtOrd → ExtOrd) :
    Circuit ι → ExtOrd → ExtOrd
  | .atom i => f i
  | .meet a b => fun x => min (a.eval f x) (b.eval f x)
  | .join a b => fun x => max (a.eval f x) (b.eval f x)

/-- Every circuit of normalized faithful atoms is faithful, at every threshold.
An external search need only supply the expression; the atoms and this theorem are
checked in Lean. Row readback and joint controller obligations remain separate. -/
theorem Circuit.witness {ι : Type*} {K : ℕ} {f : ι → ExtOrd → ExtOrd}
    (hf : ∀ i, Witness (gTop K) (f i)) (e : Circuit ι) :
    Witness (gTop K) (e.eval f) := by
  induction e with
  | atom i => exact hf i
  | meet _ _ ha hb => exact min_witness ha hb
  | join _ _ ha hb => exact ha.max hb

/-- With the normalized suppressor, clipping the shifter at a visible value preserves
the full witness. This is not an assertion about arbitrary suppressors. -/
theorem clip_witness {τ : ExtOrd → ExtOrd} {K : ℕ} {C : ExtOrd}
    (hτ : Witness (gTop K) τ) (hC : SelfVis K C) :
    Witness (gTop K) (fun x => min (τ x) C) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [hτ.bot, min_bot_left]
  mono := fun _ _ h => min_le_min (hτ.mono h) le_rfl
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ K
    · have hm : Monotone (fun a => extVisibilityReplace a k i) := fun _ _ h => evr_mono h hi
      rw [hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
        hm.map_min, evr_eq_self_of_selfVis (hC.mono hk)]
    · rw [gTop_of_gt (not_le.mp hk)] at hact
      by_cases hCb : C = ⊥
      · simp only [hCb, min_bot_right, extVisibilityReplace_bot]
      · have hxb : τ x = ⊥ := by
          rcases le_total (τ x) C with h | h
          · rwa [min_eq_left h, le_bot_iff] at hact
          · exact False.elim (hCb (le_bot_iff.mp (by rwa [min_eq_right h] at hact)))
        rw [hτ.clause5 x k (by rw [hxb]; exact bot_le) i hi, hxb,
          extVisibilityReplace_bot, min_bot_left, extVisibilityReplace_bot]

/-- Add a high tail at a limit block, without changing the old bottom fibre below it. -/
noncomputable def shifter (τ : ExtOrd → ExtOrd) (n : ℕ) (U : ExtOrd) : ExtOrd → ExtOrd :=
  fun x => max (τ x) (stepShifter n ⊥ U x)

/-- No nonbottom hypothesis is needed: the added step can start a new nonbottom block. -/
theorem witness {τ : ExtOrd → ExtOrd} {K n : ℕ} {U : ExtOrd}
    (hτ : Witness (gTop K) τ) (hU : SelfVis K U) :
    Witness (gTop K) (shifter τ n U) :=
  hτ.max (Witness.stepLimit K n bot_le (by exact extVisibilityReplace_bot K K) hU)

theorem shifter_below {τ : ExtOrd → ExtOrd} {n : ℕ} {U x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * (n : Ordinal))) : shifter τ n U x = τ x := by
  by_cases hb : x = ⊥
  · simp only [hb, shifter, stepShifter_bot, max_bot_right]
  · rw [shifter, stepShifter_of_lt hb hx, max_bot_right]

theorem shifter_above {τ : ExtOrd → ExtOrd} {n : ℕ} {U x : ExtOrd}
    (hx : ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ x) (hbound : τ x ≤ U) :
    shifter τ n U x = U := by
  rw [shifter, stepShifter_of_ge hx, max_eq_right hbound]

/-- A source at the controller grade, in a block beyond the old inventory. -/
def source (K n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * (n : Ordinal) + K)

theorem source_coded (K n : ℕ) : IsCodedLabel K (source K n) :=
  Or.inr ⟨n, K, by omega, rfl⟩

theorem source_visible (K n : ℕ) : SelfVis K (source K n) := by
  rw [source, selfVis_ofOrd_iff, finitePart_mul_add]

theorem limit_le_source (K n : ℕ) :
    ofOrd (Ordinal.omega0 * (n : Ordinal)) ≤ source K n :=
  ofOrd_le_ofOrd.mpr le_self_add

/-- Every finite coded inventory lies below a limit block chosen without target data. -/
theorem exists_limit_above {D : Type*} [Finite D] {K : ℕ} (E : D → ExtOrd)
    (hE : ∀ d, IsCodedLabel K (E d)) :
    ∃ n : ℕ, 0 < n ∧ ∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
  classical
  let _ := Fintype.ofFinite D
  have hlocal : ∀ d, ∃ n : ℕ, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)) := by
    intro d
    rcases hE d with hb | ⟨i, j, _, he⟩
    · exact ⟨1, hb ▸ bot_lt_ofOrd _⟩
    · refine ⟨i + 1, ?_⟩
      rw [he, ofOrd_lt_ofOrd]
      exact code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self i)) j
  choose n hn using hlocal
  refine ⟨Finset.univ.sup n + 1, Nat.zero_lt_succ _, ?_⟩
  intro d
  apply (hn d).trans_le
  apply ofOrd_le_ofOrd.mpr
  exact mul_le_mul_right (Nat.cast_le.mpr
    ((Finset.le_sup (Finset.mem_univ d)).trans (Nat.le_succ _)))
    _

/-- Adjoin one fresh coordinate. Old coordinates are not identified or reordered. -/
def append {D α : Type*} (f : D → α) (x : α) : Option D → α
  | none => x
  | some d => f d

/-- At a source-only cutoff, an actual controller locality extends with arbitrary larger
visible diagonal. The retained outputs are the old capped targets, not uncapped labels
that might have exceeded the old controller. -/
theorem transforms_append {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
    {n : ℕ} {U : ExtOrd} (hmax : ∀ d, grade d ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hcut : ∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (hU : SelfVis (grade c) U) (hCU : p c ≤ U) :
    TransformsTo (append grade (grade c)) (append E (source (grade c) n))
      (append (fun d => min (p d) (p c)) U) := by
  obtain ⟨τ, hτ, hbound, hsrc⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  apply (witness (n := n) hτ hU).transformsTo
  rintro (_ | d)
  · change U = min (shifter τ n U (source (grade c) n)) (gTop (grade c) (grade c))
    rw [shifter_above (limit_le_source _ _) ((hbound _).trans hCU),
      gTop_of_le le_rfl, min_top_right]
  · change min (p d) (p c) = min (shifter τ n U (E d)) (gTop (grade c) (grade d))
    rw [shifter_below (hcut d), hsrc, gTop_of_le (hmax d), min_top_right]

/-- The diagonal can also move downward. Then the old targets are recapped at the new
value; they are not claimed literal above it. This permits an inactive controller to
hide distinctions rather than forcing every controller to remain high. -/
theorem transforms_append_recapped {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
    {n : ℕ} {U : ExtOrd} (hmax : ∀ d, grade d ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hcut : ∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (hU : SelfVis (grade c) U) :
    TransformsTo (append grade (grade c)) (append E (source (grade c) n))
      (append (fun d => min (min (p d) (p c)) U) U) := by
  have hid (a b : ExtOrd) : min (min a U) (min b U) = min (min a b) U := by grind
  have hlocal : TransformsTo grade E (fun d => min (min (p d) U) (min (p c) U)) := by
    simpa only [hid] using TransformsTo.capped hmax hU hloc
  simpa only [hid] using
    transforms_append hmax (selfVis_min hvis hU) hlocal hcut hU (min_le_right _ _)

/-- Relative lifting for this single row has an explicit high value: the maximum of
the previous high and the retuned old cap. Agreement at the old controller suffices for
agreement at the new diagonal. No visibility of the external agreement cap is needed.
This is not scheme bountifulness: other controller localities and availability remain. -/
theorem relative_lift {D : Type*} {grade : D → ℕ} {E p q : D → ExtOrd} {c : D}
    {n : ℕ} {V γ : ExtOrd} (hmax : ∀ d, grade d ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hcut : ∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (hV : SelfVis (grade c) V) (hqV : q c ≤ V)
    (hagree : ∀ d, min (min (p d) (p c)) γ = min (min (q d) (q c)) γ) :
    TransformsTo (append grade (grade c)) (append E (source (grade c) n))
      (append (fun d => min (p d) (p c)) (max V (p c))) ∧
    ∀ d, min (append (fun d => min (p d) (p c)) (max V (p c)) d) γ =
      min (append (fun d => min (q d) (q c)) V d) γ := by
  refine ⟨transforms_append hmax hvis hloc hcut (selfVis_max hV hvis)
    (le_max_right _ _), ?_⟩
  rintro (_ | d)
  · change min (max V (p c)) γ = min V γ
    have hc : min (p c) γ = min (q c) γ := by simpa only [min_self] using hagree c
    have hdom : min (p c) γ ≤ min V γ := hc ▸ min_le_min hqV le_rfl
    grind
  · exact hagree d

/-- With a bottom old row, a fresh limit block still permits an arbitrary visible high,
including top. A bottom-preserving in-block raise alone cannot do this. -/
theorem bottom_prefix {D : Type*} {grade : D → ℕ} {E : D → ExtOrd} {K n : ℕ} {U : ExtOrd}
    (hmax : ∀ d, grade d ≤ K)
    (hcut : ∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal)))
    (hU : SelfVis K U) :
    TransformsTo (append grade K) (append E (source K n)) (append (fun _ => ⊥) U) := by
  apply (Witness.stepLimit K n bot_le (selfVis_bot K) hU).transformsTo
  rintro (_ | d)
  · change U = min (stepShifter n ⊥ U (source K n)) (gTop K K)
    rw [stepShifter_of_ge (limit_le_source _ _), gTop_of_le le_rfl, min_top_right]
  · change ⊥ = min (stepShifter n ⊥ U (E d)) (gTop K (grade d))
    rw [gTop_of_le (hmax d), min_top_right]
    by_cases hb : E d = ⊥
    · rw [hb, stepShifter_bot]
    · exact (stepShifter_of_lt hb (hcut d)).symm

/-- The exposed `ω+1` probe keeps its compulsory `ω+2` orbit point, but a diagonal
in the next block is unrestricted above `ω+2`. This uses the same fixed sources
for every high value, including top. -/
theorem omega_one_regression {U : ExtOrd} (hU : SelfVis 2 U)
    (hle : ofOrd (Ordinal.omega0 + 2) ≤ U) :
    TransformsTo (fun i : Fin 3 => if i = 0 then 1 else 2)
      ![ofOrd (Ordinal.omega0 + 1), ofOrd 2, source 2 2]
      ![ofOrd (Ordinal.omega0 + 1), ofOrd 2, U] := by
  let C : ExtOrd := ofOrd (Ordinal.omega0 + 2)
  have hC : SelfVis 2 C := by
    simpa only [source, Nat.cast_one, mul_one, Nat.cast_ofNat, C] using source_visible 2 1
  have hw := witness (n := 2) (clip_witness (witness_id 2) hC) hU
  have hlow : ofOrd (Ordinal.omega0 + 1) < ofOrd (Ordinal.omega0 * (2 : ℕ)) := by
    simpa only [Nat.cast_one, mul_one, Nat.cast_ofNat] using
      ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (by decide : 1 < 2)) 1)
  have htwo : ofOrd (2 : Ordinal) < ofOrd (Ordinal.omega0 * (2 : ℕ)) := by
    simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_ofNat] using
      ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (by decide : 0 < 2)) 2)
  have hlowC : ofOrd (Ordinal.omega0 + 1) ≤ C := by
    apply ofOrd_le_ofOrd.mpr
    exact add_le_add_right (by norm_num : (1 : Ordinal) ≤ 2) _
  have htwoC : ofOrd (2 : Ordinal) ≤ C := by
    apply ofOrd_le_ofOrd.mpr
    exact le_add_self
  apply hw.transformsTo
  intro i
  fin_cases i
  · change ofOrd (Ordinal.omega0 + 1) =
      min (shifter (fun x => min x C) 2 U (ofOrd (Ordinal.omega0 + 1))) (gTop 2 1)
    rw [shifter_below hlow, min_eq_left hlowC, gTop_of_le (by decide), min_top_right]
  · change ofOrd (2 : Ordinal) =
      min (shifter (fun x => min x C) 2 U (ofOrd (2 : Ordinal))) (gTop 2 2)
    rw [shifter_below htwo, min_eq_left htwoC, gTop_of_le le_rfl, min_top_right]
  · change U = min (shifter (fun x => min x C) 2 U (source 2 2)) (gTop 2 2)
    rw [shifter_above (τ := fun x => min x C) (limit_le_source 2 2)
        ((min_le_right (source 2 2) C).trans hle),
      gTop_of_le le_rfl, min_top_right]

/-- Quantifier order: one fixed sharply coded source extension serves every actual
controller-capped input and every larger visible high. Bottom and top are included.
This uniformity is for one row, not for a jointly consistent controller family. -/
theorem exists_fixed_extension {D : Type*} [Finite D] (grade : D → ℕ) (E : D → ExtOrd)
    (c : D) (hmax : ∀ d, grade d ≤ grade c)
    (hE : ∀ d, IsCodedLabel (grade c) (E d))
    (ho : ∀ d, SelfVis (grade d) (E d)) :
    ∃ n : ℕ, 0 < n ∧
      (∀ d, E d < ofOrd (Ordinal.omega0 * (n : Ordinal))) ∧
      (∀ d, IsCodedLabel (grade c) (append E (source (grade c) n) d)) ∧
      (∀ d, SelfVis (append grade (grade c) d) (append E (source (grade c) n) d)) ∧
      ∀ (p : D → ExtOrd), SelfVis (grade c) (p c) →
        TransformsTo grade E (fun d => min (p d) (p c)) →
        ∀ U, SelfVis (grade c) U → p c ≤ U →
          TransformsTo (append grade (grade c)) (append E (source (grade c) n))
            (append (fun d => min (p d) (p c)) U) := by
  obtain ⟨n, hn, hcut⟩ := exists_limit_above E hE
  refine ⟨n, hn, hcut, ?_, ?_, ?_⟩
  · rintro (_ | d)
    · exact source_coded _ _
    · exact hE d
  · rintro (_ | d)
    · exact source_visible _ _
    · exact ho d
  · intro p hvis hloc U hU hCU
    exact transforms_append hmax hvis hloc hcut hU hCU

end FreeDiagonal

end VaughtConjecture.Knight
