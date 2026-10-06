/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteFloorCompletion
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.RecodingTriangle

/-! # The coded ambient locality of a controller-capped row: the chain

    actual ambient locality  →  controller-capped witness  →  finite floor-completed certificate
      →  keyed encoded certificate  →  the owned coded lower row respects the ambient semantics

**The actual obligation.**  In the assembled scheme, consistency (Def. 2.5.12) demands, for an
owned coded witness row `enc ∘ p` and every proper cell `d` below it, the locality
`E ⇒ enc ∘ p ∧ enc (p c)` from the core's locality `E ⇒ p ∧ p c` toward the **controller** `c` of
maximal grade, which attains the common cap `p c` (`RespectsSemantics.locality`).

* `exists_cappedWitness` — the shifter capped at `p c` is a faithful witness, equal to the displayed
  target at every source, commuting with every replacement at thresholds `≤ grade c`
  unconditionally, and propagating `⊥` (the sibling's controller-capped shifter, in V-C's calculus;
  the key step `cap_le_of_evr` applies the ambient clause 5 at the replaced point).
* `coded_locality_of_capped_S` — the chain for a **fixed key set** `S` in which the capped targets
  are keyed: the floor completion of the capped witness on the bounded replacement closure of the
  sources (`inventory`) is a keyed certificate, which the counted encoding transports.
* `coded_locality_S` (with the bottom cap), `coded_locality` (`S` the primitive range of the row),
  and `coded_locality_valuesAt` — the instantiation on the owned witness's own value set
  `valuesAt gradeP F l` (`Knight/RecodingTriangle.lean`), keyedness derived from the construction,
  with the required target `min (enc_S (p d)) (enc_S (p c))` obtained from preservation of minima.
* Regression instances: a nonconstant mixed-grade locality (`transformsTo_M`, `coded_M`,
  `encT_controller_M`), and the same locality coded with a global key set containing a key absent
  from the controller's local target (`coded_M_global`, `encT_controller_global`): the block numbers
  differ, which is why one shared key set is required for assembly.

**Not here**: full-scope bountifulness, truncations, and the three-level scheme assembly.
Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Part 3 — the chain on an actual ambient locality

`coded_locality_of_capped` / `coded_locality`: an actual ambient locality `E ⇒ p ∧ p(c)` toward a
maximal-grade controller `c`, with `p` orderly on the lower set, gives the **coded** locality
`E ⇒ enc ∘ (p ∧ p(c))` at any coding grade `l ≥ grade c`, with the counted encoding over the
primitive range of the capped target row.  No normalization, keyed-table, orbit, or bridge
hypothesis remains: keyedness is derived from the primitive range and the bounded replacement
closure of the sources, the certificate is the floor completion of the capped witness, and the
cashout is the kernel's.  The bottom-cap case is handled separately (every target is `⊥`). -/

section Chain

variable {D : Type*} [Fintype D]

/-- The primitive range of a row: its ordinal values. -/
noncomputable def primRange (target : D → ExtOrd) : Finset Ordinal.{0} :=
  Finset.univ.biUnion fun d =>
    match target d with
    | some (some v) => {v}
    | _ => ∅

theorem mem_primRange_of_eq {target : D → ExtOrd} {d : D} {v : Ordinal.{0}}
    (h : target d = ofOrd v) : v ∈ primRange target := by
  unfold primRange
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ d, ?_⟩
  rw [h]
  exact Finset.mem_singleton_self v

theorem keyed_target (l : ℕ) (target : D → ExtOrd) (d : D) :
    Keyed l (primRange target) (target d) := by
  rcases ExtOrd.cases (target d) with h | h | ⟨v, h⟩
  · rw [h]; exact keyed_bot _ _
  · rw [h]; exact keyed_top _ _
  · rw [h]; exact keyed_of_mem _ _ (mem_primRange_of_eq h)

/-- The bounded replacement closure of the sources at the controller grade. -/
noncomputable def inventory (K : ℕ) (E : D → ExtOrd) : Finset ExtOrd :=
  Finset.univ.image E ∪
    (Finset.univ.image E).biUnion fun x =>
      (Finset.range (K + 1)).image fun i => extVisibilityReplace x K i

theorem source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) : E d ∈ inventory K E :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem E (Finset.mem_univ d))

theorem evr_source_mem_inventory (K : ℕ) (E : D → ExtOrd) (d : D) {i : ℕ} (hi : i ≤ K) :
    extVisibilityReplace (E d) K i ∈ inventory K E := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨E d, Finset.mem_image_of_mem E (Finset.mem_univ d),
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩⟩

theorem mem_inventory_iff {K : ℕ} {E : D → ExtOrd} {y : ExtOrd} :
    y ∈ inventory K E ↔ (∃ d, y = E d) ∨ ∃ d, ∃ i ≤ K, y = extVisibilityReplace (E d) K i := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨d, rfl⟩
    · obtain ⟨x, hx, hm⟩ := Finset.mem_biUnion.mp h
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      exact Or.inr ⟨d, i, by have := Finset.mem_range.mp hi; omega, rfl⟩
  · rintro (⟨d, rfl⟩ | ⟨d, i, hi, rfl⟩)
    · exact source_mem_inventory K E d
    · exact evr_source_mem_inventory K E d hi

/-- A replacement of a source at a threshold `≤ K` is a replacement at `K`, or the source. -/
theorem evr_eq_evr_K {x : ExtOrd} {K k i : ℕ} (hk : k ≤ K) (_hi : i ≤ k) :
    extVisibilityReplace x k i = extVisibilityReplace x K i ∨ extVisibilityReplace x k i = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · right; rfl
  · right; rfl
  · by_cases hfp : finitePart a < k
    · left
      rw [extVisibilityReplace_of_finitePart_lt hfp,
        extVisibilityReplace_of_finitePart_lt (by omega)]
    · right
      exact extVisibilityReplace_of_le_finitePart (not_lt.mp hfp) i

/-- **The inventory is closed under every replacement at thresholds `≤ K`.** -/
theorem inventory_closed (K : ℕ) (E : D → ExtOrd) :
    ∀ x ∈ inventory K E, ∀ k i : ℕ, k ≤ K → i ≤ k → extVisibilityReplace x k i ∈ inventory K E := by
  intro x hx k i hk hi
  rcases mem_inventory_iff.mp hx with ⟨d, rfl⟩ | ⟨d, j, hj, rfl⟩
  · rcases evr_eq_evr_K hk hi with h | h
    · rw [h]; exact evr_source_mem_inventory K E d (hi.trans hk)
    · rw [h]; exact source_mem_inventory K E d
  · rcases ExtOrd.cases (E d) with h0 | h0 | ⟨b, hb⟩
    · rw [h0, extVisibilityReplace_bot, extVisibilityReplace_bot]
      rw [← extVisibilityReplace_bot K j, ← h0]; exact evr_source_mem_inventory K E d hj
    · rw [h0, extVisibilityReplace_top, extVisibilityReplace_top]
      rw [← extVisibilityReplace_top K j, ← h0]; exact evr_source_mem_inventory K E d hj
    · rw [hb]
      by_cases hfb : finitePart b < K
      · rw [extVisibilityReplace_of_finitePart_lt hfb]
        by_cases hjk : j < k
        · rw [extVisibilityReplace_of_finitePart_lt
              (by rw [finitePart_limitPart_add_nat]; exact hjk),
            limitPart_limitPart_add_nat, ← extVisibilityReplace_of_finitePart_lt (k := K) hfb, ← hb]
          exact evr_source_mem_inventory K E d (hi.trans hk)
        · rw [extVisibilityReplace_of_le_finitePart (by rw [finitePart_limitPart_add_nat]; omega),
            ← extVisibilityReplace_of_finitePart_lt (k := K) hfb, ← hb]
          exact evr_source_mem_inventory K E d hj
      · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfb),
          extVisibilityReplace_of_le_finitePart (by omega), ← hb]
        exact source_mem_inventory K E d

variable (grade : D → ℕ) (E p : D → ExtOrd) (c : D)

/-- **The coded locality from an actual controller-capped ambient locality**, for a fixed key set
`S` in which the capped targets are keyed (nonbottom cap). -/
theorem coded_locality_of_capped_S (hmax : ∀ d, grade d ≤ grade c)
    (hordp : ∀ d, SelfVis (grade d) (p d)) (hne : p c ≠ ⊥)
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l : ℕ} (hl : grade c ≤ l)
    (S : Finset Ordinal.{0}) (hS : ∀ d, Keyed l S (min (p d) (p c))) :
    TransformsTo grade E fun d => encT l S (min (p d) (p c)) := by
  classical
  obtain ⟨g', τ, -, -, hbot, hmono, -, -, hcap, hsrc, hcomm, hbotprop⟩ :=
    exists_cappedWitness grade E p c hmax (hordp c) hne hloc
  set target : D → ExtOrd := fun d => min (p d) (p c) with htarget
  set K := grade c with hK
  have hTail : ∀ k, K < k → finiteTargetSuppressor grade target k = ⊥ := fun k hk =>
    finiteTargetSuppressor_eq_bot_of_lt grade target hmax hk
  obtain ⟨hB, hM, hO, hBr⟩ :=
    floorCompletion K (inventory K E) τ (finiteTargetSuppressor grade target)
    (inventory_closed K E) hbot hmono hbotprop
    (fun x k i hk hi => hcomm x k i hk hi) hTail
  -- the uncoded certificate
  let C : FiniteBlockBridgeCertificate grade E target :=
    { tableDomain := stripDomain K (inventory K E)
      table := fun x => τ (roundUp (inventory K E) x)
      bottom := hB
      monotone := hM
      orbit := hO
      bridge := hBr
      source_mem := fun d => subset_stripDomain K _ (source_mem_inventory K E d)
      realizes := fun d => by
        show target d = min (τ (roundUp (inventory K E) (E d))) _
        rw [roundUp_of_mem (source_mem_inventory K E d), hsrc d,
          min_eq_left (target_le_finiteTargetSuppressor grade target d)] }
  -- keyedness of the table on its domain
  have hkeyed : ∀ y ∈ C.tableDomain, Keyed l S (C.table y) := by
    intro y hy
    show Keyed l S (τ (roundUp (inventory K E) y))
    have hmem := roundUp_mem K (inventory K E) (inventory_closed K E) hy
    rcases mem_inventory_iff.mp hmem with ⟨d, hd⟩ | ⟨d, i, hi, hd⟩
    · rw [hd, hsrc d]; exact hS d
    · rw [hd, hcomm _ K i le_rfl hi, hsrc d]
      exact keyed_evr l S hl (hS d) hi
  have hord : IsOrderly grade target := fun d =>
    (selfVis_min (hordp d) (selfVis_mono (hordp c) (hmax d))).symm
  exact transformsTo_encode C (fun d => (hmax d).trans hl) hS hkeyed
    (isOrderly_encode (fun d => (hmax d).trans hl) hord)

/-- **The coded locality for a fixed key set, including the bottom cap.** -/
theorem coded_locality_S (hmax : ∀ d, grade d ≤ grade c)
    (hordp : ∀ d, SelfVis (grade d) (p d))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l : ℕ} (hl : grade c ≤ l)
    (S : Finset Ordinal.{0}) (hS : ∀ d, Keyed l S (min (p d) (p c))) :
    TransformsTo grade E fun d => encT l S (min (p d) (p c)) := by
  by_cases hne : p c = ⊥
  · refine ⟨fun _ => ⊥, fun _ => ⊥, fun _ _ _ => le_rfl,
      fun n => (extVisibilityReplace_bot n n).symm,
      rfl, fun _ _ _ => le_rfl, fun _ _ _ _ _ => by rw [extVisibilityReplace_bot], fun d => ?_⟩
    change encT l S (min (p d) (p c)) = min ⊥ ⊥
    rw [hne, min_eq_right bot_le, encT_bot, min_self]
  · exact coded_locality_of_capped_S grade E p c hmax hordp hne hloc hl S hS

/-- With `S` the primitive range of the capped row. -/
theorem coded_locality_of_capped (hmax : ∀ d, grade d ≤ grade c)
    (hordp : ∀ d, SelfVis (grade d) (p d)) (hne : p c ≠ ⊥)
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l : ℕ} (hl : grade c ≤ l) :
    TransformsTo grade E fun d =>
      encT l (primRange fun d => min (p d) (p c)) (min (p d) (p c)) :=
  coded_locality_of_capped_S grade E p c hmax hordp hne hloc hl _
    (keyed_target l fun d => min (p d) (p c))


/-- **The coded locality with the primitive range, including the bottom cap.** -/
theorem coded_locality (hmax : ∀ d, grade d ≤ grade c)
    (hordp : ∀ d, SelfVis (grade d) (p d))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) {l : ℕ} (hl : grade c ≤ l) :
    TransformsTo grade E fun d =>
      encT l (primRange fun d => min (p d) (p c)) (min (p d) (p c)) :=
  coded_locality_S grade E p c hmax hordp hloc hl _ (keyed_target l fun d => min (p d) (p c))

/-- **The instantiation on the owned witness's value set.**  For a core row `F` over the proper
part `P` and its value set `valuesAt gradeP F l` at the coding grade `l`: the locality of `F`
toward the controller `c` (a cell of its own lower set `ι : D → P`, of maximal grade `≤ l`)
gives the coded locality of the owned witness row, with the target
`min (enc_S (F (ι d))) (enc_S (F (ι c)))`.  Keyedness is derived: every capped target is a value
of `F` at a cell of grade `≤ l`, or `⊥`. -/
theorem coded_locality_valuesAt {P : Type*} [Fintype P] [DecidableEq P] (gradeP : P → ℕ)
    (F : P → ExtOrd) (l : ℕ) (hne_top : ∀ x, F x ≠ ⊤) (ι : D → P) (hcl : gradeP (ι c) ≤ l)
    (hmax : ∀ d, gradeP (ι d) ≤ gradeP (ι c)) (hordp : ∀ d, SelfVis (gradeP (ι d)) (F (ι d)))
    (hloc : TransformsTo (fun d => gradeP (ι d)) E (fun d => min (F (ι d)) (F (ι c)))) :
    TransformsTo (fun d => gradeP (ι d)) E fun d =>
      min (encT l (valuesAt gradeP F l) (F (ι d))) (encT l (valuesAt gradeP F l) (F (ι c))) := by
  classical
  have hkeyedF : ∀ x, gradeP x ≤ l → Keyed l (valuesAt gradeP F l) (F x) := by
    intro x hx
    rcases ExtOrd.cases (F x) with h | h | ⟨v, h⟩
    · rw [h]; exact keyed_bot _ _
    · exact absurd h (hne_top x)
    · rw [h]
      exact keyed_of_mem _ _ ((mem_valuesAt gradeP).mpr ⟨x, hx, h⟩)
  have hkc : Keyed l (valuesAt gradeP F l) (F (ι c)) := hkeyedF (ι c) hcl
  have hkd : ∀ d, Keyed l (valuesAt gradeP F l) (F (ι d)) := fun d =>
    hkeyedF (ι d) ((hmax d).trans hcl)
  have h := coded_locality_S (fun d => gradeP (ι d)) E (fun d => F (ι d)) c hmax hordp hloc hcl
    (valuesAt gradeP F l) (fun d => keyed_min _ _ (hkd d) hkc)
  -- pull the minimum out of the encoding
  have heq : (fun d => encT l (valuesAt gradeP F l) (min (F (ι d)) (F (ι c)))) =
      fun d =>
        min (encT l (valuesAt gradeP F l) (F (ι d))) (encT l (valuesAt gradeP F l) (F (ι c))) :=
    funext fun d => encT_min_keyed _ _ (hkd d) hkc
  rw [← heq]
  exact h

end Chain

/-! ## Part 4 — a nonconstant mixed-grade instance

Two cells: `a` of grade 1 with source `ω·2 + 1` and value `ω + 1`; the controller `c` of grade 2
with source `ω·3 + 2` and value `ω·5 + 2`.  The ambient shifter is `⊥` below the source block of
`a`, `ω + min(fp, 2)` on that block, `ω·5 + min(fp, 2)` on the controller's block, and the constant
`ω·5 + 2` above; the suppressor is the cap through grade 2.  The locality is verified
(`transformsTo_M`), so `coded_locality` applies at coding grade 2 (`coded_M`).  There the
primitive range `{ω + 1, ω·5 + 2}` has keys `{ω, ω·5}`, and the encoding is **not** the identity:
the controller's value `ω·5 + 2` is coded `ω·2 + 2` (`encT_controller_M`). -/

section Instance

/-- `ω·t + j` with the casts the part lemmas expect. -/
noncomputable def wv (t j : ℕ) : Ordinal.{0} := Ordinal.omega0 * (t : Ordinal) + (j : Ordinal)

theorem fp_wv (t j : ℕ) : finitePart (wv t j) = j := finitePart_mul_add t j
theorem lp_wv (t j : ℕ) : limitPart (wv t j) = Ordinal.omega0 * (t : Ordinal) :=
  limitPart_mul_add t j

theorem omul_le_omul {t t' : ℕ} (h : t ≤ t') :
    Ordinal.omega0 * (t : Ordinal) ≤ Ordinal.omega0 * (t' : Ordinal) := by
  gcongr

theorem omul_lt_omul {t t' : ℕ} (h : t < t') :
    Ordinal.omega0 * (t : Ordinal) < Ordinal.omega0 * (t' : Ordinal) :=
  calc Ordinal.omega0 * (t : Ordinal) < Ordinal.omega0 * (t : Ordinal) + Ordinal.omega0 :=
        lt_add_of_pos_right _ Ordinal.omega0_pos
    _ = Ordinal.omega0 * ((t + 1 : ℕ) : Ordinal) := by rw [Nat.cast_succ, mul_add, mul_one]
    _ ≤ Ordinal.omega0 * (t' : Ordinal) := omul_le_omul h

theorem wv_le_wv_of_lt {t t' j j' : ℕ} (h : t < t') : wv t j ≤ wv t' j' :=
  calc wv t j ≤ Ordinal.omega0 * (t : Ordinal) + Ordinal.omega0 :=
        add_le_add le_rfl (Ordinal.natCast_lt_omega0 _).le
    _ = Ordinal.omega0 * ((t + 1 : ℕ) : Ordinal) := by rw [Nat.cast_succ, mul_add, mul_one]
    _ ≤ Ordinal.omega0 * (t' : Ordinal) := omul_le_omul h
    _ ≤ wv t' j' := le_self_add

theorem wv_le_wv_iff {t j j' : ℕ} : wv t j ≤ wv t j' ↔ j ≤ j' := by
  unfold wv; rw [add_le_add_iff_left, Nat.cast_le]

/-- A limit part below `ω·T` is `ω·t` for a natural `t < T`. -/
theorem limitPart_eq_omul_of_lt {x : Ordinal.{0}} {T : ℕ}
    (h : limitPart x < Ordinal.omega0 * (T : Ordinal)) :
    ∃ t : ℕ, t < T ∧ limitPart x = Ordinal.omega0 * (t : Ordinal) := by
  rw [limitPart_eq_mul_blockIdx] at h ⊢
  have hlt : blockIdx x < (T : Ordinal) := by
    by_contra hc
    have hc := not_lt.mp hc
    exact absurd h (not_lt.mpr (by gcongr))
  obtain ⟨t, ht⟩ := Ordinal.lt_omega0.mp (hlt.trans (Ordinal.natCast_lt_omega0 T))
  refine ⟨t, ?_, by rw [ht]⟩
  rw [ht] at hlt
  exact_mod_cast hlt

/-- The two cells. -/
inductive M2 | a | c
  deriving DecidableEq

instance : Fintype M2 := ⟨{.a, .c}, by intro x; cases x <;> simp⟩

def gradeM : M2 → ℕ | .a => 1 | .c => 2
noncomputable def EM : M2 → ExtOrd | .a => ofOrd (wv 2 1) | .c => ofOrd (wv 3 2)
noncomputable def pM : M2 → ExtOrd | .a => ofOrd (wv 1 1) | .c => ofOrd (wv 5 2)

/-- The ambient shifter, by source block. -/
noncomputable def σM : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some x) =>
      if limitPart x < Ordinal.omega0 * ((2 : ℕ) : Ordinal) then ⊥
      else if limitPart x < Ordinal.omega0 * ((3 : ℕ) : Ordinal) then
        ofOrd (wv 1 (min (finitePart x) 2))
      else if limitPart x < Ordinal.omega0 * ((4 : ℕ) : Ordinal) then
        ofOrd (wv 5 (min (finitePart x) 2))
      else ofOrd (wv 5 2)

noncomputable def gM : ℕ → ExtOrd := fun k => if k ≤ 2 then ofOrd (wv 5 2) else ⊥

theorem σM_ofOrd (x : Ordinal.{0}) : σM (ofOrd x) =
    if limitPart x < Ordinal.omega0 * ((2 : ℕ) : Ordinal) then ⊥
      else if limitPart x < Ordinal.omega0 * ((3 : ℕ) : Ordinal) then
        ofOrd (wv 1 (min (finitePart x) 2))
      else if limitPart x < Ordinal.omega0 * ((4 : ℕ) : Ordinal) then
        ofOrd (wv 5 (min (finitePart x) 2))
      else ofOrd (wv 5 2) := rfl

/-- The shifter on a block `ω·t`, by region. -/
theorem σM_wv (t j : ℕ) : σM (ofOrd (wv t j)) =
    if t < 2 then ⊥ else if t < 3 then ofOrd (wv 1 (min j 2))
      else if t < 4 then ofOrd (wv 5 (min j 2)) else ofOrd (wv 5 2) := by
  rw [σM_ofOrd, lp_wv, fp_wv]
  by_cases h2 : t < 2
  · rw [ite_eq_left (omul_lt_omul h2), ite_eq_left h2]
  · rw [ite_eq_right (not_lt.mpr (omul_le_omul (by omega))), ite_eq_right h2]
    by_cases h3 : t < 3
    · rw [ite_eq_left (omul_lt_omul h3), ite_eq_left h3]
    · rw [ite_eq_right (not_lt.mpr (omul_le_omul (by omega))), ite_eq_right h3]
      by_cases h4 : t < 4
      · rw [ite_eq_left (omul_lt_omul h4), ite_eq_left h4]
      · rw [ite_eq_right (not_lt.mpr (omul_le_omul (by omega))), ite_eq_right h4]

/-- Every ordinal label's shifter value is determined by its block region and finite part. -/
theorem σM_eq_region (x : Ordinal.{0}) :
    σM (ofOrd x) = σM (ofOrd (limitPart x + finitePart x)) := by rw [limitPart_add_finitePart]

theorem σM_le_cap (x : ExtOrd) (hx : x ≠ ⊤) : σM x ≤ ofOrd (wv 5 2) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · exact absurd rfl hx
  · rw [σM_ofOrd]
    split_ifs
    · exact bot_le
    · exact ofOrd_le_ofOrd.mpr (wv_le_wv_of_lt (by omega))
    · exact ofOrd_le_ofOrd.mpr (wv_le_wv_iff.mpr (min_le_right _ _))
    · exact le_rfl

theorem σM_mono : Monotone σM := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · exact absurd hxy (not_ofOrd_le_bot a)
    · exact le_top
    · have hab := ofOrd_le_ofOrd.mp hxy
      have hlp := limitPart_mono hab
      rw [σM_ofOrd, σM_ofOrd]
      -- regions of `a` then of `b`
      by_cases ha2 : limitPart a < Ordinal.omega0 * ((2 : ℕ) : Ordinal)
      · rw [ite_eq_left ha2]; exact bot_le
      · rw [ite_eq_right ha2]
        have hb2 : ¬ limitPart b < Ordinal.omega0 * ((2 : ℕ) : Ordinal) :=
          fun h => ha2 (hlp.trans_lt h)
        rw [ite_eq_right hb2]
        by_cases ha3 : limitPart a < Ordinal.omega0 * ((3 : ℕ) : Ordinal)
        · rw [ite_eq_left ha3]
          by_cases hb3 : limitPart b < Ordinal.omega0 * ((3 : ℕ) : Ordinal)
          · rw [ite_eq_left hb3]
            -- both on the block `ω·2`
            obtain ⟨t, ht3, hta⟩ := limitPart_eq_omul_of_lt ha3
            obtain ⟨t', ht3', htb⟩ := limitPart_eq_omul_of_lt hb3
            have ht2 : 2 ≤ t := by
              by_contra hc
              exact ha2 (by rw [hta]; exact omul_lt_omul (not_le.mp hc))
            have ht2' : 2 ≤ t' := by
              by_contra hc
              exact hb2 (by rw [htb]; exact omul_lt_omul (not_le.mp hc))
            have heq : limitPart a = limitPart b := by
              rw [hta, htb]; congr 2; omega
            have hfp := finitePart_le_of_le_of_limitPart_eq hab heq
            exact ofOrd_le_ofOrd.mpr (wv_le_wv_iff.mpr (by omega))
          · rw [ite_eq_right hb3]
            split_ifs
            · exact ofOrd_le_ofOrd.mpr (wv_le_wv_of_lt (by omega))
            · exact ofOrd_le_ofOrd.mpr (wv_le_wv_of_lt (by omega))
        · rw [ite_eq_right ha3]
          have hb3 : ¬ limitPart b < Ordinal.omega0 * ((3 : ℕ) : Ordinal) :=
            fun h => ha3 (hlp.trans_lt h)
          rw [ite_eq_right hb3]
          by_cases ha4 : limitPart a < Ordinal.omega0 * ((4 : ℕ) : Ordinal)
          · rw [ite_eq_left ha4]
            by_cases hb4 : limitPart b < Ordinal.omega0 * ((4 : ℕ) : Ordinal)
            · rw [ite_eq_left hb4]
              obtain ⟨t, ht4, hta⟩ := limitPart_eq_omul_of_lt ha4
              obtain ⟨t', ht4', htb⟩ := limitPart_eq_omul_of_lt hb4
              have ht3 : 3 ≤ t := by
                by_contra hc
                exact ha3 (by rw [hta]; exact omul_lt_omul (not_le.mp hc))
              have ht3' : 3 ≤ t' := by
                by_contra hc
                exact hb3 (by rw [htb]; exact omul_lt_omul (not_le.mp hc))
              have heq : limitPart a = limitPart b := by
                rw [hta, htb]; congr 2; omega
              have hfp := finitePart_le_of_le_of_limitPart_eq hab heq
              exact ofOrd_le_ofOrd.mpr (wv_le_wv_iff.mpr (by omega))
            · rw [ite_eq_right hb4]
              exact ofOrd_le_ofOrd.mpr (wv_le_wv_iff.mpr (min_le_right _ _))
          · rw [ite_eq_right ha4]
            have hb4 : ¬ limitPart b < Ordinal.omega0 * ((4 : ℕ) : Ordinal) :=
              fun h => ha4 (hlp.trans_lt h)
            rw [ite_eq_right hb4]

/-- The bounded commutation of the instance shifter: unconditional at thresholds `≤ 2`. -/
theorem σM_comm (a : Ordinal.{0}) {k i : ℕ} (hk : k ≤ 2) (hi : i ≤ k) :
    σM (extVisibilityReplace (ofOrd a) k i) = extVisibilityReplace (σM (ofOrd a)) k i := by
  by_cases hfp : finitePart a < k
  · rw [extVisibilityReplace_of_finitePart_lt hfp, σM_ofOrd, σM_ofOrd, limitPart_limitPart_add_nat,
      finitePart_limitPart_add_nat]
    have hi2 : min i 2 = i := min_eq_left (by omega)
    have ha2 : min (finitePart a) 2 = finitePart a := min_eq_left (by omega)
    split_ifs
    · rfl
    · rw [hi2, ha2, extVisibilityReplace_of_finitePart_lt (by rw [fp_wv]; exact hfp), lp_wv]; rfl
    · rw [hi2, ha2, extVisibilityReplace_of_finitePart_lt (by rw [fp_wv]; exact hfp), lp_wv]; rfl
    · rw [extVisibilityReplace_of_le_finitePart (by rw [fp_wv]; omega)]
  · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfp), σM_ofOrd]
    split_ifs
    · rfl
    · rw [extVisibilityReplace_of_le_finitePart (by rw [fp_wv]; omega)]
    · rw [extVisibilityReplace_of_le_finitePart (by rw [fp_wv]; omega)]
    · rw [extVisibilityReplace_of_le_finitePart (by rw [fp_wv]; omega)]

/-- **The instance's ambient locality.** -/
theorem transformsTo_M : TransformsTo gradeM EM (fun d => min (pM d) (pM .c)) := by
  refine ⟨gM, σM, ?_, ?_, rfl, σM_mono, ?_, ?_⟩
  · intro n m hnm
    unfold gM
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    unfold gM
    split_ifs with h
    · exact (extVisibilityReplace_of_le_finitePart (by rw [fp_wv]; omega) n).symm
    · rfl
  · intro x k hact i hi
    rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
    · rfl
    · exfalso
      unfold gM at hact
      split_ifs at hact
      · exact absurd (top_le_iff.mp hact) (ofOrd_ne_top _)
      · exact absurd (top_le_iff.mp hact) (by simp)
    · by_cases hk : k ≤ 2
      · exact σM_comm a hk hi
      · -- above grade 2 only `⊥` is active: the label is in the bottom region
        unfold gM at hact
        rw [ite_eq_right hk] at hact
        have hbot : σM (ofOrd a) = ⊥ := le_bot_iff.mp hact
        have hreg : limitPart a < Ordinal.omega0 * ((2 : ℕ) : Ordinal) := by
          by_contra hc
          rw [σM_ofOrd, ite_eq_right hc] at hbot
          split_ifs at hbot <;> exact absurd hbot (ofOrd_ne_bot _)
        rw [hbot, extVisibilityReplace_bot]
        by_cases hfp : finitePart a < k
        · rw [extVisibilityReplace_of_finitePart_lt hfp, σM_ofOrd,
            ite_eq_left (by rw [limitPart_limitPart_add_nat]; exact hreg)]
        · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfp), hbot]
  · intro d
    cases d
    · change min (ofOrd (wv 1 1)) (ofOrd (wv 5 2)) = min (σM (ofOrd (wv 2 1))) (gM 1)
      rw [σM_wv, ite_eq_right (by omega), ite_eq_left (by omega),
        min_eq_left (show (1 : ℕ) ≤ 2 by omega)]
      unfold gM
      rw [ite_eq_left (by omega)]
    · change min (ofOrd (wv 5 2)) (ofOrd (wv 5 2)) = min (σM (ofOrd (wv 3 2))) (gM 2)
      rw [σM_wv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      simp only [min_self]
      unfold gM
      rw [ite_eq_left le_rfl, min_self]

/-- **The coded locality of the instance**, at coding grade 2. -/
theorem coded_M : TransformsTo gradeM EM fun d =>
    encT 2 (primRange fun d => min (pM d) (pM .c)) (min (pM d) (pM .c)) :=
  coded_locality gradeM EM pM .c (fun d => by cases d <;> decide)
    (fun d => by
      cases d
      · show extVisibilityReplace (ofOrd (wv 1 1)) 1 1 = ofOrd (wv 1 1)
        exact extVisibilityReplace_of_le_finitePart (by rw [fp_wv]) 1
      · show extVisibilityReplace (ofOrd (wv 5 2)) 2 2 = ofOrd (wv 5 2)
        exact extVisibilityReplace_of_le_finitePart (by rw [fp_wv]) 2)
    transformsTo_M le_rfl


/-- The primitive range of the instance's target row. -/
theorem primRange_M : primRange (fun d => min (pM d) (pM .c)) = {wv 1 1, wv 5 2} := by
  unfold primRange
  rw [show (Finset.univ : Finset M2) = {M2.a, M2.c} from rfl, Finset.biUnion_insert,
    Finset.singleton_biUnion]
  dsimp only
  have ha : min (pM .a) (pM .c) = ofOrd (wv 1 1) := by
    show min (ofOrd (wv 1 1)) (ofOrd (wv 5 2)) = _
    exact min_eq_left (ofOrd_le_ofOrd.mpr (wv_le_wv_of_lt (by omega)))
  have hc : min (pM .c) (pM .c) = ofOrd (wv 5 2) := min_self _
  rw [ha, hc]
  rfl

theorem omul_ne {t t' : ℕ} (h : t ≠ t') :
    Ordinal.omega0 * (t : Ordinal) ≠ Ordinal.omega0 * (t' : Ordinal) := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · exact (omul_lt_omul hlt).ne
  · exact (omul_lt_omul hlt).ne'

/-- **The encoding is not the identity on the instance**: the controller's value `ω·5 + 2` is
coded `ω·2 + 2` (two keys, `ω` and `ω·5`, lie at or below its key). -/
theorem encT_controller_M :
    encT 2 (primRange fun d => min (pM d) (pM .c)) (ofOrd (wv 5 2)) = ofOrd (wv 2 2) := by
  classical
  rw [primRange_M, encT_ofOrd]
  unfold encOrdK blockOf blockOfKey keys
  rw [Finset.image_insert, Finset.image_singleton]
  have hk1 : keyOrd 2 (wv 1 1) = Ordinal.omega0 * ((1 : ℕ) : Ordinal) := by
    unfold keyOrd; rw [ite_eq_left (by rw [fp_wv]; omega), lp_wv]
  have hk5 : keyOrd 2 (wv 5 2) = Ordinal.omega0 * ((5 : ℕ) : Ordinal) := by
    unfold keyOrd; rw [ite_eq_left (by rw [fp_wv]), lp_wv]
  rw [hk1, hk5, Finset.filter_insert, Finset.filter_singleton,
    ite_eq_left (omul_le_omul (by omega)), ite_eq_left le_rfl,
    Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact omul_ne (by omega)),
    Finset.card_singleton, fp_wv, min_self]
  rfl

/-- A **global** key set containing a key (`ω·3`) absent from the controller's local target. -/
noncomputable def Sg : Finset Ordinal.{0} := {wv 1 1, wv 3 1, wv 5 2}

theorem keyed_Sg (d : M2) : Keyed 2 Sg (min (pM d) (pM .c)) := by
  cases d
  · show Keyed 2 Sg (min (ofOrd (wv 1 1)) (ofOrd (wv 5 2)))
    rw [min_eq_left (ofOrd_le_ofOrd.mpr (wv_le_wv_of_lt (by omega)))]
    exact keyed_of_mem _ _ (by unfold Sg; simp)
  · show Keyed 2 Sg (min (ofOrd (wv 5 2)) (ofOrd (wv 5 2)))
    rw [min_self]
    exact keyed_of_mem _ _ (by unfold Sg; simp)

/-- **The coded locality of the instance with the global key set.** -/
theorem coded_M_global : TransformsTo gradeM EM fun d => encT 2 Sg (min (pM d) (pM .c)) :=
  coded_locality_S gradeM EM pM .c (fun d => by cases d <;> decide)
    (fun d => by
      cases d
      · show extVisibilityReplace (ofOrd (wv 1 1)) 1 1 = ofOrd (wv 1 1)
        exact extVisibilityReplace_of_le_finitePart (by rw [fp_wv]) 1
      · show extVisibilityReplace (ofOrd (wv 5 2)) 2 2 = ofOrd (wv 5 2)
        exact extVisibilityReplace_of_le_finitePart (by rw [fp_wv]) 2)
    transformsTo_M le_rfl Sg keyed_Sg

/-- **The block numbers differ with the global key set**: the controller's value is coded
`ω·3 + 2` there (three keys at or below `ω·5`), against `ω·2 + 2` locally. -/
theorem encT_controller_global : encT 2 Sg (ofOrd (wv 5 2)) = ofOrd (wv 3 2) := by
  classical
  rw [encT_ofOrd]
  unfold encOrdK blockOf blockOfKey keys Sg
  rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  have hk1 : keyOrd 2 (wv 1 1) = Ordinal.omega0 * ((1 : ℕ) : Ordinal) := by
    unfold keyOrd; rw [ite_eq_left (by rw [fp_wv]; omega), lp_wv]
  have hk3 : keyOrd 2 (wv 3 1) = Ordinal.omega0 * ((3 : ℕ) : Ordinal) := by
    unfold keyOrd; rw [ite_eq_left (by rw [fp_wv]; omega), lp_wv]
  have hk5 : keyOrd 2 (wv 5 2) = Ordinal.omega0 * ((5 : ℕ) : Ordinal) := by
    unfold keyOrd; rw [ite_eq_left (by rw [fp_wv]), lp_wv]
  rw [hk1, hk3, hk5, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    ite_eq_left (omul_le_omul (by omega)), ite_eq_left (omul_le_omul (by omega)),
    ite_eq_left le_rfl,
    Finset.card_insert_of_notMem (by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact not_or.mpr ⟨omul_ne (by omega), omul_ne (by omega)⟩),
    Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact omul_ne (by omega)),
    Finset.card_singleton, fp_wv, min_self]
  rfl

end Instance

end VaughtConjecture.Knight
