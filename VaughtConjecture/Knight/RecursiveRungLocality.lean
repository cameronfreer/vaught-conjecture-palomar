/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungMasterLocality

/-! # Charts at every inherited auxiliary owner of the recursive renderer

Higher leaf charts propagate through each later outer decoder by repaired
composition on that leaf's native short row. Long base-rung charts are instead
read directly from the exact whole-base formula. Every chart includes complete
original fields and all auxiliaries at or below the owner's birth grade.

This proves the auxiliary-owner locality incidences on the tagged master
inventory. Geometric installation, original-owner lawfulness, catalogue
admission and the availability ledger remain separate.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RecursiveRungLocality
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison RecursiveRungRendering
noncomputable section
universe u v
variable {X : Type u} {B : Type v} [Fintype X] {Q : ℕ → Type v}

/-- Literal inclusion: each later grade retains every earlier coordinate. -/
def raiseAux {n : ℕ} : (t : ℕ) → Aux X B Q n → Aux X B Q (n + t)
  | 0, d => d
  | t + 1, d => .inl (raiseAux t d)

def raise {n : ℕ} (t : ℕ) : Point X B Q n → Point X B Q (n + t) :=
  Sum.map id (raiseAux t)

theorem raise_zero {n : ℕ} (d : Point X B Q n) : raise 0 d = d := by
  cases d <;> rfl

theorem raise_injective {n : ℕ} (t : ℕ) :
    Function.Injective (raise (X := X) (B := B) (Q := Q) (n := n) t) := by
  have hi : Function.Injective (raiseAux (X := X) (B := B) (Q := Q) (n := n) t) := by
    induction t with
    | zero => exact Function.injective_id
    | succ t ih => exact Sum.inl_injective.comp ih
  exact Sum.map_injective.mpr ⟨Function.injective_id, hi⟩

variable (ranks : B → X → ℕ) (fields : (j : ℕ) → Q j → X → ExtOrd)

/-- Restriction of a later rendering is an outer image of a new lower call,
not an equality with the earlier rendering at the old parameters. -/
theorem render_raise_succ {n : ℕ} (t : ℕ) {p : X → ExtOrd}
    {G : Finset ExtOrd} {C : ExtOrd} (hp : ∀ d, p d ≠ ⊤)
    (hG : ∀ z ∈ G, SelfVis (n + t + 2) z) (hC : SelfVis (n + t + 2) C)
    (d : Point X B Q n) :
    render ranks fields (n + (t + 1)) p G C (raise (t + 1) d) =
      PairedSlotDecoder.decode (n + t + 2) (values p) G C
        (render ranks fields (n + t) (normalize (n + t + 2) p)
          (grid X (n + t + 2)) (ceiling X (n + t + 2)) (raise t d)) := by
  cases d with
  | inl d => exact (PairedSlotDecoder.decode_normalize hG hC hp d).symm
  | inr d => rfl

private theorem normalized_bound (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) (d : X) :
    normalize j p d ≤ ceiling X j := by
  apply (PairedSlotProfiles.normalize_le_ceiling hp d).trans
  apply ofOrd_le_ofOrd.mpr
  exact add_le_add (by gcongr; omega) le_rfl

private theorem normalized_proper (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) :
    ∀ d, normalize j p d ≠ ⊤ :=
  (CanonicalPairedProfiles.normalize_mem_inventory X j hp).2

private theorem cap_bounded {j : ℕ} {h : ExtOrd} (hh : SelfVis j h) :
    BoundedMap j (fun x : ExtOrd => min x h) where
  bot := min_eq_left bot_le
  mono := fun _ _ hxy => min_le_min_right _ hxy
  comm x k i hk hi := by
    rw [(extVisibilityReplace_mono k i hi).map_min,
      evr_eq_self_of_selfVis (selfVis_mono hh hk) i]

/-- At its birth grade, every catalogue leaf has a constructed faithful chart.
The rendered input need not itself have a catalogue entry. -/
theorem leaf_chart (n : ℕ) (a : Q (n + 2))
    (ha : ∀ d, fields (n + 2) a d ≠ ⊤)
    (haC : ∀ d, fields (n + 2) a d ≤ ceiling X (n + 2))
    (haS : ∀ d, Short (n + 2) (fields (n + 2) a d))
    {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 2) z) (hC : SelfVis (n + 2) C) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (n + 2)) τ ∧
      ∀ d, τ (raw ranks fields n (fields (n + 2) a) d) =
        min (render ranks fields (n + 1) p G C d)
          (render ranks fields (n + 1) p G C (.inr (.inr a))) := by
  let q := normalize (n + 2) p
  let h := cut (grid X (n + 2)) q (fields (n + 2) a)
  have hh : h ∈ grid X (n + 2) := cut_mem (sourceGrid_bot _ _) _ _
  have hag := raw_agreement ranks fields n (normalized_proper _ hp) ha
    (normalized_bound _ hp) haC hh (agree_cut (sourceGrid_bot _ _) _ _)
  let σ := (fun x : ExtOrd => min x h) ∘ trim (n + 2)
  have hσ : Witness (gTop (n + 2)) σ := (cap_bounded (sourceGrid_visible hh)).witness
  have hshort (d : Point X B Q (n + 1)) :
      Short (n + 2) (raw ranks fields n (fields (n + 2) a) d) :=
    raw_short ranks fields n haS d
  obtain ⟨τ, hτ, hread⟩ := comp_read hσ (PairedSlotDecoder.decode_witness hG hC) le_rfl
  refine ⟨τ, hτ, fun d => ?_⟩
  rw [hread _ (hshort d)]
  change PairedSlotDecoder.decode (n + 2) (values p) G C
    (min (trim (n + 2) (raw ranks fields n (fields (n + 2) a) d)) h) = _
  rw [trim_of_short (hshort d), ← hag d,
    (PairedSlotDecoder.decode_witness hG hC).mono.map_min,
    ← render_eq_decode ranks fields n hp hG hC d]
  rfl

/-- A leaf's native row stays literal through arbitrarily many later grades.
Only its source row is short; the inherited long rung rows are not flattened. -/
theorem inherited_leaf_chart (n t : ℕ) (a : Q (n + 2))
    (ha : ∀ d, fields (n + 2) a d ≠ ⊤)
    (haC : ∀ d, fields (n + 2) a d ≤ ceiling X (n + 2))
    (haS : ∀ d, Short (n + 2) (fields (n + 2) a d))
    {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + t + 2) z)
    (hC : SelfVis (n + t + 2) C) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (n + 2)) τ ∧
      ∀ d : Point X B Q (n + 1), τ (raw ranks fields n (fields (n + 2) a) d) =
        min (render ranks fields (n + 1 + t) p G C (raise t d))
          (render ranks fields (n + 1 + t) p G C (raise t (.inr (.inr a)))) := by
  induction t generalizing p G C with
  | zero =>
    simpa only [Nat.add_zero, raise_zero] using leaf_chart ranks fields n a ha haC haS hp hG hC
  | succ t ih =>
    have hj : n + (t + 1) + 2 = n + 1 + t + 2 := by omega
    have hG' : ∀ z ∈ G, SelfVis (n + 1 + t + 2) z := hj ▸ hG
    have hC' : SelfVis (n + 1 + t + 2) C := hj ▸ hC
    obtain ⟨σ, hσ, hs⟩ := ih (p := normalize (n + 1 + t + 2) p)
      (G := grid X (n + 1 + t + 2)) (C := ceiling X (n + 1 + t + 2))
      (normalized_proper (n + 1 + t + 2) hp)
      (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
    have hν := PairedSlotDecoder.decode_witness (S := values p) hG' hC'
    obtain ⟨τ, hτ, ht⟩ := comp_read hσ hν (by omega : n + 2 ≤ n + 1 + t + 2)
    refine ⟨τ, hτ, fun d => ?_⟩
    rw [ht _ (raw_short ranks fields n haS d), hs,
      hν.mono.map_min,
      render_raise_succ ranks fields (n := n + 1) t hp hG' hC' d,
      render_raise_succ ranks fields (n := n + 1) t hp hG' hC' (.inr (.inr a))]

def basePoint (n : ℕ) : RungMasterLocality.Master X B → Point X B Q n :=
  Sum.map id (baseAt n)

/-- The exact base formula includes original field columns as well as rungs. -/
theorem render_base_master (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hC : SelfVis (n + 1) C) (hb : ∀ d, p d ≤ C) (d : RungMasterLocality.Master X B) :
    render ranks fields n p G C (basePoint n d) = RungMasterLocality.table ranks p C d := by
  cases d with
  | inl d => rfl
  | inr v =>
    exact render_base ranks fields n hp hG hC hb v

/-- Long inherited rung charts use the direct table interpolation, not composition. -/
theorem inherited_rung_chart [Finite B] (n : ℕ) (c : Base X B)
    {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hv : ∀ d, SelfVis 1 (p d))
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hC : SelfVis (n + 1) C)
    (hb : ∀ d, p d ≤ C) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop 1) τ ∧
      ∀ d : RungMasterLocality.Master X B, τ (RungMasterLocality.row ranks c d) =
        min (render ranks fields n p G C (basePoint n d))
          (render ranks fields n p G C (basePoint n (.inr c))) := by
  obtain ⟨τ, hτ, _, hr⟩ := RungMasterLocality.exists_chart ranks c hv
    (selfVis_mono hC (by omega)) hb
  refine ⟨τ, hτ, fun d => ?_⟩
  rw [render_base_master ranks fields n hp hG hC hb,
    render_base_master ranks fields n hp hG hC hb]
  exact hr d

end
end VaughtConjecture.Knight.RecursiveRungLocality
