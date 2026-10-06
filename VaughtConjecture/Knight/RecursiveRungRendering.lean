/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungTableRendering
public import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Recursive raw rows and rendered prefixes over the long rung base

Stage `n` retains the entire rung base and the leaf catalogues of grades
2 through `n + 1`. The catalogue and every occurrence are fixed before an
input is rendered. Raw rows use the previous renderer at the new native grid;
rendered vectors apply one outer paired-slot decoder to the normalized row.

The prefix theorem is proved by grade induction, not carried as a field of
an invariant. Support follows from the outer decoder. The exact base formula
includes every unused rung and follows from whole-table decoding.

These are numerical master vectors, including complete original fields. No
admission, geometric installation, consistency, or bountifulness is asserted.
In particular, retaining the occurrence type does not assert equality of
independently selected renderings at different construction grades.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RecursiveRungRendering
open Transform Value ExtOrd SourcePrefixRows
open PairedSlotEncoding PairedSlotComparison
noncomputable section

universe u v
variable {X : Type u} {B : Type v} [Fintype X] {Q : ℕ → Type v}

abbrev height (X : Type*) [Fintype X] : ℕ := Fintype.card X + 1
abbrev Base (X B : Type*) [Fintype X] := RungOnlyLadder.Point (height X) B

/-- Every earlier leaf and every base rung stays a separate coordinate. -/
def Aux (X : Type u) (B : Type v) [Fintype X] (Q : ℕ → Type v) : ℕ → Type v
  | 0 => Base X B
  | n + 1 => Aux X B Q n ⊕ Q (n + 2)

instance [Fintype B] [∀ j, Fintype (Q j)] (n : ℕ) : Fintype (Aux X B Q n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Base X B))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Aux X B Q n ⊕ Q (n + 2)))

abbrev Point (X : Type u) (B : Type v) [Fintype X] (Q : ℕ → Type v) (n : ℕ) :=
  X ⊕ Aux X B Q n
abbrev grid (X : Type*) [Fintype X] (j : ℕ) := sourceGrid j (Fintype.card X)
abbrev ceiling (X : Type*) [Fintype X] (j : ℕ) := CanonicalFieldLayer.ceiling j X

def baseAt : (n : ℕ) → Base X B → Aux X B Q n
  | 0, v => v
  | n + 1, v => .inl (baseAt n v)

variable (ranks : B → X → ℕ) (fields : (j : ℕ) → Q j → X → ExtOrd)

/-- Native lower calls use the upper profile's own numerical values. -/
def renderAux : (n : ℕ) → (X → ExtOrd) → Finset ExtOrd → ExtOrd → Aux X B Q n → ExtOrd
  | 0, p, _, C, v => RungTableRendering.render ranks p C v
  | n + 1, p, G, C, v =>
    PairedSlotDecoder.decode (n + 2) (values p) G C
      (Sum.elim
        (renderAux n (normalize (n + 2) p) (grid X (n + 2)) (ceiling X (n + 2)))
        (fun q => cut (grid X (n + 2)) (normalize (n + 2) p) (fields (n + 2) q)) v)

def rawAux (n : ℕ) (a : X → ExtOrd) : Aux X B Q (n + 1) → ExtOrd :=
  Sum.elim (renderAux ranks fields n a (grid X (n + 2)) (ceiling X (n + 2)))
    (fun q => cut (grid X (n + 2)) a (fields (n + 2) q))

def render (n : ℕ) (p : X → ExtOrd) (G : Finset ExtOrd) (C : ExtOrd) :
    Point X B Q n → ExtOrd := Sum.elim p (renderAux ranks fields n p G C)

def raw (n : ℕ) (a : X → ExtOrd) : Point X B Q (n + 1) → ExtOrd :=
  Sum.elim a (rawAux ranks fields n a)

theorem renderAux_succ (n : ℕ) (p : X → ExtOrd) (G : Finset ExtOrd) (C : ExtOrd)
    (v : Aux X B Q (n + 1)) :
    renderAux ranks fields (n + 1) p G C v =
      PairedSlotDecoder.decode (n + 2) (values p) G C
        (rawAux ranks fields n (normalize (n + 2) p) v) := rfl

theorem render_field (n : ℕ) (p : X → ExtOrd) (G : Finset ExtOrd) (C : ExtOrd) (d : X) :
    render ranks fields n p G C (.inl d) = p d := rfl

theorem raw_lower (n : ℕ) (a : X → ExtOrd) (v : Aux X B Q n) :
    rawAux ranks fields n a (.inl v) =
      renderAux ranks fields n a (grid X (n + 2)) (ceiling X (n + 2)) v := rfl

private theorem normalized_bound (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) (d : X) :
    normalize j p d ≤ ceiling X j := by
  apply (PairedSlotProfiles.normalize_le_ceiling hp d).trans
  apply ofOrd_le_ofOrd.mpr
  exact add_le_add (by gcongr; omega) le_rfl

private theorem normalized_proper (j : ℕ) {p : X → ExtOrd} (hp : ∀ d, p d ≠ ⊤) :
    ∀ d, normalize j p d ≠ ⊤ :=
  (CanonicalPairedProfiles.normalize_mem_inventory X j hp).2

omit [Fintype X] in
private theorem cut_prefix {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {p q : X → ExtOrd} {h : ExtOrd} (hh : h ∈ G) (hag : Agree p q h) (r : X → ExtOrd) :
    min (cut G p r) h = min (cut G q r) h := by
  have he := congrArg (fun x => min x h) (cross_agreement hbot p q r)
  simpa only [min_assoc, min_eq_right (le_cut hh hag)] using he

/-- The two halves of PREFIX are composed in the successor case. The only
recursive call is the previous grade's already proved rendered prefix. -/
theorem renderAux_agreement (n : ℕ) {p q : X → ExtOrd} {G : Finset ExtOrd} {C h : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hC : SelfVis (n + 1) C)
    (hpC : ∀ d, p d ≤ C) (hqC : ∀ d, q d ≤ C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (renderAux ranks fields n p G C) (renderAux ranks fields n q G C) h := by
  induction n generalizing p q G C h with
  | zero => exact RungTableRendering.render_agreement ranks le_rfl hpC hqC hhC hag
  | succ n ih =>
    obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ :=
      exists_common_cut hG hC hC hh hhC hhC hp hq hag
    have hraw : Agree (rawAux ranks fields n (normalize (n + 2) p))
        (rawAux ranks fields n (normalize (n + 2) q)) e := by
      intro v
      cases v with
      | inl v =>
        exact ih (normalized_proper _ hp) (normalized_proper _ hq)
          (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
          (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
          (normalized_bound _ hp) (normalized_bound _ hq) heG
          (CanonicalFieldLayer.grid_bound _ _ heG) he v
      | inr a => exact cut_prefix (sourceGrid_bot _ _) heG he (fields (n + 2) a)
    exact hraw.decode (PairedSlotDecoder.decode_witness hG hC).mono
      (PairedSlotDecoder.decode_witness hG hC).mono hpe hqe (fun _ _ => hcompare _)

theorem render_agreement (n : ℕ) {p q : X → ExtOrd} {G : Finset ExtOrd} {C h : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hC : SelfVis (n + 1) C)
    (hpC : ∀ d, p d ≤ C) (hqC : ∀ d, q d ≤ C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (render ranks fields n p G C) (render ranks fields n q G C) h := by
  intro v
  cases v with
  | inl d => exact hag d
  | inr v => exact renderAux_agreement ranks fields n hp hq hG hC hpC hqC hh hhC hag v

/-- Raw agreement is derived on the entire master vector, including each leaf. -/
theorem raw_agreement (n : ℕ) {p q : X → ExtOrd} {h : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hq : ∀ d, q d ≠ ⊤)
    (hpC : ∀ d, p d ≤ ceiling X (n + 2)) (hqC : ∀ d, q d ≤ ceiling X (n + 2))
    (hh : h ∈ grid X (n + 2)) (hag : Agree p q h) :
    Agree (raw ranks fields n p) (raw ranks fields n q) h := by
  intro v
  rcases v with d | (v | a)
  · exact hag d
  · exact renderAux_agreement ranks fields n hp hq
      (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
      hpC hqC hh (CanonicalFieldLayer.grid_bound _ _ hh) hag v
  · exact cut_prefix (sourceGrid_bot _ _) hh hag (fields (n + 2) a)

/-- Original readback and numerical decoding agree, including at every auxiliary. -/
theorem render_eq_decode (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 2) z) (hC : SelfVis (n + 2) C)
    (v : Point X B Q (n + 1)) :
    render ranks fields (n + 1) p G C v =
      PairedSlotDecoder.decode (n + 2) (values p) G C
        (raw ranks fields n (normalize (n + 2) p) v) := by
  cases v with
  | inl d => exact (PairedSlotDecoder.decode_normalize hG hC hp d).symm
  | inr v => rfl

theorem renderAux_bound (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hC : SelfVis (n + 1) C) (hpC : ∀ d, p d ≤ C) (v : Aux X B Q n) :
    renderAux ranks fields n p G C v ≤ C := by
  cases n with
  | zero => exact RungTableRendering.render_bound ranks hpC v
  | succ n =>
    apply PairedSlotDecoder.decode_le hC
    intro a ha
    obtain ⟨d, hd⟩ := PairedSlotEncoding.mem_values.mp ha
    simpa only [hd] using hpC d

omit [Fintype X] in
private theorem field_supported {K : ℕ} {G : Set ExtOrd} {p : X → ExtOrd} (d : X) :
    OrbitPrefixSupport.Supported K G p (p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inr ⟨d, K, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
  · by_cases hk : finitePart a < K
    · exact Or.inr (Or.inr ⟨d, finitePart a, hk.le, by
        rw [ha, extVisibilityReplace_of_finitePart_lt hk, limitPart_add_finitePart]⟩)
    · exact Or.inr (Or.inr ⟨d, K, le_rfl, by
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)]⟩)

/-- Support of higher coordinates comes directly from the one outer decoder. -/
theorem render_supported (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    {K : ℕ} (hnK : n + 1 ≤ K) (hCG : C ∈ G) (v : Point X B Q n) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (render ranks fields n p G C v) := by
  cases v with
  | inl d => exact field_supported d
  | inr v =>
    cases n with
    | zero =>
      rcases RungTableRendering.render_supported ranks p C v with hz | ⟨d, hd⟩ | hc
      · exact Or.inl hz
      · rw [show render ranks fields 0 p G C (.inr v) = p d from hd]
        exact field_supported d
      · change OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
          (RungTableRendering.render ranks p C v)
        rw [hc]
        exact Or.inr (Or.inl hCG)
    | succ n => exact PairedSlotDecoder.decode_supported hnK hCG _

/-- BASE-FORM: the entire base restriction is the original ceiling-filled
table. No cross-grade identity on the higher leaves is used or asserted. -/
theorem render_base (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hC : SelfVis (n + 1) C) (hpC : ∀ d, p d ≤ C) (v : Base X B) :
    renderAux ranks fields n p G C (baseAt n v) = RungTableRendering.render ranks p C v := by
  induction n generalizing p G C with
  | zero => rfl
  | succ n ih =>
    change PairedSlotDecoder.decode (n + 2) (values p) G C
      (renderAux ranks fields n (normalize (n + 2) p)
        (grid X (n + 2)) (ceiling X (n + 2)) (baseAt n v)) = _
    rw [ih (p := normalize (n + 2) p) (G := grid X (n + 2))
      (C := ceiling X (n + 2)) (normalized_proper _ hp)
      (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
      (normalized_bound _ hp)]
    exact RungTableRendering.decode_normalized ranks (n + 2) p hp hG hC
      (decode_reserved_ceiling hC hpC) v

/-- The long base is lawful by its exact table, not by unrestricted composition. -/
theorem render_base_lawful [Finite B] (n : ℕ) (a : B) {p : X → ExtOrd}
    {G : Finset ExtOrd} {C : ExtOrd} (ha : ranks a = LadderScalarRendering.fieldRank p)
    (hp : ∀ d, p d ≠ ⊤) (hv : ∀ d, SelfVis 1 (p d))
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hC : SelfVis (n + 1) C)
    (hpC : ∀ d, p d ≤ C) :
    RungOnlyLadder.Lawful ranks (fun v => renderAux ranks fields n p G C (baseAt n v)) := by
  have he := funext (render_base ranks fields n hp hG hC hpC)
  rw [he]
  exact RungTableRendering.render_lawful ranks a ha hv (selfVis_mono hC (by omega)) hpC

/-- Every base anchor retains its spare tip; a matching anchor reads the ceiling. -/
theorem render_base_ceiling (n : ℕ) (a : B) {p : X → ExtOrd}
    {G : Finset ExtOrd} {C : ExtOrd} (ha : ranks a = LadderScalarRendering.fieldRank p)
    (hp : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hC : SelfVis (n + 1) C) (hpC : ∀ d, p d ≤ C) :
    renderAux ranks fields n p G C (baseAt n (a, Fin.last (Fintype.card X))) = C := by
  rw [render_base ranks fields n hp hG hC hpC]
  simp only [RungTableRendering.render, ha, FiniteProfileControllers.cut_refl,
    Fin.val_last, height, min_self]
  exact ite_eq_left (Nat.lt_succ_of_le (LadderScalarRendering.values_card_le p))

theorem raw_bound (n : ℕ) {p : X → ExtOrd}
    (hpC : ∀ d, p d ≤ ceiling X (n + 2)) (v : Point X B Q (n + 1)) :
    raw ranks fields n p v ≤ ceiling X (n + 2) := by
  rcases v with d | (v | a)
  · exact hpC d
  · exact renderAux_bound ranks fields n
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega)) hpC v
  · exact cut_le (fun _ hh => CanonicalFieldLayer.grid_bound _ _ hh) _ _

theorem raw_supported (n : ℕ) (p : X → ExtOrd) (v : Point X B Q (n + 1)) :
    OrbitPrefixSupport.Supported (n + 2) (grid X (n + 2) : Set ExtOrd) p
      (raw ranks fields n p v) := by
  rcases v with d | (v | a)
  · exact field_supported d
  · exact render_supported ranks fields n (by omega) (sourceGrid_endpoint le_rfl) (.inr v)
  · exact Or.inr (Or.inl (cut_mem (sourceGrid_bot _ _) _ _))

/-- Only the higher native rows are shown short at their own grade.
The long grade-one table is deliberately not covered by this statement. -/
theorem raw_short (n : ℕ) {p : X → ExtOrd}
    (hp : ∀ d, SharpWitnessComposition.Short (n + 2) (p d))
    (v : Point X B Q (n + 1)) : SharpWitnessComposition.Short (n + 2) (raw ranks fields n p v) :=
  PairedCoupledSections.supported_short (fun _ hh => CanonicalFieldLayer.grid_short _ _ hh)
    hp (raw_supported ranks fields n p v)

theorem raw_diagonal (n : ℕ) (a : Q (n + 2)) :
    raw ranks fields n (fields (n + 2) a) (.inr (.inr a)) = ceiling X (n + 2) :=
  cut_refl (sourceGrid_endpoint le_rfl) (fun _ hh => CanonicalFieldLayer.grid_bound _ _ hh) _

/-- New-controller locality follows from the derived raw prefix at its actual
cross-reading. This is one incidence class, not whole native consistency. -/
theorem raw_controller_locality (n : ℕ) (a b : Q (n + 2))
    (grade : Point X B Q (n + 1) → ℕ) (hg : ∀ d, grade d ≤ n + 2)
    (ha : ∀ d, fields (n + 2) a d ≠ ⊤) (hb : ∀ d, fields (n + 2) b d ≠ ⊤)
    (haC : ∀ d, fields (n + 2) a d ≤ ceiling X (n + 2))
    (hbC : ∀ d, fields (n + 2) b d ≤ ceiling X (n + 2)) :
    TransformsTo grade (raw ranks fields n (fields (n + 2) a))
      (fun d => min (raw ranks fields n (fields (n + 2) b) d)
        (raw ranks fields n (fields (n + 2) b) (.inr (.inr a)))) := by
  have hm := cut_mem (sourceGrid_bot (n + 2) (Fintype.card X))
    (fields (n + 2) b) (fields (n + 2) a)
  have he := raw_agreement ranks fields n hb ha hbC haC hm
    (agree_cut (sourceGrid_bot _ _) _ _)
  have ht := (TransformsTo.refl (grade := grade) (raw ranks fields n (fields (n + 2) a))).cap
    hg (sourceGrid_visible hm)
  convert ht using 1
  exact funext (fun d => he d)

/-- An actual catalogue entry for the normalized profile supplies the upper ceiling. -/
theorem render_leaf_ceiling (n : ℕ) {p : X → ExtOrd} {G : Finset ExtOrd} {C : ExtOrd}
    (a : Q (n + 2)) (ha : fields (n + 2) a = normalize (n + 2) p)
    (hC : SelfVis (n + 2) C) (hpC : ∀ d, p d ≤ C) :
    renderAux ranks fields (n + 1) p G C (.inr a) = C := by
  change PairedSlotDecoder.decode (n + 2) (values p) G C
    (cut (grid X (n + 2)) (normalize (n + 2) p) (fields (n + 2) a)) = C
  rw [ha, cut_refl (sourceGrid_endpoint le_rfl)
    (fun _ hh => CanonicalFieldLayer.grid_bound _ _ hh)]
  exact decode_reserved_ceiling hC hpC

end
end VaughtConjecture.Knight.RecursiveRungRendering
