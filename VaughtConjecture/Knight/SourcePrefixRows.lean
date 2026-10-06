/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition

/-! # Common-grid rows with all lower-controller occurrences retained

The row-layer step of the coupled source-prefix construction. A finite grid
and boundary profiles determine every same-grade cross-reading. Previously
constructed lower sections are used once, as whole sections. Their grid
agreement is the grade-induction hypothesis, not assumed future locality.

This module constructs the new/new faithful incidences and full-index
availability. It does not claim the lower-section induction, geometric
installation, bountifulness, or maximal coatom supply.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SourcePrefixRows

open Transform Value ExtOrd

variable {X Y Q : Type*}

def Agree (a b : X → ExtOrd) (h : ExtOrd) : Prop :=
  ∀ x, min (a x) h = min (b x) h

theorem Agree.mono {a b : X → ExtOrd} {h c : ExtOrd}
    (hab : Agree a b h) (hc : c ≤ h) : Agree a b c := by
  intro x
  have hh := congrArg (fun z => min z c) (hab x)
  simpa only [min_assoc, min_eq_right hc] using hh

/-- Lift a scalar decoder comparison to all occurrences of two sections.
The comparison is needed only at actual common source values strictly below
their agreement cut. Values at or above the cut are handled by monotonicity.
This consumes, but does not assert existence of, the right-filled decoder
comparison required by the coupled construction. -/
theorem Agree.decode {a b : X → ExtOrd} {s h : ExtOrd} {ν μ : ExtOrd → ExtOrd}
    (hab : Agree a b s) (hν : Monotone ν) (hμ : Monotone μ)
    (hsν : h ≤ ν s) (hsμ : h ≤ μ s)
    (hcompare : ∀ d, a d < s → min (ν (a d)) h = min (μ (a d)) h) :
    Agree (fun d => ν (a d)) (fun d => μ (b d)) h := by
  intro d
  change min (ν (a d)) h = min (μ (b d)) h
  by_cases hd : a d < s
  · have hb : b d < s := by
      by_contra hn
      have he := hab d
      rw [min_eq_left hd.le, min_eq_right (le_of_not_gt hn)] at he
      exact (ne_of_lt hd) he
    have he := hab d
    rw [min_eq_left hd.le, min_eq_left hb.le] at he
    rw [← he]
    exact hcompare d hd
  · have ha : s ≤ a d := le_of_not_gt hd
    have hb : s ≤ b d := by
      have he := hab d
      rw [min_eq_right ha] at he
      exact he.trans_le (min_le_left _ _)
    rw [min_eq_right (hsν.trans (hν ha)), min_eq_right (hsμ.trans (hμ hb))]

open Classical in
noncomputable def cut (G : Finset ExtOrd) (a b : X → ExtOrd) : ExtOrd :=
  (G.filter (Agree a b)).sup id

theorem cut_le {G : Finset ExtOrd} {H : ExtOrd}
    (hG : ∀ h ∈ G, h ≤ H) (a b : X → ExtOrd) : cut G a b ≤ H := by
  classical
  apply Finset.sup_le
  intro h hh
  exact hG h (Finset.mem_filter.mp hh).1

theorem le_cut {G : Finset ExtOrd} {a b : X → ExtOrd} {h : ExtOrd}
    (hh : h ∈ G) (ha : Agree a b h) : h ≤ cut G a b := by
  classical
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hh, ha⟩)

theorem cut_mem {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    cut G a b ∈ G := by
  classical
  have hn : (G.filter (Agree a b)).Nonempty :=
    ⟨⊥, Finset.mem_filter.mpr ⟨hbot, fun _ => by simp⟩⟩
  obtain ⟨h, hh, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  change h = cut G a b at he
  exact he ▸ (Finset.mem_filter.mp hh).1

theorem agree_cut {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    Agree a b (cut G a b) := by
  classical
  have hn : (G.filter (Agree a b)).Nonempty :=
    ⟨⊥, Finset.mem_filter.mpr ⟨hbot, fun _ => by simp⟩⟩
  obtain ⟨h, hh, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  change h = cut G a b at he
  exact he ▸ (Finset.mem_filter.mp hh).2

theorem cut_symm {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    cut G a b = cut G b a := by
  apply le_antisymm
  · exact le_cut (cut_mem hbot a b) (fun x => (agree_cut hbot a b x).symm)
  · exact le_cut (cut_mem hbot b a) (fun x => (agree_cut hbot b a x).symm)

theorem cut_refl {G : Finset ExtOrd} {H : ExtOrd}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H) (a : X → ExtOrd) :
    cut G a a = H :=
  le_antisymm (cut_le hG a a) (le_cut hH (fun _ => rfl))

theorem cut_triangle {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b c : X → ExtOrd) :
    min (cut G a b) (cut G b c) ≤ cut G a c := by
  have hm : min (cut G a b) (cut G b c) ∈ G := by
    rcases le_total (cut G a b) (cut G b c) with h | h
    · simpa only [min_eq_left h] using cut_mem hbot a b
    · simpa only [min_eq_right h] using cut_mem hbot b c
  apply le_cut hm
  intro x
  exact ((agree_cut hbot a b).mono (min_le_left _ _) x).trans
    ((agree_cut hbot b c).mono (min_le_right _ _) x)

theorem cross_agreement {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b c : X → ExtOrd) :
    min (cut G a c) (cut G a b) = min (cut G b c) (cut G a b) := by
  apply le_antisymm
  · apply le_min _ (min_le_right _ _)
    have hh := cut_triangle hbot b a c
    rw [cut_symm hbot b a, min_comm] at hh
    exact hh
  · apply le_min _ (min_le_right _ _)
    simpa only [min_comm] using cut_triangle hbot a b c

/-- Proper cells, existing full lower controllers, and the new controllers
remain distinct occurrences. -/
abbrev Occ (X Y Q : Type*) := (X ⊕ Y) ⊕ Q

def grade (gx : X → ℕ) (gy : Y → ℕ) (k : ℕ) : Occ X Y Q → ℕ :=
  Sum.elim (Sum.elim gx gy) (fun _ => k)

noncomputable def row (G : Finset ExtOrd) (a : Q → X → ExtOrd)
    (lower : Q → Y → ExtOrd) (q : Q) : Occ X Y Q → ExtOrd
  | .inl (.inl x) => a q x
  | .inl (.inr y) => lower q y
  | .inr p => cut G (a q) (a p)

/-- This is precisely the lower-grade induction hypothesis consumed by
the row formula. No faithful incidence is included in it. -/
def GridCompatible (G : Finset ExtOrd) (a : Q → X → ExtOrd)
    (lower : Q → Y → ExtOrd) : Prop :=
  ∀ p q h, h ∈ G → Agree (a p) (a q) h → Agree (lower p) (lower q) h

theorem whole_agreement {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hlower : GridCompatible G a lower) (p q : Q) :
    Agree (row G a lower p) (row G a lower q) (cut G (a p) (a q)) := by
  intro d
  rcases d with (x | y) | r
  · exact agree_cut hbot (a p) (a q) x
  · exact hlower p q _ (cut_mem hbot _ _) (agree_cut hbot _ _) y
  · exact cross_agreement hbot (a p) (a q) (a r)

theorem whole_prefix {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hlower : GridCompatible G a lower) {p q : Q} {h : ExtOrd}
    (hh : h ∈ G) (ha : Agree (a p) (a q) h) :
    Agree (row G a lower p) (row G a lower q) h :=
  (whole_agreement hbot hlower p q).mono (le_cut hh ha)

theorem diagonal {G : Finset ExtOrd} {H : ExtOrd}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H)
    (a : Q → X → ExtOrd) (lower : Q → Y → ExtOrd) (q : Q) :
    row G a lower q (.inr q) = H := cut_refl hH hG _

theorem row_bound {G : Finset ExtOrd} {H : ExtOrd}
    (hG : ∀ h ∈ G, h ≤ H) {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (ha : ∀ q x, a q x ≤ H) (hl : ∀ q y, lower q y ≤ H)
    (q : Q) (d : Occ X Y Q) : row G a lower q d ≤ H := by
  rcases d with (x | y) | p
  · exact ha q x
  · exact hl q y
  · exact cut_le hG _ _

/-- Every requester is dominated by this row's own full-index controller.
The witness is an actual occurrence of the constructed row layer. -/
theorem full_availability {G : Finset ExtOrd} {H : ExtOrd}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (ha : ∀ q x, a q x ≤ H) (hl : ∀ q y, lower q y ≤ H)
    (q : Q) (d : Occ X Y Q) :
    ∃ p : Q, row G a lower q d ≤ row G a lower q (.inr p) := by
  refine ⟨q, ?_⟩
  rw [diagonal hH hG]
  exact row_bound hG ha hl q d

theorem grade_le {gx : X → ℕ} {gy : Y → ℕ} {k : ℕ}
    (hx : ∀ x, gx x ≤ k) (hy : ∀ y, gy y ≤ k) (d : Occ X Y Q) :
    grade gx gy k d ≤ k := by
  rcases d with (x | y) | q
  · exact hx x
  · exact hy y
  · exact le_rfl

theorem row_orderly {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {gx : X → ℕ} {gy : Y → ℕ} {k : ℕ}
    (hG : ∀ h ∈ G, SelfVis k h)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (ha : ∀ q x, SelfVis (gx x) (a q x))
    (hl : ∀ q y, SelfVis (gy y) (lower q y)) (q : Q) :
    ∀ d, SelfVis (grade gx gy k d) (row G a lower q d) := by
  intro d
  rcases d with (x | y) | p
  · exact ha q x
  · exact hl q y
  · exact hG _ (cut_mem hbot _ _)

/-- A direct identity-and-cap witness handles every new controller. The
target cap is its actual reading in the owning row, not the row ceiling. -/
theorem controller_locality {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {gx : X → ℕ} {gy : Y → ℕ} {k : ℕ}
    (hx : ∀ x, gx x ≤ k) (hy : ∀ y, gy y ≤ k)
    (hG : ∀ h ∈ G, SelfVis k h)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hlower : GridCompatible G a lower) (p q : Q) :
    TransformsTo (grade gx gy k) (row G a lower p)
      (fun d => min (row G a lower q d) (row G a lower q (.inr p))) := by
  have he : (fun d => min (row G a lower p d) (cut G (a q) (a p))) =
      (fun d => min (row G a lower q d) (cut G (a q) (a p))) :=
    funext fun d => (whole_agreement hbot hlower q p d).symm
  have ht := (TransformsTo.refl (grade := grade gx gy k) (row G a lower p)).cap
    (grade_le hx hy) (hG _ (cut_mem hbot (a q) (a p)))
  rw [he] at ht
  exact ht

/-- All new-controller incidences still hold after an arbitrary normalized
decoder. Shortness is needed only of the new source rows. The repaired
witness has clause 5 at all thresholds, not merely on observed sources. -/
theorem decoded_controller_locality {G : Finset ExtOrd} (hbot : ⊥ ∈ G)
    {gx : X → ℕ} {gy : Y → ℕ} {k K : ℕ}
    (hx : ∀ x, gx x ≤ k) (hy : ∀ y, gy y ≤ k) (hkK : k ≤ K)
    (hG : ∀ h ∈ G, SelfVis k h)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hlower : GridCompatible G a lower)
    (hshort : ∀ p d, SharpWitnessComposition.Short k (row G a lower p d))
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop K) ν) (p q : Q) :
    TransformsTo (grade gx gy k) (row G a lower p)
      (fun d => min (ν (row G a lower q d)) (ν (row G a lower q (.inr p)))) := by
  exact SharpWitnessComposition.map_capped_locality
    (c := (.inr p : Occ X Y Q)) (grade_le hx hy) hkK (hshort p)
    (hG _ (cut_mem hbot (a q) (a p)))
    (controller_locality hbot hx hy hG hlower p q) hν

theorem decoded_full_availability {G : Finset ExtOrd} {H : ExtOrd}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H)
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (ha : ∀ q x, a q x ≤ H) (hl : ∀ q y, lower q y ≤ H)
    {ν : ExtOrd → ExtOrd} (hν : Monotone ν) (q : Q) (d : Occ X Y Q) :
    ∃ p : Q, ν (row G a lower q d) ≤ ν (row G a lower q (.inr p)) := by
  obtain ⟨p, hp⟩ := full_availability hH hG ha hl q d
  exact ⟨p, hν hp⟩

/-! ## Boundary-orbit support and hidden prefixes

The support predicate records actual boundary occurrences, not merely a set
of numerical blocks. The lower section's support is an induction hypothesis;
the support of every new-controller reading follows from the row formula.
-/

/-- Values permitted in a supported section. In particular an invisible
auxiliary must be a boundary value or a replacement of one, unless it is
itself a designated grid point. -/
def Supported (G : Finset ExtOrd) (k : ℕ) (b : X → ExtOrd) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ x ∈ G ∨ (∃ d, x = b d) ∨
    ∃ d i, i ≤ k ∧ x = extVisibilityReplace (b d) k i

theorem row_supported {G : Finset ExtOrd} (hbot : ⊥ ∈ G) {k : ℕ}
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hl : ∀ q y, Supported G k (a q) (lower q y)) (q : Q) :
    ∀ d, Supported G k (a q) (row G a lower q d) := by
  intro d
  rcases d with (x | y) | p
  · exact Or.inr (Or.inr (Or.inl ⟨x, rfl⟩))
  · exact hl q y
  · exact Or.inr (Or.inl (cut_mem hbot _ _))

/-- A replacement strictly below a visible cut has its actual boundary
anchor strictly below that cut too. No order reflection of a decoder is
used here. -/
theorem anchor_lt_of_replace_lt {b h : ExtOrd} {k i : ℕ}
    (hh : SelfVis k h) (hb : extVisibilityReplace b k i < h) : b < h := by
  by_contra hn
  exact (not_le_of_gt hb) (le_extVisibilityReplace_of_selfVis_le hh (le_of_not_gt hn))

/-- Fixing the grid and the literal proper prefix fixes all supported
auxiliaries below the cut, even those invisible at the controller grade.
The orbit case uses clause 5, not an assumed action on hidden values. -/
theorem fixes_supported_prefix {G : Finset ExtOrd} {k : ℕ}
    {b : X → ExtOrd} {h x : ExtOrd} {ν : ExtOrd → ExtOrd}
    (hν : Witness (gTop k) ν) (hh : SelfVis k h)
    (hgrid : ∀ t ∈ G, t < h → ν t = t)
    (hboundary : ∀ d, b d < h → ν (b d) = b d)
    (hs : Supported G k b x) (hx : x < h) : ν x = x := by
  rcases hs with rfl | hxG | ⟨d, rfl⟩ | ⟨d, i, hi, rfl⟩
  · exact hν.bot
  · exact hgrid x hxG hx
  · exact hboundary d hx
  · rw [hν.clause5 (b d) k (by rw [gTop_of_le le_rfl]; exact le_top) i hi,
      hboundary d (anchor_lt_of_replace_lt hh hx)]

/-- A monotone decoder fixing supported values below the cut and not lowering
the cut preserves all capped readings of a supported section. This includes
bottom and literal top cuts, with no strict-positive-cap assumption. -/
theorem decode_supported_prefix {G : Finset ExtOrd} {k : ℕ}
    {b : X → ExtOrd} {s : Y → ExtOrd} {h : ExtOrd} {ν : ExtOrd → ExtOrd}
    (hν : Witness (gTop k) ν) (hh : SelfVis k h)
    (hgrid : ∀ t ∈ G, t < h → ν t = t)
    (hboundary : ∀ d, b d < h → ν (b d) = b d)
    (hcut : h ≤ ν h) (hs : ∀ d, Supported G k b (s d)) :
    Agree (fun d => ν (s d)) s h := by
  intro d
  change min (ν (s d)) h = min (s d) h
  by_cases hd : s d < h
  · rw [fixes_supported_prefix hν hh hgrid hboundary (hs d) hd]
  · have hle : h ≤ s d := le_of_not_gt hd
    rw [min_eq_right (hcut.trans (hν.mono hle)), min_eq_right hle]

/-- The precise source-prefix conclusion for the constructed row layer.
Literal boundary readback and agreement at every auxiliary follow from the
decoder's boundary equations and lower-grade support/grid compatibility.
Whole-domain lawfulness still needs the proper/lower incoming incidences;
this theorem does not assume or assert those unconstructed incidences. -/
theorem decoded_source_prefix {G : Finset ExtOrd} (hbot : ⊥ ∈ G) {k : ℕ}
    {a : Q → X → ExtOrd} {lower : Q → Y → ExtOrd}
    (hlower : GridCompatible G a lower)
    (hsupport : ∀ q y, Supported G k (a q) (lower q y))
    {p q : Q} {h : ExtOrd} (hhG : h ∈ G) (hh : SelfVis k h)
    (hpq : Agree (a p) (a q) h)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop k) ν)
    (hgrid : ∀ t ∈ G, t < h → ν t = t)
    (hboundary : ∀ d, a q d < h → ν (a q d) = a q d)
    (hcut : h ≤ ν h) {r : X → ExtOrd} (hread : ∀ d, ν (a q d) = r d) :
    (∀ d, ν (row G a lower q (.inl (.inl d))) = r d) ∧
      Agree (fun d => ν (row G a lower q d)) (row G a lower p) h := by
  refine ⟨hread, ?_⟩
  have hfix := decode_supported_prefix hν hh hgrid hboundary hcut
    (row_supported hbot hsupport q)
  intro d
  exact (hfix d).trans ((whole_prefix hbot hlower hhG hpq d).symm)

end VaughtConjecture.Knight.SourcePrefixRows
