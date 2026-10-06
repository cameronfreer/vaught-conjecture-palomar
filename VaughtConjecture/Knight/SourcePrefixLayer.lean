/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Installing one common-prefix controller layer

On an actual finite cell scheme, replace the rows at one maximal full-scope
grade by common-prefix rows. All other rows stay literal. The input profiles
are lawful only on the already constructed lower domains. The new-controller
incidences and their availability are constructed here, not input assumptions.

This is the row-installation half of the coupled grade induction. Existence
of the supported, grid-compatible selected lower profiles is still separate;
no full source-prefix extension or bountifulness theorem is claimed here.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SourcePrefixLayer

open Transform Value ExtOrd SourcePrefixRows

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

abbrev Controller (D : CellScheme A) (k : ℕ) := {c : Cell D // D.cell c = (A, k)}

/-- An old owner's entire lower domain is old. In particular no full-scope
controller at grade `k` has been smuggled into a proper face. -/
theorem below_old (hmax : ∀ d : Cell D, D.grade d ≤ k)
    {c : Cell D} (hc : D.cell c ≠ (A, k)) (d : D.below (D.cell c)) :
    D.cell d.1 ≠ (A, k) := by
  intro hd
  apply hc
  apply Prod.ext
  · apply Finset.Subset.antisymm (D.isPlan.subset_of_mem (D.scope_mem_plan c))
    change A ⊆ (D.cell c).1
    simpa only [hd] using d.2.1
  · apply le_antisymm (hmax c)
    change k ≤ (D.cell c).2
    simpa only [hd] using d.2.2

/-- The actual lower-domain input to one grade step. `lower_lawful` concerns
only old owners. `grid_agreement` is the grid-agreement invariant of the already
constructed whole lower sections, not new-row locality or future completion.
The new-controller source readings are not fields: `profile` constructs them.
-/
structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  max_grade : ∀ d : Cell D, D.grade d ≤ k
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → Cell D → ExtOrd
  lower_bound : ∀ q d, D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.cell c ≠ (A, k) →
    RespectsSemanticsBelow base (D.cell c) (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

namespace Data

variable (F : Data D k X)

noncomputable def profile (q : Controller D k) (d : Cell D) : ExtOrd :=
  if hd : D.cell d = (A, k) then cut F.grid (F.boundary q) (F.boundary ⟨d, hd⟩)
  else F.lower q d

theorem profile_old (q : Controller D k) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    F.profile q d = F.lower q d := by simp only [profile, hd, ↓reduceDIte]

theorem profile_new (q p : Controller D k) :
    F.profile q p.1 = cut F.grid (F.boundary q) (F.boundary p) := by
  simp only [profile, p.2, ↓reduceDIte]

theorem profile_diagonal (q : Controller D k) : F.profile q q.1 = F.ceiling := by
  rw [F.profile_new]
  exact cut_refl F.ceiling_mem F.grid_bound _

theorem profile_bound (q : Controller D k) (d : Cell D) : F.profile q d ≤ F.ceiling := by
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new]
    exact cut_le F.grid_bound _ _
  · rw [F.profile_old q hd]
    exact F.lower_bound q d hd

theorem profile_visible (q : Controller D k) (d : Cell D) :
    SelfVis (D.grade d) (F.profile q d) := by
  by_cases hd : D.cell d = (A, k)
  · have hg : D.grade d = k := congrArg Prod.snd hd
    rw [hg, show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new]
    exact F.grid_visible _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q hd]
    exact ((F.lower_lawful q d hd).orderly ⟨d, GradedLe.refl _⟩).symm

theorem profile_agreement (q p : Controller D k) :
    Agree (F.profile q) (F.profile p) (cut F.grid (F.boundary q) (F.boundary p)) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new, F.profile_new]
    exact cross_agreement F.bot_mem _ _ _
  · rw [F.profile_old q hd, F.profile_old p hd]
    exact F.grid_agreement q p _ (cut_mem F.bot_mem _ _) (agree_cut F.bot_mem _ _) d hd

theorem profile_prefix {p q : Controller D k} {h : ExtOrd}
    (hh : h ∈ F.grid) (hpq : Agree (F.boundary p) (F.boundary q) h) :
    Agree (F.profile p) (F.profile q) h :=
  (F.profile_agreement p q).mono (le_cut hh hpq)

/-- Shortness of new rows is proved entry by entry, not imposed as a new-row
locality assumption. Only the selected old part and source grid are inputs. -/
theorem profile_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d)) (q : Controller D k) :
    ∀ d, SharpWitnessComposition.Short k (F.profile q d) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new]
    exact hgrid _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q hd]
    exact hlower q d hd

theorem profile_supported
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      Supported F.grid k (F.boundary q) (F.lower q d)) (q : Controller D k) :
    ∀ d, Supported F.grid k (F.boundary q) (F.profile q d) := by
  intro d
  by_cases hd : D.cell d = (A, k)
  · rw [show d = (⟨d, hd⟩ : Controller D k).1 from rfl, F.profile_new]
    exact Or.inr (Or.inl (cut_mem F.bot_mem _ _))
  · rw [F.profile_old q hd]
    exact hlower q d hd

/-- The scalar comparison gives whole-section grid compatibility, including
every lower and new controller. This is the implication used to close the
next grade's invariant once the right-filled decoders have been constructed.
-/
theorem decoded_profiles_agree
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d))
    (p q : Controller D k) {ν μ : ExtOrd → ExtOrd} {h : ExtOrd}
    (hν : Monotone ν) (hμ : Monotone μ)
    (hp : h ≤ ν (cut F.grid (F.boundary p) (F.boundary q)))
    (hq : h ≤ μ (cut F.grid (F.boundary p) (F.boundary q)))
    (hcompare : ∀ x, SharpWitnessComposition.Short k x →
      x < cut F.grid (F.boundary p) (F.boundary q) → min (ν x) h = min (μ x) h) :
    Agree (fun d => ν (F.profile p d)) (fun d => μ (F.profile q d)) h :=
  (F.profile_agreement p q).decode hν hμ hp hq
    (fun d hd => hcompare _ (F.profile_short hgrid hlower p d) hd)

noncomputable def rows : Semantics D where
  E c d := if hc : D.cell c = (A, k) then F.profile ⟨c, hc⟩ d.1 else F.base.E c d
  orderly c d := by
    dsimp only
    split_ifs with hc
    · exact (F.profile_visible ⟨c, hc⟩ d.1).symm
    · exact F.base.orderly c d

theorem row_old {c : Cell D} (hc : D.cell c ≠ (A, k)) : F.rows.E c = F.base.E c := by
  funext d
  simp only [rows, hc, ↓reduceDIte]

theorem row_new (q : Controller D k) (d : D.below (D.cell q.1)) :
    F.rows.E q.1 d = F.profile q d.1 := by
  simp only [rows, q.2, ↓reduceDIte]

/-- Full-source shortness propagates from the preceding layers. -/
theorem full_source_short
    (hgrid : ∀ h ∈ F.grid, SharpWitnessComposition.Short k h)
    (hlower : ∀ q d, D.cell d ≠ (A, k) →
      SharpWitnessComposition.Short k (F.lower q d))
    (hbase : ∀ c : Cell D, D.scope c = A → D.cell c ≠ (A, k) →
      ∀ d : D.below (D.cell c), SharpWitnessComposition.Short (D.grade c) (F.base.E c d)) :
    ∀ c : Cell D, D.scope c = A → ∀ d : D.below (D.cell c),
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d) := by
  intro c hs d
  by_cases hc : D.cell c = (A, k)
  · have he : F.rows.E c d = F.profile ⟨c, hc⟩ d.1 := F.row_new ⟨c, hc⟩ d
    rw [he, show D.grade c = k from congrArg Prod.snd hc]
    exact F.profile_short hgrid hlower ⟨c, hc⟩ d.1
  · rw [F.row_old hc]
    exact hbase c hs hc d

/-- Respect on each old lower domain is literally unchanged. -/
theorem old_respects_iff {c : Cell D} (hc : D.cell c ≠ (A, k))
    {r : D.below (D.cell c) → ExtOrd} :
    RespectsSemanticsBelow F.rows (D.cell c) r ↔
      RespectsSemanticsBelow F.base (D.cell c) r := by
  constructor <;> intro hr <;> refine ⟨hr.orderly, ?_, hr.availability⟩
  · intro d
    simpa only [F.row_old (below_old F.max_grade hc d)] using hr.locality d
  · intro d
    rw [F.row_old (below_old F.max_grade hc d)]
    exact hr.locality d

/-- Locality at every newly installed controller, using its actual
cross-reading as cap. The identity-and-cap witness covers the whole lower
domain, including every previously installed auxiliary. -/
theorem new_locality (q p : Controller D k) :
    TransformsTo (fun d : D.below (D.cell p.1) => D.grade d.1)
      (F.rows.E p.1) (fun d => min (F.profile q d.1) (F.profile q p.1)) := by
  have ht := (TransformsTo.refl
    (grade := fun d : D.below (D.cell p.1) => D.grade d.1) (F.rows.E p.1)).cap
    (fun d => F.max_grade d.1)
    (F.grid_visible _ (cut_mem F.bot_mem (F.boundary q) (F.boundary p)))
  have he : (fun d : D.below (D.cell p.1) =>
      min (F.rows.E p.1 d) (cut F.grid (F.boundary q) (F.boundary p))) =
      (fun d => min (F.profile q d.1) (F.profile q p.1)) := by
    funext d
    rw [F.row_new, F.profile_new]
    exact (F.profile_agreement q p d.1).symm
  rwa [he] at ht

/-- A constructed whole row is lawful on the actual carrier. Old-target
availability is taken from that target's lawful lower section; new-target
availability uses the row's own diagonal controller inside the target.
No whole-section lawfulness is assumed. -/
theorem profile_respects (q : Controller D k) : RespectsSemantics F.rows (F.profile q) where
  orderly d := (F.profile_visible q d).symm
  locality c := by
    by_cases hc : D.cell c = (A, k)
    · exact F.new_locality q ⟨c, hc⟩
    · have ht := (F.lower_lawful q c hc).locality ⟨c, GradedLe.refl _⟩
      simpa only [F.row_old hc, F.profile_old q hc,
        F.profile_old q (below_old F.max_grade hc _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    by_cases ht : D.cell t = (A, k)
    · refine ⟨q.1, q.2.trans ht.symm, ?_⟩
      rw [F.profile_diagonal]
      exact F.profile_bound q c
    · have hc : GradedLe (D.cell c) (D.cell t) := ⟨hs, hg.le⟩
      obtain ⟨w, hw, hle⟩ := (F.lower_lawful q t ht).availability
        ⟨c, hc⟩ ⟨t, GradedLe.refl _⟩ hs hg
      refine ⟨w.1, hw, ?_⟩
      simpa only [F.profile_old q (below_old F.max_grade ht ⟨c, hc⟩),
        F.profile_old q (below_old F.max_grade ht w)] using hle

/-- The actual one-layer consistency constructor. It consumes consistency
only at old owners, never a consistency assumption for the rows it creates. -/
theorem consistent
    (hbase : ∀ c : Cell D, D.cell c ≠ (A, k) →
      RespectsSemanticsBelow F.base (D.cell c) (F.base.E c)) : F.rows.IsConsistent := by
  intro c
  by_cases hc : D.cell c = (A, k)
  · let q : Controller D k := ⟨c, hc⟩
    have hp := F.profile_respects q
    have he : F.rows.E q.1 = fun d => F.profile q d.1 := funext (F.row_new q)
    change RespectsSemanticsBelow F.rows (D.cell q.1) (F.rows.E q.1)
    refine ⟨F.rows.orderly c, ?_, ?_⟩
    · intro d
      simpa only [he, CellScheme.below.incl] using hp.locality d.1
    · intro d t hs hg
      obtain ⟨w, hw, hle⟩ := hp.availability d.1 t.1 hs hg
      refine ⟨⟨w, ?_⟩, hw, ?_⟩
      · rw [hw]
        exact t.2
      · simpa only [he] using hle
  · rw [F.row_old hc]
    exact (F.old_respects_iff hc).mpr (hbase c hc)

/-- Decode a constructed row without assuming that protected proper rows
are short. Proper-owner locality comes from the literal decoded boundary.
All full-scope source rows are grade-short by the coupled construction, so
the repaired composition theorem supplies their faithful witnesses, including
clause 5 at every threshold. Availability is transported on actual indices.
-/
theorem decoded_respects (q : Controller D k) {K : ℕ} (hkK : k ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop K) ν)
    (hproper : ∀ c : Cell D, D.scope c ≠ A →
      RespectsSemanticsBelow F.base (D.cell c) (fun d => ν (F.lower q d.1)))
    (hshort : ∀ c : Cell D, D.scope c = A → ∀ d : D.below (D.cell c),
      SharpWitnessComposition.Short (D.grade c) (F.rows.E c d)) :
    RespectsSemantics F.rows (fun d => ν (F.profile q d)) where
  orderly d := by
    have h := hν.clause5 (F.profile q d) (D.grade d)
      (by rw [gTop_of_le ((F.max_grade d).trans hkK)]; exact le_top) (D.grade d) le_rfl
    rwa [F.profile_visible q d] at h
  locality c := by
    by_cases hc : D.scope c = A
    · exact SharpWitnessComposition.map_capped_locality
        (grade := fun d : D.below (D.cell c) => D.grade d.1)
        (c := (⟨c, GradedLe.refl _⟩ : D.below (D.cell c)))
        (p := fun d : D.below (D.cell c) => F.profile q d.1) (fun d => d.2.2)
        ((F.max_grade c).trans hkK) (hshort c hc) (F.profile_visible q c)
        ((F.profile_respects q).locality c) hν
    · have hc' : D.cell c ≠ (A, k) := fun he => hc (congrArg Prod.fst he)
      have ht := (hproper c hc).locality ⟨c, GradedLe.refl _⟩
      simpa only [F.row_old hc', F.profile_old q hc',
        F.profile_old q (below_old F.max_grade hc' _), CellScheme.below.incl] using ht
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := (F.profile_respects q).availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

/-- The hidden-prefix conclusion on actual occurrences. Lower support is
used only to fix hidden sub-cut values; all cross-controller values are
already supported by their membership in the constructed source grid. -/
theorem decoded_prefix
    (hsupport : ∀ q d, D.cell d ≠ (A, k) →
      Supported F.grid k (F.boundary q) (F.lower q d))
    {p q : Controller D k} {h : ExtOrd} (hh : h ∈ F.grid)
    (hpq : Agree (F.boundary p) (F.boundary q) h)
    {ν : ExtOrd → ExtOrd} (hν : Witness (gTop k) ν)
    (hgrid : ∀ t ∈ F.grid, t < h → ν t = t)
    (hboundary : ∀ d, F.boundary q d < h → ν (F.boundary q d) = F.boundary q d)
    (hcut : h ≤ ν h) :
    Agree (fun d => ν (F.profile q d)) (F.profile p) h := by
  have hfix := decode_supported_prefix hν (F.grid_visible h hh) hgrid hboundary hcut
    (F.profile_supported hsupport q)
  intro d
  exact (hfix d).trans ((F.profile_prefix hh hpq d).symm)

end Data

end VaughtConjecture.Knight.SourcePrefixLayer
