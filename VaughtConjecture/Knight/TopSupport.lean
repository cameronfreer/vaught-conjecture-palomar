/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceOnlyCompositionRepair
public import VaughtConjecture.Knight.RelativeTailFloor
public import VaughtConjecture.Knight.CappedCore

/-! # The finite top-support criterion

The reviewer's notes20 §2 / plan34 §2 (2026-09-19): after the proper labels of a lawful
section `P` are fixed, the remaining ambiguity about which `⊤`-labelled cells stay top has a
finite description.

For `H` a set of top cells of `P` and a proper `β` above every proper label of `P` and visible
at the maximum grade, the **uniform lowering** `lower P H β` keeps every non-top label, keeps
`⊤` on `H`, and replaces `⊤` by `β` off `H`.  It is lawful exactly when

* **top availability** (`TopAvailable`): a surviving top has a surviving top owner at every
  larger same-grade index, and
* **source separation** (`SourceSeparated`): beneath every surviving top owner `c` of grade
  `k`, the rounded source `R_k(E_c(d))` of every lowered top `d` lies strictly below the source
  `E_c(a)` of every surviving top `a` (the diagonal `a = c` included).

**Necessity** (`admissible_of_respects`) holds for an arbitrary lawful `Q` fixing the non-top
labels of `P`, with `H` the actual top set of `Q`: at a surviving top owner the normalized
witness sends surviving top sources to `⊤`, lowered sources to their non-top labels, and
rounded lowered sources to rounded non-top labels, so monotonicity forbids
`E_c(a) ≤ R_k(E_c(d))`.  **Sufficiency** (`respects_lower`) is proved per owner: a proper or
bottom owner sees a literally unchanged locality target; a lowered owner sees the old target
capped at `β`; a surviving owner gets a **retuned witness** — the old normalized witness capped
at `β` below the visible cut `t_c = max R_k(E_c(d))` over the lowered tops beneath `c`, and
unchanged above it.  The retuned map is a bounded map at grade `k` with the bottom fibre of the
old witness (`β` is positive), so the source-block interpolation criterion
(`interpolate_iff_source_blocks`) supplies a faithful witness; long rows and several owners at
one index need nothing extra, and an empty cut collapses the retuned map to the old witness.
It is *not* a scalar post-composition of the old witness, since two sources with the same image
`⊤` can be split by the cut.

The criterion uses neither bountifulness, amalgamation, nor any completion constructor.  The
receiving corollaries (conditional on finite-cut receiving) are in `TopSupportReceiving`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight.TopSupport

open Transform Value ExtOrd SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-! ## The top set, the uniform lowering, and the two conditions -/

/-- The top-labelled cells of a labelling (of any cell type: whole schemes or lower sets). -/
def topSet {X : Type*} (P : X → ExtOrd) : Set X := {d | P d = ⊤}

theorem mem_topSet {X : Type*} {P : X → ExtOrd} {d : X} : d ∈ topSet P ↔ P d = ⊤ := Iff.rfl

open Classical in
/-- The **uniform lowering**: non-top labels are kept, `⊤` is kept on `H` and replaced by `β`
off `H`. -/
noncomputable def lower (P : Cell D → ExtOrd) (H : Set (Cell D)) (β : ExtOrd) (d : Cell D) :
    ExtOrd :=
  if P d = ⊤ then (if d ∈ H then ⊤ else β) else P d

theorem lower_of_ne_top {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d ≠ ⊤) : lower P H β d = P d := by
  unfold lower; rw [ite_eq_right h]

theorem lower_of_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∈ H) : lower P H β d = ⊤ := by
  unfold lower; rw [ite_eq_left h, ite_eq_left hd]

theorem lower_of_not_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∉ H) : lower P H β d = β := by
  unfold lower; rw [ite_eq_left h, ite_eq_right hd]

/-- The top set of the lowering is `H`, for `H` a set of top cells and `β` proper. -/
theorem topSet_lower {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd}
    (hH : H ⊆ topSet P) (hβ : β ≠ ⊤) : topSet (lower P H β) = H := by
  ext d
  constructor
  · intro hd
    by_cases hP : P d = ⊤
    · by_contra hdH
      exact hβ ((lower_of_not_mem hP hdH).symm.trans hd)
    · exact absurd ((lower_of_ne_top hP).symm.trans hd) hP
  · intro hd
    exact lower_of_mem (hH hd) hd

/-- **Top availability**: a cell of `H` has a cell of `H` at every larger same-grade index. -/
def TopAvailable (D : CellScheme A) (H : Set (Cell D)) : Prop :=
  ∀ d ∈ H, ∀ Xi₀ : Cell D, D.scope d ⊆ D.scope Xi₀ → D.grade d = D.grade Xi₀ →
    ∃ Xi : Cell D, D.cell Xi = D.cell Xi₀ ∧ Xi ∈ H

/-- **Source separation**: beneath every surviving top owner `c` of grade `k`, the rounded
source of every lowered top lies strictly below the source of every surviving top. -/
def SourceSeparated (sem : Semantics D) (P : Cell D → ExtOrd) (H : Set (Cell D)) : Prop :=
  ∀ c ∈ H, ∀ a : D.below (D.cell c), a.1 ∈ H →
    ∀ d : D.below (D.cell c), P d.1 = ⊤ → d.1 ∉ H →
      extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c) < sem.E c a

/-- An **admissible** top support: a set of top cells satisfying both conditions. -/
structure Admissible (sem : Semantics D) (P : Cell D → ExtOrd) (H : Set (Cell D)) : Prop where
  subset : H ⊆ topSet P
  available : TopAvailable D H
  separated : SourceSeparated sem P H

/-! ## Necessity, for an arbitrary lawful alternative -/

/-- A replacement of a non-top label is not top. -/
theorem evr_ne_top {x : ExtOrd} (h : x ≠ ⊤) (k i : ℕ) : extVisibilityReplace x k i ≠ ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_ne_top
  · exact absurd rfl h
  · rw [extVisibilityReplace_ofOrd]; exact ofOrd_ne_top _

theorem selfVis_top_ext (k : ℕ) : SelfVis k ⊤ := extVisibilityReplace_top k k

theorem selfVis_max_of {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by
  change extVisibilityReplace (max a b) K K = max a b
  rw [extVisibilityReplace_max a b le_rfl]
  change extVisibilityReplace a K K = a at ha
  change extVisibilityReplace b K K = b at hb
  rw [ha, hb]

/-- A rounding at grade `K` is `K`-visible. -/
theorem selfVis_evr_self (K : ℕ) (t : ExtOrd) : SelfVis K (extVisibilityReplace t K K) := by
  rcases ExtOrd.cases t with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot K
  · rw [extVisibilityReplace_top]; exact selfVis_top_ext K
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs with h <;> omega

/-- A value is at most its own rounding. -/
theorem le_evr_self (x : ExtOrd) (k : ℕ) : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · exact le_top
  · by_cases h : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart h]
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp h), ofOrd_le_ofOrd]
      calc a = limitPart a + (finitePart a : Ordinal) := (limitPart_add_finitePart a).symm
        _ ≤ limitPart a + (k : Ordinal) := by
          gcongr; exact_mod_cast (not_le.mp h).le

variable {sem : Semantics D}

/-- The top set of a lawful labelling is top-available. -/
theorem topAvailable_of_respects {Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q) :
    TopAvailable D (topSet Q) := by
  intro d hd Xi₀ hs hg
  obtain ⟨Xi, hc, hle⟩ := hQ.availability d Xi₀ hs hg
  refine ⟨Xi, hc, ?_⟩
  rw [mem_topSet] at hd ⊢
  rw [hd] at hle
  exact top_le_iff.mp hle

/-- **Necessity of source separation**: the top set of any lawful `Q` is source-separated
relative to any `P` (the argument reads only the tops of `Q`). -/
theorem sourceSeparated_of_respects (P : Cell D → ExtOrd) {Q : Cell D → ExtOrd}
    (hQ : RespectsSemantics sem Q) : SourceSeparated sem P (topSet Q) := by
  intro c hc a ha d hdP hdQ
  rw [mem_topSet] at hc ha hdQ
  obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
    (grade := fun d : D.below (D.cell c) => D.grade d.1) (E := sem.E c)
    (p := fun d => Q d.1) (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2)
    (by rw [hc]; exact selfVis_top_ext _) (hQ.locality c)
  by_contra hle
  have hle' := not_lt.mp hle
  have h1 : τ (sem.E c a) = ⊤ := by rw [hread a, ha, hc]; rfl
  have h2 : τ (extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)) =
      extVisibilityReplace (τ (sem.E c d)) (D.grade c) (D.grade c) :=
    hτ.clause5 _ _ (by rw [gTop_of_le le_rfl]; exact le_top) _ le_rfl
  have h3 : τ (sem.E c d) ≠ ⊤ := by rw [hread d, hc, min_top_right]; exact hdQ
  have h4 := hτ.mono hle'
  rw [h1, h2] at h4
  exact evr_ne_top h3 _ _ (top_le_iff.mp h4)

/-- **Nonuniform necessity**: the actual top set of any lawful `Q` fixing the non-top labels of
`P` is an admissible top support of `P`. -/
theorem admissible_of_respects {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) : Admissible sem P (topSet Q) where
  subset d hd := by
    rw [mem_topSet] at hd ⊢
    by_contra h
    exact h ((hoff d h).symm.trans hd)
  available := topAvailable_of_respects hQ
  separated := sourceSeparated_of_respects P hQ

/-- Necessity for the uniform lowering. -/
theorem admissible_of_respects_lower {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd}
    (hH : H ⊆ topSet P) (hβ : β ≠ ⊤) (h : RespectsSemantics sem (lower P H β)) :
    Admissible sem P H :=
  topSet_lower hH hβ ▸ admissible_of_respects h (fun _ hd => lower_of_ne_top hd)

/-! ## Sufficiency: the retuned witness at a surviving top owner -/

/-- The **retuned map**: the old witness capped at `β` at and below the cut `t`, unchanged
above it. -/
noncomputable def retune (σ : ExtOrd → ExtOrd) (t β x : ExtOrd) : ExtOrd :=
  if x ≤ t then min (σ x) β else σ x

theorem retune_of_le {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (h : x ≤ t) :
    retune σ t β x = min (σ x) β := ite_eq_left h

theorem retune_of_gt {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (h : ¬ x ≤ t) :
    retune σ t β x = σ x := ite_eq_right h

/-- The retuned map has the bottom fibre of the old witness. -/
theorem retune_eq_bot_iff {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (hβ : β ≠ ⊥) :
    retune σ t β x = ⊥ ↔ σ x = ⊥ := by
  by_cases h : x ≤ t
  · rw [retune_of_le h, min_eq_bot, or_iff_left hβ]
  · rw [retune_of_gt h]

/-- **The retuned map is a bounded map** at grade `K`, for a `K`-visible cut and cap. -/
theorem boundedMap_retune {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ) {t β : ExtOrd}
    (ht : SelfVis K t) (hβ : SelfVis K β) : BoundedMap K (retune σ t β) where
  bot := by rw [retune_of_le bot_le, hσ.bot, min_eq_left bot_le]
  mono := by
    intro x y hxy
    by_cases hy : y ≤ t
    · rw [retune_of_le (hxy.trans hy), retune_of_le hy]
      exact min_le_min_right β (hσ.mono hxy)
    · rw [retune_of_gt hy]
      by_cases hx : x ≤ t
      · rw [retune_of_le hx]; exact (min_le_left _ _).trans (hσ.mono hxy)
      · rw [retune_of_gt hx]; exact hσ.mono hxy
  comm := by
    intro x k i hk hi
    have hcomm := hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi
    by_cases hx : x ≤ t
    · rw [retune_of_le hx, retune_of_le ((le_iff_evr_le (ht.mono hk) hi).mp hx), hcomm,
        evr_min_of_selfVis hβ hk hi]
    · have hx' : ¬ extVisibilityReplace x k i ≤ t := fun h =>
        hx ((le_iff_evr_le (ht.mono hk) hi).mpr h)
      rw [retune_of_gt hx, retune_of_gt hx', hcomm]

/-- The retuned map interpolates to a faithful witness on any finite source set (the bottom
fibre is unchanged, so the source-block criterion is inherited from the old witness). -/
theorem exists_witness_retune {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ)
    {t β : ExtOrd} (ht : SelfVis K t) (hβ : SelfVis K β) (hβbot : β ≠ ⊥) (s : Finset ExtOrd) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop K) τ ∧ ∀ x ∈ s, τ x = retune σ t β x := by
  apply ((boundedMap_retune hσ ht hβ).interpolate_iff_source_blocks s).mpr
  intro x _ y _ hb hx
  rw [retune_eq_bot_iff hβbot] at hx ⊢
  exact witness_bot_of_same_block hσ hb hx

/-- The rounded sources of the lowered tops beneath an owner are self-visible at its grade. -/
theorem selfVis_sup_evr {X : Type*} (s : Finset X) (f : X → ExtOrd) (k : ℕ) :
    SelfVis k (s.sup fun x => extVisibilityReplace (f x) k k) := by
  exact Finset.sup_induction (selfVis_bot k) (fun a ha b hb => selfVis_max_of ha hb)
    fun x _ => selfVis_evr_self k (f x)

/-! ## Sufficiency -/

/-- **Sufficiency**: an admissible top support gives a lawful uniform lowering. -/
theorem respects_lower {P : Cell D → ExtOrd} (hP : RespectsSemantics sem P) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {β : ExtOrd} (hβ : SelfVis K β) (hβbot : β ≠ ⊥)
    (hβgt : ∀ d, P d ≠ ⊤ → P d < β) {H : Set (Cell D)} (hH : Admissible sem P H) :
    RespectsSemantics sem (lower P H β) where
  orderly d := by
    by_cases hd : P d = ⊤
    · by_cases hdH : d ∈ H
      · rw [lower_of_mem hd hdH]; exact (selfVis_top_ext _).symm
      · rw [lower_of_not_mem hd hdH]; exact (hβ.mono (hK d)).symm
    · rw [lower_of_ne_top hd]; exact hP.orderly d
  availability Sig Xi₀ hs hg := by
    by_cases hS : P Sig = ⊤
    · by_cases hSH : Sig ∈ H
      · obtain ⟨Xi, hc, hXi⟩ := hH.available Sig hSH Xi₀ hs hg
        refine ⟨Xi, hc, ?_⟩
        rw [lower_of_mem (hH.subset hXi) hXi]; exact le_top
      · obtain ⟨Xi, hc, hle⟩ := hP.availability Sig Xi₀ hs hg
        refine ⟨Xi, hc, ?_⟩
        rw [hS] at hle
        have hXi : P Xi = ⊤ := top_le_iff.mp hle
        rw [lower_of_not_mem hS hSH]
        by_cases hXiH : Xi ∈ H
        · rw [lower_of_mem hXi hXiH]; exact le_top
        · rw [lower_of_not_mem hXi hXiH]
    · obtain ⟨Xi, hc, hle⟩ := hP.availability Sig Xi₀ hs hg
      refine ⟨Xi, hc, ?_⟩
      rw [lower_of_ne_top hS]
      by_cases hXi : P Xi = ⊤
      · by_cases hXiH : Xi ∈ H
        · rw [lower_of_mem hXi hXiH]; exact le_top
        · rw [lower_of_not_mem hXi hXiH]; exact (hβgt Sig hS).le
      · rw [lower_of_ne_top hXi]; exact hle
  locality c := by
    by_cases hc : P c = ⊤
    · by_cases hcH : c ∈ H
      · -- a surviving top owner: the retuned witness
        classical
        let _ := Fintype.ofFinite (D.below (D.cell c))
        obtain ⟨σ, hσ, -, hread⟩ := exists_bounded_exact_capped_witness
          (grade := fun d : D.below (D.cell c) => D.grade d.1) (E := sem.E c)
          (p := fun d => P d.1) (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2)
          (by rw [hc]; exact selfVis_top_ext _) (hP.locality c)
        have hread' : ∀ d : D.below (D.cell c), σ (sem.E c d) = P d.1 := fun d => by
          rw [hread d]; change min (P d.1) (P c) = P d.1; rw [hc, min_top_right]
        -- the cut
        let L : Finset (D.below (D.cell c)) := Finset.univ.filter fun d => P d.1 = ⊤ ∧ d.1 ∉ H
        let R : D.below (D.cell c) → ExtOrd := fun d =>
          extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)
        let t : ExtOrd := L.sup R
        have ht : SelfVis (D.grade c) t := selfVis_sup_evr L (sem.E c) (D.grade c)
        have hcut : ∀ d : D.below (D.cell c), P d.1 = ⊤ → d.1 ∉ H → sem.E c d ≤ t := by
          intro d hd hdH
          exact (le_evr_self _ (D.grade c)).trans
            (Finset.le_sup (f := R) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hdH⟩))
        have hsep : ∀ a : D.below (D.cell c), a.1 ∈ H → ¬ sem.E c a ≤ t := by
          intro a haH hle
          by_cases hL : L.Nonempty
          · obtain ⟨d, hdL, hdt⟩ := Finset.exists_mem_eq_sup L hL R
            obtain ⟨-, hd, hdH⟩ := Finset.mem_filter.mp hdL
            have hlt := hH.separated c hcH a haH d hd hdH
            have hle' : sem.E c a ≤ R d := by rw [← hdt]; exact hle
            exact absurd (hle'.trans_lt hlt) (lt_irrefl _)
          · rw [Finset.not_nonempty_iff_eq_empty] at hL
            have ht0 : t = ⊥ := by simp only [t, hL, Finset.sup_empty]
            rw [ht0, le_bot_iff] at hle
            have h1 := hread' a
            rw [hle, hσ.bot, hH.subset haH] at h1
            exact bot_ne_top h1
        obtain ⟨τ, hτ, hτread⟩ := exists_witness_retune hσ ht (hβ.mono (hK c)) hβbot
          (Finset.univ.image (sem.E c))
        apply hτ.transformsTo
        intro d
        have hg : gTop (D.grade (⟨c, GradedLe.refl _⟩ : D.below (D.cell c)).1) (D.grade d.1) = ⊤ :=
          gTop_of_le d.2.2
        rw [hg, min_top_right, hτread _ (Finset.mem_image_of_mem _ (Finset.mem_univ d)),
          lower_of_mem hc hcH, min_top_right]
        by_cases hd : P d.1 = ⊤
        · by_cases hdH : d.1 ∈ H
          · rw [lower_of_mem hd hdH, retune_of_gt (hsep d hdH), hread', hd]
          · rw [lower_of_not_mem hd hdH, retune_of_le (hcut d hd hdH), hread', hd, min_top_left]
        · rw [lower_of_ne_top hd]
          by_cases hdt : sem.E c d ≤ t
          · rw [retune_of_le hdt, hread', min_eq_left (hβgt _ hd).le]
          · rw [retune_of_gt hdt, hread']
      · -- a lowered top owner: the old target capped at `β`
        have key := TransformsTo.capped (K := D.grade c) (fun d => d.2.2) (hβ.mono (hK c))
          (hP.locality c)
        have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
            fun d => min (min (P d.1) (P c)) β := by
          funext d
          rw [lower_of_not_mem hc hcH, hc, min_top_right]
          by_cases hd : P d.1 = ⊤
          · rw [hd, min_top_left]
            by_cases hdH : d.1 ∈ H
            · rw [lower_of_mem hd hdH, min_top_left]
            · rw [lower_of_not_mem hd hdH, min_self]
          · rw [lower_of_ne_top hd]
        rw [e]; exact key
    · -- a proper or bottom owner: a literally unchanged target
      have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
          fun d => min (P d.1) (P c) := by
        funext d
        rw [lower_of_ne_top hc]
        by_cases hd : P d.1 = ⊤
        · rw [hd, min_top_left]
          by_cases hdH : d.1 ∈ H
          · rw [lower_of_mem hd hdH, min_top_left]
          · rw [lower_of_not_mem hd hdH, min_eq_right (hβgt c hc).le]
        · rw [lower_of_ne_top hd]
      rw [e]; exact hP.locality c

/-- **The finite top-support criterion**: the uniform lowering is lawful iff the support is
admissible.  The answer does not depend on `β` beyond its visibility and lower bound. -/
theorem respects_lower_iff {P : Cell D → ExtOrd} (hP : RespectsSemantics sem P) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {β : ExtOrd} (hβ : SelfVis K β) (hβbot : β ≠ ⊥) (hβtop : β ≠ ⊤)
    (hβgt : ∀ d, P d ≠ ⊤ → P d < β) {H : Set (Cell D)} (hH : H ⊆ topSet P) :
    RespectsSemantics sem (lower P H β) ↔ TopAvailable D H ∧ SourceSeparated sem P H :=
  ⟨fun h => ⟨(admissible_of_respects_lower hH hβtop h).available,
      (admissible_of_respects_lower hH hβtop h).separated⟩,
    fun h => respects_lower hP hK hβ hβbot hβgt ⟨hH, h.1, h.2⟩⟩

/-! ## Exact readback from a unique or minimal admissible support -/

/-- **Unique admissible support ⇒ exact readback**: if the only admissible support containing
the retained tops `TB` is the whole top set, then a lawful `Q` fixing the non-top labels and
keeping `TB` top is `P`. -/
theorem eq_of_unique_admissible {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    {TB : Set (Cell D)} (huniq : ∀ H, TB ⊆ H → Admissible sem P H → H = topSet P)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) (hTB : ∀ d ∈ TB, Q d = ⊤) : Q = P := by
  have hH : topSet Q = topSet P :=
    huniq _ (fun d hd => hTB d hd) (admissible_of_respects hQ hoff)
  funext d
  by_cases hd : P d = ⊤
  · rw [hd]; exact (mem_topSet.mp (hH ▸ (mem_topSet.mpr hd)))
  · exact hoff d hd

/-- **Minimal admissible support ⇒ exact occurrence of its lowering**: for `H` inclusion-minimal
among admissible supports containing `TB`, a lawful `Q` fixing the non-top labels of
`lower P H β` and keeping `TB` top is `lower P H β`. -/
theorem eq_lower_of_minimal {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    {TB H : Set (Cell D)} {β : ExtOrd} (hβtop : β ≠ ⊤)
    (hmin : ∀ H', TB ⊆ H' → Admissible sem P H' → H' ⊆ H → H' = H)
    (hoff : ∀ d, lower P H β d ≠ ⊤ → Q d = lower P H β d) (hTB : ∀ d ∈ TB, Q d = ⊤) :
    Q = lower P H β := by
  have hoffP : ∀ d, P d ≠ ⊤ → Q d = P d := fun d hd => by
    rw [hoff d (by rw [lower_of_ne_top hd]; exact hd), lower_of_ne_top hd]
  have hsub : topSet Q ⊆ H := fun d hd => by
    rw [mem_topSet] at hd
    by_contra hdH
    by_cases hP : P d = ⊤
    · have h1 := hoff d (by rw [lower_of_not_mem hP hdH]; exact hβtop)
      rw [lower_of_not_mem hP hdH, hd] at h1
      exact hβtop h1.symm
    · exact hP ((hoffP d hP).symm.trans hd)
  have hH : topSet Q = H := hmin _ (fun d hd => hTB d hd) (admissible_of_respects hQ hoffP) hsub
  funext d
  by_cases hd : lower P H β d = ⊤
  · rw [hd]
    have hdH : d ∈ H := by
      by_contra hdH
      by_cases hP : P d = ⊤
      · exact hβtop ((lower_of_not_mem hP hdH).symm.trans hd)
      · exact hP ((lower_of_ne_top hP).symm.trans hd)
    exact mem_topSet.mp (hH ▸ hdH)
  · exact hoff d hd

end VaughtConjecture.Knight.TopSupport
