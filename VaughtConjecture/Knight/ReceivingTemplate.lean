/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeReset
public import VaughtConjecture.Knight.BlockCode

/-! # The receiving template: donor cleaning and the encoded candidate

The reviewer's notes7 (`mixed_proper_top_charts.md` §6, 2026-09-19), at the level of the
finite schemes.  Three steps, each a theorem:

* **Donor cleaning** (`cleaned_respects`, `exists_cleanedDonor`): the cap's row with the actual
  labelling's bottom pattern is lawful on the cap's lower domain.  The cleaning map
  `ν x = ⊥` if the reading witness kills `x`, `x` otherwise, is a bounded map, and the
  cleaned row has the bottom pattern of the actual (lawful) labelling; so
  `map_respects_of_same_bottom_pattern` applies.  No semantic row is changed.
* **The template from an encoding** (`template_of_encoding`): a bounded map `enc` through the
  candidate's grades, reflecting bottom on the candidate's values, sending the root labels to
  the donor's root sources, every exact request to its reference strip at its offset, every
  high request to the marker's offset-`R` replacement, and bottom to bottom, makes
  `enc ∘ P` a lawful template with literal donor root, correct against the donor, and
  satisfying the frame inequalities.  A block code (`BlockCode.code`) is such an `enc`.
* **The capped variant** (`template_of_encoding_capped`): root agreement is required only
  below `h = R_{N,R}(e a)`; the candidate's bountifulness at the root–top pair at cap `h`
  restores the literal donor root.  This is what top-labelled root cells need: their sources
  dominate `h` while the encoding sends `⊤` to `h`.
* **The relative data** (`mkRelativeData`): the assembled `RelativeData`, with the donor
  *constructed* from the actual labelling and the cap's row, and the template supplied by
  the two theorems above.  `Knight/ReceivingContext.lean` discharges every encoding
  hypothesis from an actual receiving context.

**The root alignment hypothesis.**  The template's root must be the donor's root
*sources* `E_C(κ r)`, while the encoding acts on the root *labels* `P(κ r) = u₀(κ r)`.  The
note asserts "its root equals `e|B` capped at `h`"; that holds only when every root cell's
source lies on the strip chosen for its label's block at its own offset
(`hroot_enc`).  It is not automatic: the reading witness of the cap's row may merge two
source strips into one label block, so two root cells with labels in one block can have
sources on different strips, and then no scalar encoding of the labels recovers both sources
(`TemplateRegression.no_scalar_root` in `Knight/TemplateRegression.lean`).  The hypothesis is
therefore explicit, and it is the first clause the model-side construction has to discharge.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Donor cleaning -/

section Cleaning

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- The cleaning map of a reading witness: bottom where the witness reads bottom. -/
noncomputable def cleaner (σ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  if σ x = ⊥ then ⊥ else x

theorem cleaner_of_eq {σ : ExtOrd → ExtOrd} {x : ExtOrd} (h : σ x = ⊥) : cleaner σ x = ⊥ :=
  ite_eq_left h

theorem cleaner_of_ne {σ : ExtOrd → ExtOrd} {x : ExtOrd} (h : σ x ≠ ⊥) : cleaner σ x = x :=
  ite_eq_right h

theorem cleaner_eq_bot_iff {σ : ExtOrd → ExtOrd} (hσ : σ ⊥ = ⊥) (x : ExtOrd) :
    cleaner σ x = ⊥ ↔ σ x = ⊥ := by
  by_cases h : σ x = ⊥
  · rw [cleaner_of_eq h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [cleaner_of_ne h]
    exact ⟨fun hx => by rw [hx] at h; exact absurd hσ h, fun hx => absurd hx h⟩

/-- The cleaning map of a bounded map is a bounded map. -/
theorem boundedMap_cleaner {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ) :
    BoundedMap K (cleaner σ) where
  bot := cleaner_of_eq hσ.bot
  mono x y hxy := by
    by_cases hy : σ y = ⊥
    · have hx : σ x = ⊥ := le_bot_iff.mp (hy ▸ hσ.mono hxy)
      rw [cleaner_of_eq hx, cleaner_of_eq hy]
    · rw [cleaner_of_ne hy]
      by_cases hx : σ x = ⊥
      · rw [cleaner_of_eq hx]; exact bot_le
      · rw [cleaner_of_ne hx]; exact hxy
  comm x k i hk hi := by
    have h := hσ.comm x k i hk hi
    by_cases hx : σ x = ⊥
    · have h' : σ (extVisibilityReplace x k i) = ⊥ := by rw [h, hx, extVisibilityReplace_bot]
      rw [cleaner_of_eq hx, cleaner_of_eq h', extVisibilityReplace_bot]
    · have h' : σ (extVisibilityReplace x k i) ≠ ⊥ := by
        rw [h]; exact fun hb => hx ((evr_eq_bot_iff _ _).mp hb)
      rw [cleaner_of_ne hx, cleaner_of_ne h']

/-- Cleaning only needs the reading's bottom pattern, including on long source rows. -/
theorem cleaned_respects_of_bottom_agreement {BJ : Finset ι × ℕ} {r u : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hu : RespectsSemanticsBelow sem BJ u) {K : ℕ}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ)
    (hbot : ∀ d, σ (r d) = ⊥ ↔ u d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => if u d = ⊥ then ⊥ else r d) := by
  have h := map_respects_of_same_bottom_pattern hr hu hK (boundedMap_cleaner hσ)
    (fun d => (cleaner_eq_bot_iff hσ.bot _).trans (hbot d))
  have e : (fun d => cleaner σ (r d)) = fun d => if u d = ⊥ then ⊥ else r d := by
    funext d
    simp only [cleaner, hbot d]
  rwa [e] at h

/-- **Donor cleaning**: a lawful section read by a bounded map to a lawful section stays lawful
after erasing exactly the positions the reading sends to bottom. -/
theorem cleaned_respects {BJ : Finset ι × ℕ} {r u : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hu : RespectsSemanticsBelow sem BJ u) {K : ℕ}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ)
    (hread : ∀ d, σ (r d) = u d) :
    RespectsSemanticsBelow sem BJ (fun d => if u d = ⊥ then ⊥ else r d) := by
  exact cleaned_respects_of_bottom_agreement hr hu hK hσ (fun d => by rw [hread d])

end Cleaning

/-! ## The cleaned donor at a cap -/

section Cap

variable {ιA : Type*} [DecidableEq ιA] {A : Finset ιA} {DA : CellScheme A} {semA : Semantics DA}

/-- **The cleaned donor at a top cap**: for a lawful row at the cap and a lawful labelling
reading the cap at `⊤`, the row with the labelling's bottom pattern is lawful below the cap,
has bottom exactly where the labelling does, and is the row elsewhere. -/
theorem exists_cleanedDonor {C : Cell DA}
    (hrow : RespectsSemanticsBelow semA (DA.cell C) (semA.E C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ C = ⊤) :
    ∃ e : DA.below (DA.cell C) → ExtOrd, RespectsSemanticsBelow semA (DA.cell C) e ∧
      (∀ d, e d = ⊥ ↔ u₀ d.1 = ⊥) ∧ ∀ d, u₀ d.1 ≠ ⊥ → e d = semA.E C d := by
  have hvis : SelfVis (DA.grade C) (u₀ C) := (hu₀.orderly C).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := DA.below (DA.cell C)) (grade := fun d => DA.grade d.1) (p := fun d => u₀ d.1)
    (c := ⟨C, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hu₀.locality C)
  have hτ : BoundedMap (DA.grade C) τ := ⟨hbot, hmono, fun x k i hk hi => hcomm x k i hk hi⟩
  have hread' : ∀ d : DA.below (DA.cell C), τ (semA.E C d) = u₀ d.1 := by
    intro d
    rw [hread d]
    change min (u₀ d.1) (u₀ C) = u₀ d.1
    rw [hC, min_top_right]
  refine ⟨fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E C d,
    cleaned_respects hrow (hu₀.toBelow _) (fun d => d.2.2) hτ hread', ?_, ?_⟩
  · intro d
    by_cases h : u₀ d.1 = ⊥
    · simp only [h, ite_true]
    · simp only [h, ite_false, iff_false]
      intro hE
      apply h
      rw [← hread' d, hE, hbot]
  · intro d h
    simp only [h, ite_false]

end Cap

/-! ## The template from an encoding -/

section Template

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- **The template from an encoding.**  Given the requests, a donor section `e` below the cap,
a lawful candidate `P` whose cells lie below `top` with `top.2 ≤ R`, and a bounded map `enc`
through grade `R` that reflects bottom on `P`'s values, sends the root labels to the donor's
root values, every exact request to its reference strip at its offset, and every high request
to the marker's offset-`R` replacement, with the frame inequality on the strips: the encoded
candidate is a lawful template with literal donor root, correct against the donor, and
satisfying the frame inequalities. -/
theorem template_of_encoding (req : Requests DA DQ) (e : DA.below (DA.cell req.C) → ExtOrd)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {top : Finset ιQ × ℕ}
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap req.R enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥) {root : Finset ιQ × ℕ}
    (κ : DQ.below root → DA.below (DA.cell req.C)) (hroot_enc : ∀ r, enc (P r.1) = e (κ r))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R)
    (hframe : req.T.Nonempty → ∀ f ∈ req.F,
      extVisibilityReplace (e (req.ρ f)) req.N (req.off f) ≤
        extVisibilityReplace (e req.a) req.N req.R) :
    RespectsSemantics semQ (fun d => enc (P d)) ∧ (∀ r, enc (P r.1) = e (κ r)) ∧
      req.Correct e (fun d => enc (P d)) ∧
      (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) := by
  refine ⟨?_, hroot_enc, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine RespectsSemantics.of_below_top below_top
      (map_respects_of_same_bottom_pattern (hP.toBelow top) (hP.toBelow top)
        (fun d => d.2.2.trans top_le_R) henc ?_)
    intro d
    exact ⟨hbotP d.1, fun h => by rw [h, henc.bot]⟩
  · intro z hz
    change min (enc (P z)) (e req.capCell) = ⊥
    rw [hZ z hz, henc.bot]
    exact min_eq_left bot_le
  · intro f hf
    change min (enc (P f)) (e req.capCell) = req.tOf e f
    rw [hF f hf]
    rfl
  · intro y hy
    change req.dOf e ≤ min (enc (P y)) (e req.capCell)
    rw [hT y hy]
    exact le_rfl
  · intro hT' f hf
    exact min_le_min_right _ (hframe hT' f hf)

/-- **The assembled relative data**: the cleaned donor is *constructed* from the actual
labelling and the cap's row; the template and its four properties are supplied by
`template_of_encoding` or `template_of_encoding_capped`. -/
noncomputable def mkRelativeData (req : Requests DA DQ) (grade_C : DA.grade req.C = req.N)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (a_ne : u₀ req.a.1 ≠ ⊥) (ρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥)
    (off_lt : ∀ f ∈ req.F, req.off f ≤ req.N) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_N : top.2 ≤ req.N)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (V : Cell DQ → ExtOrd) (V_respects : RespectsSemantics semQ V)
    (V_root : ∀ r : DQ.below root, V r.1 = if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r))
    (V_correct : req.Correct (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) V)
    (frame : req.T.Nonempty → ∀ f ∈ req.F,
      req.tOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) f ≤
        req.dOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d)) :
    RelativeData DA semA DQ semQ where
  req := req
  grade_C := grade_C
  ZA := {d | u₀ d.1 = ⊥}
  C_notin := by
    change ¬ u₀ req.C = ⊥
    rw [hC]; exact top_ne_bot
  a_notin := a_ne
  ρ_notin := ρ_ne
  off_lt := off_lt
  e := fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d
  e_bot := fun d => by
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = ⊥ ↔ u₀ d.1 = ⊥
    by_cases h : u₀ d.1 = ⊥
    · simp only [h, ite_true]
    · simp only [h, ite_false, iff_false]
      intro hE
      have _ := hrow
      obtain ⟨g, σ, _, _, hbot, _, _, hread⟩ := hu₀.locality req.C
      have hd := hread d
      change min (u₀ d.1) (u₀ req.C) = min (σ (semA.E req.C d)) (g (DA.grade d.1)) at hd
      rw [hC, min_top_right, hE, hbot, min_eq_left bot_le] at hd
      exact h hd
  e_eq := fun d hd => by
    have hd' : ¬ u₀ d.1 = ⊥ := hd
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = _
    rw [ite_eq_right hd']
  root := root
  top := top
  root_mem := root_mem
  top_mem := top_mem
  root_le := root_le
  root_ne := root_ne
  below_top := below_top
  top_le_N := top_le_N
  κ := κ
  hroot := hroot
  bountiful := bountiful
  cover := cover
  V := V
  V_respects := V_respects
  V_root := V_root
  V_correct := V_correct
  frame := frame

/-- Capped template repair needs encoding commutation only through the donor's top grade. -/
theorem template_of_encoding_at_grade (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap top.2 enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis top.2 (extVisibilityReplace (e req.a) req.N req.R))
    (hroot_cap : ∀ r, min (enc (P r.1)) (extVisibilityReplace (e req.a) req.N req.R) =
      min (e (κ r)) (extVisibilityReplace (e req.a) req.N req.R))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R)
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f)) ∧
      (∀ y ∈ req.T, extVisibilityReplace (e req.a) req.N req.R ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  set h := extVisibilityReplace (e req.a) req.N req.R with hh
  have hne : h ≠ ⊥ := fun h0 => ha_ne ((evr_eq_bot_iff _ _).mp h0)
  -- the encoded candidate is lawful
  have hV0 : RespectsSemantics semQ (fun d => enc (P d)) :=
    RespectsSemantics.of_below_top below_top
      (map_respects_of_same_bottom_pattern (hP.toBelow top) (hP.toBelow top)
        (fun d => d.2.2) henc
        (fun d => ⟨hbotP d.1, fun h => by rw [h, henc.bot]⟩))
  -- restore the literal donor root at cap `h`
  obtain ⟨q', hq', hcap, hface⟩ := bountiful root top root_mem top_mem root_le root_ne
    (fun d => e (κ d)) (fun d => enc (P d.1)) h (hroot e he) (hV0.toBelow top)
    hvis (fun d => hroot_cap d)
  set V : Cell DQ → ExtOrd := fun d => q' ⟨d, below_top d⟩ with hVdef
  have hVr : RespectsSemantics semQ V := RespectsSemantics.of_below_top below_top hq'
  have hVcap : ∀ d, min (V d) h = min (enc (P d)) h := fun d => hcap ⟨d, below_top d⟩
  have hVF : ∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    intro f hf
    have h1 := hVcap f
    rw [hF f hf, min_eq_left (hFlt f hf).le] at h1
    -- KVC's RelativeLift exports this scalar helper without GuardActivation.
    exact eq_of_min_eq_of_lt' h1 (hFlt f hf)
  have hVT : ∀ y ∈ req.T, h ≤ V y := by
    intro y hy
    have h1 := hVcap y
    rw [hT y hy, min_self] at h1
    exact min_eq_right_iff.mp h1
  have hVZ : ∀ z ∈ req.Z, V z = ⊥ := by
    intro z hz
    have h1 := hVcap z
    rw [hZ z hz, henc.bot, min_eq_left bot_le] at h1
    rcases min_eq_bot.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hne
  refine ⟨V, hVr, fun r => hface r, ⟨?_, ?_, ?_⟩, ?_, hVF, hVT, hVZ⟩
  · intro z hz
    rw [hVZ z hz]
    exact min_eq_left bot_le
  · intro f hf
    rw [hVF f hf]
    rfl
  · intro y hy
    exact min_le_min_right _ (hVT y hy)
  · intro _ f hf
    exact min_le_min_right _ (hFlt f hf).le

/-- **The template from an encoding, with root agreement below the top code only.**  When
the encoded candidate agrees with the donor's root only below `h = R_{N,R}(e a)` (the case of
top-labelled root cells, whose sources dominate `h`), the candidate's bountifulness at the
root–top pair at cap `h` restores the literal donor root while retaining every `h`-reading;
the exact requests must then sit strictly below `h`. -/
theorem template_of_encoding_capped (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap req.R enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R))
    (hroot_cap : ∀ r, min (enc (P r.1)) (extVisibilityReplace (e req.a) req.N req.R) =
      min (e (κ r)) (extVisibilityReplace (e req.a) req.N req.R))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R)
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f)) ∧
      (∀ y ∈ req.T, extVisibilityReplace (e req.a) req.N req.R ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  exact template_of_encoding_at_grade req e he ha_ne hP root_mem top_mem root_le root_ne
    below_top κ hroot bountiful
    ⟨henc.bot, henc.mono, fun x k i hk hi => henc.comm x k i (hk.trans top_le_R) hi⟩
    hbotP (hvis.mono top_le_R) hroot_cap hZ hF hFlt hT

/-- The assembled data's donor is lawful below the cap (donor cleaning). -/
theorem mkRelativeData_e_respects (req : Requests DA DQ)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤) :
    RespectsSemanticsBelow semA (DA.cell req.C)
      (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) := by
  obtain ⟨e', he', he'bot, he'eq⟩ := exists_cleanedDonor hrow hu₀ hC
  have : e' = fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d := by
    funext d
    by_cases h : u₀ d.1 = ⊥
    · rw [ite_eq_left h]; exact (he'bot d).mpr h
    · rw [ite_eq_right h]; exact he'eq d h
  rwa [this] at he'

end Template

end VaughtConjecture.Knight
