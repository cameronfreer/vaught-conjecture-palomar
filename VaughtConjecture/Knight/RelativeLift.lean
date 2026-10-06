/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLiftData
-- Ported from V-C 4d2e8cb. Only the unrelated model-side GuardActivation
-- import is removed; its scalar cancellation helper is proved locally.

/-! # The relative lifting theorem from one lawful reference template

The reviewer's notes3 relative lifting lemma (`guarded_probe_construction.md` §4), in full:
**every allowed pair has every relative old-face lift.**  Given an allowed pair `(u, v)`
(`RelativeData.Allowed`) and an arbitrary lawful replacement `u'` of the entire old face
agreeing with `u` below an `N`-visible cap `γ`, there is a lawful candidate labelling `v'`
with the literal root `u'|_B`, the same `γ`-reading as `v`, and `(u', v')` allowed
(`relative_lift`).  The four cases:

* **Case 0** — `u'` is outside the distinguished bottom-pattern class: install the new root by
  the candidate's bountifulness at `γ`; correctness is vacuous (`lift_case0`).
* **Case 1** — `u'` in the class, `c' = u'(C) ≤ γ`: the same lift; every relation at `c'` is
  retained since `c' ≤ γ`, `c'` is `N`-visible, and the references agree at `c'`
  (`correct_of_cap_le`).
* **Case 2** — in the class, `c' > γ`, high values requested, `d' = d(u') < γ`: the frame puts
  every exact value below `γ`, so the lift at `γ` fixes them literally; the high values keep a
  reading at least `d'` (`correct_of_dOf_lt`).
* **Case 3** — in the class, `c' > γ`, and no high values or `γ ≤ d'`: the **template image**
  `w = θ ∘ V` under the capped decoder of `u'` at the cap is lawful by same-bottom-pattern
  transport (long rows harmless: every reference is nonbottom in the class), has the
  `γ`-reading of `v`, and its root is `u'|_B ∧ c'`; the candidate's bountifulness at `c'`
  restores the literal root, retaining every `c'`-reading and hence the `γ`-reading
  (`template_image_respects`, `lift_case3`).  At `γ = ⊥` the `γ`-agreement is trivial and
  the lawfulness of `w` comes from its bottom pattern, not from a positive-cap argument.

The proof uses the **original candidate's** bountifulness and the template only; no
controller is added and no row changed.  Existence of the template and existence of the
legal guarded probe are separate conclusions, not supplied here.

**General cap (notes7).**  The cap is a full-scope grade-`N` cell of a possibly larger private
context; the pattern test, the donor and the decoder live on its lower domain, and the
correctness relations read only cells there (`Requests.sec`).  The marker reads at offset
`R < N`.  Cells above the cap are carried along untouched by `u'`, which is a lawful labelling
of the whole private scheme.  The selector's cap is retained by every lift
(`RelativeData.selector_cap_agree`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Meets under nested caps -/

theorem min_cap_of_le {x x' c' γ : ExtOrd} (h : c' ≤ γ) (hag : min x γ = min x' γ) :
    min x c' = min x' c' := by
  calc min x c' = min (min x γ) c' := by rw [min_assoc, min_eq_right h]
    _ = min (min x' γ) c' := by rw [hag]
    _ = min x' c' := by rw [min_assoc, min_eq_right h]

theorem min_min_of_le {x c c' : ExtOrd} (h : c' ≤ c) : min (min x c) c' = min x c' := by
  rw [min_assoc, min_eq_right h]

/-- `min e c = v` with `v < c` forces `e = v`. -/
theorem eq_of_min_eq_of_lt' {e c v : ExtOrd} (h : min e c = v) (hv : v < c) : e = v :=
by
  rcases le_total e c with he | he
  · simpa only [min_eq_left he] using h
  · exact (hv.ne ((min_eq_right he).symm.trans h).symm).elim

namespace RelativeData

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem tOf_eq (u : Cell DA → ExtOrd) (f : Cell DQ) : X.req.tOf (X.req.sec u) f =
    min (extVisibilityReplace (u (X.req.ρ f).1) X.req.N (X.req.off f)) (u X.req.C) := rfl

theorem dOf_eq (u : Cell DA → ExtOrd) : X.req.dOf (X.req.sec u) =
    min (extVisibilityReplace (u X.req.a.1) X.req.N X.req.R) (u X.req.C) := rfl

/-- The correctness relations of a whole old labelling, read at the cap's label. -/
theorem correct_sec_iff (u : Cell DA → ExtOrd) (v : Cell DQ → ExtOrd) :
    X.req.Correct (X.req.sec u) v ↔
      (∀ z ∈ X.req.Z, min (v z) (u X.req.C) = ⊥) ∧
      (∀ f ∈ X.req.F, min (v f) (u X.req.C) = X.req.tOf (X.req.sec u) f) ∧
      ∀ y ∈ X.req.T, X.req.dOf (X.req.sec u) ≤ min (v y) (u X.req.C) := Iff.rfl

theorem R_le_N : X.req.R ≤ X.req.N := X.req.R_lt_N.le

/-- The cap's label is `N`-visible. -/
theorem cap_selfVis {u : Cell DA → ExtOrd} (hu : RespectsSemantics semA u) :
    SelfVis X.req.N (u X.req.C) := by
  have := (hu.orderly X.req.C).symm
  rwa [X.grade_C] at this

/-! ## Case 0 -/

/-- **Case 0**: outside the class, the root lift at `γ` suffices. -/
theorem lift_case0 {u v u' : _} (hall : X.Allowed u v) (hu' : RespectsSemantics semA u')
    {γ : ExtOrd} (hγ : SelfVis X.req.N γ) (hag : ∀ d, min (u' d) γ = min (u d) γ)
    (hcls : ¬ InClass X.ZA u') :
    ∃ v' : Cell DQ → ExtOrd, X.Allowed u' v' ∧ ∀ d, min (v' d) γ = min (v d) γ := by
  obtain ⟨-, hv, hroot, -⟩ := hall
  obtain ⟨v', hv', hr', hcap⟩ := X.lift_root hu' hv hγ
    (fun r => by rw [hroot r]; exact (hag _).symm)
  exact ⟨v', ⟨hu', hv', hr', fun h => absurd h hcls⟩, hcap⟩

/-! ## Case 1 -/

/-- **Case 1**: in the class with `c' ≤ γ`, correctness transfers to any `γ`-agreeing lift. -/
theorem correct_of_cap_le {u v u' v' : _} (hu' : RespectsSemantics semA u')
    (hC : X.req.Correct (X.req.sec u) v) {γ : ExtOrd} (hag : ∀ d, min (u' d) γ = min (u d) γ)
    (hc'γ : u' X.req.C ≤ γ) (hcap : ∀ d, min (v' d) γ = min (v d) γ) :
    X.req.Correct (X.req.sec u') v' := by
  rw [X.correct_sec_iff] at hC ⊢
  have hvisc' := X.cap_selfVis hu'
  have hc'c : u' X.req.C ≤ u X.req.C := by
    have h := hag X.req.C
    rw [min_eq_left hc'γ] at h
    exact h.trans_le (min_le_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [min_cap_of_le hc'γ (hcap z), ← min_min_of_le hc'c, hC.1 z hz]
    exact min_eq_left bot_le
  · intro f hf
    have hi := X.off_lt f hf
    have e3 : min (u (X.req.ρ f).1) (u' X.req.C) = min (u' (X.req.ρ f).1) (u' X.req.C) :=
      (min_cap_of_le hc'γ (hag (X.req.ρ f).1)).symm
    rw [min_cap_of_le hc'γ (hcap f), ← min_min_of_le hc'c, hC.2.1 f hf, X.tOf_eq, X.tOf_eq,
      min_min_of_le hc'c, ← evr_min_of_selfVis hvisc' le_rfl hi, e3,
      evr_min_of_selfVis hvisc' le_rfl hi]
  · intro y hy
    have e1 : min (v' y) (u' X.req.C) = min (min (v y) (u X.req.C)) (u' X.req.C) :=
      (min_cap_of_le hc'γ (hcap y)).trans (min_min_of_le hc'c).symm
    have e2 : X.req.dOf (X.req.sec u') = min (X.req.dOf (X.req.sec u)) (u' X.req.C) := by
      rw [X.dOf_eq, X.dOf_eq, ← evr_min_of_selfVis hvisc' le_rfl X.R_le_N,
        min_cap_of_le hc'γ (hag X.req.a.1), evr_min_of_selfVis hvisc' le_rfl X.R_le_N,
        min_min_of_le hc'c]
    rw [e1, e2]
    exact min_le_min_right _ (hC.2.2 y hy)

/-! ## Case 2 -/

/-- **Case 2**: in the class with `c' > γ`, high values requested, and `d' < γ`: the frame
fixes every exact value below `γ`, so correctness transfers to any `γ`-agreeing lift. -/
theorem correct_of_dOf_lt {u v u' v' : _}
    (hcls : InClass X.ZA u) (hC : X.req.Correct (X.req.sec u) v) {γ : ExtOrd}
    (hγ : SelfVis X.req.N γ) (hag : ∀ d, min (u' d) γ = min (u d) γ)
    (hγc' : γ < u' X.req.C) (hd' : X.req.dOf (X.req.sec u') < γ)
    (hframe' : ∀ f ∈ X.req.F, X.req.tOf (X.req.sec u') f ≤ X.req.dOf (X.req.sec u'))
    (hcap : ∀ d, min (v' d) γ = min (v d) γ) :
    X.req.Correct (X.req.sec u') v' := by
  rw [X.correct_sec_iff] at hC ⊢
  have hcne : u X.req.C ≠ ⊥ := X.cap_ne_bot hcls
  have hγne : γ ≠ ⊥ := ne_bot_of_gt hd'
  have hcγ : γ ≤ u X.req.C := by
    have h := hag X.req.C
    rw [min_eq_right hγc'.le] at h
    exact min_eq_right_iff.mp h.symm
  -- `d' = R_{N,R}(u' a)` and `u a = u' a`
  have hd'eq : X.req.dOf (X.req.sec u') =
      extVisibilityReplace (u' X.req.a.1) X.req.N X.req.R := by
    rw [X.dOf_eq] at hd' ⊢
    rcases le_total (extVisibilityReplace (u' X.req.a.1) X.req.N X.req.R) (u' X.req.C)
      with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h] at hd'; exact absurd (hγc'.trans hd') (lt_irrefl _)
  have hua : u X.req.a.1 = u' X.req.a.1 := by
    have hlt : u' X.req.a.1 < γ := lt_of_evr_lt hγ (hd'eq ▸ hd')
    have h := hag X.req.a.1
    rw [min_eq_left hlt.le] at h
    exact eq_of_min_eq_of_lt' h.symm hlt
  have hdu : X.req.dOf (X.req.sec u) = X.req.dOf (X.req.sec u') := by
    rw [X.dOf_eq, hua, hd'eq]
    exact min_eq_left ((hd'eq ▸ hd').le.trans hcγ)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hvz : v z = ⊥ := by
      rcases min_eq_bot.mp (hC.1 z hz) with h | h
      · exact h
      · exact absurd h hcne
    have h := hcap z
    rw [hvz, min_eq_left bot_le] at h
    rcases min_eq_bot.mp h with h' | h'
    · rw [h']; exact min_eq_left bot_le
    · exact absurd h' hγne
  · intro f hf
    have ht' : X.req.tOf (X.req.sec u') f < γ := (hframe' f hf).trans_lt hd'
    have ht'eq : X.req.tOf (X.req.sec u') f =
        extVisibilityReplace (u' (X.req.ρ f).1) X.req.N (X.req.off f) := by
      rw [X.tOf_eq] at ht' ⊢
      rcases le_total (extVisibilityReplace (u' (X.req.ρ f).1) X.req.N (X.req.off f))
        (u' X.req.C) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h] at ht'; exact absurd (hγc'.trans ht') (lt_irrefl _)
    have huρ : u (X.req.ρ f).1 = u' (X.req.ρ f).1 := by
      have hlt : u' (X.req.ρ f).1 < γ := lt_of_evr_lt hγ (ht'eq ▸ ht')
      have h := hag (X.req.ρ f).1
      rw [min_eq_left hlt.le] at h
      exact eq_of_min_eq_of_lt' h.symm hlt
    have htu : X.req.tOf (X.req.sec u) f = X.req.tOf (X.req.sec u') f := by
      rw [X.tOf_eq, huρ, ht'eq]
      exact min_eq_left ((ht'eq ▸ ht').le.trans hcγ)
    have hvf : v f = X.req.tOf (X.req.sec u') f :=
      eq_of_min_eq_of_lt' ((hC.2.1 f hf).trans htu) (ht'.trans_le hcγ)
    have hv'f : v' f = X.req.tOf (X.req.sec u') f := by
      have h := hcap f
      rw [hvf, min_eq_left ht'.le] at h
      exact eq_of_min_eq_of_lt' h ht'
    rw [hv'f]
    exact min_eq_left (ht'.trans hγc').le
  · intro y hy
    have h1 : X.req.dOf (X.req.sec u') ≤ v y :=
      hdu ▸ (hC.2.2 y hy).trans (min_le_left _ _)
    have h2 : X.req.dOf (X.req.sec u') ≤ min (v' y) γ := by
      rw [hcap y]; exact le_min h1 hd'.le
    exact le_min (h2.trans (min_le_left _ _)) (hd'.trans hγc').le

/-! ## Case 3: the template image -/

section Template

variable {u' : Cell DA → ExtOrd} (hu' : RespectsSemantics semA u') (hcls' : InClass X.ZA u')
  {θ : ExtOrd → ExtOrd} (hθ : BoundedMap X.req.N θ) (hθle : ∀ x, θ x ≤ u' X.req.C)
  (hθe : ∀ d, θ (X.e d) = min (X.req.sec u' d) (u' X.req.C))

include hθ in
theorem θ_min (x y : ExtOrd) : θ (min x y) = min (θ x) (θ y) := hθ.mono.map_min

include hθ in
theorem θ_evr (x : ExtOrd) {i : ℕ} (hi : i ≤ X.req.N) :
    θ (extVisibilityReplace x X.req.N i) = extVisibilityReplace (θ x) X.req.N i :=
  hθ.comm x X.req.N i le_rfl hi

include hθe in
theorem θ_cap : θ (X.e X.req.capCell) = u' X.req.C := by
  rw [hθe, Requests.sec_capCell, min_self]

theorem tOf_e_eq (f : Cell DQ) : X.req.tOf X.e f =
    min (extVisibilityReplace (X.e (X.req.ρ f)) X.req.N (X.req.off f)) (X.e X.req.capCell) := rfl

theorem dOf_e_eq : X.req.dOf X.e =
    min (extVisibilityReplace (X.e X.req.a) X.req.N X.req.R) (X.e X.req.capCell) := rfl

include hu' hθ hθe in
/-- The decoder sends `t_f(e)` to `t_f(u')`. -/
theorem θ_tOf {f : Cell DQ} (hf : f ∈ X.req.F) :
    θ (X.req.tOf X.e f) = X.req.tOf (X.req.sec u') f := by
  rw [X.tOf_e_eq, X.tOf_eq, θ_min X hθ, θ_evr X hθ _ (X.off_lt f hf), θ_cap X hθe, hθe,
    Requests.sec_apply, evr_min_of_selfVis (X.cap_selfVis hu') le_rfl (X.off_lt f hf),
    min_assoc, min_self]

include hu' hθ hθe in
/-- The decoder sends `d(e)` to `d(u')`. -/
theorem θ_dOf : θ (X.req.dOf X.e) = X.req.dOf (X.req.sec u') := by
  rw [X.dOf_e_eq, X.dOf_eq, θ_min X hθ, θ_evr X hθ _ X.R_le_N, θ_cap X hθe, hθe,
    Requests.sec_apply, evr_min_of_selfVis (X.cap_selfVis hu') le_rfl X.R_le_N, min_assoc,
    min_self]

include hu' hθ hθe in
/-- The frame inequalities transport to `u'`. -/
theorem frame_transport (hT : X.req.T.Nonempty) {f : Cell DQ} (hf : f ∈ X.req.F) :
    X.req.tOf (X.req.sec u') f ≤ X.req.dOf (X.req.sec u') := by
  rw [← θ_tOf X hu' hθ hθe hf, ← θ_dOf X hu' hθ hθe]
  exact hθ.mono (X.frame hT f hf)

include hu' hθ hθe in
/-- On the exact requests, the template image reads `t_f(u')` under the cap. -/
theorem image_tOf {f : Cell DQ} (hf : f ∈ X.req.F) :
    min (θ (X.V f)) (u' X.req.C) = X.req.tOf (X.req.sec u') f := by
  rw [← θ_cap X hθe, ← θ_min X hθ, X.V_correct.2.1 f hf, θ_tOf X hu' hθ hθe hf]

include hu' hθ hθe in
/-- On the high requests, the template image reads at least `d(u')` under the cap. -/
theorem image_dOf {y : Cell DQ} (hy : y ∈ X.req.T) :
    X.req.dOf (X.req.sec u') ≤ min (θ (X.V y)) (u' X.req.C) := by
  rw [← θ_cap X hθe, ← θ_min X hθ, ← θ_dOf X hu' hθ hθe]
  exact hθ.mono (X.V_correct.2.2 y hy)

/-- The template is bottom on the requested-bottom cells. -/
theorem V_bot {z : Cell DQ} (hz : z ∈ X.req.Z) : X.V z = ⊥ := by
  rcases min_eq_bot.mp (X.V_correct.1 z hz) with h | h
  · exact h
  · exact absurd ((X.e_bot _).mp h) X.C_notin

include hθe in
/-- On the root, the template image is the capped old labelling. -/
theorem image_root (r : DQ.below X.root) :
    θ (X.V r.1) = min (u' (X.κ r).1) (u' X.req.C) := by
  rw [X.V_root r, hθe, Requests.sec_apply]

include hu' hcls' hθ hθe in
/-- **The template image is lawful** on the candidate, by same-bottom-pattern transport: in the
class every reference, the marker, and the cap are nonbottom, so the image has exactly the
template's bottom pattern. -/
theorem template_image_respects : RespectsSemantics semQ (fun d => θ (X.V d)) := by
  have hc'ne := X.cap_ne_bot hcls'
  have hpat : ∀ d : DQ.below X.top, θ (X.V d.1) = ⊥ ↔ X.V d.1 = ⊥ := by
    intro d
    constructor
    · intro h
      rcases X.cover d.1 with hz | hf | hy | ⟨r, hr⟩
      · exact X.V_bot hz
      · exfalso
        have h1 := image_tOf X hu' hθ hθe hf
        rw [h, min_eq_left bot_le, X.tOf_eq] at h1
        rcases min_eq_bot.mp h1.symm with h2 | h2
        · exact X.ρ_notin _ hf ((hcls' _).mp ((evr_eq_bot_iff _ _).mp h2))
        · exact hc'ne h2
      · exfalso
        have h1 := image_dOf X hu' hθ hθe hy
        rw [h, min_eq_left bot_le, le_bot_iff, X.dOf_eq] at h1
        rcases min_eq_bot.mp h1 with h2 | h2
        · exact X.a_notin ((hcls' _).mp ((evr_eq_bot_iff _ _).mp h2))
        · exact hc'ne h2
      · rw [← hr, image_root X hθe r] at h
        rcases min_eq_bot.mp h with h2 | h2
        · rw [← hr, X.V_root r]
          exact (X.e_bot _).mpr ((hcls' _).mp h2)
        · exact absurd h2 hc'ne
    · intro h
      rw [h, hθ.bot]
  exact RespectsSemantics.of_below_top X.below_top
    (map_respects_of_same_bottom_pattern (X.V_respects.toBelow X.top) (X.V_respects.toBelow X.top)
      (fun d => X.grade_le d.1) hθ hpat)

end Template

/-! ## The theorem -/

/-- **The relative lifting theorem** (notes3 §4): every allowed pair has every relative
old-face lift at every `N`-visible comparison cap, bottom included. -/
theorem relative_lift {u v u' : _} (hall : X.Allowed u v) (hu' : RespectsSemantics semA u')
    {γ : ExtOrd} (hγ : SelfVis X.req.N γ) (hag : ∀ d, min (u' d) γ = min (u d) γ) :
    ∃ v' : Cell DQ → ExtOrd, X.Allowed u' v' ∧ ∀ d, min (v' d) γ = min (v d) γ := by
  by_cases hcls' : InClass X.ZA u'
  swap
  · exact X.lift_case0 hall hu' hγ hag hcls'
  obtain ⟨hu, hv, hroot, hcorr⟩ := hall
  obtain ⟨θ, hθ, hθle, hθe⟩ := X.decoder hu' hcls'
  have hc'ne := X.cap_ne_bot hcls'
  have hvisc' := X.cap_selfVis hu'
  -- in the class with a positive cap, `u` is in the class too
  have hclsu : γ ≠ ⊥ → InClass X.ZA u := by
    intro hγne d
    rw [← bottom_pattern_of_cap_agreement hγne hag d.1]
    exact hcls' d
  by_cases hc'γ : u' X.req.C ≤ γ
  · -- Case 1
    have hγne : γ ≠ ⊥ := fun h => hc'ne (le_bot_iff.mp (h ▸ hc'γ))
    obtain ⟨v', hv', hr', hcap⟩ := X.lift_root hu' hv hγ
      (fun r => by rw [hroot r]; exact (hag _).symm)
    exact ⟨v', ⟨hu', hv', hr', fun _ =>
      X.correct_of_cap_le hu' (hcorr (hclsu hγne)) hag hc'γ hcap⟩, hcap⟩
  have hγc' : γ < u' X.req.C := not_le.mp hc'γ
  by_cases hcase2 : X.req.T.Nonempty ∧ X.req.dOf (X.req.sec u') < γ
  · -- Case 2
    obtain ⟨hT, hd'⟩ := hcase2
    have hγne : γ ≠ ⊥ := ne_bot_of_gt hd'
    obtain ⟨v', hv', hr', hcap⟩ := X.lift_root hu' hv hγ
      (fun r => by rw [hroot r]; exact (hag _).symm)
    exact ⟨v', ⟨hu', hv', hr', fun _ =>
      X.correct_of_dOf_lt (hclsu hγne) (hcorr (hclsu hγne)) hγ hag hγc' hd'
        (fun f hf => frame_transport X hu' hθ hθe hT hf) hcap⟩, hcap⟩
  -- Case 3
  have hT : X.req.T.Nonempty → γ ≤ X.req.dOf (X.req.sec u') := fun hT =>
    not_lt.mp fun h => hcase2 ⟨hT, h⟩
  set w : Cell DQ → ExtOrd := fun d => θ (X.V d) with hw
  have hwr : RespectsSemantics semQ w := template_image_respects X hu' hcls' hθ hθe
  have hwle : ∀ d, w d ≤ u' X.req.C := fun d => hθle _
  obtain ⟨v', hv', hr', hcap'⟩ := X.lift_root hu' hwr hvisc'
    (fun r => by
      change min (θ (X.V r.1)) (u' X.req.C) = _
      rw [image_root X hθe r, min_assoc, min_self])
  have hcapw : ∀ d, min (v' d) (u' X.req.C) = w d := fun d =>
    (hcap' d).trans (min_eq_left (hwle d))
  refine ⟨v', ⟨hu', hv', hr', fun _ => (X.correct_sec_iff u' v').mpr ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · intro z hz
    rw [hcapw z]
    change θ (X.V z) = ⊥
    rw [X.V_bot hz, hθ.bot]
  · intro f hf
    rw [hcapw f, ← image_tOf X hu' hθ hθe hf]
    exact (min_eq_left (hwle f)).symm
  · intro y hy
    rw [hcapw y]
    exact (image_dOf X hu' hθ hθe hy).trans (min_le_left _ _)
  · -- the `γ`-reading
    intro d
    rw [← min_min_of_le hγc'.le (x := v' d), hcapw d]
    rcases eq_or_ne γ ⊥ with rfl | hγne
    · simp
    have hcls := hclsu hγne
    have hC := (X.correct_sec_iff u v).mp (hcorr hcls)
    have hcne := X.cap_ne_bot hcls
    have hcγ : γ ≤ u X.req.C := by
      have h := hag X.req.C
      rw [min_eq_right hγc'.le] at h
      exact min_eq_right_iff.mp h.symm
    rcases X.cover d with hz | hf | hy | ⟨r, hr⟩
    · have h1 : w d = ⊥ := by change θ (X.V d) = ⊥; rw [X.V_bot hz, hθ.bot]
      have h2 : v d = ⊥ := by
        rcases min_eq_bot.mp (hC.1 d hz) with h | h
        · exact h
        · exact absurd h hcne
      rw [h1, h2]
    · have h1 : min (w d) γ =
          min (extVisibilityReplace (u (X.req.ρ d).1) X.req.N (X.req.off d)) γ := by
        have hw' : min (w d) (u' X.req.C) = X.req.tOf (X.req.sec u') d :=
          image_tOf X hu' hθ hθe hf
        rw [← min_min_of_le hγc'.le (x := w d), hw', X.tOf_eq, min_min_of_le hγc'.le,
          ← evr_min_of_selfVis hγ le_rfl (X.off_lt d hf), hag,
          evr_min_of_selfVis hγ le_rfl (X.off_lt d hf)]
      have h2 : min (v d) γ =
          min (extVisibilityReplace (u (X.req.ρ d).1) X.req.N (X.req.off d)) γ := by
        rw [← min_min_of_le hcγ (x := v d), hC.2.1 d hf, X.tOf_eq, min_min_of_le hcγ]
      rw [h1, h2]
    · have hγd := hT ⟨d, hy⟩
      have h1 : min (w d) γ = γ := min_eq_right
        (hγd.trans ((image_dOf X hu' hθ hθe hy).trans (min_le_left _ _)))
      have hu'a : γ ≤ u' X.req.a.1 :=
        le_of_le_evr hγ X.req.R_lt_N (hγd.trans (min_le_left _ _))
      have hua : γ ≤ u X.req.a.1 := by
        have h := hag X.req.a.1
        rw [min_eq_right hu'a] at h
        exact min_eq_right_iff.mp h.symm
      have hdu : γ ≤ X.req.dOf (X.req.sec u) := by
        rw [X.dOf_eq]
        exact le_min (le_evr_of_le hγ hua _) hcγ
      have h2 : min (v d) γ = γ :=
        min_eq_right (hdu.trans ((hC.2.2 d hy).trans (min_le_left _ _)))
      rw [h1, h2]
    · rw [← hr]
      change min (θ (X.V r.1)) γ = min (v r.1) γ
      rw [image_root X hθe r, min_min_of_le hγc'.le, hag, hroot r]

end RelativeData

end VaughtConjecture.Knight
