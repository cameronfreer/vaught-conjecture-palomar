/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledRepairSufficiency

/-! # The relative capped paste: shared-probe pasting, the two grade-three face obligations,
and bountifulness of the repaired semantics

**The capped paste** on a linear order (`paste g q s`: `q` where `q < g`, otherwise `max g s`;
after the reviewer's research scout `SharedProbePaste.lean` and its handoff
`SHARED-PROBE-PASTING.md`, `research/smt` at `b9e221d`, ported here with the same names): it
agrees with the first label below the cap (`paste_cap`), it is literally the second wherever the
two agree below the cap (`paste_eq_of_agree`), it is monotone, **preserves minima exactly**
(`paste_min`), preserves fixed points of any operation fixing the cap (`paste_fixed`), preserves
paired bottom implications (`paste_coupling`), and **commutes with a monotone operation fixing
the cap when the two inputs agree below the cap** (`map_paste_of_agree`; not without the
agreement).  At cap `⊥` it is the second label (`paste_bot_cap`), so the face sections of
`CoupledRepairSufficiency` are the cap-`⊥` case.

**One shared coordinate is enough for legality** (`legal_paste_of_proper_agreement`): the
coordinatewise paste of two admissible parameter sets is admissible given a grade-three-visible
cap and agreement of the two **proper values** below the cap — no face-section formula and no
further compatibility law.  The exact orbit is the one equation that needs the shared
coordinate: `z₁ = R₃ (min v w) = min (R₃ v) w` since `R₃` is monotone and `w` is fixed by it, so
the pasted orbit is `paste_min` and `map_paste_of_agree` applied to `R₃`; the `(3, 1)` fixing law
and both minimum-visibility conditions are `paste_fixed` and `paste_min`, the two bottom
couplings `paste_coupling`.  Pasting the seven parameters and reconstructing the labelling is
exactly **cellwise** pasting (`shape_paste`; the dependent value `min x₀ H` through `paste_min`),
so two respecting labellings whose proper values agree below the cap paste to a respecting one
(`respects_paste_of_proper_agreement`).

**Sections give the relative lift** (`relative_lift_of_section`): for a protected collection of
cells containing a proper grade-one cell, a prescribed labelling on it, any respecting section
extending it literally, and a respecting ambient labelling agreeing with it below a
grade-three-visible cap, the cellwise paste respects `rowsR`, is literally the prescribed
labelling on the collection, and agrees with the ambient one below the cap on **every** cell.
Full agreement on the protected face is still what literal preservation needs; legality needs
only the shared proper probe.

**The two face obligations** (`faceA_liftR`, `faceB_liftR`) are the instances at the two face
sections `faceA_extendsR`, `faceB_extendsR`, anchored at the shared singleton cell `({1}, 1)`.
Bottom and top caps are covered: the cap is any grade-three self-visible value.

**Bountifulness** (`properToFullR_three`, `properToFullR`, `rowsR_isBountiful`): the
scope-changing obligation at target grade three — sources below grade three through the
transferred endpoints and `bountiful_full_scope`; at grade three the proper side is one of the two
protected faces (`proper_side`) and the face lift applies — hence `ProperToFullRLow` in full and
bountifulness of the repaired semantics through the existing reduction `rowsR_isBountiful_of`.

**The unconditional domain** (`semSchemeR : SemScheme 4`, `repaired_realization`): a coded,
consistent, **bountiful** semantics on the glued scheme, agreeing with the fixed glue on both
input faces, with a respecting labelling of `(univ, 3)` realizing the original prescribed pair
`(p₀, p₁)`.  This is claim 2 (a legal common extension of the two inputs realizing the pair);
general request service, comparison inside fixed models, and fragment-tail countability are
separate.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

/-! ## The capped paste on a linear order

After the reviewer's `SharedProbePaste.lean` (`research/smt`, `b9e221d`). -/

section Order

variable {α : Type*} [LinearOrder α]

/-- **The capped paste**: the first label where it is below the cap, otherwise the second raised
to the cap. -/
def paste (g q s : α) : α := if q < g then q else max g s

variable {g q s : α}

theorem paste_of_lt (h : q < g) : paste g q s = q := by unfold paste; rw [ite_eq_left h]
theorem paste_of_ge (h : g ≤ q) : paste g q s = max g s := by
  unfold paste; rw [ite_eq_right (not_lt.mpr h)]

theorem paste_self (g q : α) : paste g q q = q := by
  unfold paste
  split_ifs with h
  · rfl
  · exact max_eq_right (le_of_not_gt h)

/-- **Capped agreement**: the paste agrees with the first label below the cap. -/
theorem paste_cap (g q s : α) : min (paste g q s) g = min q g := by
  unfold paste
  split_ifs with h
  · rfl
  · rw [min_eq_right (le_max_left _ _), min_eq_right (le_of_not_gt h)]

/-- **Literal preservation**: where the two labels agree below the cap, the paste is the second. -/
theorem paste_eq_of_agree (h : min q g = min s g) : paste g q s = s := by
  unfold paste
  split_ifs with hq
  · have hs : s < g := by grind
    simpa only [min_eq_left hq.le, min_eq_left hs.le] using h
  · have hs : g ≤ s := by grind
    exact max_eq_right hs

theorem paste_mono {q' s' : α} (hq : q ≤ q') (hs : s ≤ s') : paste g q s ≤ paste g q' s' := by
  unfold paste
  split_ifs <;> grind

/-- **Exact minima**: the paste of minima is the minimum of the pastes. -/
theorem paste_min (g q₁ s₁ q₂ s₂ : α) :
    paste g (min q₁ q₂) (min s₁ s₂) = min (paste g q₁ s₁) (paste g q₂ s₂) := by
  unfold paste
  split_ifs <;> grind

/-- An operation fixing the cap and both labels fixes their paste (no monotonicity needed). -/
theorem paste_fixed (f : α → α) (hg : f g = g) (hq : f q = q) (hs : f s = s) :
    f (paste g q s) = paste g q s := by
  unfold paste
  split_ifs
  · exact hq
  · rcases le_total g s with h | h
    · simpa only [max_eq_right h] using hs
    · simpa only [max_eq_left h] using hg

/-- **A monotone operation fixing the cap commutes with the paste when the two inputs agree below
the cap.**  Not without the agreement. -/
theorem map_paste_of_agree (f : α → α) (hf : Monotone f) (hg : f g = g)
    (h : min q g = min s g) : f (paste g q s) = paste g (f q) (f s) := by
  by_cases hq : q < g
  · have hs : s < g := by grind
    have hqs : q = s := by
      simpa only [min_eq_left hq.le, min_eq_left hs.le] using h
    subst s
    rw [paste_self, paste_self]
  · have hqg : g ≤ q := le_of_not_gt hq
    have hfg : g ≤ f q := hg ▸ hf hqg
    simp only [paste, ite_eq_right hq, ite_eq_right (not_lt.mpr hfg), hf.map_max, hg]

end Order

section Bottom

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- At cap `⊥` the paste is the second label: the face sections are the cap-`⊥` case. -/
theorem paste_bot_cap (q s : α) : paste ⊥ q s = s := by
  rw [paste_of_ge bot_le, max_eq_right bot_le]

theorem paste_bot (g : α) : paste g ⊥ ⊥ = ⊥ := paste_self g ⊥

/-- Paired bottom implications are preserved by the paste. -/
theorem paste_coupling {g q s q' s' : α} (hq : q = ⊥ → q' = ⊥) (hs : s = ⊥ → s' = ⊥)
    (h : paste g q s = ⊥) : paste g q' s' = ⊥ := by
  by_cases hg : g = ⊥
  · subst g
    simp only [paste, not_lt_bot, ↓reduceIte, max_eq_right bot_le] at h ⊢
    exact hs h
  · have hbg : (⊥ : α) < g := bot_lt_iff_ne_bot.mpr hg
    unfold paste at h
    split_ifs at h with hqg
    · rw [hq h]
      simp only [paste, hbg, ↓reduceIte]
    · exact False.elim (hg (le_bot_iff.mp (h ▸ le_max_left g s)))

end Bottom

/-! ## Shared-probe pasting: one shared coordinate is enough for legality -/

section SharedProbe

theorem paste_visible {k : ℕ} {g q s : ExtOrd} (hg : SelfVis k g) (hq : SelfVis k q)
    (hs : SelfVis k s) : SelfVis k (paste g q s) :=
  paste_fixed (fun x => extVisibilityReplace x k k) hg hq hs

/-- **Legality of the pasted parameters** from agreement of the proper values below a
grade-three-visible cap alone.  The exact orbit is the one equation needing the shared
coordinate: `z₁ = R₃ (min v w) = min (R₃ v) w`. -/
theorem legal_paste_of_proper_agreement {g v x₀ x₁ H z₁ z₂ w v' x₀' x₁' H' z₁' z₂' w' : ExtOrd}
    (L : Legal₃ v x₀ x₁ H z₁ z₂ w) (S : Legal₃ v' x₀' x₁' H' z₁' z₂' w') (hg : SelfVis 3 g)
    (hv : min v g = min v' g) :
    Legal₃ (paste g v v') (paste g x₀ x₀') (paste g x₁ x₁') (paste g H H') (paste g z₁ z₁')
      (paste g z₂ z₂') (paste g w w') := by
  have hg1 : SelfVis 1 g := hg.mono (by omega)
  have hg2 : SelfVis 2 g := hg.mono (by omega)
  have htwo : Legal₂ (paste g v v') (paste g x₀ x₀') (paste g x₁ x₁') (paste g H H') := by
    refine ⟨paste_visible hg1 L.two.visP S.two.visP,
      paste_mono L.two.vle S.two.vle, paste_mono L.two.le01 S.two.le01,
      paste_coupling L.two.coup S.two.coup,
      paste_visible hg1 L.two.vis0 S.two.vis0, paste_visible hg1 L.two.vis1 S.two.vis1,
      paste_visible hg2 L.two.visH S.two.visH, paste_mono L.two.Hle S.two.Hle, ?_⟩
    rw [← paste_min]
    exact paste_visible hg2 L.two.vismin S.two.vismin
  refine ⟨htwo, paste_mono L.z12 S.z12, paste_mono L.z2x S.z2x,
    paste_mono L.z2w S.z2w, paste_mono L.wH S.wH,
    paste_visible hg L.vis1 S.vis1, paste_visible hg L.vis2 S.vis2,
    paste_visible hg L.visw S.visw, ?_, ?_, ?_,
    paste_coupling L.coup₃ S.coup₃, ?_⟩
  · rw [← paste_min]
    exact paste_visible hg L.vismin S.vismin
  · let R : ExtOrd → ExtOrd := fun x => extVisibilityReplace x 3 3
    have hR : Monotone R := fun _ _ h => evr_mono h le_rfl
    have hw : R w = w := L.visw
    have hw' : R w' = w' := S.visw
    have hpw : R (paste g w w') = paste g w w' := paste_visible hg L.visw S.visw
    change paste g z₁ z₁' = R (min (paste g v v') (paste g w w'))
    calc
      paste g z₁ z₁' = paste g (min (R v) w) (min (R v') w') := by
        rw [L.orbit, S.orbit]
        change paste g (R (min v w)) (R (min v' w')) = _
        rw [hR.map_min, hR.map_min, hw, hw']
      _ = min (paste g (R v) (R v')) (paste g w w') := paste_min _ _ _ _ _
      _ = min (R (paste g v v')) (paste g w w') := by
        rw [← map_paste_of_agree R hR hg hv]
      _ = R (min (paste g v v') (paste g w w')) := by rw [hR.map_min, hpw]
  · rw [← paste_min]
    exact paste_fixed (fun x => extVisibilityReplace x 3 1)
      (fix₃₁_of_selfVis₃ hg) L.fix S.fix
  · rw [← paste_min]
    exact paste_coupling L.coup₄ S.coup₄

/-- **Pasting the parameters is cellwise pasting** (the dependent value `min x₀ H` through
`paste_min`). -/
theorem shape_paste {q s : D₂.below (Finset.univ, 3) → ExtOrd}
    {v x₀ x₁ H z₁ z₂ w v' x₀' x₁' H' z₁' z₂' w' : ExtOrd}
    (Q : Shape₃ q v x₀ x₁ H z₁ z₂ w) (S : Shape₃ s v' x₀' x₁' H' z₁' z₂' w') (g : ExtOrd) :
    Shape₃ (fun d => paste g (q d) (s d))
      (paste g v v') (paste g x₀ x₀') (paste g x₁ x₁') (paste g H H')
      (paste g z₁ z₁') (paste g z₂ z₂') (paste g w w') where
  at_H₀old := by rw [Q.at_H₀old, S.at_H₀old]
  at_H₀new := by rw [Q.at_H₀new, S.at_H₀new]
  at_U_H := by rw [Q.at_U_H, S.at_U_H]
  at_s₀old := by rw [Q.at_s₀old, S.at_s₀old, paste_min]
  at_s₀new := by rw [Q.at_s₀new, S.at_s₀new]
  at_U_S := by rw [Q.at_U_S, S.at_U_S]
  at_a₁old := by rw [Q.at_a₁old, S.at_a₁old]
  at_A₁c := by rw [Q.at_A₁c, S.at_A₁c]
  at_a₂old := by rw [Q.at_a₂old, S.at_a₂old]
  at_A₂c := by rw [Q.at_A₂c, S.at_A₂c]
  at_b₁new := by rw [Q.at_b₁new, S.at_b₁new]
  at_ub₁ := by rw [Q.at_ub₁, S.at_ub₁]
  at_proper d hd := by
    rw [Q.at_proper d hd, S.at_proper d hd]
    split_ifs
    · exact paste_bot g
    · rfl

/-- **Two respecting labellings whose proper values agree below a grade-three-visible cap paste
to a respecting labelling.** -/
theorem respects_paste_of_proper_agreement {q s : D₂.below (Finset.univ, 3) → ExtOrd}
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (hs : RespectsSemanticsBelow rowsR (Finset.univ, 3) s)
    (sc : D₂.below (Finset.univ, 3)) (hsc : IsProper sc.1) (hgrade : D₂.grade sc.1 = 1)
    (s1 : D₂.below (Finset.univ, 3)) (hs1 : IsProper s1.1) (hs1c : D₂.cell s1.1 = ({1}, 1))
    {g : ExtOrd} (hg : SelfVis 3 g) (hagree : min (q sc) g = min (s sc) g) :
    RespectsSemanticsBelow rowsR (Finset.univ, 3) (fun d => paste g (q d) (s d)) := by
  obtain ⟨Q, LQ⟩ := shape_legal_of_respectsR hq sc hsc hgrade s1 hs1 hs1c
  obtain ⟨S, LS⟩ := shape_legal_of_respectsR hs sc hsc hgrade s1 hs1 hs1c
  exact respects_of_shape₃ (legal_paste_of_proper_agreement LQ LS hg hagree) (shape_paste Q S g)

/-- **Sections give the relative lift**: a prescribed labelling `p` on a protected collection of
cells containing a proper grade-one anchor, a respecting section `s` extending it literally, and
a respecting ambient labelling `q` agreeing with `p` below a grade-three-visible cap have a
common refinement — the cellwise paste — respecting `rowsR`, literally `p` on the collection,
and agreeing with `q` below the cap on every cell. -/
theorem relative_lift_of_section {I : Type*} (embed : I → D₂.below (Finset.univ, 3)) (anchor : I)
    (hprotected : IsProper (embed anchor).1) (hgrade : D₂.grade (embed anchor).1 = 1)
    (s1 : D₂.below (Finset.univ, 3)) (hs1 : IsProper s1.1) (hs1c : D₂.cell s1.1 = ({1}, 1))
    (p : I → ExtOrd) (q s : D₂.below (Finset.univ, 3) → ExtOrd)
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (hs : RespectsSemanticsBelow rowsR (Finset.univ, 3) s)
    (hsection : ∀ d, s (embed d) = p d) {g : ExtOrd} (hg : SelfVis 3 g)
    (hagree : ∀ d, min (q (embed d)) g = min (p d) g) :
    ∃ r : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) r ∧
      (∀ d, min (r d) g = min (q d) g) ∧ (∀ d, r (embed d) = p d) := by
  refine ⟨fun d => paste g (q d) (s d), ?_, fun d => paste_cap g (q d) (s d), ?_⟩
  · apply respects_paste_of_proper_agreement hq hs (embed anchor) hprotected hgrade s1 hs1 hs1c hg
    rw [hsection anchor]
    exact hagree anchor
  · intro d
    change paste g (q (embed d)) (s (embed d)) = p d
    rw [hsection d]
    exact paste_eq_of_agree (hagree d)

end SharedProbe

/-! ## The two face obligations: the relative lift at the two face sections -/

section FaceLifts

/-- **The A-face obligation**: a labelling respecting the repaired semantics on the old face
`({0,1,2}, 3)` and one respecting it on `(univ, 3)`, agreeing on the face below a
grade-three-visible cap, have a common refinement — the paste with the A-face section. -/
theorem faceA_liftR (p : D₂.below faceA → ExtOrd) (hp : RespectsSemanticsBelow rowsR faceA p)
    (q : D₂.below (Finset.univ, 3) → ExtOrd) (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (γ : ExtOrd) (hγ : SelfVis 3 γ)
    (hagree : ∀ d : D₂.below faceA, min (q (CellScheme.below.mono faceA_le d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below faceA, q' (CellScheme.below.mono faceA_le d) = p d) := by
  obtain ⟨s, hs, hsp⟩ := faceA_extendsR p hp
  obtain ⟨s1, hs1c⟩ := D₂_complete _ hsing₁
  have hs1A : GradedLe (D₂.cell s1) faceA := by rw [hs1c]; exact ⟨by decide, by decide⟩
  have hs1P : IsProper s1 := isProper_of_cell_singleton s1 1 hs1c
  have hg1 : D₂.grade s1 = 1 := by change (D₂.cell s1).2 = 1; rw [hs1c]
  exact relative_lift_of_section (CellScheme.below.mono faceA_le) ⟨s1, hs1A⟩ hs1P hg1
    ⟨s1, hs1A.trans faceA_le⟩ hs1P hs1c p q s hq hs hsp hγ hagree

/-- **The B-face obligation**: the same for the copy face `({1,2,3}, 3)`, with the B-face
section. -/
theorem faceB_liftR (p : D₂.below faceB → ExtOrd) (hp : RespectsSemanticsBelow rowsR faceB p)
    (q : D₂.below (Finset.univ, 3) → ExtOrd) (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (γ : ExtOrd) (hγ : SelfVis 3 γ)
    (hagree : ∀ d : D₂.below faceB, min (q (CellScheme.below.mono faceB_le d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below faceB, q' (CellScheme.below.mono faceB_le d) = p d) := by
  obtain ⟨s, hs, hsp⟩ := faceB_extendsR p hp
  obtain ⟨s1, hs1c⟩ := D₂_complete _ hsing₁
  have hs1B : GradedLe (D₂.cell s1) faceB := by rw [hs1c]; exact ⟨by decide, by decide⟩
  have hs1P : IsProper s1 := isProper_of_cell_singleton s1 1 hs1c
  have hg1 : D₂.grade s1 = 1 := by change (D₂.cell s1).2 = 1; rw [hs1c]
  exact relative_lift_of_section (CellScheme.below.mono faceB_le) ⟨s1, hs1B⟩ hs1P hg1
    ⟨s1, hs1B.trans faceB_le⟩ hs1P hs1c p q s hq hs hsp hγ hagree

end FaceLifts

/-! ## The scope-changing obligation at grade three, and bountifulness -/

section Bountiful

theorem card_univ_fin4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
theorem mem_faceA_of_ne_three : ∀ x : Fin 4, x ≠ 3 → x ∈ ({0, 1, 2} : Finset (Fin 4)) := by
  decide
theorem mem_faceB_of_ne_zero : ∀ x : Fin 4, x ≠ 0 → x ∈ ({1, 2, 3} : Finset (Fin 4)) := by
  decide

/-- **The scope-changing obligation at target grade three**: below grade three through the
transferred endpoints and full-scope bountifulness; at grade three, the proper side is one of the
two protected faces, and the face lift applies. -/
theorem properToFullR_three (CI : Finset (Fin 4) × ℕ) (hCI : CI ∈ Plan.gradedPlan plan₄)
    (hC : CI.1 ≠ Finset.univ) (hU : (Finset.univ, 3) ∈ Plan.gradedPlan plan₄)
    (h : GradedLe CI (Finset.univ, 3))
    (p : D₂.below CI → ExtOrd) (q : D₂.below (Finset.univ, 3) → ExtOrd) (γ : ExtOrd)
    (hp : RespectsSemanticsBelow rowsR CI p) (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (hγ : extVisibilityReplace γ 3 3 = γ)
    (hagree : ∀ d : D₂.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D₂.below (Finset.univ, 3) → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q' ∧
      (∀ d, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D₂.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨C, i⟩ := CI
  obtain ⟨hCp, hi0, hic⟩ := Plan.mem_gradedPlan.mp hCI
  dsimp only at hCp hi0 hic hC
  have hi3 : i ≤ 3 := h.2
  have hUp : (Finset.univ : Finset (Fin 4)) ∈ plan₄ := (Plan.mem_gradedPlan.mp hU).1
  by_cases hi2 : i ≤ 2
  · have hi : GradedLe ((Finset.univ : Finset (Fin 4)), i) (Finset.univ, 3) :=
      ⟨Finset.Subset.refl _, hi3⟩
    have hCi : GradedLe (C, i) (Finset.univ, i) := ⟨Finset.subset_univ _, le_rfl⟩
    have hUi : ((Finset.univ : Finset (Fin 4)), i) ∈ Plan.gradedPlan plan₄ :=
      Plan.mem_gradedPlan.mpr ⟨hUp, hi0, by rw [card_univ_fin4]; omega⟩
    have hγi : extVisibilityReplace γ i i = γ := (show SelfVis 3 γ from hγ).mono hi3
    obtain ⟨qᵢ, hqᵢ, hqᵢγ, hqᵢext⟩ := properToFullR_of_le_two (C, i) i hi2 hCI hC hUi hCi p
      (fun d => q (CellScheme.below.mono hi d)) γ hp (hq.mono hi) hγi (fun d => hagree d)
    obtain ⟨q', hq', hq'γ, hq'ext⟩ :=
      bountiful_full_scope rowsR hi qᵢ q γ hqᵢ hq hγ (fun d => (hqᵢγ d).symm)
    refine ⟨q', hq', hq'γ, fun d => ?_⟩
    have e : CellScheme.below.mono h d =
        CellScheme.below.mono hi (CellScheme.below.mono hCi d) := rfl
    rw [e, hq'ext, hqᵢext]
  · have hi3' : i = 3 := by omega
    subst hi3'
    rcases proper_side C hCp hC with h3 | h0
    · have hCe : C = {0, 1, 2} := Finset.eq_of_subset_of_card_le
        (fun x hx => mem_faceA_of_ne_three x fun e => h3 (e ▸ hx))
        (by rw [show ({0, 1, 2} : Finset (Fin 4)).card = 3 from by decide]; exact hic)
      subst hCe
      exact faceA_liftR p hp q hq γ hγ hagree
    · have hCe : C = {1, 2, 3} := Finset.eq_of_subset_of_card_le
        (fun x hx => mem_faceB_of_ne_zero x fun e => h0 (e ▸ hx))
        (by rw [show ({1, 2, 3} : Finset (Fin 4)).card = 3 from by decide]; exact hic)
      subst hCe
      exact faceB_liftR p hp q hq γ hγ hagree

/-- **The scope-changing obligation of the repaired semantics holds at every grade.** -/
theorem properToFullR : ProperToFullRLow := by
  intro CI j hj hCI hC hU h p q γ hp hq hγ hagree
  by_cases hj2 : j ≤ 2
  · exact properToFullR_of_le_two CI j hj2 hCI hC hU h p q γ hp hq hγ hagree
  · have hj3 : j = 3 := by omega
    subst hj3
    exact properToFullR_three CI hCI hC hU h p q γ hp hq hγ hagree

/-- **The repaired semantics is bountiful.** -/
theorem rowsR_isBountiful : rowsR.IsBountiful := rowsR_isBountiful_of properToFullR

/-- **The repaired coupled domain**: unconditional. -/
noncomputable def semSchemeR : SemScheme 4 where
  scheme := D₂
  rows := rowsR
  rows_coded := rowsR_coded
  consistent := rowsR_consistent
  bountiful := rowsR_isBountiful
  complete := D₂_complete

/-- **The repaired construction realizes the prescribed pair**: a coded, consistent, bountiful
semantics on the glued scheme, agreeing with the fixed glue on both input faces, together with a
respecting labelling of the full grade-three lower set realizing the original prescribed pair. -/
theorem repaired_realization :
    ∃ sem : Semantics D₂, sem.IsCoded ∧ sem.IsConsistent ∧ sem.IsBountiful ∧
      (∀ (i : Cell C₀) (d : D₂.below (D₂.cell (Fin.castAdd (Fintype.card New₂) i))),
        sem.E (Fin.castAdd (Fintype.card New₂) i) d =
          rows₂.E (Fin.castAdd (Fintype.card New₂) i) d) ∧
      (∀ (c : Cell C₁) (d : D₂.below (D₂.cell (copyB c))),
        sem.E (copyB c) d = rows₂.E (copyB c) d) ∧
      ∃ q : D₂.below (Finset.univ, 3) → ExtOrd,
        RespectsSemanticsBelow sem (Finset.univ, 3) q ∧ RealizesPair q :=
  ⟨rowsR, rowsR_coded, rowsR_consistent, rowsR_isBountiful,
    fun i d => rowsR_E_of_A (aFace_castAdd i) d, fun c d => rowsR_E_of_B (copyB_mem c) d,
    fun d => qL d.1, qL_respectsR, qL_realizes⟩

end Bountiful

end VaughtConjecture.Knight
