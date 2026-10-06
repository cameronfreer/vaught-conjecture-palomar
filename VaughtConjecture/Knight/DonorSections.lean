/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AdmissibleDonors

/-! # Sections of one mixed incidence: bottom caps and positive caps

The reviewer's task (2026-09-15, item 2): at a unique old controller, test a source refinement
that preserves the controller's own source order and retains the distinctions the selected
display erases, while adding the fresh reading; construct the incoming and outgoing faithful
witnesses explicitly, including clause 5; then prove bottom-cap sections for arbitrary lawful
prescribed old faces, not merely the selected display; if successful, test positive caps
against arbitrary lawful target-local ambients.

**The refinement is the controller's own row.**  At a mixed donor `D` the mixed row
(`MixedDonor.mixedSource`) is the donor's row itself on its old lower domain — so it preserves
the donor's source order and retains every distinction, in particular those the display's
capping erases — extended by the fresh reading, the visibility replacement of the donor's
reading of the representative at the requested offset.  Its incoming witnesses are the
receiver's own localities (`old_to_donor_locality`) and the self-visible constant at the fresh
cell (`fresh_to_donor_locality`); its outgoing witness for the selected display is the donor's
exact witness with clause 5 at the donor's grade (`mixed_transformsTo`).  At a unique old
controller the donor is the only candidate at its index, and the diagonal test of
`AdmissibleDonors` reduces to its admissibility (`unique_diagonal_iff`).

**Bottom-cap sections for arbitrary lawful old faces.**  For *every* respecting labelling `p`
of the donor's old lower domain — not only the display — the mixed row transforms to `p`
extended by the forced fresh reading `sectionFresh p` (the replacement at the donor's grade of
`p`'s capped value at the representative), capped at `p`'s value at the donor
(`section_transformsTo`, witness: the exact capped witness of `p`, clause 5 at the donor's
grade).  The forced reading is self-visible at every grade at most the requested offset
(`sectionFresh_selfVis`).  Hence every lawful section of any proper old sub-index extends,
through the receiver's own bottom-cap bountifulness, to a lawful old face and then to the mixed
carrier (`bottomCap_section`).

**Positive caps against arbitrary lawful ambients.**  Any labelling `q` of the mixed carrier
to which the mixed row transforms, capped at `q`'s value at the donor, reads the fresh cell,
capped at the donor, as the replacement of its own capped value at the representative
(`capped_fresh`, the analogue of `ReferenceOrbitRow.capped_orbit`).  Given such a `q` and a
lawful old face `p` agreeing with `q` under a cap `γ` self-visible at the donor's grade, the
repaired labelling — `p` on old cells, at the fresh cell the forced reading when it is strictly
below `p`'s donor value and otherwise the larger of that value and `q`'s fresh reading — agrees
with `q` under `γ` everywhere (`repairedFresh_agree`), is self-visible at the fresh grade
(`repairedFresh_selfVis`), and is a faithful capped target of the mixed row
(`repaired_transformsTo`).  This is the positive-cap completion at one mixed incidence: the
donor's locality, orderliness and the fresh cell's own locality.  It is not whole-domain
bountifulness: the carrier has one fresh cell and no intermediate mixed cells, and availability
toward mixed indices is the coverage obligation of `AdmissibleDonors`.

Two inequalities for capped replacement carry the case analysis: a value at least a
`K`-self-visible `γ` stays at least `γ` after replacement at threshold `K`
(`le_extVisibilityReplace_of_le`), and replacement respects agreement under such a `γ`
(`min_extVisibilityReplace_eq`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## Capped visibility replacement -/

/-- **Replacement stays above a self-visible cap**: if `γ ≤ y` and `γ` is `K`-self-visible,
then `γ ≤ extVisibilityReplace y K m`. -/
theorem le_extVisibilityReplace_of_le {K m : ℕ} {y γ : ExtOrd} (hγ : SelfVis K γ) (hy : γ ≤ y) :
    γ ≤ extVisibilityReplace y K m := by
  rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
  · rw [extVisibilityReplace_bot]; exact hy
  · rw [extVisibilityReplace_top]; exact le_top
  · rcases ExtOrd.cases γ with rfl | rfl | ⟨c, rfl⟩
    · exact bot_le
    · exact absurd hy (not_top_le_ofOrd β)
    · have hc : K ≤ finitePart c := selfVis_ofOrd_iff.mp hγ
      have hcβ : c ≤ β := ofOrd_le_ofOrd.mp hy
      rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
      unfold visibilityReplace
      split_ifs with hβ
      · unfold ordinalReplace
        rcases (limitPart_mono hcβ).lt_or_eq with hlt | heq
        · have h := limitPart_add_omega0_le hlt
          calc c = limitPart c + (finitePart c : Ordinal) := (decomposition c).symm
            _ ≤ limitPart c + Ordinal.omega0 :=
                add_le_add_right (Ordinal.natCast_lt_omega0 _).le _
            _ ≤ limitPart β := h
            _ ≤ limitPart β + (m : Ordinal) := le_self_add
        · exfalso
          have h1 : limitPart c + (finitePart c : Ordinal) ≤
              limitPart c + (finitePart β : Ordinal) := by
            rw [decomposition c, heq, decomposition β]
            exact hcβ
          have h2 : finitePart c ≤ finitePart β := by
            exact_mod_cast (add_le_add_iff_left _).mp h1
          omega
      · exact hcβ

/-- **Replacement respects agreement under a self-visible cap.** -/
theorem min_extVisibilityReplace_eq {K m : ℕ} {y y' γ : ExtOrd} (hγ : SelfVis K γ)
    (h : min y γ = min y' γ) :
    min (extVisibilityReplace y K m) γ = min (extVisibilityReplace y' K m) γ := by
  rcases le_or_gt γ y with hy | hy
  · rcases le_or_gt γ y' with hy' | hy'
    · rw [min_eq_right (le_extVisibilityReplace_of_le hγ hy),
        min_eq_right (le_extVisibilityReplace_of_le hγ hy')]
    · rw [min_eq_right hy, min_eq_left hy'.le] at h
      exact absurd hy' (not_lt.mpr h.le)
  · rw [min_eq_left hy.le] at h
    rcases le_or_gt γ y' with hy' | hy'
    · rw [min_eq_right hy'] at h
      exact absurd hy (not_lt.mpr h.ge)
    · rw [min_eq_left hy'.le] at h
      rw [h]

private theorem min_min_right_distrib (a b γ : ExtOrd) :
    min (min a b) γ = min (min a γ) (min b γ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (min_le_min_right γ h)]
  · rw [min_eq_right h, min_eq_right (min_le_min_right γ h)]

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

/-! ## A unique old controller -/

/-- **At a unique old controller the diagonal test is admissibility**: the only coindexed cell
is the controller itself. -/
theorem unique_diagonal_iff (g₀ : ℕ) {BJ : Finset (Fin C.m) × ℕ}
    (c : C.p₀.scheme.scheme.below BJ)
    (huniq : ∀ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 → w.1 = c.1) :
    (∃ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 ∧
        C.pool i g₀ BJ (CellScheme.below.incl c w) ∧
        C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ C.p₀.scheme.rows.E c.1 w) ↔
      C.Admissible i g₀ c.1 := by
  constructor
  · rintro ⟨w, hw, ha, -⟩
    have h : w.1 = c.1 := huniq w hw
    change C.Admissible i g₀ w.1 at ha
    rw [h] at ha
    exact ha
  · intro h
    exact ⟨⟨c.1, GradedLe.refl _⟩, rfl, h, le_rfl⟩

namespace MixedDonor

variable (D : C.MixedDonor i)

/-! ## The forced fresh reading under an arbitrary lawful old face -/

/-- **The forced fresh reading** under a labelling `p` of the donor's lower domain: the
replacement, at the donor's grade with the requested offset, of `p`'s capped value at the
representative. -/
noncomputable def sectionFresh (p : D.Old → ExtOrd) : ExtOrd :=
  extVisibilityReplace (min (p D.rep) (p D.owner)) (C.p₀.scheme.scheme.grade D.cell)
    reqs[i.val].offset

/-- The forced reading is at most `p`'s value at the donor. -/
theorem sectionFresh_le (p : D.Old → ExtOrd) (hvis : SelfVis (C.p₀.scheme.scheme.grade D.cell)
    (p D.owner)) : D.sectionFresh p ≤ p D.owner :=
  extVisibilityReplace_le_of_le_selfVis D.offset_le hvis (min_le_right _ _)

/-- The forced reading is self-visible at every grade at most the requested offset. -/
theorem sectionFresh_selfVis (p : D.Old → ExtOrd) {g₀ : ℕ} (hg₀ : g₀ ≤ reqs[i.val].offset) :
    SelfVis g₀ (D.sectionFresh p) := by
  unfold sectionFresh
  rcases ExtOrd.cases (min (p D.rep) (p D.owner)) with h | h | ⟨β, h⟩ <;> rw [h]
  · exact extVisibilityReplace_bot _ _
  · exact extVisibilityReplace_top _ _
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff]
    unfold visibilityReplace
    split_ifs with hβ
    · unfold ordinalReplace
      rw [finitePart_limitPart_add_nat]
      exact hg₀
    · exact hg₀.trans (D.offset_le.trans (not_lt.mp hβ))

/-- **The outgoing witness for an arbitrary lawful old face**: the mixed row transforms to `p`
extended by the forced fresh reading, capped at `p`'s value at the donor.  The witness is the
exact capped witness of `p`; clause 5 is applied at the donor's grade, where the suppressor is
`⊤`. -/
theorem section_transformsTo (p : D.Old → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p)
    (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) :
    TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
      D.mixedSource (fun x => min (Sum.elim p (fun _ => D.sectionFresh p) x) (p D.owner)) := by
  have hloc : TransformsTo (fun d : D.Old => C.p₀.scheme.scheme.grade d.1)
      (C.p₀.scheme.rows.E D.cell) (fun d => min (p d) (p D.owner)) := hp.locality D.owner
  obtain ⟨τ, hτ, -, hread⟩ : ∃ τ : ExtOrd → ExtOrd,
      Witness (gTop (C.p₀.scheme.scheme.grade D.cell)) τ ∧ (∀ x, τ x ≤ p D.owner) ∧
      ∀ d : D.Old, τ (C.p₀.scheme.rows.E D.cell d) = min (p d) (p D.owner) :=
    exists_bounded_exact_capped_witness (c := D.owner) (p := p) (fun d => d.2.2)
      (hp.orderly D.owner).symm hloc
  apply hτ.transformsTo
  intro x
  rcases x with d | u
  · change min (p d) (p D.owner) = min (τ (D.mixedSource (Sum.inl d)))
      (gTop (C.p₀.scheme.scheme.grade D.cell) (C.p₀.scheme.scheme.grade d.1))
    rw [mixedSource_old, gTop_of_le (show C.p₀.scheme.scheme.grade d.1 ≤
      C.p₀.scheme.scheme.grade D.cell from d.2.2), min_top_right, hread]
  · change min (D.sectionFresh p) (p D.owner) = min (τ (D.mixedSource (Sum.inr ())))
      (gTop (C.p₀.scheme.scheme.grade D.cell) g₀)
    rw [gTop_of_le hg₀, min_top_right, mixedSource_fresh, hτ.clause5 _ _
      (by rw [gTop_of_le le_rfl]; exact le_top) _ D.offset_le, hread D.rep]
    exact min_eq_left (D.sectionFresh_le p (hp.orderly D.owner).symm)

/-- **Bottom-cap sections for arbitrary lawful prescribed old faces**: every respecting
labelling of a proper old sub-index of the donor extends, through the receiver's own
bottom-cap bountifulness, to a respecting labelling of the donor's lower domain, which the
mixed row carries to the mixed carrier with the forced fresh reading. -/
theorem bottomCap_section (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    {CI : Finset (Fin C.m) × ℕ} (hCI : CI ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan)
    (hle : GradedLe CI (C.p₀.scheme.scheme.cell D.cell)) (hne : CI ≠ C.p₀.scheme.scheme.cell D.cell)
    (p : C.p₀.scheme.scheme.below CI → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows CI p) :
    ∃ p' : D.Old → ExtOrd,
      RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p' ∧
      (∀ d : C.p₀.scheme.scheme.below CI, p' (CellScheme.below.mono hle d) = p d) ∧
      TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
        D.mixedSource
        (fun x => min (Sum.elim p' (fun _ => D.sectionFresh p') x) (p' D.owner)) := by
  obtain ⟨p', hp', -, hres⟩ := C.p₀.scheme.bountiful CI _ hCI
    (C.p₀.scheme.scheme.cell_mem D.cell) hle hne p (fun _ => ⊥) ⊥ hp (respectsBelow_bot _ _)
    (extVisibilityReplace_bot _ _) (fun _ => by rw [min_eq_right bot_le, min_eq_right bot_le])
  exact ⟨p', hp', hres, D.section_transformsTo p' hp' g₀ hg₀⟩

/-! ## Positive caps against arbitrary lawful ambients -/

/-- **Every faithful capped target of the mixed row reads the fresh cell by the replacement
equation** (the analogue of `ReferenceOrbitRow.capped_orbit`): capped at the donor, the fresh
reading is the replacement of the target's capped value at the representative. -/
theorem capped_fresh (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell)
    (q : D.Old ⊕ Unit → ExtOrd)
    (hvis : SelfVis (C.p₀.scheme.scheme.grade D.cell) (q (Sum.inl D.owner)))
    (hloc : TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
      D.mixedSource (fun x => min (q x) (q (Sum.inl D.owner)))) :
    min (q (Sum.inr ())) (q (Sum.inl D.owner)) =
      extVisibilityReplace (min (q (Sum.inl D.rep)) (q (Sum.inl D.owner)))
        (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset := by
  have hmax : ∀ x : D.Old ⊕ Unit,
      Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ : Unit => g₀) x ≤
        C.p₀.scheme.scheme.grade D.cell := by
    intro x
    rcases x with d | u
    · exact d.2.2
    · exact hg₀
  obtain ⟨τ, hτ, -, hread⟩ : ∃ τ : ExtOrd → ExtOrd,
      Witness (gTop (C.p₀.scheme.scheme.grade D.cell)) τ ∧
      (∀ x, τ x ≤ q (Sum.inl D.owner)) ∧
      ∀ d, τ (D.mixedSource d) = min (q d) (q (Sum.inl D.owner)) :=
    exists_bounded_exact_capped_witness hmax hvis hloc
  have hnew := hread (Sum.inr ())
  have href := hread (Sum.inl D.rep)
  rw [mixedSource_fresh, hτ.clause5 _ (C.p₀.scheme.scheme.grade D.cell)
    (by rw [gTop_of_le le_rfl]; exact le_top) _ D.offset_le] at hnew
  rw [mixedSource_old] at href
  rw [href] at hnew
  exact hnew.symm

/-- **The repaired fresh reading** for a positive cap: the forced reading when it is strictly
below `p`'s donor value, otherwise the larger of that value and the ambient's fresh reading. -/
noncomputable def repairedFresh (p : D.Old → ExtOrd) (F : ExtOrd) : ExtOrd :=
  if D.sectionFresh p < p D.owner then D.sectionFresh p else max (p D.owner) F

/-- The repaired labelling is a faithful capped target of the mixed row (for any ambient fresh
reading). -/
theorem repaired_transformsTo (p : D.Old → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p)
    (g₀ : ℕ) (hg₀ : g₀ ≤ C.p₀.scheme.scheme.grade D.cell) (F : ExtOrd) :
    TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
      D.mixedSource
      (fun x => min (Sum.elim p (fun _ => D.repairedFresh p F) x) (p D.owner)) := by
  have h := D.section_transformsTo p hp g₀ hg₀
  convert h using 1
  funext x
  rcases x with d | u
  · rfl
  · change min (D.repairedFresh p F) (p D.owner) = min (D.sectionFresh p) (p D.owner)
    unfold repairedFresh
    split_ifs with hlt
    · rfl
    · have heq : D.sectionFresh p = p D.owner :=
        le_antisymm (D.sectionFresh_le p (hp.orderly D.owner).symm) (not_lt.mp hlt)
      rw [heq, min_eq_right (le_max_left _ _), min_self]

/-- The repaired fresh reading is self-visible at the fresh grade. -/
theorem repairedFresh_selfVis (p : D.Old → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p)
    {g₀ : ℕ} (hg₀ : g₀ ≤ reqs[i.val].offset) {F : ExtOrd} (hF : SelfVis g₀ F) :
    SelfVis g₀ (D.repairedFresh p F) := by
  unfold repairedFresh
  split_ifs
  · exact D.sectionFresh_selfVis p hg₀
  · rcases le_total (p D.owner) F with h | h
    · rw [max_eq_right h]; exact hF
    · rw [max_eq_left h]
      have hK : SelfVis (C.p₀.scheme.scheme.grade D.cell) (p D.owner) := (hp.orderly D.owner).symm
      exact hK.mono (hg₀.trans D.offset_le)

/-- **Positive-cap agreement**: for a lawful ambient `q` of the mixed carrier and a lawful old
face `p` agreeing with `q` under a cap `γ` self-visible at the donor's grade, the repaired
fresh reading agrees with `q`'s fresh reading under `γ`. -/
theorem repairedFresh_agree (g₀ : ℕ) (hg₀ : g₀ ≤ reqs[i.val].offset) {γ : ExtOrd}
    (hγ : SelfVis (C.p₀.scheme.scheme.grade D.cell) γ) (p : D.Old → ExtOrd)
    (hp : RespectsSemanticsBelow C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell) p)
    (q : D.Old ⊕ Unit → ExtOrd)
    (hqvis : SelfVis (C.p₀.scheme.scheme.grade D.cell) (q (Sum.inl D.owner)))
    (hloc : TransformsTo (Sum.elim (fun d : D.Old => C.p₀.scheme.scheme.grade d.1) (fun _ => g₀))
      D.mixedSource (fun x => min (q x) (q (Sum.inl D.owner))))
    (hagree : ∀ d : D.Old, min (q (Sum.inl d)) γ = min (p d) γ) :
    min (D.repairedFresh p (q (Sum.inr ()))) γ = min (q (Sum.inr ())) γ := by
  have hE := D.capped_fresh g₀ (hg₀.trans D.offset_le) q hqvis hloc
  have hφ : D.sectionFresh p = extVisibilityReplace (min (p D.rep) (p D.owner))
      (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset := rfl
  have hy : min (min (p D.rep) (p D.owner)) γ =
      min (min (q (Sum.inl D.rep)) (q (Sum.inl D.owner))) γ := by
    rw [min_min_right_distrib, ← hagree D.rep, ← hagree D.owner, ← min_min_right_distrib]
  have hRγ : min (D.sectionFresh p) γ = min (extVisibilityReplace
      (min (q (Sum.inl D.rep)) (q (Sum.inl D.owner))) (C.p₀.scheme.scheme.grade D.cell)
      reqs[i.val].offset) γ := by
    rw [hφ]
    exact min_extVisibilityReplace_eq hγ hy
  have ho : min (p D.owner) γ = min (q (Sum.inl D.owner)) γ := (hagree D.owner).symm
  have hφle : D.sectionFresh p ≤ p D.owner := D.sectionFresh_le p (hp.orderly D.owner).symm
  -- below the cap the donor values agree and so do the capped representative values
  have hlow : q (Sum.inl D.owner) < γ → p D.owner = q (Sum.inl D.owner) ∧
      min (p D.rep) (p D.owner) = min (q (Sum.inl D.rep)) (q (Sum.inl D.owner)) := by
    intro hlt
    have ho' : p D.owner = q (Sum.inl D.owner) := by
      rw [min_eq_left hlt.le] at ho
      rcases le_or_gt (p D.owner) γ with h | h
      · rw [min_eq_left h] at ho; exact ho
      · rw [min_eq_right h.le] at ho
        exact absurd hlt (not_lt.mpr ho.le)
    refine ⟨ho', ?_⟩
    have hr := hagree D.rep
    have hoγ : p D.owner ≤ γ := ho' ▸ hlt.le
    calc min (p D.rep) (p D.owner) = min (min (p D.rep) γ) (p D.owner) := by
          rw [min_assoc, min_eq_right hoγ]
      _ = min (min (q (Sum.inl D.rep)) γ) (p D.owner) := by rw [hr]
      _ = min (q (Sum.inl D.rep)) (p D.owner) := by rw [min_assoc, min_eq_right hoγ]
      _ = min (q (Sum.inl D.rep)) (q (Sum.inl D.owner)) := by rw [ho']
  unfold repairedFresh
  split_ifs with hlt
  · rcases le_or_gt γ (q (Sum.inl D.owner)) with h | h
    · calc min (D.sectionFresh p) γ = _ := hRγ
        _ = min (min (q (Sum.inr ())) (q (Sum.inl D.owner))) γ := by rw [hE]
        _ = min (q (Sum.inr ())) γ := by rw [min_assoc, min_eq_right h]
    · obtain ⟨ho', hyy⟩ := hlow h
      have hF : q (Sum.inr ()) = D.sectionFresh p := by
        have h1 : min (q (Sum.inr ())) (q (Sum.inl D.owner)) = D.sectionFresh p := by
          rw [hE, ← hyy, ← hφ]
        rcases le_or_gt (q (Sum.inr ())) (q (Sum.inl D.owner)) with hFo | hFo
        · rw [min_eq_left hFo] at h1; exact h1
        · rw [min_eq_right hFo.le] at h1
          have : D.sectionFresh p < q (Sum.inl D.owner) := ho' ▸ hlt
          exact absurd this (not_lt.mpr h1.le)
      rw [hF]
  · have hφo : D.sectionFresh p = p D.owner := le_antisymm hφle (not_lt.mp hlt)
    rcases le_or_gt γ (q (Sum.inl D.owner)) with h | h
    · have hγo : γ ≤ p D.owner := by
        have h' := ho
        rw [min_eq_right h] at h'
        exact min_eq_right_iff.mp h'
      have hFγ : γ ≤ q (Sum.inr ()) := by
        have h1 : min (extVisibilityReplace (min (q (Sum.inl D.rep)) (q (Sum.inl D.owner)))
            (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset) γ = γ := by
          rw [← hRγ, hφo, min_eq_right hγo]
        have h2 := min_eq_right_iff.mp h1
        have h3 : extVisibilityReplace (min (q (Sum.inl D.rep)) (q (Sum.inl D.owner)))
            (C.p₀.scheme.scheme.grade D.cell) reqs[i.val].offset ≤ q (Sum.inr ()) := by
          rw [← hE]; exact min_le_left _ _
        exact h2.trans h3
      rw [min_eq_right (hγo.trans (le_max_left _ _)), min_eq_right hFγ]
    · obtain ⟨ho', hyy⟩ := hlow h
      have hFo : p D.owner ≤ q (Sum.inr ()) := by
        have h1 : min (q (Sum.inr ())) (q (Sum.inl D.owner)) = q (Sum.inl D.owner) := by
          rw [hE, ← hyy, ← hφ, hφo, ho']
        rw [ho']
        exact min_eq_right_iff.mp h1
      rw [max_eq_right hFo]

end MixedDonor

end ReferenceContext

end VaughtConjecture.Knight
