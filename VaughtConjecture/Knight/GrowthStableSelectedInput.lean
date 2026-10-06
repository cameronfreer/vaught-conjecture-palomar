/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFilteredRoot
public import VaughtConjecture.Knight.StableLiftCore
public import VaughtConjecture.Knight.ReceivingTemplate

/-! # Stable-root compatibility for selected growth donors

The donor extends the stable root, not the actual root. The stable labelling
of an actual private cover supplies a lawful compatible complete vector. This
uses the original model only, not modelhood of its stable lift. Admission is
proved below activation; calibrated request correctness above activation is
deliberately not assumed or asserted here.

The proper-field bound is at the next block. A proper stable value of an
actual top prevents replacing that bound by the original stage bound.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthStableSelectedInput
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open CellScheme.restrictFace
open SharpWitnessComposition
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  (hM : W.IsModel) {n J : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
  (hp : W.eval t = some p) {u : Fin J ↪ M} {C : S α.1 J}
  (hC : W.eval u = some C) {f : Fin n ↪ Fin J} (hfu : f.trans u = t)
  (hf : typeMap f C = some p)
  {q : S α.nextBlock.1 (n + 1)} (hq : IsCoface (stableLiftType hM t p hp) q)

include hfu in
/-- Stable face compatibility follows from consistency of the original model;
no occurrence of the chosen donor is assumed. -/
theorem stable_face :
    typeMap f (stableLiftType hM u C hC) = some (stableLiftType hM t p hp) := by
  have h := stableLift_consistent hM u (stableLiftType hM u C hC) f
    (stableLift_eval_some hM hC)
  rw [hfu, stableLift_eval_some hM hp] at h
  exact h.symm

/-- All fields are stored, including those beyond a later physical cutoff. -/
def state : Growth.State C.scheme.scheme q.scheme.scheme :=
  ⟨W.stableValue u C, q.label⟩

include hM hC in
theorem private_lawful : RespectsSemantics C.scheme.rows (state (W := W) (u := u)
    (C := C) (q := q)).privateValues := stableLiftRespects hM hC

theorem donor_lawful : RespectsSemantics q.scheme.rows (state (W := W) (u := u)
    (C := C) (q := q)).donorValues := q.respects

include hC hfu in
/-- The two actual occurrence maps, rather than an isomorphism of label
vectors, identify the complete root. -/
theorem root_readback (d : Cell p.scheme.scheme) :
    q.label (mapCell hq d) = W.stableValue u C (mapCell hf d) := by
  exact (label_mapCell hq d).trans
    (stableValue_mapCell hM.consistent hM.covering hp hC hfu hf d).symm

include hf hq in
/-- Both ordered schemes have the literal original root scheme. Only their
labellings have moved to the next block. -/
theorem common_faces :
    ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
      (hvC : Finset.univ.image f ∈ C.scheme.scheme.plan),
      q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme ∧
      C.scheme.restrictFace f hvC = p.scheme := by
  refine ⟨visible_of_typeMap_eq_some hq, visible_of_typeMap_eq_some hf, ?_, ?_⟩
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hq)
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hf)

/-- Exact criterion for mistakenly using the actual private vector. -/
theorem actual_root_compatible_iff :
    (∀ d : Cell p.scheme.scheme, q.label (mapCell hq d) = C.label (mapCell hf d)) ↔
      ∀ d, W.stableValue t p d = p.label d := by
  have hr (d : Cell p.scheme.scheme) :
      q.label (mapCell hq d) = W.stableValue t p d := label_mapCell hq d
  simp only [hr, label_mapCell hf]

/-- An actual root top with proper stable value obstructs the actual-label
recipe, even though both proposed component labellings are lawful. -/
theorem actual_root_obstruction (d : Cell p.scheme.scheme) (hd : p.label d = ⊤)
    (hs : W.stableValue t p d ≠ ⊤) :
    q.label (mapCell hq d) ≠ C.label (mapCell hf d) := by
  have hr : q.label (mapCell hq d) = W.stableValue t p d := label_mapCell hq d
  rwa [hr, label_mapCell hf, hd]

include hM hC in
theorem proper_bound (a : Growth.Field C.scheme.scheme q.scheme.scheme)
    (ha : (state (W := W) (u := u) (C := C) (q := q)).profile a ≠ ⊤) :
    (state (W := W) (u := u) (C := C) (q := q)).profile a < ofOrd α.nextBlock.1 := by
  cases a with
  | inl d => exact ((stableLiftType hM u C hC).label_bound d).resolve_right ha
  | inr d => exact (q.label_bound d).resolve_right ha

include hM hC in
/-- Stable private labels have the actual private bottom pattern, even where
they do not have the actual private values. -/
theorem private_bottom (d : Cell C.scheme.scheme) :
    W.stableValue u C d = ⊥ ↔ C.label d = ⊥ := by
  have h := truncExt_stableValue hM.consistent hM.covering hC d
  rw [← h]
  exact truncExt_eq_bot_iff.symm

include hM hC in
/-- Cleaning uses the actual top cap; decoding uses its independently lawful
stable labelling. Consequently a proper stable cap is no obstruction to
constructing the lawful cleaned source and its bounded reading chart. -/
theorem exists_cleaned_source_chart (c : Cell C.scheme.scheme) (hc : C.label c = ⊤) :
    ∃ e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd,
      RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e ∧
      (∀ d, e d = ⊥ ↔ C.label d.1 = ⊥) ∧
      (∀ d, C.label d.1 ≠ ⊥ → e d = C.scheme.rows.E c d) ∧
      ∃ θ : ExtOrd → ExtOrd, BoundedMap (C.scheme.scheme.grade c) θ ∧
        (∀ x, θ x ≤ W.stableValue u C c) ∧
        ∀ d, θ (e d) = min (W.stableValue u C d.1) (W.stableValue u C c) := by
  have hl := stableLiftRespects hM hC
  have hvis : SelfVis (C.scheme.scheme.grade c) (W.stableValue u C c) :=
    (hl.orderly c).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := C.scheme.scheme.below (C.scheme.scheme.cell c))
    (grade := fun d => C.scheme.scheme.grade d.1) (p := fun d => W.stableValue u C d.1)
    (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hl.locality c)
  have hcb : W.stableValue u C c ≠ ⊥ := by
    intro h
    exact top_ne_bot (hc.symm.trans ((private_bottom hM hC c).mp h))
  have hbottom (d : C.scheme.scheme.below (C.scheme.scheme.cell c)) :
      τ (C.scheme.rows.E c d) = ⊥ ↔ W.stableValue u C d.1 = ⊥ := by
    rw [hread d]
    exact ⟨fun h => (min_eq_bot.mp h).resolve_right hcb,
      fun h => by rw [h, min_eq_left bot_le]⟩
  let e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd :=
    fun d => if C.label d.1 = ⊥ then ⊥ else C.scheme.rows.E c d
  have he : RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e := by
    have h := cleaned_respects_of_bottom_agreement (C.scheme.consistent c) (hl.toBelow _)
      (fun d => d.2.2) ⟨hbot, hmono, hcomm⟩ hbottom
    simpa only [private_bottom hM hC] using h
  have heq (d) (hd : C.label d.1 ≠ ⊥) : e d = C.scheme.rows.E c d := ite_eq_right hd
  have heb (d) : e d = ⊥ ↔ C.label d.1 = ⊥ := by
    by_cases hd : C.label d.1 = ⊥
    · simp only [e, hd, ite_true]
    · rw [heq d hd]
      exact ⟨fun h => (hd ((private_bottom hM hC d.1).mp
        ((hbottom d).mp (by rw [h, hbot])))).elim, fun h => (hd h).elim⟩
  refine ⟨e, he, heb, heq, fun x => min (τ x) (W.stableValue u C c),
    ⟨?_, ?_, ?_⟩, fun x => min_le_right _ _, ?_⟩
  · rw [hbot, min_eq_left bot_le]
  · intro x y hxy
    exact min_le_min_right _ (hmono hxy)
  · intro x k i hk hi
    rw [hcomm x k i hk hi, evr_min_of_selfVis hvis hk hi]
  · intro d
    change min (τ (e d)) (W.stableValue u C c) =
      min (W.stableValue u C d.1) (W.stableValue u C c)
    by_cases hd : C.label d.1 = ⊥
    · rw [(heb d).mpr hd, hbot, (private_bottom hM hC d.1).mpr hd]
    · rw [heq d hd, hread d, min_assoc, min_self]

include hC in
theorem no_old_stage_bound (d : Cell C.scheme.scheme) (hd : C.label d = ⊤)
    (hs : W.stableValue u C d ≠ ⊤) :
    ¬ ∀ a : Growth.Field C.scheme.scheme q.scheme.scheme,
      (state (W := W) (u := u) (C := C) (q := q)).profile a ≠ ⊤ →
      (state (W := W) (u := u) (C := C) (q := q)).profile a < ofOrd α.1 := by
  intro hb
  exact (not_lt_of_ge (le_stableValue_of_top hC hd)) (hb (.inl d) hs)

/-- Minimal obstruction to calibrating a proper new-block request with the
actual labels of an actual top reference and top cap. Stable labels are
needed for this calculation; merely installing the same scheme is not enough. -/
theorem actual_top_reference_obstruction
    (r : Requests C.scheme.scheme q.scheme.scheme)
    (hc : C.label r.C = ⊤) (d : Cell q.scheme.scheme) (hd : d ∈ r.F)
    (hr : C.label (r.ρ d).1 = ⊤) (hdp : q.label d ≠ ⊤) :
    ¬ r.Correct (r.sec C.label) q.label := by
  intro h
  have he := h.2.1 d hd
  change min (q.label d) (C.label r.C) =
    min (extVisibilityReplace (C.label (r.ρ d).1) r.N (r.off d)) (C.label r.C) at he
  rw [hc, hr, extVisibilityReplace_top, min_top_right, min_self] at he
  exact hdp he

section Attachment
variable
  (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
  (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
  (hvC : Finset.univ.image f ∈ C.scheme.scheme.plan)
  (hF : C.scheme.restrictFace f hvC = p.scheme)
  (X : RelativeData C.scheme.scheme C.scheme.rows q.scheme.scheme q.scheme.rows)
  (T : Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP f hvC hF X)

include hM hp hC hfu hq T in
/-- The occurrence receipt required by `Growth.Admitted.shared`, on the
literal attachment used by the existing physical carrier. -/
theorem shared (a : q.scheme.scheme.below X.root) :
    q.label a.1 = W.stableValue u C (X.κ a).1 := by
  let b : q.scheme.scheme.below (Finset.univ.image Fin.castSuccEmb, n) :=
    ⟨a.1, T.root_eq ▸ a.2⟩
  have hP' : q.restrictFace Fin.castSuccEmb hvP = stableLiftType hM t p hp :=
    restrictFace_eq_of_typeMap_eq_some hq
  have hC' : (stableLiftType hM u C hC).restrictFace f hvC =
      stableLiftType hM t p hp :=
    restrictFace_eq_of_typeMap_eq_some (stable_face hM hp hC hfu)
  have he := (congrArg (W.stableValue u C)
    (commonFace_val Fin.castSuccEmb hvP hP f hvC hF n b)).trans
    ((StageType.label_castCell hC'.symm _).trans
    ((StageType.label_castCell hP' _).trans
      (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ b))))
  exact he.symm.trans (congrArg (W.stableValue u C) (T.occurrence a)).symm

include hM hp hC hfu hq T in
/-- Genuine pre-activation admission: component lawfulness and the literal
root equation are derived from the actual model and the donor coface. This
does not construct the calibrated relative datum `X`. -/
theorem admitted_before {j : ℕ} (hj : j < X.req.N) :
    Growth.Admitted X j (state (W := W) (u := u) (C := C) (q := q)) where
  private_lawful := (stableLiftRespects hM hC).toBelow _
  donor_lawful := q.respects.toBelow _
  visible a := by
    cases a with
    | inl d =>
      have hv : SelfVis (C.scheme.scheme.grade d) (W.stableValue u C d) :=
        ((stableLiftRespects hM hC).orderly d).symm
      exact hv.mono (C.scheme.scheme.grade_pos d)
    | inr d =>
      have hv : SelfVis (q.scheme.scheme.grade d) (q.label d) := (q.respects.orderly d).symm
      exact hv.mono (q.scheme.scheme.grade_pos d)
  shared := shared hM hp hC hfu hq hvP hP hvC hF X T
  correct hn := (not_le_of_gt hj hn).elim

include hM hp hC hfu hq T in
/-- Audit boundary at activation: with the intended actual bottom class,
request correctness is exactly the remaining admission obligation. This is
an equivalence exposing that obligation, not a supplied-correctness producer. -/
theorem admitted_at_activation_iff {j : ℕ} (hj : X.req.N ≤ j)
    (hZ : X.ZA = {d | C.label d.1 = ⊥}) :
    Growth.Admitted X j (state (W := W) (u := u) (C := C) (q := q)) ↔
      X.req.Correct (X.req.sec (W.stableValue u C)) q.label := by
  have hc : InClass X.ZA (W.stableValue u C) := by
    intro d
    rw [hZ]
    exact private_bottom hM hC d.1
  constructor
  · intro h
    exact h.correct hj hc
  · intro h
    have hb := admitted_before hM hp hC hfu hq hvP hP hvC hF X T
      ((Nat.zero_le X.req.R).trans_lt X.req.R_lt_N)
    exact ⟨(stableLiftRespects hM hC).toBelow _, q.respects.toBelow _,
      hb.visible, hb.shared, fun _ _ => h⟩

end Attachment

/-- The hollow producer's full-width block encoder cannot represent the new
stable block below a marker in that same block at offset `L < N`. This
rejects that encoder instantiation, not the existence of a capped encoder. -/
theorem no_full_width_new_block (B : BlockCode) {μ ξ : Ordinal.{0}} {L N : ℕ}
    (hLN : L < N) (hN : B.N = N) (hμ : B.Λ μ = some ξ)
    (htop : B.htop = ξ + L) : False := by
  have hle := B.Λ_le μ ξ hμ
  rw [hN, htop] at hle
  have hlt : ξ + (L : Ordinal.{0}) < ξ + (N : Ordinal.{0}) :=
    (add_lt_add_iff_left ξ).mpr (Nat.cast_lt.mpr hLN)
  exact (not_le_of_gt hlt) hle

end
end VaughtConjecture.Knight.GrowthStableSelectedInput
