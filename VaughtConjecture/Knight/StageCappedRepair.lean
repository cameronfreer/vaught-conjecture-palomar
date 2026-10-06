/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CapObservation
public import VaughtConjecture.Knight.CappedLifting

/-! # Capped repair with stage-valued output

The donor's own bountifulness restores the visible face literally. Strict
truncation restores the stage bound and preserves each observation below it.
The raw repair and its historical names remain available.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCoverReceiving
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace
variable {α : LimitStage}

/-- Every cell of a scheme on `m` points has grade at most `m`. -/
theorem grade_le_points {m : ℕ} (D : SemScheme m) (d : Cell D.scheme) : D.scheme.grade d ≤ m :=
  (CellScheme.grade_le_card_scope _ d).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _))

/-- Every cell lies below the full index `(univ, m)`. -/
theorem gradedLe_full {m : ℕ} (D : SemScheme m) (d : Cell D.scheme) :
    GradedLe (D.scheme.cell d) (Finset.univ, m) :=
  ⟨Finset.subset_univ _, grade_le_points D d⟩

/-- Strict truncation below the stage does not change caps below the stage. -/
theorem min_truncExt_of_lt {γ : ExtOrd} (hγ : γ < ofOrd α.1) (x : ExtOrd) :
    min (truncExt α.1 x) γ = min x γ :=
  min_truncExt_of_le hγ.le x

/-- An ordinal is at most its sum with a natural number. -/
theorem le_add_nat (ν : Ordinal.{0}) (m : ℕ) : ν ≤ ν + m := by
  first
    | exact Ordinal.le_add_right ν m
    | exact le_self_add

/-- Adding a finite offset stays below a nonzero limit stage. -/
theorem add_nat_lt_limitStage {ν : Ordinal.{0}} (hν : ν < α.1) (m : ℕ) : ν + m < α.1 := by
  induction m with
  | zero => simpa using hν
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact α.2.succ_lt ih

/-- `ofOrd (ν + m)` is self-visible at `m`. -/
theorem selfVis_ofOrd_add_nat (ν : Ordinal.{0}) (m : ℕ) : SelfVis m (ofOrd (ν + m)) := by
  rw [selfVis_ofOrd_iff]
  have h : ν + (m : Ordinal.{0}) = limitPart ν + ((finitePart ν + m : ℕ) : Ordinal.{0}) := by
    conv_lhs => rw [← limitPart_add_finitePart ν]
    rw [add_assoc, Nat.cast_add]
  rw [h, finitePart_limitPart_add_nat]
  exact Nat.le_add_left m _

/-- **Bountifulness along an arbitrary visible face**: a lawful labelling `Q` of `D` and a stage
type `q'` on the face `g` agreeing with `Q` below a cap `γ` self-visible at `D`'s point count are
joined by a lawful labelling of `D` restricting to `q'` literally and agreeing with `Q` below
`γ`.  For a proper face this is `D.bountiful` on the pair `(g[univ], k) ≺ (univ, m)`; for the
full face the transported `q'` itself serves. -/
theorem exists_respects_extends_capped_emb {k m : ℕ} (hk : 0 < k) (D : SemScheme m)
    (g : Fin k ↪ Fin m) (hv : Finset.univ.image g ∈ D.scheme.plan) (q' : S α.1 k)
    (hs : D.restrictFace g hv = q'.scheme) {Q : Cell D.scheme → ExtOrd}
    (hQ : RespectsSemantics D.rows Q) {γ : ExtOrd} (hγ : SelfVis m γ)
    (hcap : ∀ i, min (Q (toCell D.scheme g hv i)) γ = min (q'.label (SemScheme.castCell hs i)) γ) :
    ∃ l : Cell D.scheme → ExtOrd, RespectsSemantics D.rows l ∧
      (∀ d, min (l d) γ = min (Q d) γ) ∧
      ∀ i, l (toCell D.scheme g hv i) = q'.label (SemScheme.castCell hs i) := by
  obtain ⟨Ps, pl, pb, pr⟩ := q'
  dsimp only at hs hcap ⊢
  subst hs
  set CI : Finset (Fin m) × ℕ := (Finset.univ.image g, k) with hCIdef
  set BJ : Finset (Fin m) × ℕ := (Finset.univ, m) with hBJdef
  have hcardg : (Finset.univ.image g).card = k := by
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
  have hkm : k ≤ m := by
    rw [← hcardg]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hCI : CI ∈ Plan.gradedPlan D.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨hv, hk, by change k ≤ (Finset.univ.image g).card; rw [hcardg]⟩
  have hBJ : BJ ∈ Plan.gradedPlan D.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨D.scheme.isPlan.domain_mem, hk.trans_le hkm, by
      change m ≤ (Finset.univ : Finset (Fin m)).card
      rw [Finset.card_univ, Fintype.card_fin]⟩
  have hle : GradedLe CI BJ := ⟨Finset.subset_univ _, hkm⟩
  have hpush : pushGraded g ((Finset.univ : Finset (Fin k)), k) = CI := rfl
  let pC : D.scheme.below CI → ExtOrd :=
    (fun d => pl d.1) ∘ (belowEquiv D.scheme g hv hpush).symm
  have hpC : RespectsSemanticsBelow D.rows CI pC :=
    (pr.toBelow (Finset.univ, k)).of_restrictFace hpush
  have hall : ∀ d : Cell D.scheme, GradedLe (D.scheme.cell d) BJ := gradedLe_full D
  have hcapC : ∀ d : D.scheme.below CI,
      min (Q (CellScheme.below.mono hle d).1) γ = min (pC d) γ := by
    intro d
    have h := hcap ((belowEquiv D.scheme g hv hpush).symm d).1
    change min (Q (toCell D.scheme g hv ((belowEquiv D.scheme g hv hpush).symm d).1)) γ =
      min (pl ((belowEquiv D.scheme g hv hpush).symm d).1) γ at h
    rw [toCell_belowEquiv_symm_val] at h
    exact h
  have hc : ∀ c : Cell (D.scheme.restrictFace g hv),
      GradedLe (D.scheme.cell (toCell D.scheme g hv c)) CI := fun c =>
    (gradedLe_cell_pushGraded_iff D.scheme g hv c).mp (gradedLe_full (D.restrictFace g hv) c)
  have hface : ∀ c : Cell (D.scheme.restrictFace g hv),
      pC ⟨toCell D.scheme g hv c, hc c⟩ = pl c := by
    intro c
    change pl ((belowEquiv D.scheme g hv hpush).symm ⟨toCell D.scheme g hv c, hc c⟩).1 = pl c
    rw [belowEquiv_symm_mk]
  obtain ⟨q'', hq'', hq''γ, hq''p⟩ :=
    CoatomBoundaryExtension.lift_of_bountiful D.bountiful hCI hBJ hle
      pC (fun d => Q d.1) γ hpC (hQ.toBelow BJ) hγ hcapC
  refine ⟨fun d => q'' ⟨d, hall d⟩, hq''.toRespects hall, fun d => hq''γ ⟨d, hall d⟩,
    fun c => ?_⟩
  calc q'' ⟨toCell D.scheme g hv c, hall _⟩
      = q'' (CellScheme.below.mono hle ⟨toCell D.scheme g hv c, hc c⟩) := rfl
    _ = pC ⟨toCell D.scheme g hv c, hc c⟩ := hq''p _
    _ = pl c := hface c

/-- Stage-valued capped repair on any visible face, including the empty and full face. -/
theorem exists_stage_extends_capped_emb {k m : ℕ} (D : SemScheme m)
    (g : Fin k ↪ Fin m) (hv : Finset.univ.image g ∈ D.scheme.plan) (p : S α.1 k)
    (hs : D.restrictFace g hv = p.scheme) {v : Cell D.scheme → ExtOrd}
    (hlaw : RespectsSemantics D.rows v) {γ : ExtOrd} (hγ : SelfVis m γ)
    (hγα : γ < ofOrd α.1)
    (hcap : ∀ i, min (v (toCell D.scheme g hv i)) γ =
      min (p.label (SemScheme.castCell hs i)) γ) :
    ∃ Q : S α.1 m, ∃ he : Q.scheme = D, typeMap g Q = some p ∧
      ∀ d, min (Q.label d) γ = min (v (SemScheme.castCell he d)) γ := by
  have raw : ∃ l : Cell D.scheme → ExtOrd, RespectsSemantics D.rows l ∧
      (∀ d, min (l d) γ = min (v d) γ) ∧
      ∀ i, l (toCell D.scheme g hv i) = p.label (SemScheme.castCell hs i) := by
    by_cases hk : 0 < k
    · exact exists_respects_extends_capped_emb hk D g hv p hs hlaw hγ hcap
    · have hk0 : k = 0 := by omega
      subst k
      exact ⟨v, hlaw, fun _ => rfl,
        fun i => ((CellScheme.isEmpty_cell_fin0 _).false i).elim⟩
  obtain ⟨l, hl, hlγ, hlp⟩ := raw
  let Q := ofRespects α.2 D l hl
  refine ⟨Q, rfl, ?_, fun d => (min_truncExt_of_lt hγα (l d)).trans (hlγ d)⟩
  rw [typeMap_eq_some g Q hv, Option.some.injEq]
  have he : ∀ i, (Q.restrictFace g hv).label i = p.label (SemScheme.castCell hs i) := by
    intro i
    change truncExt α.1 (l (toCell D.scheme g hv i)) = _
    rw [hlp i]
    exact truncExt_id_of_bound (p.label_bound _)
  obtain ⟨ps, pl, pb, pr⟩ := p
  dsimp only at hs he ⊢
  cases hs
  exact StageType.ext rfl (heq_of_eq (funext he))

/-- The coface form of stage-valued repair, with an exact original scheme. -/
theorem exists_stage_extends_capped {n : ℕ} {p : S α.1 n} {D : SemScheme (n + 1)}
    (hD : ExtendsDomain p D) {v : Cell D.scheme → ExtOrd}
    (hlaw : RespectsSemantics D.rows v) {γ : ExtOrd} (hγ : SelfVis (n + 1) γ)
    (hγα : γ < ofOrd α.1)
    (hcap : ∀ d, min (v (hD.cellOf d)) γ = min (p.label d) γ) :
    ∃ Q : S α.1 (n + 1), ∃ he : Q.scheme = D, IsCoface p Q ∧
      ∀ d, min (Q.label d) γ = min (v (SemScheme.castCell he d)) γ := by
  apply exists_stage_extends_capped_emb D Fin.castSuccEmb hD.visible p hD.restrict hlaw hγ hγα
  intro i
  have hcast : SemScheme.castCell hD.restrict.symm (SemScheme.castCell hD.restrict i) = i :=
    Fin.ext rfl
  simpa only [ExtendsDomain.cellOf, hcast] using
    hcap (SemScheme.castCell hD.restrict i)

end VaughtConjecture.Knight.FiniteCoverReceiving
