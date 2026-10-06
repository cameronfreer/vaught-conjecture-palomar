/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderLayer
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Actual serving leaves for arbitrary padded-ladder ambients

Availability first supplies a maximal owner. Its actual row identifies its
diagonal with the same-source ceiling leaf, so locality promotes that leaf to
the maximum. Its bounded witness reads every actual grade-one coordinate. This
does not assume synchronization, a selected ambient, or bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (hp : ∀ d, D.scope d ≠ A)

def leafOccurrence (a : Q) : (carrier D hA (X := X) (Q := Q)).below (A, 1) :=
  ⟨added D hA (SupportLadderRows.leaf (Nat.succ_pos _) a), by
    rw [added_index]; exact GradedLe.refl _⟩

/-- The maximizer can be chosen to be an actual ceiling leaf, including when
the original maximizing owner was a zero-rank shadow. -/
theorem exists_maximal_leaf (seed : Q)
    {q : (carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D sem hA field fields hp) (A, 1) q) :
    ∃ a : Q, ∀ d, q d ≤ q (leafOccurrence D hA a) := by
  obtain ⟨chart⟩ := AmbientGradeCharts.exists_chart hq
    ⟨leafOccurrence D hA seed, added_index D hA _⟩
  have hg (d : (carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      (carrier D hA (X := X) (Q := Q)).grade d.1 = 1 :=
    le_antisymm d.2.2 ((carrier D hA).grade_pos d.1)
  obtain ⟨v, hv⟩ : ∃ v, chart.owner.1 = added D hA v := by
    rcases cell_cases D hA chart.owner.1 with ⟨c, hc⟩ | hv
    · have he := chart.index
      rw [hc, old_index] at he
      exact (hp c (congrArg Prod.fst he)).elim
    · exact hv
  have hr (d : (carrier D hA (X := X) (Q := Q)).below (A, 1)) :
      chart.shift (ladderRow D hA field fields v d.1) = q d := by
    have hh := chart.read_grade d (hg d)
    have he : (rows D sem hA field fields hp).E chart.owner.1
        (chart.occurrence d (hg d).le) = ladderRow D hA field fields v d.1 := by
      simp only [rows, hv, view, added, SourceLayerCarrier.toOcc_toCell,
        AmbientGradeCharts.Chart.occurrence]
    rwa [he] at hh
  let a := SupportLadderRows.parent v
  have he : ladderRow D hA field fields v (leafOccurrence D hA a).1 =
      ladderRow D hA field fields v chart.owner.1 := by
    rw [hv]
    change ladderRow D hA field fields v
      (added D hA (SupportLadderRows.leaf (Nat.succ_pos _) a)) = _
    simp only [ladderRow, image, rankIndex_added]
    exact SupportLadderRows.row_parent (fun a x => (rank_bound fields a x).le)
      (Nat.succ_pos _) v
  have hqeq : q (leafOccurrence D hA a) = q chart.owner := by
    rw [← hr, ← hr, he]
  exact ⟨a, fun d => (chart.dominates d (hg d)).trans_eq hqeq.symm⟩

/-- The actual leaf's witness reads the entire ambient exactly, not only its
original fields. Higher inherited cells are outside this grade-one domain. -/
theorem exists_leaf_chart (seed : Q)
    {q : (carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D sem hA field fields hp) (A, 1) q) :
    ∃ a : Q, ∃ τ : ExtOrd → ExtOrd, Witness (gTop 1) τ ∧
      (∀ x, τ x ≤ q (leafOccurrence D hA a)) ∧
      ∀ d, τ (ladderRow D hA field fields
        (SupportLadderRows.leaf (Nat.succ_pos _) a) d.1) = q d := by
  obtain ⟨a, hmax⟩ := exists_maximal_leaf D sem hA field fields hp seed hq
  let c := leafOccurrence (X := X) D hA a
  let self : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA).cell c.1) := ⟨c.1, GradedLe.refl _⟩
  have hg : (carrier D hA (X := X) (Q := Q)).grade c.1 = 1 :=
    congrArg Prod.snd (added_index D hA _)
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hq.orderly c).symm (hq.locality c)
  refine ⟨a, τ, hg ▸ hτ, hb, ?_⟩
  intro d
  let e : (carrier D hA (X := X) (Q := Q)).below
      ((carrier D hA).cell c.1) := ⟨d.1, by
        simpa only [c, leafOccurrence, added_index] using d.2⟩
  have hh := hr e
  have he := row_added D sem hA field fields hp
    (SupportLadderRows.leaf (Nat.succ_pos _) a) e
  change (rows D sem hA field fields hp).E c.1 e =
    ladderRow D hA field fields (SupportLadderRows.leaf (Nat.succ_pos _) a) d.1 at he
  rw [he] at hh
  exact hh.trans (min_eq_left (hmax d))

/-- Cap first, then extract the serving leaf. The witness is globally bounded by
the original cap, and reads every capped physical coordinate. -/
theorem exists_capped_leaf_chart (seed : Q)
    {q : (carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows D sem hA field fields hp) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) :
    ∃ a : Q, ∃ τ : ExtOrd → ExtOrd, Witness (gTop 1) τ ∧
      (∀ x, τ x ≤ γ) ∧ ∀ d,
        τ (ladderRow D hA field fields (SupportLadderRows.leaf (Nat.succ_pos _) a) d.1) =
          min (q d) γ := by
  obtain ⟨a, τ, hw, hb, hr⟩ := exists_leaf_chart D sem hA field fields hp seed (hq.cap hγ)
  exact ⟨a, τ, hw, fun x => (hb x).trans (min_le_right _ _), hr⟩

end
end VaughtConjecture.Knight.RelativeLadderLayer
