/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.CapFirstScalar

/-! # The actual capped ambient of a common-prefix layer

Extract one active source row from an arbitrary lawful full-target ambient.
The existing grade-chart theorem supplies its actual locality witness; clipping
that witness reads every occurrence at the original cap, not merely the top
grade or the original boundary. This is Plan 29's ambient receipt, not a
replacement-section or prescribed-owner alignment theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SourcePrefixAmbient

open Transform Value ExtOrd SourcePrefixLayer
noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
variable (F : Data D k X)

def occurrence (d : Cell D) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), F.max_grade d⟩

theorem exists_active_source (seed : Controller D k)
    {q : D.below (A, k) → ExtOrd} (hq : RespectsSemanticsBelow F.rows (A, k) q)
    (d : D.below (A, k)) (hd : D.grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : Controller D k) (τ : ExtOrd → ExtOrd),
      γ ≤ q (occurrence F a.1) ∧ Witness (gTop k) τ ∧
      (∀ x, τ x ≤ γ) ∧ τ F.ceiling = γ ∧
      (∀ x : D.below (A, k), τ (F.profile a x.1) = min (q x) γ) := by
  obtain ⟨C⟩ := AmbientGradeCharts.exists_chart hq
    ⟨occurrence F seed.1, seed.2⟩
  have hc : γ ≤ q C.owner := hactive.trans (C.dominates d hd)
  let a : Controller D k := ⟨C.owner.1, C.index⟩
  let τ : ExtOrd → ExtOrd := fun x => min (C.shift x) γ
  have hread (x : D.below (A, k)) : τ (F.profile a x.1) = min (q x) γ := by
    have he := F.row_new a (C.occurrence x (F.max_grade x.1))
    change min (C.shift (F.profile a x.1)) γ = _
    exact (congrArg (fun z => min (C.shift z) γ) he.symm).trans
      (C.read_under_cap hc x (F.max_grade x.1))
  refine ⟨a, τ, hc, FreeDiagonal.clip_witness C.witness hγ,
    fun _ => min_le_right _ _, ?_, hread⟩
  have he := hread C.owner
  rw [F.profile_diagonal a] at he
  exact he.trans (min_eq_right hc)

/-- The first grid cut reaching the output cap is constructed from the finite
grid. Minimality is only among GRID cuts; unused points inside a strip need not
lie strictly below the output cap. -/
theorem exists_first_cut {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop k) τ)
    {γ : ExtOrd} (hb : γ ≠ ⊥) (hbound : ∀ x, τ x ≤ γ) (hC : τ F.ceiling = γ) :
    ∃ h : ExtOrd, h ∈ F.grid ∧ SelfVis k h ∧ ⊥ < h ∧ h ≤ F.ceiling ∧
      τ h = γ ∧ ∀ z ∈ F.grid, z < h → τ z < γ := by
  classical
  let S := F.grid.filter (fun h => γ ≤ τ h)
  have hne : S.Nonempty := ⟨F.ceiling, Finset.mem_filter.mpr
    ⟨F.ceiling_mem, hC.ge⟩⟩
  let h := S.min' hne
  have hm : h ∈ S := Finset.min'_mem S hne
  have hG : h ∈ F.grid := (Finset.mem_filter.mp hm).1
  have he : τ h = γ := le_antisymm (hbound h) (Finset.mem_filter.mp hm).2
  refine ⟨h, hG, F.grid_visible h hG, ?_, F.grid_bound h hG, he, ?_⟩
  · apply bot_lt_iff_ne_bot.mpr
    intro hz
    exact hb (he.symm.trans (hz ▸ hτ.bot))
  · intro z hz hzh
    by_contra hn
    have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hz, le_of_not_gt hn⟩
    exact (not_le_of_gt hzh) (Finset.min'_le S z hzS)

end
end VaughtConjecture.Knight.SourcePrefixAmbient
