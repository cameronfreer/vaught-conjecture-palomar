/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.HighGradeSource
public import VaughtConjecture.Knight.HighLayerBountiful

/-! # A coded, active maximal full-scope apex

The mute-base transport follows the integration lane's `MuteFullLayer` proof.
The actual output is not mute: the high-grade source constructor gives its
apex literal top while retaining the entire old lawful display and all old rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.MaximalFullLayer
open Transform Value ExtOrd AmalgamationPlan SourceLayerCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K)
  (hKl : K < l) (hlA : l ≤ A.card)

abbrev positive : 0 < l := (Nat.zero_le K).trans_lt hKl
abbrev separated := HighLayerBountiful.separated D l K hK hKl
abbrev scheme := SourceLayerCarrier.scheme D Unit l (positive K l hKl) hlA
abbrev old (d : Cell D) := toCell D Unit l (positive K l hKl) hlA (.inl d)
abbrev apex : Cell (scheme D K l hKl hlA) :=
  toCell D Unit l (positive K l hKl) hlA (.inr ())
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D Unit l
  (positive K l hKl) hlA (separated D K l hK hKl)
abbrev base := SeparatedSourceLayerCarrier.base D Unit l
  (positive K l hKl) hlA (separated D K l hK hKl) sem

theorem old_index (d : Cell D) : (scheme D K l hKl hlA).cell (old D K l hKl hlA d) =
    D.cell d := cell_toCell _ _ _ _ _ _
theorem apex_index : (scheme D K l hKl hlA).cell (apex D K l hKl hlA) = (A, l) :=
  cell_toCell _ _ _ _ _ _

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (base D sem K l hK hKl hlA).E (old D K l hKl hlA c)
      (ownerEquiv D K l hK hKl hlA c d) = sem.E c d :=
  SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) : (base D sem K l hK hKl hlA).IsConsistent := by
  intro c
  obtain ⟨x, rfl⟩ := (enumeration D Unit l (positive K l hKl) hlA).surjective c
  change RespectsSemanticsBelow (base D sem K l hK hKl hlA)
    ((scheme D K l hKl hlA).cell (toCell D Unit l (positive K l hKl) hlA x))
    ((base D sem K l hK hKl hlA).E (toCell D Unit l (positive K l hKl) hlA x))
  cases x with
  | inl c =>
    apply (SeparatedSourceLayerCarrier.base_respects_iff D Unit l
      (positive K l hKl) hlA (separated D K l hK hKl) sem c _).mpr
    have he : (base D sem K l hK hKl hlA).E (old D K l hKl hlA c) ∘
        ownerEquiv D K l hK hKl hlA c = sem.E c :=
      funext (inherited_row D sem K l hK hKl hlA c)
    rw [he]
    exact hs c
  | inr u =>
    have he : (base D sem K l hK hKl hlA).E
        (toCell D Unit l (positive K l hKl) hlA (.inr u)) = fun _ => ⊥ := by
      funext d
      simp only [base, SeparatedSourceLayerCarrier.base, toOcc_toCell,
        SeparatedSourceLayerCarrier.oldTable]
    rw [he]
    refine ⟨fun _ => (extVisibilityReplace_bot _ _).symm, ?_,
      fun _ b _ _ => ⟨b, rfl, le_rfl⟩⟩
    intro b
    simpa only [min_self] using TransformsTo.to_bot ((base D sem K l hK hKl hlA).E b.1)

theorem bountiful (hpos : 0 < K) (hb : sem.IsBountiful) :
    (base D sem K l hK hKl hlA).IsBountiful :=
  HighLayerBountiful.bountiful D Unit l (positive K l hKl) hlA K hK hKl sem
    (base D sem K l hK hKl hlA) (inherited_row D sem K l hK hKl hlA) hpos hb

theorem coded (hc : sem.IsCoded) : (base D sem K l hK hKl hlA).IsCoded := by
  apply CanonicalCodingSupport.layer D Unit l (positive K l hKl) hlA
    (separated D K l hK hKl) sem _ hc (inherited_row D sem K l hK hKl hlA)
  intro u d
  apply Or.inl
  simp only [base, SeparatedSourceLayerCarrier.base, toOcc_toCell,
    SeparatedSourceLayerCarrier.oldTable]

theorem complete (hc : ∀ J ∈ Plan.gradedPlan D.plan, J ≠ (A, l) → ∃ d, D.cell d = J) :
    (scheme D K l hKl hlA).IsComplete := by
  intro J hJ
  by_cases he : J = (A, l)
  · exact ⟨apex D K l hKl hlA, (apex_index D K l hKl hlA).trans he.symm⟩
  · obtain ⟨d, hd⟩ := hc J hJ he
    exact ⟨old D K l hKl hlA d, (old_index D K l hKl hlA d).trans hd⟩

/-- All old labels, not just either face separately, remain literal. -/
theorem exists_active (hk : 1 ≤ K) (hc : sem.IsConsistent) (hb : sem.IsBountiful)
    (hcode : sem.IsCoded) {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ (out : Semantics (scheme D K l hKl hlA)) (q : Cell (scheme D K l hKl hlA) → ExtOrd),
      out.IsConsistent ∧ out.IsBountiful ∧ out.IsCoded ∧ RespectsSemantics out q ∧
      (∀ c d, out.E (old D K l hKl hlA c) (ownerEquiv D K l hK hKl hlA c d) = sem.E c d) ∧
      (∀ d, q (old D K l hKl hlA d) = p d) ∧ q (apex D K l hKl hlA) = ⊤ := by
  have hsep : ¬ GradedLe (A, l) (A, K) := fun h => (not_le_of_gt hKl) h.2
  let e := HighLayerBountiful.equiv D Unit l (positive K l hKl) hlA (A, K) hsep
  let low : (scheme D K l hKl hlA).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hlaw : RespectsSemanticsBelow (base D sem K l hK hKl hlA) (A, K) low :=
    (HighLayerBountiful.respects_iff D Unit l (positive K l hKl) hlA K hK hKl sem
      (base D sem K l hK hKl hlA) (inherited_row D sem K l hK hKl hlA)
      (A, K) hsep (fun d => p d.1)).mp (hp.toBelow (A, K))
  have hg : (scheme D K l hKl hlA).grade (apex D K l hKl hlA) = l :=
    congrArg Prod.snd (apex_index D K l hKl hlA)
  have hs : (scheme D K l hKl hlA).scope (apex D K l hKl hlA) = A :=
    congrArg Prod.fst (apex_index D K l hKl hlA)
  obtain ⟨out, q, hoc, hob, hcod, hq, he, hread, htop⟩ :=
    HighGradeExtension.exists_extension (base D sem K l hK hKl hlA)
      (apex D K l hKl hlA) (by rw [hg]; exact hKl) hs low hlaw ⊤
      (by simp only [SelfVis, extVisibilityReplace_top]) hk
      (consistent D sem K l hK hKl hlA hc)
      (bountiful D sem K l hK hKl hlA (Nat.zero_lt_of_lt hk) hb)
      (coded D sem K l hK hKl hlA hcode)
  refine ⟨out, q, hoc, hob, hcod, hq, ?_, ?_, htop⟩
  · intro c d
    rw [he _ (by change ((scheme D K l hKl hlA).cell _).2 ≤ K
                 rw [old_index]; exact hK c)]
    exact inherited_row D sem K l hK hKl hlA c d
  · intro d
    let dlow : D.below (A, K) := ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hK d⟩
    have hh := hread (e dlow)
    dsimp only [low] at hh
    rw [e.symm_apply_apply] at hh
    exact hh

end
end VaughtConjecture.Knight.MaximalFullLayer
