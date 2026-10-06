/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedLocality

/-! # Constructed mixed extension at every installed cutoff

All native owners and availability obligations are checked before duplication.
Literal extension and the independently proved restriction injectivity give
all-cap same-grade mixed lifting on one fixed final carrier. No bountifulness
of the completed carrier or supplied extension is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

theorem native_orderly (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (d : (P).carrier.below (A, j)) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1 =
      extVisibilityReplace (nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1)
        ((P).carrier.grade d.1) ((P).carrier.grade d.1) := by
  rcases original_or_full I X T hA hB hC t ht d.1 with ⟨e, he⟩ | hd
  · have hh : GradedLe (I.boundary.cell e) (A, j) :=
      (original_index I X T hA hB hC t ht e) ▸ (he ▸ d.2)
    have hv := (boundary_projection I X T hA hB hC t ht U hU hm j hj hj0 hp hjt).orderly ⟨e, hh⟩
    simpa only [he, native_original, boundaryValue, CellScheme.grade, original_index] using hv
  · rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p d.1 hd d.2.2]
    have hv := hp.orderly (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2)
    have hi := congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2)
    change (D).grade (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2).1 =
      (P).carrier.grade d.1 at hi
    change _ = extVisibilityReplace _
      ((D).grade (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2).1)
      ((D).grade (place I X T hA hB hC t ht U hU hm j hj d.1 hd d.2.2).1) at hv
    rw [hi] at hv
    exact hv

theorem native_le_gradeMax (p : (D).below (U, j) → ExtOrd)
    (d : Cell (P).carrier) (hd : (P).carrier.grade d ≤ j) :
    nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d ≤
      gradeMax I X T hA hB hC t ht U j p ((P).carrier.grade d) := by
  rcases original_or_full I X T hA hB hC t ht d with ⟨e, rfl⟩ | hf
  · have he : (P).carrier.grade (original I X T hA hB hC t ht e) = I.boundary.grade e :=
      congrArg Prod.snd (original_index I X T hA hB hC t ht e)
    rw [he] at hd ⊢
    rw [native_original, boundaryValue, height]
    split_ifs with he1
    · rw [min_top_right]
      have heq : I.boundary.grade e = 1 := le_antisymm he1 (I.boundary.grade_pos e)
      rw [heq]
      apply Finset.sup_le
      intro a _
      exact le_gradeMax I X T hA hB hC t ht U j p 1 _
        (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 _))
    · exact min_le_right _ _
  · rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p d hf hd]
    have hi := congrArg Prod.snd (place_index I X T hA hB hC t ht U hU hm j hj d hf hd)
    exact le_gradeMax I X T hA hB hC t ht U j p _ _ hi

theorem native_availability (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    (c v : (P).carrier.below (A, j))
    (hs : (P).carrier.scope c.1 ⊆ (P).carrier.scope v.1)
    (hg : (P).carrier.grade c.1 = (P).carrier.grade v.1) :
    ∃ w : (P).carrier.below (A, j), (P).carrier.cell w.1 = (P).carrier.cell v.1 ∧
      nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p c.1 ≤
        nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p w.1 := by
  rcases original_or_full I X T hA hB hC t ht v.1 with ⟨e, he⟩ | hv
  · have hev : (P).carrier.cell v.1 = I.boundary.cell e :=
      he ▸ original_index I X T hA hB hC t ht e
    have hem : GradedLe (I.boundary.cell e) (A, j) := hev ▸ v.2
    rcases original_or_full I X T hA hB hC t ht c.1 with ⟨d, hd⟩ | hc
    · have hdc : (P).carrier.cell c.1 = I.boundary.cell d :=
        hd ▸ original_index I X T hA hB hC t ht d
      have hdm : GradedLe (I.boundary.cell d) (A, j) := hdc ▸ c.2
      have hb := boundary_projection I X T hA hB hC t ht U hU hm j hj hj0 hp hjt
      obtain ⟨w, hw, hle⟩ := hb.availability
        ⟨d, hdm⟩ ⟨e, hem⟩
        ((congrArg Prod.fst hdc).symm.le.trans (hs.trans (congrArg Prod.fst hev).le))
        ((congrArg Prod.snd hdc).symm.trans (hg.trans (congrArg Prod.snd hev)))
      refine ⟨⟨original I X T hA hB hC t ht w.1,
        (original_index I X T hA hB hC t ht w.1) ▸ w.2⟩,
        (original_index I X T hA hB hC t ht w.1).trans (hw.trans hev.symm), ?_⟩
      simpa only [hd, native_original, boundaryValue] using hle
    · exact (GrowthOrderedBase.proper I hB hC e (le_antisymm
        (I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan e))
        (hc.symm.le.trans (hs.trans (congrArg Prod.fst hev).le)))).elim
  · obtain ⟨w, hw, hwg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj
      hp ((P).carrier.grade v.1) ((P).carrier.grade_pos v.1) v.2.2 (v.2.2.trans hjt)
    refine ⟨⟨w, hw.le, hwg.le.trans v.2.2⟩, Prod.ext (hw.trans hv.symm) hwg, ?_⟩
    rw [native_full I X T hA hB hC t ht U hU hm j hj hj0 p w hw (hwg.le.trans v.2.2),
      hmax, ← hg]
    exact native_le_gradeMax I X T hA hB hC t ht U hU hm j hj hj0 p c.1 c.2.2

/-- Every locality and availability obligation of the constructed native
section is proved on its actual lower domain. -/
theorem native_lawful (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) :
    RespectsSemanticsBelow (P).rows (A, j)
      (fun d => nativeValue I X T hA hB hC t ht U hU hm j hj hj0 p d.1) where
  orderly := native_orderly I X T hA hB hC t ht U hU hm j hj hj0 hp hjt
  locality c := by
    by_cases hc1 : (P).carrier.grade c.1 ≤ 1
    · exact (native_one_lawful I X T hA hB hC t ht U hU hm j hj hj0 hp).locality
        ⟨c.1, c.2.1, hc1⟩
    rcases c with ⟨c, hcut⟩
    change ¬ (P).carrier.grade c ≤ 1 at hc1
    rcases original_or_full I X T hA hB hC t ht c with ⟨d, hd⟩ | hc
    · have hgd : I.boundary.grade d ≤ j :=
        (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.le.trans
          ((congrArg (P).carrier.grade hd).symm.le.trans hcut.2)
      subst c
      exact (original_respects I X T hA hB hC t ht U hU hm j hj hj0 hp hjt d hgd).locality
        ⟨original I X T hA hB hC t ht d, GradedLe.refl _⟩
    · exact higher_locality I X T hA hB hC t ht U hU hm j hj hj0 hp hjt c hc hcut.2 (by omega)
  availability := native_availability I X T hA hB hC t ht U hU hm j hj hj0 hp hjt

theorem lawful (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2) (V : Finset ι) :
    RespectsSemanticsBelow Rows (V, j) (value I X T hA hB hC t ht U hU hm j hj hj0 p) :=
  ScopeReplicationSemantics.duplicateBelow_respects (P).carrier B C
    (GrowthReplicatedRows.proper_covered P) (P).rows (J := (V, j)) (K := (A, j))
    (fun d => ⟨(P).carrier.isPlan.subset_of_mem ((P).carrier.scope_mem_plan _),
      (ScopeReplicationCarrier.erase_grade (P).carrier B C d.1).le.trans d.2.2⟩)
    (native_lawful I X T hA hB hC t ht U hU hm j hj hj0 hp hjt)

include hU hm hj hj0 in
theorem lawfulExtension (hjt : j ≤ t + 2) (V : Finset ι) (hUV : U ⊆ V) :
    ExtensionInjectivity.LawfulExtension Rows
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) := by
  intro p hp
  exact ⟨value I X T hA hB hC t ht U hU hm j hj hj0 p,
    lawful I X T hA hB hC t ht U hU hm j hj hj0 hp hjt V,
    literal I X T hA hB hC t ht U hU hm j hj hj0 p hp hjt hUV⟩

include hU hm hj hj0 in
/-- At every installed cutoff on one fixed carrier, choose an extension before any cap or
ambient. Every individual auxiliary occurrence is included in the simultaneous receipts. -/
theorem allCapsExtension (hjt : j ≤ t + 2) (V : Finset ι) (hV : V ∈ R)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hjV : j ≤ V.card) (hUV : U ⊆ V) :
    ExtensionInjectivity.AllCapsExtension Rows
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) := by
  apply ExtensionInjectivity.allCapsExtension_of_extension_injective
    (lawfulExtension I X T hA hB hC t ht U hU hm j hj hj0 hjt V hUV)
  intro r s hr hs hag z
  exact congrFun (eq_of_restriction I X T hA hB hC t ht U V hU hV hm hmV j hj hjV hj0 hjt hUV
    hr hs hag) z

include hU hm hj hj0 in
/-- All-cap mixed lifting on one fixed final carrier, at any installed
positive cutoff. Every target occurrence retains its own cap. -/
theorem cappedLift (hjt : j ≤ t + 2) (V : Finset ι) (hV : V ∈ R)
    (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hjV : j ≤ V.card) (hUV : U ⊆ V) :
    CoatomBoundaryExtension.CappedLift Rows
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) :=
  (allCapsExtension I X T hA hB hC t ht U hU hm j hj hj0 hjt V hV hmV hjV hUV).cappedLift

end
end VaughtConjecture.Knight.GrowthHigherMixed
