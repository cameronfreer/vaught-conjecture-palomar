/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RequestAttachment

/-! # Literal ordered restrictions of the inherited boundary

An occurrence-exact semantic face with a strictly increasing occurrence map
and the correct plan restricts literally to its input cell scheme. The
restricted occurrence map is the installed map, even when the input is not
an initial segment. Rows are recovered on every original lower-domain argument.

Both faces of `WholeDonorBoundary` satisfy these hypotheses. No legality of
the incomplete boundary, or of a future mixed completion, is assumed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OrderedFaceRestriction

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap)

variable {m n : ℕ} {B : Finset (Fin n)}
variable (D : SemScheme m) (K : CellScheme (ι := Fin n) Finset.univ)
  (sem : Semantics K) (f : Fin m ↪ Fin n) (hB : Finset.univ.image f = B)
  (F : ExactSemanticFace (PointImageSemantics.rows D.scheme f hB D.rows) sem)
  (hmono : StrictMono F.map)
  (hplan : Plan.restrictPlan K.plan B = D.scheme.plan.image (Finset.image f))

include hB hplan in
theorem visible : Finset.univ.image f ∈ K.plan := by
  have hh : B ∈ Plan.restrictPlan K.plan B := by
    rw [hplan, ← hB]
    exact Finset.mem_image.mpr ⟨_, D.scheme.isPlan.domain_mem, rfl⟩
  exact hB ▸ (Finset.mem_inter.mp hh).1

theorem scope_map (c : Cell D.scheme) : K.scope (F.map c) ⊆ Finset.univ.image f := by
  change (K.cell (F.map c)).1 ⊆ _
  rw [F.index c]
  exact Finset.image_subset_image (Finset.subset_univ _)

include F hmono in
theorem card_face :
    (K.restrictFace f (visible D K f hB hplan)).card = D.scheme.card :=
  CellScheme.restrictFace.card_restrictFace_of_emb K f (visible D K f hB hplan)
    hmono (scope_map D K sem f hB F)
    (fun d hd => F.exhaustive d (hB ▸ hd))

theorem toCell_eq (c : Cell D.scheme) :
    toCell K f (visible D K f hB hplan)
      (Fin.cast (card_face D K sem f hB F hmono hplan).symm c) = F.map c :=
  CellScheme.restrictFace.toCell_cast_eq_of_emb K f (visible D K f hB hplan)
    hmono (scope_map D K sem f hB F) (card_face D K sem f hB F hmono hplan) c

include F hmono in
/-- Literal cell-scheme equality, not just an equivalence of lawful sections. -/
theorem scheme_eq : K.restrictFace f (visible D K f hB hplan) = D.scheme := by
  refine CellScheme.ext_of_components ?_ (card_face D K sem f hB F hmono hplan) ?_
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    rw [CellScheme.restrictFace.cell_eq, toCell_eq D K sem f hB F hmono hplan]
    apply Prod.ext
    · apply Finset.image_injective f.injective
      rw [CellScheme.image_pullCell_fst K f (scope_map D K sem f hB F c)]
      exact congrArg Prod.fst (F.index c)
    · change K.grade (F.map c) = D.scheme.grade c
      exact congrArg Prod.snd (F.index c)

private theorem E_congr {c c' : Cell K} (h : c = c') (x : K.below (K.cell c)) :
    sem.E c x = sem.E c' ⟨x.1, h ▸ x.2⟩ := by
  subst h
  rfl

/-- Every restricted row argument is exactly the corresponding original argument. -/
theorem row_eq (c : Cell D.scheme) (d : D.scheme.below (D.scheme.cell c)) :
    (sem.restrictFace f (visible D K f hB hplan)).E
      (Fin.cast (card_face D K sem f hB F hmono hplan).symm c)
      ⟨Fin.cast (card_face D K sem f hB F hmono hplan).symm d.1, by
        rw [CellScheme.cell_cast_of_eq (scheme_eq D K sem f hB F hmono hplan) d.1,
          CellScheme.cell_cast_of_eq (scheme_eq D K sem f hB F hmono hplan) c]
        exact d.2⟩ = D.rows.E c d := by
  refine (E_congr K sem (toCell_eq D K sem f hB F hmono hplan c) _).trans ?_
  have hr := F.row c (PointImageSemantics.belowEquiv D.scheme f hB c d)
  refine (congrArg (sem.E (F.map c)) (Subtype.ext ?_)).trans hr
  exact toCell_eq D K sem f hB F hmono hplan d.1

end VaughtConjecture.Knight.OrderedFaceRestriction

namespace VaughtConjecture.Knight.WholeDonorBoundary.Input

open AmalgamationPlan

variable {n m nL nR : ℕ} {B C : Finset (Fin n)}
  {R : Finset (Finset (Fin n))} (I : Input Finset.univ B C R m nL nR)

theorem left_visible : Finset.univ.image I.placeLeft ∈ I.boundary.plan :=
  OrderedFaceRestriction.visible I.left I.boundary I.placeLeft I.imageLeft I.planLeft

theorem right_visible : Finset.univ.image I.placeRight ∈ I.boundary.plan :=
  OrderedFaceRestriction.visible I.right I.boundary I.placeRight I.imageRight I.planRight

theorem restrict_left : I.boundary.restrictFace I.placeLeft I.left_visible = I.left.scheme :=
  OrderedFaceRestriction.scheme_eq I.left I.boundary I.rows I.placeLeft I.imageLeft
    I.leftFace I.left_order I.planLeft

theorem restrict_right : I.boundary.restrictFace I.placeRight I.right_visible = I.right.scheme :=
  OrderedFaceRestriction.scheme_eq I.right I.boundary I.rows I.placeRight I.imageRight
    I.rightFace I.right_order I.planRight

end VaughtConjecture.Knight.WholeDonorBoundary.Input
