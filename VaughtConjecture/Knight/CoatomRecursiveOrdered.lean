/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveApex
public import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows

/-! # Ordered original faces of the activated recursive coatom output -/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CoatomRecursiveOrdered
open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan
open SemSchemeBoundaryInput CoatomRecursiveApex
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {s : Step A} {m n : ℕ}
variable (I : Input s m (n + 3) (n + 3)) {α : Ordinal.{0}}
  {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
  (O : Display I α p q)

abbrev boundary (d : Cell I.boundary) := old I (CoatomRecursiveDisplay.boundary I d)

theorem boundary_index (d : Cell I.boundary) : (scheme I).cell (boundary I d) =
    I.boundary.cell d :=
  (MaximalFullLayer.old_index _ _ _ _ _ _).trans
    (CanonicalRecursiveInventory.boundary_cell _ _ _ d)

theorem boundary_order : StrictMono (boundary I) :=
  (SourceLayerCarrier.old_order _ _ _ _ _).comp
    (CoatomRecursiveDisplay.boundary I).strictMono

theorem boundary_exhaustive (hB : ¬ A ⊆ B) (z : Cell (scheme I))
    (hz : (scheme I).scope z ⊆ B) :
    ∃ d, boundary I d = z := by
  have hn : (scheme I).cell z ≠ (A, n + 4) := fun h => hB (by
    change ((scheme I).cell z).1 ⊆ B at hz
    simpa only [h] using hz)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (CoatomRecursiveInput.scheme I)
    Unit (n + 4) (by omega) (finalHeight I) z hn
  have hx : (CoatomRecursiveInput.scheme I).scope x ⊆ B := by
    change ((scheme I).cell (old I x)).1 ⊆ B at hz
    rwa [MaximalFullLayer.old_index] at hz
  rcases RecursiveSourceCarrier.classify I.boundary (CanonicalRecursiveInventory.Profile I.rows)
      (n + 3) (CoatomRecursiveInput.height_le I) x with ⟨d, hd⟩ | ⟨j, _, _, he⟩
  · exact ⟨d, congrArg (old I) hd⟩
  · apply False.elim
    apply hB
    change ((CoatomRecursiveInput.scheme I).cell x).1 ⊆ B at hx
    simpa only [he] using hx

theorem boundary_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    O.rows.E (boundary I c) ⟨boundary I d.1, by rw [boundary_index, boundary_index]; exact d.2⟩ =
      I.rows.E c d := by
  let cb := CoatomRecursiveDisplay.boundary I c
  let db : (CoatomRecursiveInput.scheme I).below ((CoatomRecursiveInput.scheme I).cell cb) :=
    ⟨CoatomRecursiveDisplay.boundary I d.1, by
      rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
      exact d.2⟩
  exact (O.old_row cb db).trans
    (CanonicalRecursiveLiteralRows.row I.rows I.proper n (CoatomRecursiveInput.height_le I) c d)

def face {D : CellScheme B} {sem : Semantics D} (F : ExactSemanticFace sem I.rows)
    (hB : ¬ A ⊆ B) : ExactSemanticFace sem O.rows where
  map := ⟨fun d => boundary I (F.map d), (boundary_order I).injective.comp F.map.injective⟩
  index d := (boundary_index I _).trans (F.index d)
  exhaustive z hz := by
    obtain ⟨d, rfl⟩ := boundary_exhaustive I hB z hz
    have hd : I.boundary.scope d ⊆ B := by
      change ((scheme I).cell (boundary I d)).1 ⊆ B at hz
      rwa [boundary_index] at hz
    obtain ⟨x, rfl⟩ := F.exhaustive d hd
    exact ⟨x, rfl⟩
  row c d := (boundary_row I O (F.map c) (F.belowMap c d)).trans (F.row c d)

end
end VaughtConjecture.Knight.CoatomRecursiveOrdered

namespace VaughtConjecture.Knight
open Transform Value ExtOrd AmalgamationPlan
noncomputable section

/-- Exact physical rows, exhaustive occurrence order, plan, and labels suffice
for literal ordered restriction; no relabelling or equivalence of types. -/
theorem typeMap_of_pointImage_face {α : Ordinal.{0}} {m n : ℕ}
    (t : S α n) (p : S α m) (f : Fin m ↪ Fin n) {B : Finset (Fin n)}
    (hB : Finset.univ.image f = B)
    (F : ExactSemanticFace (PointImageSemantics.rows p.scheme.scheme f hB p.scheme.rows)
      t.scheme.rows) (hmono : StrictMono F.map)
    (hplan : Plan.restrictPlan t.scheme.scheme.plan B = p.scheme.scheme.plan.image (Finset.image f))
    (hlabel : ∀ d, t.label (F.map d) = p.label d) : typeMap f t = some p := by
  have hv : Finset.univ.image f ∈ t.scheme.scheme.plan := by
    have hh : B ∈ Plan.restrictPlan t.scheme.scheme.plan B := by
      rw [hplan, ← hB]
      exact Finset.mem_image.mpr ⟨_, p.scheme.scheme.isPlan.domain_mem, rfl⟩
    exact hB ▸ (Finset.mem_inter.mp hh).1
  have hvis (c : Cell p.scheme.scheme) : t.scheme.scheme.scope (F.map c) ⊆ Finset.univ.image f := by
    change (t.scheme.scheme.cell (F.map c)).1 ⊆ _
    rw [F.index c]
    exact Finset.image_subset_image (Finset.subset_univ _)
  apply typeMap_eq_some_of_emb f t p hv F.map hmono hvis
    (fun d hd => F.exhaustive d (hB ▸ hd))
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    apply Prod.ext
    · apply Finset.image_injective f.injective
      rw [CellScheme.image_pullCell_fst _ _ (hvis c)]
      exact congrArg Prod.fst (F.index c)
    · exact show t.scheme.scheme.grade (F.map c) = p.scheme.scheme.grade c from
        congrArg Prod.snd (F.index c)
  · exact hlabel
  · intro c d d' hd
    have hh := F.row c (PointImageSemantics.belowEquiv p.scheme.scheme f hB c d)
    exact (congrArg (t.scheme.rows.E (F.map c)) (Subtype.ext hd)).trans hh

end
end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.CoatomRecursiveOrdered
open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan
open SemSchemeBoundaryInput CoatomRecursiveApex
noncomputable section
variable {n m : ℕ} {α : Ordinal.{0}}
  {s : Step (Finset.univ : Finset (Fin (n + 4)))}
  (I : Input s m (n + 3) (n + 3))
  {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
  (O : Display I α p q)

theorem left_typeMap (hp : RespectsSemantics I.left.rows p)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) :
    typeMap I.placeLeft O.toType = some (⟨I.left, p, hpb, hp⟩ : S α (n + 3)) := by
  have hn : ¬ (Finset.univ : Finset (Fin (n + 4))) ⊆ Finset.univ.erase s.a :=
    fun h => Finset.notMem_erase s.a Finset.univ (h s.ha)
  apply typeMap_of_pointImage_face O.toType ⟨I.left, p, hpb, hp⟩ I.placeLeft I.imageLeft
    (face I O I.leftFace hn)
  · exact (boundary_order I).comp
      (AmalgamatedBoundary.left_order s I.leftScheme I.rightScheme I.shared I.planLeft I.planRight)
  · have he : (scheme I).plan = s.plan :=
      CanonicalRecursiveBoundaryTransport.plan_eq I.rows (n + 3) (CoatomRecursiveInput.height_le I)
    change Plan.restrictPlan (scheme I).plan (Finset.univ.erase s.a) = _
    rw [he, restrict_left, ← I.planLeft]
  · exact O.left_read

theorem right_typeMap (hq : RespectsSemantics I.right.rows q)
    (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤) :
    typeMap I.placeRight O.toType = some (⟨I.right, q, hqb, hq⟩ : S α (n + 3)) := by
  have hn : ¬ (Finset.univ : Finset (Fin (n + 4))) ⊆ Finset.univ.erase s.b :=
    fun h => Finset.notMem_erase s.b Finset.univ (h s.hb)
  apply typeMap_of_pointImage_face O.toType ⟨I.right, q, hqb, hq⟩ I.placeRight I.imageRight
    (face I O I.rightFace hn)
  · exact (boundary_order I).comp
      (AmalgamatedBoundary.right_order s I.leftScheme I.rightScheme I.shared I.planLeft I.planRight)
  · have he : (scheme I).plan = s.plan :=
      CanonicalRecursiveBoundaryTransport.plan_eq I.rows (n + 3) (CoatomRecursiveInput.height_le I)
    change Plan.restrictPlan (scheme I).plan (Finset.univ.erase s.b) = _
    rw [he, restrict_right, ← I.planRight]
  · exact O.right_read

/-- The complete supplier for coatom input arities at least three. -/
theorem exists_amalgam (hα : Order.IsSuccLimit α) (C : CoatomPair (n + 2))
    {pa pb : S α (n + 3)} (h : C.Compatible pa pb) :
    ∃ t : S α (n + 4), C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  let I := (CoatomBoundaryPresentation.of_compatible C h).input
  let O := ofCompatible hα C h
  exact ⟨O.toType,
    ⟨left_typeMap I O pa.respects pa.label_bound,
      right_typeMap I O pb.respects pb.label_bound⟩, O.maximal⟩

end
end VaughtConjecture.Knight.CoatomRecursiveOrdered
