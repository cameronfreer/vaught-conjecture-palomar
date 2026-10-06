/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveOrdered

/-! # Installing a constructed small coatom seed

Internal receipts for the existing one- and two-grade seeds. These are proved
on each seed, not assumptions of the final all-arity supplier.
-/
@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CoatomSeedInstallation
open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
noncomputable section
variable {n m : ℕ} {s : Step (Finset.univ : Finset (Fin (n + 2)))}
  (I : Input s m (n + 1) (n + 1))

structure Seed where
  scheme : CellScheme (ι := Fin (n + 2)) Finset.univ
  rows : Semantics scheme
  plan : scheme.plan = I.boundary.plan
  boundary : Cell I.boundary ↪o Cell scheme
  index : ∀ d, scheme.cell (boundary d) = I.boundary.cell d
  exhaustive : ∀ (B : Finset (Fin (n + 2))), ¬ Finset.univ ⊆ B →
    ∀ z, scheme.scope z ⊆ B → ∃ d, boundary d = z
  row : ∀ c (d : I.boundary.below (I.boundary.cell c)),
    rows.E (boundary c) ⟨boundary d.1, by rw [index, index]; exact d.2⟩ = I.rows.E c d
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  bountiful : rows.IsBountiful
  grade : ∀ d, scheme.grade d ≤ n + 1
  complete : ∀ J ∈ Plan.gradedPlan scheme.plan, J.2 ≤ n + 1 → ∃ d, scheme.cell d = J
  extend_whole : ∀ p, RespectsSemantics I.rows p →
    ∃ q, RespectsSemantics rows q ∧ ∀ d, q (boundary d) = p d

variable (F : Seed I)
abbrev height : n + 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp
abbrev scheme := MaximalFullLayer.scheme F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev old := MaximalFullLayer.old F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev apex := MaximalFullLayer.apex F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
abbrev ownerEquiv := MaximalFullLayer.ownerEquiv F.scheme (n + 1) (n + 2) F.grade
  (by omega) (height (n := n))
abbrev boundary (d : Cell I.boundary) := old I F (F.boundary d)

theorem boundary_index (d : Cell I.boundary) : (scheme I F).cell (boundary I F d) =
    I.boundary.cell d := (MaximalFullLayer.old_index _ _ _ _ _ _).trans (F.index d)
theorem boundary_order : StrictMono (boundary I F) :=
  (SourceLayerCarrier.old_order _ _ _ _ _).comp F.boundary.strictMono

theorem complete : (scheme I F).IsComplete := by
  apply MaximalFullLayer.complete F.scheme (n + 1) (n + 2) (by omega) (height (n := n))
  intro J hJ hne
  apply F.complete J hJ
  have hg := (Plan.mem_gradedPlan.mp hJ).2.2
  have hs := F.scheme.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hJ).1
  have hc := Finset.card_le_card hs
  have ha : (Finset.univ : Finset (Fin (n + 2))).card = n + 2 := by simp
  by_contra hh
  have he : J.1 = Finset.univ := Finset.eq_of_subset_of_card_le hs (by omega)
  exact hne (Prod.ext he (by dsimp only; omega))

theorem boundary_exhaustive (B : Finset (Fin (n + 2))) (hB : ¬ Finset.univ ⊆ B)
    (z : Cell (scheme I F)) (hz : (scheme I F).scope z ⊆ B) :
    ∃ d, boundary I F d = z := by
  have hn : (scheme I F).cell z ≠ (Finset.univ, n + 2) := fun hh => hB (by
    change ((scheme I F).cell z).1 ⊆ B at hz
    simpa only [hh] using hz)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence F.scheme Unit (n + 2)
    (by omega) (height (n := n)) z hn
  have hx : F.scheme.scope x ⊆ B := by
    change ((scheme I F).cell (old I F x)).1 ⊆ B at hz
    rwa [MaximalFullLayer.old_index] at hz
  obtain ⟨d, hd⟩ := F.exhaustive B hB x hx
  exact ⟨d, congrArg (old I F) hd⟩

def face {B : Finset (Fin (n + 2))} {D : CellScheme B} {sem : Semantics D}
    (G : ExactSemanticFace sem I.rows) (hB : ¬ Finset.univ ⊆ B)
    (out : Semantics (scheme I F))
    (hrow : ∀ c d, out.E (old I F c) (ownerEquiv I F c d) = F.rows.E c d) :
    ExactSemanticFace sem out where
  map := ⟨fun d => boundary I F (G.map d), (boundary_order I F).injective.comp G.map.injective⟩
  index d := (boundary_index I F _).trans (G.index d)
  exhaustive z hz := by
    obtain ⟨d, rfl⟩ := boundary_exhaustive I F B hB z hz
    have hd : I.boundary.scope d ⊆ B := by
      change ((scheme I F).cell (boundary I F d)).1 ⊆ B at hz
      rwa [boundary_index] at hz
    obtain ⟨x, rfl⟩ := G.exhaustive d hd
    exact ⟨x, rfl⟩
  row c d := by
    let e := G.belowMap c d
    let e' : F.scheme.below (F.scheme.cell (F.boundary (G.map c))) :=
      ⟨F.boundary e.1, by rw [F.index, F.index]; exact e.2⟩
    exact (hrow (F.boundary (G.map c)) e').trans ((F.row (G.map c) e).trans (G.row c d))

/-- The already-lawful compatible old displays are glued without cap histories. -/
theorem joint_section {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r : Cell F.scheme → ExtOrd, RespectsSemantics F.rows r ∧
      (∀ d, r (F.boundary (I.leftFace.map d)) = p d) ∧
      ∀ d, r (F.boundary (I.rightFace.map d)) = q d := by
  have hl := (PointImageSemantics.respects_iff I.left.scheme I.placeLeft I.imageLeft
    I.left.rows p).mpr hp
  have hr := (PointImageSemantics.respects_iff I.right.scheme I.placeRight I.imageRight
    I.right.rows q).mpr hq
  obtain ⟨u, hu, hul, hur⟩ :=
    (AmalgamatedBoundarySemantics.section_iff s I.leftScheme I.rightScheme I.shared
      I.planLeft I.planRight I.leftRows I.rightRows I.compatible hl hr).mpr ha
  obtain ⟨r, hrr, he⟩ := F.extend_whole u hu
  exact ⟨r, hrr, fun d => (he _).trans (hul d), fun d => (he _).trans (hur d)⟩

include F in
theorem install {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ t : S α (n + 2),
      typeMap I.placeLeft t = some (⟨I.left, p, hpb, hp⟩ : S α (n + 1)) ∧
      typeMap I.placeRight t = some (⟨I.right, q, hqb, hq⟩ : S α (n + 1)) ∧
      t.HasMaximalFullCell := by
  obtain ⟨r, hr, hl, hright⟩ := joint_section I F hp hq ha
  obtain ⟨out, u, hc, hb, hcode, hu, he, hread, htop⟩ :=
    MaximalFullLayer.exists_active F.scheme F.rows (n + 1) (n + 2) F.grade
      (by omega) (height (n := n)) (by omega) F.consistent F.bountiful F.coded hr
  let t : S α (n + 2) :=
    ⟨⟨scheme I F, out, hcode, hc, hb, complete I F⟩,
      fun d => truncExt α (u d), fun _ => truncExt_bound _ _, hu.truncate hα⟩
  have hpL : ¬ (Finset.univ : Finset (Fin (n + 2))) ⊆ Finset.univ.erase s.a :=
    fun h => Finset.notMem_erase s.a Finset.univ (h s.ha)
  have hpR : ¬ (Finset.univ : Finset (Fin (n + 2))) ⊆ Finset.univ.erase s.b :=
    fun h => Finset.notMem_erase s.b Finset.univ (h s.hb)
  refine ⟨t, ?_, ?_, ?_⟩
  · apply typeMap_of_pointImage_face t ⟨I.left, p, hpb, hp⟩ I.placeLeft I.imageLeft
      (face I F I.leftFace hpL out he)
    · exact (boundary_order I F).comp
        (AmalgamatedBoundary.left_order s I.leftScheme I.rightScheme I.shared
          I.planLeft I.planRight)
    · change Plan.restrictPlan F.scheme.plan (Finset.univ.erase s.a) = _
      rw [F.plan, show I.boundary.plan = s.plan from rfl, restrict_left, ← I.planLeft]
    · intro d
      change truncExt α (u (old I F (F.boundary (I.leftFace.map d)))) = p d
      rw [hread, hl]
      exact truncExt_id_of_bound (hpb d)
  · apply typeMap_of_pointImage_face t ⟨I.right, q, hqb, hq⟩ I.placeRight I.imageRight
      (face I F I.rightFace hpR out he)
    · exact (boundary_order I F).comp
        (AmalgamatedBoundary.right_order s I.leftScheme I.rightScheme I.shared
          I.planLeft I.planRight)
    · change Plan.restrictPlan F.scheme.plan (Finset.univ.erase s.b) = _
      rw [F.plan, show I.boundary.plan = s.plan from rfl, restrict_right, ← I.planRight]
    · intro d
      change truncExt α (u (old I F (F.boundary (I.rightFace.map d)))) = q d
      rw [hread, hright]
      exact truncExt_id_of_bound (hqb d)
  · refine ⟨apex I F, ?_, ?_⟩
    · exact congrArg Prod.snd (MaximalFullLayer.apex_index _ _ _ _ _)
    · intro d
      change truncExt α (u d) ≤ truncExt α (u (apex I F))
      rw [htop, truncExt_id_of_bound (Or.inr rfl)]
      exact le_top

end
end VaughtConjecture.Knight.CoatomSeedInstallation
