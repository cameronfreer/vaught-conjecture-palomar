/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RequestAttachment

/-! # Literal attachment of a whole donor to a private context

The plan is attached along the literal common root; occurrences and rows use
the ordered union in `WholeDonorBoundary`, not `requestInventory`. No labels,
catalogue, model, or receiving predicate are needed for this input adapter.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorAttachment
open AmalgamationPlan Transform Value ExtOrd
noncomputable section
variable {n N : ℕ} (e : Fin n ↪ Fin N)

abbrev privateScope : Finset (Fin (N + 1)) := Finset.univ.image Fin.castSuccEmb
abbrev donorScope : Finset (Fin (N + 1)) := Finset.univ.image (onePointProj e)
abbrev rootScope : Finset (Fin (N + 1)) := Finset.univ.image (e.trans Fin.castSuccEmb)

theorem private_card : (privateScope (N := N)).card = N := by
  rw [privateScope, Finset.card_image_of_injective _ Fin.castSuccEmb.injective]
  exact Finset.card_fin N

theorem donor_card : (donorScope e).card = n + 1 := by
  rw [donorScope, Finset.card_image_of_injective _ (onePointProj e).injective]
  exact Finset.card_fin (n + 1)

theorem fresh_private : Fin.last N ∉ privateScope (N := N) := by
  rw [privateScope, image_castSuccEmb_univ]
  exact Finset.notMem_erase _ _

theorem fresh_donor : Fin.last N ∈ donorScope e :=
  Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, onePointProj_last e⟩

theorem root_private : rootScope e ⊆ privateScope (N := N) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image_of_mem _ (Finset.mem_univ (e i))

theorem root_left_image : (Finset.univ.image e).image Fin.castSuccEmb = rootScope e := by
  rw [Finset.image_image]
  rfl

theorem root_right_image :
    (Finset.univ.image (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))).image (onePointProj e) =
      rootScope e := by
  rw [Finset.image_image]
  congr 1
  funext i
  exact onePointProj_castSucc e i

theorem commute : e.trans Fin.castSuccEmb = Fin.castSuccEmb.trans (onePointProj e) := by
  apply Function.Embedding.ext
  intro i
  exact (onePointProj_castSucc e i).symm

theorem intersection : privateScope (N := N) ∩ donorScope e = rootScope e := by
  rw [donorScope, univ_image_onePointProj]
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hr | rfl⟩
    · exact hr
    · exact (fresh_private hp).elim
  · intro hr
    exact ⟨root_private e hr, Or.inl hr⟩

theorem union : (Finset.univ : Finset (Fin (N + 1))) = privateScope ∪ donorScope e := by
  rw [donorScope, univ_image_onePointProj, ← Finset.union_assoc,
    Finset.union_eq_left.mpr (root_private e)]
  exact image_castSuccEmb_union_last.symm

theorem private_proper : privateScope (N := N) ≠ Finset.univ := by
  intro he
  exact fresh_private (he.symm ▸ Finset.mem_univ (Fin.last N))

theorem donor_proper (h : n + 1 < N) : donorScope e ≠ Finset.univ := by
  intro he
  have hc := donor_card e
  rw [he, Finset.card_fin] at hc
  omega

section Plans
variable {a b c : ℕ} (D : SemScheme b) (Q : SemScheme a)
variable (f : Fin a ↪ Fin b) (g : Fin b ↪ Fin c)
variable (hf : Finset.univ.image f ∈ D.scheme.plan) (he : D.restrictFace f hf = Q)

include he in
/-- Plan equality is derived from literal semantic restriction. -/
theorem pushed_root_plan :
    Plan.restrictPlan (D.scheme.plan.image (Finset.image g)) (Finset.univ.image (f.trans g)) =
      Q.scheme.plan.image (Finset.image (f.trans g)) := by
  have hc : (Finset.univ.image f).image g = Finset.univ.image (f.trans g) := by
    rw [Finset.image_image]; rfl
  rw [← hc, restrictPlan_image, ← image_restrictFace_plan D.scheme f hf]
  have hp := congrArg (fun S : SemScheme a => S.scheme.plan) he
  change ((D.restrictFace f hf).scheme.plan.image (Finset.image f)).image (Finset.image g) = _
  rw [hp, Finset.image_image]
  congr 1
  funext V
  simp only [Function.comp_apply, Finset.image_image]
  rfl
end Plans

variable (P : SemScheme N) (D : SemScheme (n + 1)) (Q : SemScheme n)
variable (hp : Finset.univ.image e ∈ P.scheme.plan)
variable (hd : Finset.univ.image Fin.castSuccEmb ∈ D.scheme.plan)
variable (hpr : P.restrictFace e hp = Q) (hdr : D.restrictFace Fin.castSuccEmb hd = Q)

include hpr hdr in
theorem exists_plan : ∃ R : Finset (Finset (Fin (N + 1))),
    Plan.IsPlan Finset.univ R ∧ privateScope ∈ R ∧
    Plan.restrictPlan R privateScope = P.scheme.plan.image (Finset.image Fin.castSuccEmb) ∧
    donorScope e ∈ R ∧
    Plan.restrictPlan R (donorScope e) = D.scheme.plan.image (Finset.image (onePointProj e)) := by
  have hP := Plan.isPlan_image Fin.castSuccEmb P.scheme.isPlan
  have hroot : rootScope e ∈ P.scheme.plan.image (Finset.image Fin.castSuccEmb) :=
    Finset.mem_image.mpr ⟨_, hp, root_left_image e⟩
  have hD : Plan.IsPlan (rootScope e ∪ {Fin.last N})
      (D.scheme.plan.image (Finset.image (onePointProj e))) := by
    rw [← univ_image_onePointProj]
    exact Plan.isPlan_image _ D.scheme.isPlan
  have hrootD : rootScope e ∈ D.scheme.plan.image (Finset.image (onePointProj e)) :=
    Finset.mem_image.mpr ⟨_, hd, root_right_image e⟩
  have heq : Plan.restrictPlan (D.scheme.plan.image (Finset.image (onePointProj e)))
      (rootScope e) =
      Plan.restrictPlan (P.scheme.plan.image (Finset.image Fin.castSuccEmb)) (rootScope e) := by
    rw [pushed_root_plan P Q e Fin.castSuccEmb hp hpr, commute e]
    simpa only [← commute e] using
      pushed_root_plan D Q Fin.castSuccEmb (onePointProj e) hd hdr
  obtain ⟨R, hr, hleft, hl, hright, hr'⟩ :=
    hP.attach_one_over_face hroot fresh_private hD hrootD heq
  rw [image_castSuccEmb_union_last] at hr
  rw [← univ_image_onePointProj] at hright hr'
  exact ⟨R, hr, hleft, hl, hright, hr'⟩

def plan : Finset (Finset (Fin (N + 1))) := Classical.choose (exists_plan e P D Q hp hd hpr hdr)

theorem plan_spec : Plan.IsPlan Finset.univ (plan e P D Q hp hd hpr hdr) ∧
    privateScope ∈ plan e P D Q hp hd hpr hdr ∧
    Plan.restrictPlan (plan e P D Q hp hd hpr hdr) privateScope =
      P.scheme.plan.image (Finset.image Fin.castSuccEmb) ∧
    donorScope e ∈ plan e P D Q hp hd hpr hdr ∧
    Plan.restrictPlan (plan e P D Q hp hd hpr hdr) (donorScope e) =
      D.scheme.plan.image (Finset.image (onePointProj e)) :=
  Classical.choose_spec (exists_plan e P D Q hp hd hpr hdr)

/-- The ordered whole-input boundary with the requested literal placements. -/
def input : WholeDonorBoundary.Input Finset.univ privateScope (donorScope e)
    (plan e P D Q hp hd hpr hdr) n N (n + 1) where
  isPlan := (plan_spec e P D Q hp hd hpr hdr).1
  left := P
  right := D
  common := Q
  placeLeft := Fin.castSuccEmb
  placeRight := onePointProj e
  imageLeft := rfl
  imageRight := rfl
  commonLeft := e
  commonRight := Fin.castSuccEmb
  visibleLeft := hp
  visibleRight := hd
  faceLeft := hpr
  faceRight := hdr
  commute := commute e
  intersection := (root_left_image e).trans (intersection e).symm
  planLeft := (plan_spec e P D Q hp hd hpr hdr).2.2.1
  planRight := (plan_spec e P D Q hp hd hpr hdr).2.2.2.2

local notation "I" => input e P D Q hp hd hpr hdr

def privateOccurrence : Cell P.scheme ↪o Cell (I).boundary :=
  OrderEmbedding.ofStrictMono (I).leftFace.map (I).left_order

def donorOccurrence : Cell D.scheme ↪o Cell (I).boundary :=
  OrderEmbedding.ofStrictMono (I).rightFace.map (I).right_order

theorem private_index (c : Cell P.scheme) :
    (I).boundary.cell (privateOccurrence e P D Q hp hd hpr hdr c) =
      ((P.scheme.scope c).image Fin.castSuccEmb, P.scheme.grade c) := (I).leftFace.index c

theorem donor_index (c : Cell D.scheme) :
    (I).boundary.cell (donorOccurrence e P D Q hp hd hpr hdr c) =
      ((D.scheme.scope c).image (onePointProj e), D.scheme.grade c) := (I).rightFace.index c

def privateBelow (c : Cell P.scheme) (d : P.scheme.below (P.scheme.cell c)) :
    (I).boundary.below ((I).boundary.cell (privateOccurrence e P D Q hp hd hpr hdr c)) :=
  (I).leftFace.belowMap c (PointImageSemantics.belowEquiv P.scheme Fin.castSuccEmb rfl c d)

def donorBelow (c : Cell D.scheme) (d : D.scheme.below (D.scheme.cell c)) :
    (I).boundary.below ((I).boundary.cell (donorOccurrence e P D Q hp hd hpr hdr c)) :=
  (I).rightFace.belowMap c (PointImageSemantics.belowEquiv D.scheme (onePointProj e) rfl c d)

theorem private_row (c : Cell P.scheme) (d : P.scheme.below (P.scheme.cell c)) :
    (I).rows.E (privateOccurrence e P D Q hp hd hpr hdr c)
      (privateBelow e P D Q hp hd hpr hdr c d) = P.rows.E c d :=
  ((I).leftFace.row c (PointImageSemantics.belowEquiv P.scheme Fin.castSuccEmb rfl c d)).trans
    (PointImageSemantics.row P.scheme Fin.castSuccEmb rfl P.rows c d)

theorem donor_row (c : Cell D.scheme) (d : D.scheme.below (D.scheme.cell c)) :
    (I).rows.E (donorOccurrence e P D Q hp hd hpr hdr c)
      (donorBelow e P D Q hp hd hpr hdr c d) = D.rows.E c d :=
  ((I).rightFace.row c (PointImageSemantics.belowEquiv D.scheme (onePointProj e) rfl c d)).trans
    (PointImageSemantics.row D.scheme (onePointProj e) rfl D.rows c d)

/-- The actual occurrence maps identify precisely the literal root maps. -/
theorem shared_occurrence (c : Cell Q.scheme) :
    privateOccurrence e P D Q hp hd hpr hdr (SemSchemeBoundaryInput.faceMap P Q e hp hpr c) =
      donorOccurrence e P D Q hp hd hpr hdr
        (SemSchemeBoundaryInput.faceMap D Q Fin.castSuccEmb hd hdr c) := (I).shared_cell c

theorem private_exhaustive (c : Cell (I).boundary) (hc : (I).boundary.scope c ⊆ privateScope) :
    ∃ d, privateOccurrence e P D Q hp hd hpr hdr d = c := (I).leftFace.exhaustive c hc

theorem donor_exhaustive (c : Cell (I).boundary) (hc : (I).boundary.scope c ⊆ donorScope e) :
    ∃ d, donorOccurrence e P D Q hp hd hpr hdr d = c := (I).rightFace.exhaustive c hc

end
end VaughtConjecture.Knight.WholeDonorAttachment
