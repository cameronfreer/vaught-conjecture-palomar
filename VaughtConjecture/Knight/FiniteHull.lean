/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.PairHulls
public import VaughtConjecture.Order.FiniteSupportClosure
public import VaughtConjecture.Knight.Directedness

/-!
# Canonical finite hulls of actual chart supports

Adapted from the newsimple14 canonical-hulls draft, using the verified finite-plan geometry.
Assumptions throughout are exact consistency and
covering only.  The DecidableEq instance is only Finset bookkeeping and can
always be supplied classically.  This module must initially sit ABOVE
Directedness: using its common-cover theorem to build hulls, and then importing
hulls back into Directedness, would create a cycle.
-/

@[expose] public section

namespace VaughtConjecture.Knight.KnightRealization.FiniteHull

open TypeTower StageType

variable {α : LimitStage} {M : Type*} [DecidableEq M]
variable {R : KnightRealization α M}

noncomputable section

/-- Finite support, without choosing an order on the carrier. -/
def support {n : ℕ} (t : Fin n ↪ M) : Finset M := Finset.univ.image t

@[simp] theorem mem_support {n : ℕ} (t : Fin n ↪ M) (x : M) :
    x ∈ support t ↔ ∃ i, t i = x := by
  simp [support]

@[simp] theorem support_trans {n m : ℕ} (f : Fin n ↪ Fin m) (t : Fin m ↪ M) :
    support (f.trans t) = (support f).image t := by
  change Finset.univ.image (t ∘ f) = (Finset.univ.image f).image t
  rw [Finset.image_image]

/-- An enumeration adapter. The support, not this enumeration, is canonical. -/
def enumerate (S : Finset M) : Fin S.card ↪ M :=
  ⟨fun i => (S.equivFin.symm i : M),
    fun _ _ h => S.equivFin.symm.injective (Subtype.coe_injective h)⟩

@[simp] theorem support_enumerate (S : Finset M) : support (enumerate S) = S := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFin.symm i).2
  · intro hx
    refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem factor_of_support_subset {n m : ℕ} (t : Fin n ↪ M) (u : Fin m ↪ M)
    (h : support t ⊆ support u) :
    ∃ f : Fin n ↪ Fin m, f.trans u = t := by
  classical
  have hex : ∀ i, ∃ j, u j = t i := fun i =>
    (mem_support u (t i)).mp (h ((mem_support t (t i)).mpr ⟨i, rfl⟩))
  choose f hf using hex
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    apply t.injective
    rw [← hf i, ← hf j, hij]
  · ext i
    exact hf i

/-- Exact consistency makes the old cover preorder simply support inclusion. -/
theorem le_iff_support_subset (hcons : R.IsExactParentConsistent)
    (x y : R.LabelledExt) : x ≤ y ↔ support x.tuple ⊆ support y.tuple := by
  constructor
  · rintro ⟨f, hft, _⟩ z hz
    obtain ⟨i, rfl⟩ := (mem_support x.tuple z).mp hz
    apply (mem_support y.tuple (x.tuple i)).mpr
    refine ⟨f i, ?_⟩
    exact congrArg (fun t => t i) hft
  · intro hxy
    obtain ⟨f, hft⟩ := factor_of_support_subset x.tuple y.tuple hxy
    refine ⟨f, hft, ?_⟩
    have h := hcons y.tuple y.type f y.eval_eq
    rw [hft, x.eval_eq] at h
    exact h.symm

/-- A finite closed set is the support of an actual chart. -/
def IsActualSupport (R : KnightRealization α M) (S : Finset M) : Prop :=
  ∃ x : R.LabelledExt, support x.tuple = S

/-- Every visible coordinate face of an actual chart is an actual support. -/
theorem actual_of_face (hcons : R.IsExactParentConsistent)
    (x : R.LabelledExt) {F : Finset (Fin x.arity)}
    (hF : F ∈ x.type.scheme.scheme.plan) :
    IsActualSupport R (F.image x.tuple) := by
  let f := enumerate F
  have hf : Finset.univ.image f ∈ x.type.scheme.scheme.plan := by
    change support f ∈ x.type.scheme.scheme.plan
    rw [support_enumerate]
    exact hF
  let p := x.type.restrictFace f hf
  have hp : R.eval (f.trans x.tuple) = some p := by
    have h := hcons x.tuple x.type f x.eval_eq
    change R.eval (f.trans x.tuple) = typeMap f x.type at h
    rw [h, typeMap_eq_some f x.type hf]
  refine ⟨⟨_, f.trans x.tuple, p, hp⟩, ?_⟩
  rw [support_trans, support_enumerate]

/-- Local-to-global visibility in a supplied actual chart. In the forward
direction the negative information in exact consistency is essential. -/
theorem actual_image_iff_face (hcons : R.IsExactParentConsistent)
    (x : R.LabelledExt) (F : Finset (Fin x.arity)) :
    IsActualSupport R (F.image x.tuple) ↔ F ∈ x.type.scheme.scheme.plan := by
  constructor
  · rintro ⟨y, hy⟩
    have hsub : support y.tuple ⊆ support x.tuple := by
      rw [hy]
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact (mem_support x.tuple (x.tuple i)).mpr ⟨i, rfl⟩
    obtain ⟨f, hft, hfp⟩ := (le_iff_support_subset hcons y x).mpr hsub
    have hvisible : support f ∈ x.type.scheme.scheme.plan :=
      (typeMap_isSome_iff f x.type).mp (by rw [hfp]; rfl)
    have him : (support f).image x.tuple = F.image x.tuple := by
      rw [← support_trans, hft, hy]
    have hface : support f = F := Finset.image_injective x.tuple.injective him
    simpa only [hface] using hvisible
  · exact actual_of_face hcons x

/-- Structural covering is cofinality of the actual finite supports. -/
theorem exists_actual_superset (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    ∃ A, IsActualSupport R A ∧ S ⊆ A := by
  obtain ⟨k, u, hu, hsome⟩ := hcov (enumerate S)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨support u, ⟨⟨_, u, p, hp⟩, rfl⟩, ?_⟩
  intro z hz
  have hz' : z ∈ support (enumerate S) := by simpa only [support_enumerate] using hz
  obtain ⟨i, hi⟩ := (mem_support (enumerate S) z).mp hz'
  apply (mem_support u z).mpr
  refine ⟨Fin.castAddEmb k i, ?_⟩
  exact (congrArg (fun t => t i) hu).trans hi

/-- Intersection is performed inside one actual common chart. -/
theorem actual_inter (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (A B : Finset M)
    (hA : IsActualSupport R A) (hB : IsActualSupport R B) :
    IsActualSupport R (A ∩ B) := by
  rcases hA with ⟨x, rfl⟩
  rcases hB with ⟨y, rfl⟩
  obtain ⟨z, hxz, hyz⟩ := directed_labelledExt hcons hcov x y
  obtain ⟨f, hft, hfp⟩ := hxz
  obtain ⟨g, hgt, hgp⟩ := hyz
  have hF : support f ∈ z.type.scheme.scheme.plan :=
    (typeMap_isSome_iff f z.type).mp (by rw [hfp]; rfl)
  have hG : support g ∈ z.type.scheme.scheme.plan :=
    (typeMap_isSome_iff g z.type).mp (by rw [hgp]; rfl)
  have hFG := z.type.scheme.scheme.isPlan.inter_mem hF hG
  have hactual := actual_of_face hcons z hFG
  have heq : (support f ∩ support g).image z.tuple =
      support x.tuple ∩ support y.tuple := by
    rw [Finset.image_inter _ _ z.tuple.injective, ← support_trans, ← support_trans, hft, hgt]
  simpa only [heq] using hactual

/-- The canonical least actual finite support. Not a chosen enumeration. -/
def hull (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) :
    ClosureOperator (Finset M) :=
  FiniteSupportClosure.ofCofinalInterClosed (IsActualSupport R)
    (actual_inter hcons hcov) (exists_actual_superset hcov)

@[simp] theorem hull_isClosed (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    (hull hcons hcov).IsClosed S ↔ IsActualSupport R S := Iff.rfl

theorem hull_actual (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    IsActualSupport R (hull hcons hcov S) :=
  (hull hcons hcov).isClosed_closure S

theorem subset_hull (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    S ⊆ hull hcons hcov S := (hull hcons hcov).le_closure S

theorem hull_min (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {S A : Finset M}
    (hA : IsActualSupport R A) (hSA : S ⊆ A) : hull hcons hcov S ⊆ A := by
  exact (FiniteSupportClosure.hull_spec (IsActualSupport R)
    (actual_inter hcons hcov) (exists_actual_superset hcov) S).2.2 A hA hSA

/-- The old tuple-facing interface is recovered with literal occurrence maps. -/
theorem exists_hull_chart (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} (t : Fin n ↪ M) :
    ∃ (x : R.LabelledExt) (f : Fin n ↪ Fin x.arity),
      f.trans x.tuple = t ∧ support x.tuple = hull hcons hcov (support t) := by
  obtain ⟨x, hx⟩ := hull_actual hcons hcov (support t)
  have ht : support t ⊆ support x.tuple := by
    rw [hx]
    exact subset_hull hcons hcov (support t)
  obtain ⟨f, hf⟩ := factor_of_support_subset t x.tuple ht
  exact ⟨x, f, hf, hx⟩

/-- Closedness is independent of the enumeration of a finite support. -/
theorem eval_isSome_iff_actual (hcons : R.IsExactParentConsistent)
    {n : ℕ} (t : Fin n ↪ M) :
    (R.eval t).isSome ↔ IsActualSupport R (support t) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    exact ⟨⟨n, t, p, hp⟩, rfl⟩
  · rintro ⟨x, hx⟩
    have hsub : support t ⊆ support x.tuple := by
      simpa only [hx] using (Finset.Subset.refl (support t))
    obtain ⟨f, hft⟩ := factor_of_support_subset t x.tuple hsub
    have him : (support f).image x.tuple = Finset.univ.image x.tuple := by
      rw [← support_trans, hft]
      exact hx.symm
    have hf : support f = Finset.univ := Finset.image_injective x.tuple.injective him
    have hv : Finset.univ.image f ∈ x.type.scheme.scheme.plan := by
      change support f ∈ x.type.scheme.scheme.plan
      rw [hf]
      exact x.type.scheme.scheme.isPlan.domain_mem
    have heval := hcons x.tuple x.type f x.eval_eq
    rw [hft] at heval
    change R.eval t = typeMap f x.type at heval
    rw [heval]
    exact typeMap_isSome_of_mem f x.type hv

@[simp] theorem hull_eq_iff_actual (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    hull hcons hcov S = S ↔ IsActualSupport R S := by
  constructor
  · intro h
    have hS := hull_actual hcons hcov S
    simpa only [h] using hS
  · intro hS
    exact Finset.Subset.antisymm
      (hull_min hcons hcov hS (Finset.Subset.refl S))
      (subset_hull hcons hcov S)

/-- Partial evaluation is precisely finite hull-closedness. -/
theorem eval_isSome_iff_hull_eq (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} (t : Fin n ↪ M) :
    (R.eval t).isSome ↔ hull hcons hcov (support t) = support t :=
  (eval_isSome_iff_actual hcons t).trans (hull_eq_iff_actual hcons hcov (support t)).symm

/-- The literal root type is recovered by consistency, never a capped equality. -/
theorem exists_hull_chart_of_eval (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M}
    {p : S α.1 n} (hp : R.eval t = some p) :
    ∃ (x : R.LabelledExt) (f : Fin n ↪ Fin x.arity),
      f.trans x.tuple = t ∧ typeMap f x.type = some p ∧
      support x.tuple = hull hcons hcov (support t) := by
  obtain ⟨x, f, hft, hx⟩ := exists_hull_chart hcons hcov t
  refine ⟨x, f, hft, ?_, hx⟩
  have h := hcons x.tuple x.type f x.eval_eq
  rw [hft, hp] at h
  exact h.symm

/-- Coordinates of a finite support in a supplied chart. -/
def coordinates (x : R.LabelledExt) (S : Finset M) : Finset (Fin x.arity) :=
  Finset.univ.filter fun i => x.tuple i ∈ S

@[simp] theorem mem_coordinates (x : R.LabelledExt) (S : Finset M) (i : Fin x.arity) :
    i ∈ coordinates x S ↔ x.tuple i ∈ S := by simp [coordinates]

/-- Coordinates recover the literal support, provided the chart contains it. -/
theorem image_coordinates (x : R.LabelledExt) (S : Finset M)
    (hS : S ⊆ support x.tuple) : (coordinates x S).image x.tuple = S := by
  ext z
  constructor
  · rintro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_coordinates x S i).mp hi
  · intro hz
    obtain ⟨i, rfl⟩ := (mem_support x.tuple z).mp (hS hz)
    exact Finset.mem_image.mpr ⟨i, (mem_coordinates x S i).mpr hz, rfl⟩

/-- Compute the actual hull inside any actual chart, with literal equality of supports. -/
theorem hull_image (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt)
    (F : Finset (Fin x.arity)) :
    hull hcons hcov (F.image x.tuple) =
      (AmalgamationPlan.Plan.hull Finset.univ x.type.scheme.scheme.plan F).image x.tuple := by
  let H := hull hcons hcov (F.image x.tuple)
  have hin : F.image x.tuple ⊆ support x.tuple :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hH : H ⊆ support x.tuple := hull_min hcons hcov ⟨x, rfl⟩ hin
  have he := image_coordinates x H hH
  have hc : coordinates x H ∈ x.type.scheme.scheme.plan :=
    (actual_image_iff_face hcons x _).mp (he.symm ▸ hull_actual hcons hcov _)
  have hF : F ⊆ coordinates x H := by
    intro i hi
    exact (mem_coordinates x H i).mpr
      (subset_hull hcons hcov _ (Finset.mem_image_of_mem _ hi))
  apply Finset.Subset.antisymm
  · exact hull_min hcons hcov
      (actual_of_face hcons x x.type.scheme.scheme.isPlan.hull_mem)
      (Finset.image_subset_image (AmalgamationPlan.Plan.subset_hull (Finset.subset_univ _)))
  · change _ ⊆ H
    rw [← he]
    exact Finset.image_subset_image (AmalgamationPlan.Plan.hull_minimal hc hF)

/-- Any actual containing chart computes the canonical hull, independently of its enumeration. -/
theorem hull_eq_local (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) (S : Finset M)
    (hS : S ⊆ support x.tuple) :
    hull hcons hcov S = (AmalgamationPlan.Plan.hull Finset.univ
      x.type.scheme.scheme.plan (coordinates x S)).image x.tuple := by
  simpa only [image_coordinates x S hS] using hull_image hcons hcov x (coordinates x S)

@[simp] theorem hull_empty (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) : hull hcons hcov ∅ = ∅ := by
  obtain ⟨x⟩ := nonempty_labelledExt hcov
  apply (hull_eq_iff_actual hcons hcov ∅).mpr
  simpa using actual_of_face hcons x x.type.scheme.scheme.isPlan.empty_mem

@[simp] theorem hull_singleton (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (a : M) : hull hcons hcov {a} = {a} := by
  obtain ⟨A, ⟨x, rfl⟩, hA⟩ := exists_actual_superset hcov {a}
  obtain ⟨i, rfl⟩ := (mem_support x.tuple a).mp (hA (Finset.mem_singleton_self a))
  apply (hull_eq_iff_actual hcons hcov _).mpr
  simpa using actual_of_face hcons x
    (x.type.scheme.scheme.isPlan.singleton_mem (Finset.mem_univ i))

/-- The actual hull is generated by at most two of the input points.
The generating set need not itself be an evaluated support. -/
theorem exists_small_generator (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    ∃ T ⊆ S, T.card ≤ 2 ∧ hull hcons hcov T = hull hcons hcov S := by
  obtain ⟨x, hx⟩ := hull_actual hcons hcov S
  have hS : S ⊆ support x.tuple := hx.symm ▸ subset_hull hcons hcov S
  obtain ⟨F, hF, hcard, he⟩ := x.type.scheme.scheme.isPlan.exists_small_generator
    (Finset.subset_univ (coordinates x S))
  refine ⟨F.image x.tuple, ?_, (Finset.card_image_le).trans hcard, ?_⟩
  · rw [← image_coordinates x S hS]
    exact Finset.image_subset_image hF
  · rw [hull_image hcons hcov x F, he, hull_eq_local hcons hcov x S hS]

end
end VaughtConjecture.Knight.KnightRealization.FiniteHull
