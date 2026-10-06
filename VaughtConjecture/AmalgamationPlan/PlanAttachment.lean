/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.AmalgamationPlan.Plan

/-! # One-point attachment along a prescribed visible face

The old plan and a candidate one-point extension of one of its visible faces
can be retained simultaneously. The induction follows a coatom containing
the requested face; it need not use the fixed branch chosen by
`isPlan_extend_one`.

This is a statement about support geometry only. It constructs no semantic
rows and does not assert amalgamation of prescribed respecting labellings.
-/

@[expose] public section

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {α : Type*} [DecidableEq α]

private theorem restrict_restrict {P : Finset (Finset α)} {A B : Finset α}
    (hBA : B ⊆ A) : restrictPlan (restrictPlan P A) B = restrictPlan P B := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hBA⟩, h.2⟩⟩

private theorem restrict_self {A : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) : restrictPlan P A = P := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  exact ⟨And.left, fun h => ⟨h, hP.subset_of_mem h⟩⟩

private theorem coatom_over_face {A B : Finset α} {P : Finset (Finset α)}
    (hP : IsPlan A P) (hB : B ∈ P) (hne : B ≠ A) :
    ∃ a ∈ A, A.erase a ∈ P ∧ B ⊆ A.erase a := by
  cases hP with
  | empty =>
    exact (hne (Finset.mem_singleton.mp hB)).elim
  | singleton a =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | hB
    · exact ⟨a, by simp, by simp, Finset.empty_subset _⟩
    · exact (hne hB).elim
  | @step A a b Q R P ha hb hab hQ hR hmem hre hPeq =>
    subst P
    simp only [Finset.mem_union, Finset.mem_singleton] at hB
    rcases hB with (hB | hB) | hB
    · exact ⟨a, ha, by simp [hQ.domain_mem], hQ.subset_of_mem hB⟩
    · exact ⟨b, hb, by simp [hR.domain_mem], hR.subset_of_mem hB⟩
    · exact (hne hB).elim

private theorem restrict_glue_left {A B : Finset α} {P Q : Finset (Finset α)}
    (hP : IsPlan A P) (hQ : IsPlan B Q)
    (hres : restrictPlan P (A ∩ B) = restrictPlan Q (A ∩ B))
    {x : α} (hxB : x ∈ B) (hxA : x ∉ A) :
    restrictPlan (P ∪ Q ∪ {A ∪ B}) A = P := by
  ext S
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_powerset]
  constructor
  · rintro ⟨(hS | hS) | rfl, hSA⟩
    · exact hS
    · have hSAB : S ⊆ A ∩ B := by
        intro y hy
        exact Finset.mem_inter.mpr ⟨hSA hy, hQ.subset_of_mem hS hy⟩
      have hm : S ∈ restrictPlan Q (A ∩ B) :=
        Finset.mem_inter.mpr ⟨hS, Finset.mem_powerset.mpr hSAB⟩
      rw [← hres] at hm
      exact (Finset.mem_inter.mp hm).1
    · exact (hxA (hSA (Finset.mem_union_right _ hxB))).elim
  · intro hS
    exact ⟨Or.inl (Or.inl hS), hP.subset_of_mem hS⟩

private theorem attach_coatom {A : Finset α} {P Q : Finset (Finset α)}
    {a x : α} (hP : IsPlan A P) (ha : a ∈ A) (hx : x ∉ A)
    (hface : A.erase a ∈ P) (hQ : IsPlan (A.erase a ∪ {x}) Q)
    (hfaceQ : A.erase a ∈ Q)
    (hres : restrictPlan Q (A.erase a) = restrictPlan P (A.erase a)) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧
      A.erase a ∪ {x} ∈ R ∧ restrictPlan R (A.erase a ∪ {x}) = Q := by
  have hax : a ≠ x := fun h => hx (h ▸ ha)
  have hex : (A ∪ {x}).erase x = A := by
    rw [Finset.union_singleton, Finset.erase_insert hx]
  have hea : (A ∪ {x}).erase a = A.erase a ∪ {x} := by
    rw [Finset.union_singleton, Finset.erase_insert_of_ne hax.symm,
      Finset.union_singleton]
  have hi : A ∩ (A.erase a ∪ {x}) = A.erase a := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    aesop
  have hu : A ∪ (A.erase a ∪ {x}) = A ∪ {x} := by
    ext y
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    tauto
  have hare : a ∉ A.erase a ∪ {x} := by simp [hax]
  have hover : restrictPlan P (A ∩ (A.erase a ∪ {x})) =
      restrictPlan Q (A ∩ (A.erase a ∪ {x})) := by rw [hi, hres]
  refine ⟨P ∪ Q ∪ {A ∪ {x}}, ?_, by simp [hP.domain_mem], ?_,
    Finset.mem_union_left _ (Finset.mem_union_right _ hQ.domain_mem), ?_⟩
  · apply IsPlan.step (a := x) (b := a)
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      (Finset.mem_union_left _ ha) hax.symm
    · simpa only [hex] using hP
    · simpa only [hea] using hQ
    · simpa only [hex] using And.intro hface hfaceQ
    · change restrictPlan P (((A ∪ {x}).erase x).erase a) =
        restrictPlan Q (((A ∪ {x}).erase x).erase a)
      rw [hex, hres]
    · rfl
  · simpa only [hu] using restrict_glue_left hP hQ hover
      (Finset.mem_union_right _ (Finset.mem_singleton_self x)) hx
  · have hover' : restrictPlan Q ((A.erase a ∪ {x}) ∩ A) =
        restrictPlan P ((A.erase a ∪ {x}) ∩ A) := by
      rw [Finset.inter_comm]
      exact hover.symm
    simpa only [Finset.union_comm, hu] using
      restrict_glue_left hQ hP hover' ha hare

/-- Attach a prescribed one-point plan over any visible old face. Both the
old whole and the candidate face retain their plans literally. -/
theorem IsPlan.attach_one_over_face {A B : Finset α} {P Q : Finset (Finset α)}
    {x : α} (hP : IsPlan A P) (hB : B ∈ P) (hx : x ∉ A)
    (hQ : IsPlan (B ∪ {x}) Q) (hBQ : B ∈ Q)
    (hres : restrictPlan Q B = restrictPlan P B) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧
      B ∪ {x} ∈ R ∧ restrictPlan R (B ∪ {x}) = Q := by
  induction A using Finset.strongInductionOn generalizing B P Q with
  | _ A ih =>
    by_cases hBA : B = A
    · subst B
      exact ⟨Q, hQ, hBQ, hres.trans (restrict_self hP), hQ.domain_mem, restrict_self hQ⟩
    · obtain ⟨a, ha, hface, hBsub⟩ := coatom_over_face hP hB hBA
      have hBe : B ∈ restrictPlan P (A.erase a) :=
        Finset.mem_inter.mpr ⟨hB, Finset.mem_powerset.mpr hBsub⟩
      have hres' : restrictPlan Q B = restrictPlan (restrictPlan P (A.erase a)) B := by
        rw [restrict_restrict hBsub, hres]
      obtain ⟨E, hE, hAE, hEA, hBE, hEB⟩ := ih (A.erase a)
        (Finset.erase_ssubset ha) (restrict_isPlan hP hface) hBe
        (fun h => hx (Finset.mem_of_mem_erase h)) hQ hBQ hres'
      obtain ⟨R, hR, hAR, hRA, hER, hRE⟩ :=
        attach_coatom hP ha hx hface hE hAE hEA
      have hBEx : B ∪ {x} ⊆ A.erase a ∪ {x} :=
        Finset.union_subset_union hBsub (Finset.Subset.refl _)
      have hBR : B ∪ {x} ∈ R := by
        have hm : B ∪ {x} ∈ restrictPlan R (A.erase a ∪ {x}) := by
          rw [hRE]
          exact hBE
        exact (Finset.mem_inter.mp hm).1
      refine ⟨R, hR, hAR, hRA, hBR, ?_⟩
      calc restrictPlan R (B ∪ {x})
          = restrictPlan (restrictPlan R (A.erase a ∪ {x})) (B ∪ {x}) :=
            (restrict_restrict hBEx).symm
        _ = Q := by rw [hRE, hEB]

/-- One-point extension may be directed through any prescribed visible face.
The extension plan depends on that face; this does not make all fresh faces
visible in one common plan. -/
theorem IsPlan.extend_one_over_face {A B : Finset α} {P : Finset (Finset α)}
    {x : α} (hP : IsPlan A P) (hB : B ∈ P) (hx : x ∉ A) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧ B ∪ {x} ∈ R := by
  have hxB : x ∉ B := fun h => hx (hP.subset_of_mem hB h)
  obtain ⟨Q, hQ, hBQ, hres⟩ := isPlan_extend_one hxB (restrict_isPlan hP hB)
  obtain ⟨R, hR, hAR, hRA, hBR, -⟩ := hP.attach_one_over_face hB hx hQ hBQ hres
  exact ⟨R, hR, hAR, hRA, hBR⟩

/-- Every retained singleton can be the base of a fresh pair, with a
request-dependent extension plan preserving the whole old plan. -/
theorem IsPlan.extend_one_over_singleton {A : Finset α} {P : Finset (Finset α)}
    {a x : α} (hP : IsPlan A P) (ha : a ∈ A) (hx : x ∉ A) :
    ∃ R, IsPlan (A ∪ {x}) R ∧ A ∈ R ∧ restrictPlan R A = P ∧ {a, x} ∈ R := by
  simpa only [Finset.singleton_union] using
    hP.extend_one_over_face (hP.singleton_mem ha) hx

-- Non-vacuous regression at both ends of a three-point old domain. These
-- are separate extension plans, not simultaneous visibility claims.
example : ∀ a ∈ ({0, 1, 2} : Finset ℕ),
    ∃ R, IsPlan ({0, 1, 2} ∪ {3}) R ∧ {0, 1, 2} ∈ R ∧
      restrictPlan R {0, 1, 2} = canonicalPlan {0, 1, 2} ∧ {a, 3} ∈ R := by
  intro a ha
  exact (isPlan_canonicalPlan {0, 1, 2}).extend_one_over_singleton ha (by decide)

/-- Two finite plans agreeing on a common visible face have an amalgam on
the literal union of their domains, preserving both plans exactly. There
is no bound on how many new points the second plan contributes. This is
support-plan amalgamation, not amalgamation of semantic rows or labels. -/
theorem IsPlan.amalgamate {A C : Finset α} {P Q : Finset (Finset α)}
    (hP : IsPlan A P) (hQ : IsPlan C Q)
    (hAP : A ∩ C ∈ P) (hAQ : A ∩ C ∈ Q)
    (hres : restrictPlan P (A ∩ C) = restrictPlan Q (A ∩ C)) :
    ∃ R, IsPlan (A ∪ C) R ∧ A ∈ R ∧ restrictPlan R A = P ∧
      C ∈ R ∧ restrictPlan R C = Q := by
  induction C using Finset.strongInductionOn generalizing A P Q with
  | _ C ih =>
    by_cases hCA : C ⊆ A
    · have hi : A ∩ C = C := Finset.inter_eq_right.mpr hCA
      have hu : A ∪ C = A := Finset.union_eq_left.mpr hCA
      refine ⟨P, hu.symm ▸ hP, hP.domain_mem, restrict_self hP, hi ▸ hAP, ?_⟩
      simpa only [hi, restrict_self hQ] using hres
    · have hne : A ∩ C ≠ C := fun he => hCA (Finset.inter_eq_right.mp he)
      obtain ⟨x, hxC, hface, hsub⟩ := coatom_over_face hQ hAQ hne
      have hxA : x ∉ A := by
        intro hxA
        exact Finset.notMem_erase x C (hsub (Finset.mem_inter.mpr ⟨hxA, hxC⟩))
      have hi : A ∩ C.erase x = A ∩ C := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, (fun he => hxA (he ▸ h.1)), h.2⟩
      have hAP' : A ∩ C.erase x ∈ P := hi.symm ▸ hAP
      have hAQ' : A ∩ C.erase x ∈ restrictPlan Q (C.erase x) := by
        rw [hi]
        exact Finset.mem_inter.mpr ⟨hAQ, Finset.mem_powerset.mpr hsub⟩
      have hres' : restrictPlan P (A ∩ C.erase x) =
          restrictPlan (restrictPlan Q (C.erase x)) (A ∩ C.erase x) := by
        rw [hi, restrict_restrict hsub, hres]
      obtain ⟨R, hR, hAR, hRA, hDR, hRD⟩ := ih (C.erase x)
        (Finset.erase_ssubset hxC) hP (restrict_isPlan hQ hface) hAP' hAQ' hres'
      have hxR : x ∉ A ∪ C.erase x := by simp [hxA]
      have hCx : C.erase x ∪ {x} = C := by
        rw [Finset.union_singleton, Finset.insert_erase hxC]
      obtain ⟨S, hS, hRS, hSR, hCS, hSC⟩ := hR.attach_one_over_face hDR hxR
        (hCx.symm ▸ hQ) hface hRD.symm
      have hu : (A ∪ C.erase x) ∪ {x} = A ∪ C := by
        rw [Finset.union_assoc, hCx]
      have hAS : A ∈ S := by
        have hm : A ∈ restrictPlan S (A ∪ C.erase x) := hSR.symm ▸ hAR
        exact (Finset.mem_inter.mp hm).1
      refine ⟨S, hu ▸ hS, hAS, ?_, hCx ▸ hCS, hCx ▸ hSC⟩
      calc restrictPlan S A
          = restrictPlan (restrictPlan S (A ∪ C.erase x)) A :=
            (restrict_restrict Finset.subset_union_left).symm
        _ = P := by rw [hSR, hRA]

-- Both inputs contribute two private points, not just one. The overlap
-- is the singleton {2}; each side retains its arbitrary prescribed plan.
example {P Q : Finset (Finset ℕ)} (hP : IsPlan {0, 1, 2} P)
    (hQ : IsPlan {2, 3, 4} Q) :
    ∃ R, IsPlan ({0, 1, 2} ∪ {2, 3, 4} : Finset ℕ) R ∧
    {0, 1, 2} ∈ R ∧ restrictPlan R {0, 1, 2} = P ∧
    {2, 3, 4} ∈ R ∧ restrictPlan R {2, 3, 4} = Q := by
  have hi : ({0, 1, 2} ∩ {2, 3, 4} : Finset ℕ) = {2} := by decide
  have hp2 := hP.singleton_mem (show 2 ∈ ({0, 1, 2} : Finset ℕ) by decide)
  have hq2 := hQ.singleton_mem (show 2 ∈ ({2, 3, 4} : Finset ℕ) by decide)
  apply hP.amalgamate hQ (hi.symm ▸ hp2) (hi.symm ▸ hq2)
  rw [hi]
  ext T
  simp only [restrictPlan, Finset.mem_inter, Finset.mem_powerset]
  constructor <;> rintro ⟨_, hT⟩
  · rcases Finset.subset_singleton_iff.mp hT with rfl | rfl
    · exact ⟨hQ.empty_mem, Finset.empty_subset _⟩
    · exact ⟨hq2, Finset.Subset.refl _⟩
  · rcases Finset.subset_singleton_iff.mp hT with rfl | rfl
    · exact ⟨hP.empty_mem, Finset.empty_subset _⟩
    · exact ⟨hp2, Finset.Subset.refl _⟩

/-- Pairwise compatible prescriptions need not have a simultaneous
amalgam on their prescribed union: the three edges of a triangle cannot
all be visible. Binary amalgamation requires a visible overlap at each
successive step, not merely pairwise matching restrictions. -/
theorem not_all_triangle_edges {P : Finset (Finset (Fin 3))}
    (hP : IsPlan Finset.univ P) :
    ¬ ∀ i : Fin 3, Finset.univ.erase i ∈ P := by
  intro h
  obtain ⟨a, b, _, _, _, hp, _, _⟩ := hP.pivot_pair (by decide)
  have h0 := (hp 0 (Finset.mem_univ _)).mp (h 0)
  have h1 := (hp 1 (Finset.mem_univ _)).mp (h 1)
  have h2 := (hp 2 (Finset.mem_univ _)).mp (h 2)
  omega

end VaughtConjecture.AmalgamationPlan.Plan
