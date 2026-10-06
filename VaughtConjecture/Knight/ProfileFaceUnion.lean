/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NormalizedProfileLifting

/-! # Occurrence-exact unions of two faces

The common face is identified once; every other occurrence is retained.
The construction is independent of labels and source codes. It supplies a
boundary inventory, not the missing full-scope rows of a support plan.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ProfileFaceUnion

variable {C X Y : Type*} (f : C ↪ X) (g : C ↪ Y)

abbrev Carrier := X ⊕ {y : Y // y ∉ Set.range g}

def left (x : X) : Carrier (X := X) g := .inl x

open Classical in
noncomputable def right (y : Y) : Carrier (X := X) g :=
  if h : y ∈ Set.range g then .inl (f h.choose) else .inr ⟨y, h⟩

theorem right_shared (c : C) : right f g (g c) = left g (f c) := by
  classical
  have h : g c ∈ Set.range g := ⟨c, rfl⟩
  rw [right, dite_eq_left h]
  exact congrArg (fun d => Sum.inl (f d)) (g.injective h.choose_spec)

theorem right_private (y : {y : Y // y ∉ Set.range g}) :
    right f g y = .inr y := by
  classical
  simp only [right, dite_eq_right y.property]

theorem left_injective : Function.Injective (left g : X → Carrier (X := X) g) :=
  Sum.inl_injective

theorem right_injective : Function.Injective (right f g) := by
  classical
  intro y z h
  by_cases hy : y ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hy
    rw [right_shared] at h
    by_cases hz : z ∈ Set.range g
    · obtain ⟨d, rfl⟩ := hz
      rw [right_shared] at h
      exact congrArg g (f.injective (Sum.inl.inj h))
    · rw [right, dite_eq_right hz] at h
      cases h
  · rw [right, dite_eq_right hy] at h
    by_cases hz : z ∈ Set.range g
    · obtain ⟨d, rfl⟩ := hz
      rw [right_shared] at h
      cases h
    · rw [right, dite_eq_right hz] at h
      exact congrArg Subtype.val (Sum.inr.inj h)

theorem overlap (x : X) (y : Y) :
    left g x = right f g y ↔ ∃ c, f c = x ∧ g c = y := by
  classical
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hy
      rw [right_shared] at h
      exact ⟨c, (Sum.inl.inj h).symm, rfl⟩
    · rw [right, dite_eq_right hy] at h
      cases h
  · rintro ⟨c, rfl, rfl⟩
    exact (right_shared f g c).symm

theorem covered (z : Carrier (X := X) g) :
    (∃ x, left g x = z) ∨ ∃ y, right f g y = z := by
  cases z with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr y => exact Or.inr ⟨y, right_private f g y⟩

def paste {V : Type*} (p : X → V) (q : Y → V) : Carrier (X := X) g → V
  | .inl x => p x
  | .inr y => q y

theorem paste_left {V : Type*} (p : X → V) (q : Y → V) (x : X) :
    paste g p q (left g x) = p x := rfl

theorem paste_right {V : Type*} {p : X → V} {q : Y → V}
    (h : ∀ c, p (f c) = q (g c)) (y : Y) : paste g p q (right f g y) = q y := by
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨c, rfl⟩ := hy
    rw [right_shared]
    exact h c
  · rw [right, dite_eq_right hy]
    rfl

/-- Prescribed face values paste if and only if they agree at every
shared occurrence, including auxiliaries with coincident indices. -/
theorem paste_iff {V : Type*} (p : X → V) (q : Y → V) :
    (∃ r : Carrier (X := X) g → V, (∀ x, r (left g x) = p x) ∧
      ∀ y, r (right f g y) = q y) ↔ ∀ c, p (f c) = q (g c) := by
  constructor
  · rintro ⟨r, hl, hr⟩ c
    exact (hl _).symm.trans ((congrArg r (right_shared f g c).symm).trans (hr _))
  · intro h
    exact ⟨paste g p q, paste_left g p q, paste_right f g h⟩

open NormalizedProfileFamily Transform Value ExtOrd

/-- The boundary law is exactly the conjunction of the two face laws.
Its normalization/refinement properties are proved componentwise. -/
noncomputable def law (L : OrderLaw X) (R : OrderLaw Y) :
    OrderLaw (Carrier (X := X) g) where
  holds p := L.holds (p ∘ left g) ∧ R.holds (p ∘ right f g)
  bottom := ⟨L.bottom, R.bottom⟩
  visible hp z := by
    rcases covered f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact L.visible hp.1 x
    · exact R.visible hp.2 y
  order hp hv hz hm := ⟨L.order hp.1 (fun x => hv _) (fun x => hz _)
    (fun x y => hm _ _), R.order hp.2 (fun x => hv _) (fun x => hz _)
      (fun x y => hm _ _)⟩
  refine ha hq hb hs := ⟨L.refine ha hq.1 hb.1 (fun x y => hs _ _),
    R.refine ha hq.2 hb.2 (fun x y => hs _ _)⟩

theorem paste_lawful (L : OrderLaw X) (R : OrderLaw Y)
    {p : X → ExtOrd} {q : Y → ExtOrd} (hp : L.holds p) (hq : R.holds q)
    (h : ∀ c, p (f c) = q (g c)) : (law f g L R).holds (paste g p q) := by
  constructor
  · exact hp
  · simpa only [Function.comp_def, paste_right f g h] using hq

end VaughtConjecture.Knight.ProfileFaceUnion
