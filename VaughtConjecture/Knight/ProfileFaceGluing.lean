/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProfileFaceUnion

/-! # Original-cap completion survives face gluing and profile saturation

`CapFace` is the relative lifting property of a literal occurrence map.
Gluing two such maps along their common face constructs the property on both
inclusions into the union. Saturation preserves it by the proved profile
lifting theorem. These are boundary and row-family statements; no forcing
condition or new support-plan legality is inferred.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ProfileFaceGluing

open Transform Value ExtOrd NormalizedProfileFamily

variable {C X Y Z : Type*}

/-- Restriction and completion at the original grade-one-visible cap.
All target occurrences, not only the named face, retain their capped values. -/
structure CapFace (P : (X → ExtOrd) → Prop) (Q : (Y → ExtOrd) → Prop)
    (f : X → Y) : Prop where
  restrict : ∀ {a}, Q a → P (a ∘ f)
  lift : ∀ {p a γ}, P p → Q a → SelfVis 1 γ →
    (∀ x, min (a (f x)) γ = min (p x) γ) →
    ∃ r, Q r ∧ (∀ x, r (f x) = p x) ∧ ∀ y, min (r y) γ = min (a y) γ

theorem CapFace.comp {P : (X → ExtOrd) → Prop} {Q : (Y → ExtOrd) → Prop}
    {R : (Z → ExtOrd) → Prop} {f : X → Y} {g : Y → Z}
    (hf : CapFace P Q f) (hg : CapFace Q R g) : CapFace P R (g ∘ f) where
  restrict ha := hf.restrict (hg.restrict ha)
  lift hp ha hγ hc := by
    obtain ⟨q, hq, he, hcap⟩ := hf.lift hp (hg.restrict ha) hγ hc
    obtain ⟨r, hr, hre, hrc⟩ := hg.lift hq ha hγ (fun y => (hcap y).symm)
    exact ⟨r, hr, fun x => (hre _).trans (he x), hrc⟩

theorem CapFace.exists_section {P : (X → ExtOrd) → Prop} {Q : (Y → ExtOrd) → Prop}
    {f : X → Y} (hf : CapFace P Q f) (h0 : Q (fun _ => ⊥))
    {p : X → ExtOrd} (hp : P p) : ∃ r, Q r ∧ ∀ x, r (f x) = p x := by
  obtain ⟨r, hr, he, _⟩ := hf.lift hp h0 (selfVis_bot 1)
    (fun _ => by simp only [min_bot_right])
  exact ⟨r, hr, he⟩

variable (f : C ↪ X) (g : C ↪ Y) (L : OrderLaw X) (R : OrderLaw Y)
variable {K : (C → ExtOrd) → Prop}

open ProfileFaceUnion

/-- Completing the other face on the shared lower domain proves the
relative lifting property for the entire left face, with all auxiliaries. -/
theorem left_face (hf : CapFace K L.holds f) (hg : CapFace K R.holds g) :
    CapFace L.holds (law f g L R).holds (left g) where
  restrict ha := ha.1
  lift {p a γ} hp ha hγ hc := by
    obtain ⟨q, hq, he, hcap⟩ := hg.lift (hf.restrict hp) ha.2 hγ (by
      intro c
      simpa only [Function.comp_apply, right_shared] using hc (f c))
    have hover : ∀ c, p (f c) = q (g c) := fun c => (he c).symm
    refine ⟨ProfileFaceUnion.paste g p q, paste_lawful f g L R hp hq hover,
      paste_left g p q, ?_⟩
    intro z
    rcases covered f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact (hc x).symm
    · rw [paste_right f g hover]
      exact hcap y

theorem right_face (hf : CapFace K L.holds f) (hg : CapFace K R.holds g) :
    CapFace R.holds (law f g L R).holds (right f g) where
  restrict ha := ha.2
  lift {p a γ} hp ha hγ hc := by
    obtain ⟨q, hq, he, hcap⟩ := hf.lift (hg.restrict hp) ha.1 hγ (by
      intro c
      simpa only [Function.comp_apply, right_shared] using hc (g c))
    have hover : ∀ c, q (f c) = p (g c) := he
    refine ⟨ProfileFaceUnion.paste g q p, paste_lawful f g L R hq hp hover,
      paste_right f g hover, ?_⟩
    intro z
    rcases covered f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact hcap x
    · rw [paste_right f g hover]
      exact (hc y).symm

noncomputable instance [Fintype X] [Fintype Y] : Fintype (Carrier (X := X) g) := by
  classical
  unfold Carrier
  infer_instance

/-- Adding every normalized full profile preserves each proved capped
face inclusion. This does not postulate new-row respect or active coverage. -/
theorem family_face [Fintype X] : CapFace L.holds (family L).holds Sum.inl where
  restrict := restriction L
  lift hp ha hγ hc := by
    obtain ⟨r, hr, hcap, he⟩ := NormalizedProfileLifting.lift L ha hp hγ hc
    exact ⟨r, hr, he, hcap⟩

theorem saturated_left [Fintype X] [Fintype Y]
    (hf : CapFace K L.holds f) (hg : CapFace K R.holds g) :
    CapFace L.holds (family (law f g L R)).holds (Sum.inl ∘ left g) :=
  (left_face f g L R hf hg).comp (family_face (law f g L R))

theorem saturated_right [Fintype X] [Fintype Y]
    (hf : CapFace K L.holds f) (hg : CapFace K R.holds g) :
    CapFace R.holds (family (law f g L R)).holds (Sum.inl ∘ right f g) :=
  (right_face f g L R hf hg).comp (family_face (law f g L R))

/-- Two entire lawful faces agreeing literally on the overlap can be
prescribed simultaneously against an arbitrary lawful saturated ambient. -/
theorem simultaneous_lift [Fintype X] [Fintype Y]
    {p : X → ExtOrd} {q : Y → ExtOrd}
    {a : Carrier (X := X) g ⊕ Profile (law f g L R) → ExtOrd} {γ : ExtOrd}
    (hp : L.holds p) (hq : R.holds q) (hover : ∀ c, p (f c) = q (g c))
    (ha : (family (law f g L R)).holds a) (hγ : SelfVis 1 γ)
    (hl : ∀ x, min (a (.inl (left g x))) γ = min (p x) γ)
    (hr : ∀ y, min (a (.inl (right f g y))) γ = min (q y) γ) :
    ∃ r, (family (law f g L R)).holds r ∧
      (∀ x, r (.inl (left g x)) = p x) ∧
      (∀ y, r (.inl (right f g y)) = q y) ∧
      ∀ z, min (r z) γ = min (a z) γ := by
  obtain ⟨r, hr', he, hc⟩ := (family_face (law f g L R)).lift
    (paste_lawful f g L R hp hq hover) ha hγ (by
      intro z
      rcases covered f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact hl x
      · rw [paste_right f g hover]
        exact hr y)
  exact ⟨r, hr', fun x => he _, fun y => (he _).trans (paste_right f g hover y), hc⟩

end VaughtConjecture.Knight.ProfileFaceGluing
