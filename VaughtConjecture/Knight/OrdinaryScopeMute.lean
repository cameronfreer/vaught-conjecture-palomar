/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MaximalFullLayer
public import VaughtConjecture.Knight.HighLayerSections
public import VaughtConjecture.Knight.OrbitSupportSubstitution

/-! # Completing an ordinary scope with a mute highest owner

Use the existing zero-row high layer, not its active-apex modification. The
renderer is specified on every occurrence: old values remain literal and the
only new value is bottom. Thus one external grid and original support inventory
survive scope completion unchanged. The predecessor's bountifulness is consumed;
no bountifulness of a prospective output is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryScopeMute
open Transform Value ExtOrd SourceLayerCarrier SourcePrefixRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K)
  (hKl : K < l) (hlA : l ≤ A.card)

abbrev carrier := MaximalFullLayer.scheme D K l hKl hlA
abbrev old := MaximalFullLayer.old D K l hKl hlA
abbrev apex := MaximalFullLayer.apex D K l hKl hlA
abbrev rows := MaximalFullLayer.base D sem K l hK hKl hlA

def render (p : Cell D → ExtOrd) : Cell (carrier D K l hKl hlA) → ExtOrd :=
  fun d => Sum.elim p (fun _ => ⊥)
    (toOcc D Unit l (MaximalFullLayer.positive K l hKl) hlA d)

theorem render_old (p : Cell D → ExtOrd) (d : Cell D) :
    render D K l hKl hlA p (old D K l hKl hlA d) = p d := by
  simp only [render, old, MaximalFullLayer.old, toOcc_toCell, Sum.elim_inl]

theorem render_apex (p : Cell D → ExtOrd) :
    render D K l hKl hlA p (apex D K l hKl hlA) = ⊥ := by
  simp only [render, apex, MaximalFullLayer.apex, toOcc_toCell, Sum.elim_inr]

theorem covered (d : Cell (carrier D K l hKl hlA)) :
    (∃ c, d = old D K l hKl hlA c) ∨ d = apex D K l hKl hlA := by
  obtain ⟨x, rfl⟩ := (enumeration D Unit l (MaximalFullLayer.positive K l hKl) hlA).surjective d
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr u => cases u; exact Or.inr rfl

theorem render_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D sem K l hK hKl hlA) (render D K l hKl hlA p) := by
  obtain ⟨r, hr, hold, hnew⟩ := HighLayerBountiful.exists_zero_tail D Unit l
    (MaximalFullLayer.positive K l hKl) hlA K hK hKl sem
    (rows D sem K l hK hKl hlA) (MaximalFullLayer.inherited_row D sem K l hK hKl hlA) hp
  have he : render D K l hKl hlA p = r := by
    funext d
    rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
    · exact (render_old D K l hKl hlA p c).trans (hold c).symm
    · exact (render_apex D K l hKl hlA p).trans (hnew ()).symm
  exact he.symm ▸ hr

theorem render_bound {p : Cell D → ExtOrd} {θ : ExtOrd} (hp : ∀ d, p d ≤ θ)
    (d : Cell (carrier D K l hKl hlA)) : render D K l hKl hlA p d ≤ θ := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact bot_le

theorem render_proper {p : Cell D → ExtOrd} (hp : ∀ d, p d ≠ ⊤)
    (d : Cell (carrier D K l hKl hlA)) : render D K l hKl hlA p d ≠ ⊤ := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact bot_ne_top

/-- All cut equations survive, not just equations at represented fields. -/
theorem render_agreement {p q : Cell D → ExtOrd} {γ : ExtOrd} (hpq : Agree p q γ) :
    Agree (render D K l hKl hlA p) (render D K l hKl hlA q) γ := by
  intro d
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · simp only [render_old]; exact hpq c
  · simp only [render_apex]

/-- No new grid point or supporting original field is introduced. -/
theorem render_supported {X : Type*} {v : X → ExtOrd} {k : ℕ} {G : Set ExtOrd}
    {p : Cell D → ExtOrd} (hp : ∀ d, OrbitPrefixSupport.Supported k G v (p d))
    (d : Cell (carrier D K l hKl hlA)) :
    OrbitPrefixSupport.Supported k G v (render D K l hKl hlA p d) := by
  rcases covered D K l hKl hlA d with ⟨c, rfl⟩ | rfl
  · rw [render_old]; exact hp c
  · rw [render_apex]; exact Or.inl rfl

theorem apex_row (d : (carrier D K l hKl hlA).below
    ((carrier D K l hKl hlA).cell (apex D K l hKl hlA))) :
    (rows D sem K l hK hKl hlA).E (apex D K l hKl hlA) d = ⊥ := by
  simp only [rows, MaximalFullLayer.base, apex, MaximalFullLayer.apex,
    SeparatedSourceLayerCarrier.base, toOcc_toCell, SeparatedSourceLayerCarrier.oldTable]

theorem apex_short (d : (carrier D K l hKl hlA).below
    ((carrier D K l hKl hlA).cell (apex D K l hKl hlA))) :
    SharpWitnessComposition.Short l ((rows D sem K l hK hKl hlA).E
      (apex D K l hKl hlA) d) := by
  rw [apex_row]
  exact Or.inl rfl

/-- Inactivity follows from the installed zero row for every lawful section,
not just for the selected renderer. -/
theorem apex_inactive {p : Cell (carrier D K l hKl hlA) → ExtOrd}
    (hp : RespectsSemantics (rows D sem K l hK hKl hlA) p) :
    p (apex D K l hKl hlA) = ⊥ := by
  obtain ⟨g, σ, _, _, hb, _, _, hr⟩ := hp.locality (apex D K l hKl hlA)
  have hh := hr ⟨apex D K l hKl hlA, GradedLe.refl _⟩
  simpa only [rows, MaximalFullLayer.base, apex, MaximalFullLayer.apex,
    SeparatedSourceLayerCarrier.base, toOcc_toCell, SeparatedSourceLayerCarrier.oldTable,
    min_self, hb, min_bot_left] using hh

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D sem K l hK hKl hlA).E (old D K l hKl hlA c)
      (MaximalFullLayer.ownerEquiv D K l hK hKl hlA c d) = sem.E c d :=
  MaximalFullLayer.inherited_row D sem K l hK hKl hlA c d

/-- Existing short-row receipts transport, but inherited long rows are allowed. -/
theorem inherited_short (c : Cell D)
    (hc : ∀ d : D.below (D.cell c), SharpWitnessComposition.Short (D.grade c) (sem.E c d))
    (d : (carrier D K l hKl hlA).below
      ((carrier D K l hKl hlA).cell (old D K l hKl hlA c))) :
    SharpWitnessComposition.Short ((carrier D K l hKl hlA).grade (old D K l hKl hlA c))
      ((rows D sem K l hK hKl hlA).E (old D K l hKl hlA c) d) := by
  obtain ⟨e, rfl⟩ := (MaximalFullLayer.ownerEquiv D K l hK hKl hlA c).surjective d
  rw [inherited_row]
  simpa only [CellScheme.grade, old, MaximalFullLayer.old, cell_toCell, index] using hc e

theorem consistent (hs : sem.IsConsistent) : (rows D sem K l hK hKl hlA).IsConsistent :=
  MaximalFullLayer.consistent D sem K l hK hKl hlA hs

theorem coded (hs : sem.IsCoded) : (rows D sem K l hK hKl hlA).IsCoded :=
  MaximalFullLayer.coded D sem K l hK hKl hlA hs

theorem bountiful (hpos : 0 < K) (hs : sem.IsBountiful) :
    (rows D sem K l hK hKl hlA).IsBountiful :=
  MaximalFullLayer.bountiful D sem K l hK hKl hlA hpos hs

theorem complete (hs : ∀ J ∈ AmalgamationPlan.Plan.gradedPlan D.plan,
    J ≠ (A, l) → ∃ d, D.cell d = J) : (carrier D K l hKl hlA).IsComplete :=
  MaximalFullLayer.complete D K l hKl hlA hs

/-- When the one missing level is the scope cardinality, there are no missing
proper indices at that level. This discharges the apex-completeness ledger. -/
theorem complete_last (hcard : A.card = l) (hnext : l = K + 1)
    (hs : ∀ J ∈ AmalgamationPlan.Plan.gradedPlan D.plan, J.2 ≤ K → ∃ d, D.cell d = J) :
    (carrier D K l hKl hlA).IsComplete := by
  apply complete D K l hKl hlA
  intro J hJ hne
  apply hs J hJ
  have hmem := AmalgamationPlan.Plan.mem_gradedPlan.mp hJ
  have hgrade := hmem.2.2
  have hsub := D.isPlan.subset_of_mem hmem.1
  have hc := Finset.card_le_card hsub
  by_contra hn
  have hj : J.2 = l := by omega
  have he : J.1 = A := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne (Prod.ext he hj)

end
end VaughtConjecture.Knight.OrdinaryScopeMute
