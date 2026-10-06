/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

/-! # Common-prefix rows over a genuinely mixed proper boundary

The old inventory may contain active owners at the new grade. Every old
occurrence is a boundary coordinate, so the lower section is constructed by
literal readback, not supplied as a future completion. This installs the
full-grade layer; it does not fill missing indices of the support plan.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ProperBoundarySourceLayer

open Transform Value ExtOrd SourcePrefixRows
open SourceLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D)
variable (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hgrade : ∀ d : Cell D, D.grade d ≤ k)

noncomputable abbrev carrier := SourceLayerCarrier.scheme D Q k hk hA

noncomputable abbrev old (d : Cell D) : Cell (carrier D Q k hk hA) :=
  toCell D Q k hk hA (.inl d)

noncomputable abbrev ownerEquiv (c : Cell D) :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) c

noncomputable abbrev base : Semantics (carrier D Q k hk hA) :=
  SeparatedSourceLayerCarrier.base D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem

noncomputable def member (c : SourcePrefixLayer.Controller (carrier D Q k hk hA) k) : Q :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm c

theorem member_controller (q : Q) :
    member D Q k hk hA hproper (controller D Q k hk hA q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm_apply_apply q

noncomputable def lower (p : Q → Cell D → ExtOrd) (q : Q)
    (d : Cell (carrier D Q k hk hA)) : ExtOrd :=
  match toOcc D Q k hk hA d with
  | .inl x => p q x
  | .inr _ => ⊥

theorem lower_old (p : Q → Cell D → ExtOrd) (q : Q) (d : Cell D) :
    lower D Q k hk hA p q (old D Q k hk hA d) = p q d := by
  simp only [lower, old, toOcc_toCell]

variable (G : Finset ExtOrd) (C : ExtOrd)
variable (hbot : ⊥ ∈ G) (hC : C ∈ G) (hG : ∀ h ∈ G, h ≤ C)
variable (hvis : ∀ h ∈ G, SelfVis k h)
variable (p : Q → Cell D → ExtOrd)
variable (hp : ∀ q, RespectsSemantics sem (p q))
variable (hb : ∀ q d, p q d ≤ C)

noncomputable def data : SourcePrefixLayer.Data (carrier D Q k hk hA) k (Cell D) where
  base := base D sem Q k hk hA hproper
  max_grade d := by
    rw [CellScheme.grade, cell_eq]
    cases toOcc D Q k hk hA d with
    | inl x => exact hgrade x
    | inr q => exact le_rfl
  grid := G
  bot_mem := hbot
  ceiling := C
  ceiling_mem := hC
  grid_bound := hG
  grid_visible := hvis
  boundary c := p (member D Q k hk hA hproper c)
  lower c := lower D Q k hk hA p (member D Q k hk hA hproper c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := old_occurrence D Q k hk hA d hd
    rw [lower_old]
    exact hb _ x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := old_occurrence D Q k hk hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff D Q k hk hA
      (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem x _).mpr
    change RespectsSemanticsBelow sem (D.cell x)
      (fun d => lower D Q k hk hA p (member D Q k hk hA hproper c)
        (old D Q k hk hA d.1))
    simpa only [lower_old] using (hp (member D Q k hk hA hproper c)).toBelow (D.cell x)
  grid_agreement a b h _ hab d hd := by
    obtain ⟨x, rfl⟩ := old_occurrence D Q k hk hA d hd
    simpa only [lower_old] using hab x

noncomputable abbrev rows :=
  (data D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb).rows

noncomputable def sectionOf (q : Q) : Cell (carrier D Q k hk hA) → ExtOrd :=
  (data D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb).profile
    (controller D Q k hk hA q)

theorem section_old (q : Q) (d : Cell D) :
    sectionOf D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb q
      (old D Q k hk hA d) = p q d := by
  rw [sectionOf, SourcePrefixLayer.Data.profile_old _ _ (SeparatedSourceLayerCarrier.old_not_full
    D Q k hk hA (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) d)]
  change lower D Q k hk hA p
    (member D Q k hk hA hproper (controller D Q k hk hA q)) (old D Q k hk hA d) = _
  rw [member_controller, lower_old]

theorem section_lawful (q : Q) :
    RespectsSemantics (rows D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb)
      (sectionOf D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb q) :=
  SourcePrefixLayer.Data.profile_respects _ _

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb).E
      (old D Q k hk hA c) (ownerEquiv D Q k hk hA hproper c d) = sem.E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full
    D Q k hk hA (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) c)]
  exact SeparatedSourceLayerCarrier.base_old D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem c d

theorem consistent (hs : sem.IsConsistent) :
    (rows D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro d hd
  obtain ⟨c, rfl⟩ := old_occurrence D Q k hk hA d hd
  apply (SeparatedSourceLayerCarrier.base_respects_iff D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem c _).mpr
  have he : (base D sem Q k hk hA hproper).E (old D Q k hk hA c) ∘
      ownerEquiv D Q k hk hA hproper c = sem.E c := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old D Q k hk hA
      (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem c d
  change RespectsSemanticsBelow sem (D.cell c)
    ((base D sem Q k hk hA hproper).E (old D Q k hk hA c) ∘
      ownerEquiv D Q k hk hA hproper c)
  rw [he]
  exact hs c

theorem section_prefix (a b : Q) {h : ExtOrd} (hh : h ∈ G)
    (hab : Agree (p a) (p b) h) :
    Agree (sectionOf D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb a)
      (sectionOf D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb b) h := by
  apply SourcePrefixLayer.Data.profile_prefix _ hh
  change Agree (p (member D Q k hk hA hproper (controller D Q k hk hA a)))
    (p (member D Q k hk hA hproper (controller D Q k hk hA b))) h
  simpa only [member_controller] using hab

theorem section_supported (q : Q) (d : Cell (carrier D Q k hk hA)) :
    Supported G k (p q)
      (sectionOf D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb q d) := by
  have hs := SourcePrefixLayer.Data.profile_supported
    (data D sem Q k hk hA hproper hgrade G C hbot hC hG hvis p hp hb)
    (fun c x hx => ?_) (controller D Q k hk hA q) d
  · change Supported G k (p (member D Q k hk hA hproper (controller D Q k hk hA q))) _ at hs
    simpa only [member_controller, sectionOf] using hs
  · obtain ⟨x, rfl⟩ := old_occurrence D Q k hk hA x hx
    exact Or.inr (Or.inr (Or.inl ⟨x, lower_old D Q k hk hA p _ x⟩))

end VaughtConjecture.Knight.ProperBoundarySourceLayer
