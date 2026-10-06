/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows

/-! # Preservation of the recursive selected-section contract

Construct the next decoder on the actual successor, and recover the same
lawfulness, literal readback, boundedness, support and whole-coordinate
agreement properties. This does not assert arbitrary-ambient lifting.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveSuccessorRows SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, (n + 4)) J) :=
  HighLayerBountiful.equiv (predecessor sem n hA) (Profile sem n)
    (n + 4) (Nat.succ_pos (n + 3)) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, (n + 4)) J)
    (p : (predecessor sem n hA).below J → ExtOrd) :
    RespectsSemanticsBelow P.rows J p ↔
      RespectsSemanticsBelow (rows sem n hA hp P) J (p ∘ (equiv sem n hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem n hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (predecessor sem n hA) (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem n hA hp P b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (carrier sem n hA) → ExtOrd}
    (hread : ∀ d, r (boundary sem n hA d) = p d) :
    RespectsSemanticsBelow (rows sem n hA hp P) J (fun d => r d.1) := by
  have hl := P.proper_lawful hJ hpr (r := fun d => r (old sem n hA d)) hread
  let e := equiv sem n hA J (fun h => hJ h.1)
  have he : (fun d : (carrier sem n hA).below J => r d.1) =
      (fun d : (predecessor sem n hA).below J => r (old sem n hA d.1)) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rfl
  rw [he]
  exact (respects_iff sem n hA hp P J (fun h => hJ h.1) _).mp hl

theorem full_source_short (c : Cell (carrier sem n hA)) (hc : (carrier sem n hA).scope c = A)
    (d : (carrier sem n hA).below ((carrier sem n hA).cell c)) :
    Short ((carrier sem n hA).grade c) ((rows sem n hA hp P).E c d) := by
  by_cases he : (carrier sem n hA).cell c = (A, (n + 4))
  · have q := (controllerEquiv sem n hA hp).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller sem n hA q).1 = c := congrArg Subtype.val hq
    have hr := (data sem n hA hp P).row_new (controller sem n hA q)
    subst c
    rw [hr]
    rw [show (carrier sem n hA).grade (controller sem n hA q).1 = (n + 4) from
      congrArg Prod.snd (controller sem n hA q).2]
    change Short (n + 4) (source sem n hA hp P q d.1)
    exact source_short sem n hA hp P q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem n hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem n hA) (Profile sem n)
      (n + 4) (Nat.succ_pos (n + 3)) hA (.inl x)
    change Short ((carrier sem n hA).grade (old sem n hA x)) _
    rw [show (carrier sem n hA).grade (old sem n hA x) = (predecessor sem n hA).grade x
      from congrArg Prod.snd hi]
    exact P.full_short x ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : (n + 4) ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem n := CanonicalRecursiveInventory.encode sem (n + 1)
  (hpr.mono (show GradedLe (A, (n + 4)) (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (carrier sem n hA)) : ExtOrd :=
  PairedSlotDecoder.decode (n + 4) (values p) G C
    (source sem n hA hp P (normalized sem n hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hC : SelfVis (n + 4) C) (d : Cell D) :
    sectionOf sem n hA hp P hK hpr ht G C (boundary sem n hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hC : SelfVis (n + 4) C) :
    RespectsSemanticsBelow (rows sem n hA hp P) (A, K)
      (fun d => sectionOf sem n hA hp P hK hpr ht G C d.1) := by
  have hproper (c : Cell (carrier sem n hA)) (hc : (carrier sem n hA).scope c ≠ A)
      (hg : (carrier sem n hA).grade c ≤ K) :
      RespectsSemanticsBelow (rows sem n hA hp P) ((carrier sem n hA).cell c)
        (fun d => sectionOf sem n hA hp P hK hpr ht G C d.1) := by
    exact proper_lawful sem n hA hp P
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier sem n hA).isPlan.subset_of_mem ((carrier sem n hA).scope_mem_plan c)) ha))
      (hpr.mono ⟨(carrier sem n hA).isPlan.subset_of_mem ((carrier sem n hA).scope_mem_plan c), hg⟩)
      (section_boundary sem n hA hp P hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 4))
      (fun d => sectionOf sem n hA hp P hK hpr ht G C d.1) := by
    apply (data sem n hA hp P).decoded_respects (controller sem n hA (normalized sem n hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem n hA hp P c.1 hc)
    intro c hc
    have he : (carrier sem n hA).cell c.1 ≠ (A, (n + 4)) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data sem n hA hp P).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data sem n hA hp P).base _
      (fun d => PairedSlotDecoder.decode (n + 4) (values p) G C
        ((data sem n hA hp P).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data sem n hA hp P).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (carrier sem n hA).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp (n + 4) hA c.1 hc
    exact hl.mono ⟨(carrier sem n hA).isPlan.subset_of_mem
      ((carrier sem n hA).scope_mem_plan c.1), hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis (n + 4) C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem n hA)) : sectionOf sem n hA hp P hK hpr ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L : ℕ} (hL : (n + 4) ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem n hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem n hA hp P hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hC : SelfVis (n + 4) C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem n hA hp P hK hpr ht G C) (sectionOf sem n hA hp P hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem n hA hp P
    (normalized sem n hK hpr ht) (normalized sem n hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

/-- The semantic successor returns precisely the selected-section contract it
consumes. In particular no future selected section is a residual assumption. -/
def successor : CanonicalRecursiveContract.State sem (n + 1) hA where
  rows := rows sem n hA hp P
  consistent := consistent sem n hA hp P
  proper_lawful := proper_lawful sem n hA hp P
  full_short := full_source_short sem n hA hp P
  sectionOf := sectionOf sem n hA hp P
  section_boundary := section_boundary sem n hA hp P
  section_lawful := section_lawful sem n hA hp P
  section_bound := section_bound sem n hA hp P
  section_supported := section_supported sem n hA hp P
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    section_agreement sem n hA hp P hK hpr htp hqr htq

end
end VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections
