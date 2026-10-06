/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections

/-! # Constructed recursive semantics and selected sections

Iteration is over grades on a fixed original proper boundary. All semantic
contract fields are constructed by induction. This is not iteration of legal
attachments: unrestricted recursive bountifulness remains a separate theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSemantics
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding
open CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

/-- Construct every contract field, starting at the actual recursive seed. -/
def state : (n : ℕ) → (hA : n + 3 ≤ A.card) → State sem n hA
  | 0, hA => seed sem hA hp
  | n + 1, hA => CanonicalRecursiveSuccessorSections.successor sem n hA hp
      (state n (Nat.le_of_succ_le hA))

abbrev rows (n : ℕ) (hA : n + 3 ≤ A.card) := (state sem hp n hA).rows

theorem consistent (hs : sem.IsConsistent) (n : ℕ) (hA : n + 3 ≤ A.card) :
    (rows sem hp n hA).IsConsistent := (state sem hp n hA).consistent hs

theorem seed_rows (hA : 3 ≤ A.card) :
    rows sem hp 0 hA = CanonicalRecursiveSeedRows.rows sem hA hp := rfl

/-- Literal row preservation on each actual inherited lower domain. -/
theorem inherited_row (n : ℕ) (hA : n + 4 ≤ A.card)
    (c : Cell (carrier sem n (Nat.le_of_succ_le hA)))
    (d : (carrier sem n (Nat.le_of_succ_le hA)).below
      ((carrier sem n (Nat.le_of_succ_le hA)).cell c)) :
    (rows sem hp (n + 1) hA).E (CanonicalRecursiveSuccessorRows.old sem n hA c)
      (CanonicalRecursiveSuccessorRows.ownerEquiv sem n hA hp c d) =
      (rows sem hp n (Nat.le_of_succ_le hA)).E c d :=
  CanonicalRecursiveSuccessorRows.inherited_row sem n hA hp
    (state sem hp n (Nat.le_of_succ_le hA)) c d

/-- No future rows, sections, lawfulness or completion are inputs. Proper
profiles are the selected source-construction class, not all lift inputs. -/
theorem exists_selected (n : ℕ) (hA : n + 3 ≤ A.card)
    {K : ℕ} (hK : n + 3 ≤ K) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1))
    (ht : ∀ d, p d ≠ ⊤) {G : Finset ExtOrd} {C : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hC : SelfVis (n + 3) C)
    (hb : ∀ d, p d ≤ C) (hCG : C ∈ G) :
    ∃ r : Cell (carrier sem n hA) → ExtOrd,
      RespectsSemanticsBelow (rows sem hp n hA) (A, K) (fun d => r d.1) ∧
      (∀ d, r (boundary sem n hA d) = p d) ∧
      (∀ d, r d ≤ C) ∧
      ∀ L, n + 3 ≤ L → ∀ d, OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (r d) := by
  let S := state sem hp n hA
  exact ⟨S.sectionOf hK hpr ht G C, S.section_lawful hK hpr ht hG hC,
    S.section_boundary hK hpr ht hG hC, S.section_bound hK hpr ht hC hb,
    fun _ hL => S.section_supported hK hpr ht hL hCG⟩

/-- Fixed outer parameters give agreement on the whole enlarged carrier,
including every earlier controller and every retained higher proper cell. -/
theorem selected_agreement (n : ℕ) (hA : n + 3 ≤ A.card)
    {K : ℕ} (hK : n + 3 ≤ K) {p q : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (htp : ∀ d, p d ≠ ⊤)
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {G : Finset ExtOrd} {C h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hC : SelfVis (n + 3) C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree ((state sem hp n hA).sectionOf hK hpr htp G C)
      ((state sem hp n hA).sectionOf hK hqr htq G C) h :=
  (state sem hp n hA).section_agreement hK hpr htp hqr htq hG hC hh hhC hag

/-- Grade four is an application of the same successor, not a separately
assembled table. This statement does not assert its unrestricted lifting. -/
theorem grade_four (hA : 4 ≤ A.card) :
    state sem hp 1 hA = CanonicalRecursiveSuccessorSections.successor sem 0 hA hp
      (seed sem (Nat.le_of_succ_le hA) hp) := rfl

end
end VaughtConjecture.Knight.CanonicalRecursiveSemantics
