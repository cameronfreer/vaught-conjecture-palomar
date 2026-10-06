/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalCatalogue
public import VaughtConjecture.Knight.MixedRowDecoding

/-! # A selected physical display for the ordinary final layer

Construct a terminal catalogue member and its decoder from the actual ordinary
state. Decode every physical coordinate. Old long rows are handled by finite
bottom reflection on their original fields; new rows by own-grade shortness.
In particular **decoded predecessor lawfulness is derived**, not an input.

The remaining predecessor premises are explicit: original field readback,
original-field orbit support, common-grid source agreement (in `Input`), and
the ownerwise short-or-original classification. They are the scope-construction
contract, not a bountifulness assumption. This display, with both original
vectors literal and a top marked gate, does not establish unrestricted lifting.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalDisplay
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- Decode the selected complete source on the **actual** installed carrier.
The long-row alternative only concerns values at its real arguments. -/
theorem exists_actual_display
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hgrid : ∀ z ∈ F.grid, Short N z)
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (howners : ∀ a (c : D.below (A, N)),
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (F.sem.E c.1 d)) ∨
      (∀ d : D.below (D.cell c.1), ∃ f : Field P C, F.lower a d.1 = a.val f))
    (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d)) :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (δ : ExtOrd → ExtOrd),
      Witness (gTop N) δ ∧
      RespectsSemanticsBelow F.rows (A, N) (fun d => δ (F.source a d.1)) ∧
      (∀ d : Cell P.scheme, δ (F.source a (F.old (req d))) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (F.source a (F.old (priv d))) = R.vact d) ∧
      δ (F.source a (F.added a true)) = ⊤ ∧
      δ (F.source a (F.added a false)) = ⊤ := by
  obtain ⟨a, δ, hδ, hP, hC, hg, hreflect⟩ := exists_actual_member_reflecting R
  have hlower : RespectsSemanticsBelow F.sem (A, N) (fun d => δ (F.lower a d.1)) := by
    apply map_respects_of_short_or_reflecting (F.lower_lawful a) (fun d => d.2.2) hδ
    intro c
    rcases howners a c with hs | ho
    · exact Or.inl hs
    · refine Or.inr ?_
      intro d
      obtain ⟨f, hf⟩ := ho d
      change δ (F.lower a d.1) = ⊥ ↔ F.lower a d.1 = ⊥
      rw [hf]
      exact hreflect f
  have hshort : ∀ b f, Short N (F.fields b f) := by
    intro b f
    rw [hfields]
    exact member_short R b f
  refine ⟨a, δ, hδ, F.decoded_respects hsupport hshort hgrid a hδ hlower, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [F.source_old, hreq]
    exact hP d
  · intro d
    rw [F.source_old, hpriv]
    exact hC d
  · rw [F.source_own_marked, hgate, hfields]
    exact hg
  · rw [F.source_own_leaf]
    apply top_le_iff.mp
    have hb := hδ.mono (F.gate_bound a)
    rw [hgate, hfields, hg] at hb
    exact hb

end
end VaughtConjecture.Knight.OrdinaryFinalDisplay
