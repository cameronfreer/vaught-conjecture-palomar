/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.OrdinaryFinalCatalogue

/-! # Ordinary catalogue repair on every installed final-layer coordinate

V-C's scalar package (`414cb17`, ported unchanged) constructs the repaired
catalogue member and supported inverse. The actual source-prefix theorem then
gives a lawful physical image preserving every source-cut coordinate, including
all fixed marked columns and unused predecessor auxiliaries. The proper private
prescription is read literally. No physical completion or decoder is an input.

The source cut is not the original external cap. Owner alignment and outgoing
decoding are connected separately; this result alone is not arbitrary-input
lifting. The explicit predecessor support/section contract is unchanged.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalRepair
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SourcePrefixRows
open OrdinaryFinalCatalogue CanonicalPairedInverse
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- A proper private repair is installed in the fixed physical inventory with
lawfulness and the entire source-cut vector constructed. -/
theorem exists_source_repair
    (hfields : ∀ a f, F.fields a f = a.val f)
    (hgrid : F.grid = PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)))
    (hsupport : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (F.grid : Set ExtOrd) (F.fields a) (F.lower a d))
    (priv : Cell C.scheme ↪ Cell D)
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    (a : OrdinaryFinalCatalogue.Member R)
    {v : C.scheme.below (effC N N) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC N N) v) (hproper : ∀ d, v d ≠ ⊤)
    {B : ℕ} (hB : grid N B ∈ F.grid)
    (hag : ∀ d, min (v d) (grid N B) = min (a.val (.priv d.1)) (grid N B)) :
    ∃ (b : OrdinaryFinalCatalogue.Member R) (κ : ExtOrd → ExtOrd),
      Witness (gTop N) κ ∧
      RespectsSemanticsBelow F.rows (A, N) (fun d => κ (F.source b d.1)) ∧
      (∀ d : F.carrier.below (A, N),
        min (κ (F.source b d.1)) (grid N B) = min (F.source a d.1) (grid N B)) ∧
      (∀ d : C.scheme.below (effC N N), κ (F.source b (F.old (priv d.1))) = v d) := by
  obtain ⟨b₀, -, -, hprivate, hprefix, hcat, hnorm, κ, hκ, hread, hfix, hreach, -⟩ :=
    positive_cap_repair a.property hv hproper hag
  let b : OrdinaryFinalCatalogue.Member R := ⟨PairedSlotEncoding.normalize N b₀, hcat⟩
  have hfixFields : ∀ f, F.fields a f < grid N B → κ (F.fields a f) = F.fields a f := by
    intro f hf
    rw [hfields] at hf ⊢
    calc
      κ (a.val f) = κ (PairedSlotEncoding.normalize N b₀ f) :=
        congrArg κ (PairedSlotEncoding.eq_of_cap_eq_lt (hnorm f).symm hf)
      _ = b₀ f := hread f
      _ = a.val f := (PairedSlotEncoding.eq_of_cap_eq_lt (hprefix f).symm hf).symm
  have hfixGrid : ∀ z ∈ F.grid, z < grid N B → κ z = z := by
    rw [hgrid]
    exact fix_sourceGrid hκ.bot hfix _
  have hag' : Agree (F.fields b) (F.fields a) (grid N B) := by
    intro f
    simpa only [hfields] using hnorm f
  obtain ⟨hlaw, hcaps⟩ := F.decode_source_prefix hsupport a b hB (ofOrd_ne_bot _)
    hag' hκ hreach hfixGrid hfixFields
  refine ⟨b, κ, hκ, hlaw, hcaps, ?_⟩
  intro d
  rw [F.source_old, hpriv]
  exact (hread (.priv d.1)).trans (hprivate d)

end
end VaughtConjecture.Knight.OrdinaryFinalRepair
