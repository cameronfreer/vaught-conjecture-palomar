/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalCatalogue
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Actual private-owner factorization for the ordinary catalogue

Restrict a canonical admitted source to the original private scheme. At any
active grade-N private owner, its full scope is derived from the private arity.
KVC's owner-local factorization then constructs the reaching cut, a lawful
proper replacement, and an outgoing witness reading the prescription capped
at that owner. All N-short source readings retain their original external cap,
including unused grid/orbit values. No alignment or completion is assumed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryOwnerFactorization
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue CanonicalPairedInverse
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

abbrev privateCell (c : Cell C.scheme) : C.scheme.below (effC N N) :=
  CappedDonor.Ref.privCell c (gradeC_le c)

theorem owner_index (c : Cell C.scheme) (hc : C.scheme.grade c = N) :
    C.scheme.cell c = effC N N := by
  have hs : C.scheme.scope c = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hh := C.scheme.grade_le_card_scope c
    rw [hc] at hh
    exact le_antisymm (Finset.card_le_univ _) (by simpa using hh)
  exact Prod.ext hs (hc.trans (min_self N).symm)

/-- The source-grid cut and private factorization are constructed from actual
lawful inputs. The prescribed owner may be proper or literal top. -/
theorem exists_factorization (c : Cell C.scheme) (hc : C.scheme.grade c = N)
    (a : OrdinaryFinalCatalogue.Member R)
    {p : C.scheme.below (effC N N) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC N N) p)
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd} (hσ : Witness (gTop N) σ)
    (hγ : SelfVis N γ) (hpos : ⊥ < γ) (hpc : γ < p (privateCell c))
    (hag : ∀ d, min (σ (a.val (.priv d.1))) γ = min (p d) γ) :
    ∃ B : ℕ, grid N B ∈ PairedSlotComparison.sourceGrid N (Fintype.card (Field P C)) ∧
      ∃ (f : C.scheme.below (effC N N) → ExtOrd) (ν : ExtOrd → ExtOrd),
        RespectsSemanticsBelow C.rows (effC N N) f ∧ (∀ d, f d ≠ ⊤) ∧
        (∀ d, min (f d) (grid N B) = min (a.val (.priv d.1)) (grid N B)) ∧
        Witness (gTop N) ν ∧ (∀ x, ν x ≤ p (privateCell c)) ∧
        (∀ d, ν (f d) = min (p d) (p (privateCell c))) ∧
        γ ≤ ν (grid N B) ∧
        ∀ x, Short N x → min (ν x) γ = min (σ x) γ := by
  classical
  have hi := owner_index c hc
  let toEff := CellScheme.below.mono (D := C.scheme)
    (show GradedLe (C.scheme.cell c) (effC N N) from hi ▸ GradedLe.refl _)
  let fromEff := CellScheme.below.mono (D := C.scheme)
    (show GradedLe (effC N N) (C.scheme.cell c) from hi ▸ GradedLe.refl _)
  obtain ⟨st, hst, -, -, hprofile⟩ := a.property.2
  let s := st.v ∘ toEff
  let p' := p ∘ toEff
  have hs : RespectsSemanticsBelow C.rows (C.scheme.cell c) s := hst.v_respects.mono _
  have hp' : RespectsSemanticsBelow C.rows (C.scheme.cell c) p' := hp.mono _
  have hsource (e : C.scheme.below (C.scheme.cell c)) : s e = a.val (.priv e.1) :=
    (profile_present R st (.priv e.1)).symm.trans (congrFun hprofile (.priv e.1))
  obtain ⟨δ, hδ, hδpos, -, -, ⟨fac⟩⟩ :=
    PrivateRowFactorization.exists_factorization c (Fintype.card (Field P C)) hs hp'
      (fun e => by
        rw [hsource, hc]
        exact CanonicalPairedProfiles.inventory_coded _ _ a.property.1 _)
      (fun e => by rw [hsource, hc]; exact member_short R a _)
      (by simpa only [hc] using hσ) (by simpa only [hc] using hγ) hpos hpc
      (fun e => by rw [hsource]; exact hag (toEff e))
  rw [hc] at hδ
  rcases Finset.mem_insert.mp hδ with hz | hm
  · exact (not_lt_of_ge (le_of_eq hz) hδpos).elim
  obtain ⟨B, hB, he⟩ := Finset.mem_image.mp hm
  change grid N B = δ at he
  subst δ
  refine ⟨B, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨B, hB, rfl⟩),
    fac.source ∘ fromEff, fac.outgoing, fac.lawful.mono _,
    (fun d => fac.proper (fromEff d)), ?_, ?_, fac.bounded, ?_, fac.reaches, ?_⟩
  · intro d
    exact (fac.prefix_eq (fromEff d)).trans (congrArg (fun x => min x (grid N B)) (hsource _))
  · simpa only [hc] using fac.witness
  · intro d
    exact fac.readback (fromEff d)
  · simpa only [hc] using fac.caps

end
end VaughtConjecture.Knight.OrdinaryOwnerFactorization
