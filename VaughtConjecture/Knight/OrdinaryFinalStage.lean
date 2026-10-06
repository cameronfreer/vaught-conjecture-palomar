/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalDisplay
public import VaughtConjecture.Knight.CappedDonorDecoderStage

/-! # Stage-correct physical displays for ordinary receiving

V-C's supported terminal decoder (`7a1deef`, ported unchanged) controls every
output, including unused grid values. Here its original vector is identified
with the actual donor/private labels and the top gate. Consequently the stage
bound on the actual inputs bounds every physical auxiliary after decoding.
No bound on an unspecified private-fibre output is inferred.

The predecessor's support and short-new/original-long classification remain
the same as in `OrdinaryFinalDisplay`. No legality or model occurrence is
asserted for an unfinished scope predecessor.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalStage
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SharpWitnessComposition
open OrdinaryFinalCatalogue
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

/-- The actual complete field vector, not a repair chosen by a fibre. -/
def actualFields : Field P C → ExtOrd
  | .req d => R.p d
  | .priv d => R.vact d
  | .gate => ⊤

theorem actual_profile : (resync (R.actualState N)).sourceProfile = actualFields R := by
  funext f
  rw [profile_present R]
  cases f <;> rfl

/-- The actual vector has a reflecting decoder whose every output is
supported by the original labels, with only bottom and top added. -/
theorem exists_actual_member_supported :
    ∃ (a : OrdinaryFinalCatalogue.Member R) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      (∀ f, δ (a.val f) = actualFields R f) ∧
      (∀ f, δ (a.val f) = ⊥ ↔ a.val f = ⊥) ∧
      ∀ x, OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) (actualFields R) (δ x) := by
  let st := resync (R.actualState N)
  have hadm : R.Admitted st.sourceProfile :=
    ⟨st, (R.actual_admissible N).resync, resync_synchronized (R.actual_admissible N),
      TopSupport.selfVis_top_ext N, rfl⟩
  obtain ⟨b, -, -, hprefix, -, hb, hcan, δ, hδ, hr, hsupp⟩ := hadm.exists_terminal' 0
  refine ⟨⟨PairedSlotEncoding.normalize N b, hcan, hb⟩, δ, hδ, ?_, ?_, ?_⟩
  · intro f
    exact (hr f).trans (congrFun (actual_profile R) f)
  · intro f
    rw [hr, PairedSlotEncoding.normalize_bot_iff]
    exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hprefix f).symm
  · intro x
    simpa only [st, actual_profile] using hsupp x

theorem actualFields_bound {α : Ordinal.{0}}
    (hP : ∀ d, R.p d ≠ ⊤ → R.p d < ofOrd α)
    (hC : ∀ d, R.vact d ≠ ⊤ → R.vact d < ofOrd α) :
    ∀ f, actualFields R f ≠ ⊤ → actualFields R f < ofOrd α := by
  intro f hf
  cases f with
  | req d => exact hP d hf
  | priv d => exact hC d hf
  | gate => exact (hf rfl).elim

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- A stage-bounded lawful display on the actual final active domain.
Every physical label is controlled, not merely the represented fields. -/
theorem exists_actual_display_at_stage (α : LimitStage)
    (hP : ∀ d, R.p d ≠ ⊤ → R.p d < ofOrd α.1)
    (hC : ∀ d, R.vact d ≠ ⊤ → R.vact d < ofOrd α.1)
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
    ∃ (a : OrdinaryFinalCatalogue.Member R) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      RespectsSemanticsBelow F.rows (A, N) (fun d => δ (F.source a d.1)) ∧
      (∀ d : Cell P.scheme, δ (F.source a (F.old (req d))) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (F.source a (F.old (priv d))) = R.vact d) ∧
      δ (F.source a (F.added a true)) = ⊤ ∧
      δ (F.source a (F.added a false)) = ⊤ ∧
      ∀ d : Cell F.carrier, δ (F.source a d) < ofOrd α.1 ∨ δ (F.source a d) = ⊤ := by
  obtain ⟨a, δ, hδ, hread, hreflect, hsupp⟩ := exists_actual_member_supported R
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
  have hg : δ (F.fields a F.gate) = ⊤ := by rw [hgate, hfields]; exact hread .gate
  refine ⟨a, δ, hδ, F.decoded_respects hsupport hshort hgrid a hδ hlower,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rw [F.source_old, hreq]
    exact hread (.req d)
  · intro d
    rw [F.source_old, hpriv]
    exact hread (.priv d)
  · rw [F.source_own_marked]
    exact hg
  · rw [F.source_own_leaf]
    exact top_le_iff.mp (hg ▸ hδ.mono (F.gate_bound a))
  · intro d
    by_cases ht : δ (F.source a d) = ⊤
    · exact Or.inr ht
    · exact Or.inl (supported_top_lt_limit
        (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))
        (actualFields_bound R hP hC) (hsupp _) ht)

end
end VaughtConjecture.Knight.OrdinaryFinalStage
