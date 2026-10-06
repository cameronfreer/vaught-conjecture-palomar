/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPreactivation
public import VaughtConjecture.Knight.GrowthSupportedRepair

/-! # Required original-face growth scalar repairs at every cutoff

Private prescriptions repair at every cutoff. Donor prescriptions at a valid
donor grade repair before activation; strict donor arity below activation
excludes the remaining active same-grade owner case. This is not an assertion
that every arbitrary donor replacement above activation preserves the relation.
No physical lifting or renderer lawfulness is asserted.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan CanonicalPairedInverse
noncomputable section

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

namespace RootAttachment
include R

/-- All-cutoff private scalar repair. Future fields on both sides stay literal;
after activation the donor future receipt is vacuous by the actual grade bound. -/
theorem private_all {j : ℕ} {S : State C.scheme P.scheme} (hS : Admitted X j S)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (u d) γ = min (S.privateValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  by_cases hj : j < X.req.N
  · exact R.private_before hj hS hu hγ hag
  · obtain ⟨T, hT, hread, hcap, hfuture⟩ := private_repair X (not_lt.mp hj) hS hu hγ hag
    exact ⟨T, hT, hread, hcap, hfuture,
      fun d hd => (not_lt.mpr ((X.grade_le d).trans (not_lt.mp hj)) hd).elim⟩

/-- A fixed canonical private source is repaired at every positive encoding
grade, with protected unused endpoints and supported orbits supplied by the
constructed `ProtectedRepair`. -/
theorem private_protected_all {j B : ℕ} (hj : 1 ≤ j) {S : State C.scheme P.scheme}
    (hS : Admitted X j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) j)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.privateValues d.1) (grid j B)) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq (grid j B) T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      (∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d) ∧
      Nonempty (ProtectedRepair X S.profile T j B) := by
  obtain ⟨T, hT, hread, hcap, hfa, hfq⟩ := R.private_all hS hu (grid_visible j B) hag
  exact ⟨T, hT, hread, hcap, hfa, hfq,
    exists_protected_repair X hj hcanon hT (fun f => (hcap f).symm)⟩

theorem donor_protected_before {j B : ℕ} (hj : 1 ≤ j) (hN : j < X.req.N)
    {S : State C.scheme P.scheme} (hS : Admitted X j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) j)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.donorValues d.1) (grid j B)) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      S.CapEq (grid j B) T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      (∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d) ∧
      Nonempty (ProtectedRepair X S.profile T j B) := by
  obtain ⟨T, hT, hread, hcap, hfa, hfq⟩ := R.donor_before hN hS hv (grid_visible j B) hag
  exact ⟨T, hT, hread, hcap, hfa, hfq,
    exists_protected_repair X hj hcanon hT (fun f => (hcap f).symm)⟩

/-- Independent scalar bottom supply, before any catalogue insertion or decoding. -/
theorem private_bottom_state {j : ℕ}
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      ∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d := by
  obtain ⟨T, hT, hread, _, _, _⟩ := R.private_all (zero_admitted X j) hu
    (selfVis_bot j) (fun _ => by simp)
  exact ⟨T, hT, hread⟩

/-- Donor scalar bottom supply at a preactivation cutoff. -/
theorem donor_bottom_state {j : ℕ} (hN : j < X.req.N)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      ∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d := by
  obtain ⟨T, hT, hread, _, _, _⟩ := R.donor_before hN (zero_admitted X j) hv
    (selfVis_bot j) (fun _ => by simp)
  exact ⟨T, hT, hread⟩

/-- Independent bottom supply followed by exact supported terminal insertion.
It does not assert physical lawfulness of the decoded section. -/
theorem private_bottom_all {j : ℕ} (hj : 1 ≤ j)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      ∃ a : Catalogue X j, ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ f, δ (a.1 f) = T.profile f) ∧
        (∀ f, δ (a.1 f) = ⊥ → a.1 f = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) T.profile (δ x) := by
  obtain ⟨T, hT, hread⟩ := R.private_bottom_state hu
  obtain ⟨U, hU, hcanon, δ, hw, hdecode, hbot, hsupp⟩ := exists_supported_decoder X hj hT
  exact ⟨T, hT, hread, ⟨U.profile, hcanon, U, hU, rfl⟩, δ, hw, hdecode, hbot, hsupp⟩

theorem donor_bottom_before {j : ℕ} (hj : 1 ≤ j) (hN : j < X.req.N)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      ∃ a : Catalogue X j, ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ f, δ (a.1 f) = T.profile f) ∧
        (∀ f, δ (a.1 f) = ⊥ → a.1 f = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) T.profile (δ x) := by
  obtain ⟨T, hT, hread⟩ := R.donor_bottom_state hN hv
  obtain ⟨U, hU, hcanon, δ, hw, hdecode, hbot, hsupp⟩ := exists_supported_decoder X hj hT
  exact ⟨T, hT, hread, ⟨U.profile, hcanon, U, hU, rfl⟩, δ, hw, hdecode, hbot, hsupp⟩

end RootAttachment

/-- Strict donor arity is an independent geometric input, not a consequence
of the weak `RelativeData.grade_le` bound. -/
theorem donor_grade_lt {m N : ℕ} (D : SemScheme m) (hm : m < N) (d : Cell D.scheme) :
    D.scheme.grade d < N :=
  ((D.scheme.grade_le_card_scope d).trans
    (by simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_univ (D.scheme.scope d))).trans_lt hm

theorem donor_active_absent (hsmall : n + 1 < X.req.N) {j : ℕ} (hj : X.req.N ≤ j)
    (d : Cell P.scheme) : P.scheme.grade d ≠ j :=
  ((donor_grade_lt P hsmall d).trans_le hj).ne

theorem donor_index_before {m N j : ℕ} (D : SemScheme m) (hm : m < N)
    {B : Finset (Fin m)} (hB : (B, j) ∈ Plan.gradedPlan D.scheme.plan) : j < N :=
  ((Plan.mem_gradedPlan.mp hB).2.2.trans
    (by simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ B)).trans_lt hm

include R in
/-- Exhausts the actual graded donor indices, without demanding an active
donor fibre at a nonexistent donor owner. -/
theorem donor_at_index (hsmall : n + 1 < X.req.N) {j : ℕ}
    (hindex : (Finset.univ, j) ∈ Plan.gradedPlan P.scheme.plan)
    {S : State C.scheme P.scheme} (hS : Admitted X j S)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (v d) γ = min (S.donorValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d :=
  R.donor_before (donor_index_before P hsmall hindex) hS hv hγ hag

end
end VaughtConjecture.Knight.Growth
