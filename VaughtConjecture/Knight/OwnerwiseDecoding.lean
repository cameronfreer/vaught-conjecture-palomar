/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition

/-! # Decoding with exceptional owner localities

Orderliness and availability transport uniformly through a bounded witness.
At each owner, a short row admits repaired composition; an exceptional long
row instead supplies its own mapped locality. This does not assume lawfulness
of the whole decoded section, bottom reflection, or a particular catalogue.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- Decode uniformly at short owners; consume a separately proved decoded
locality only at exceptional owners. No full decoded lawfulness, global bottom
reflection, or shortness of the inherited long rows is assumed. -/
theorem map_respects_of_short_or_local
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : Witness (gTop K) ν)
    (hc : ∀ c : D.below BJ,
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (sem.E c.1 d)) ∨
      TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1)
        (sem.E c.1)
        (fun d => min (ν (r (CellScheme.below.incl c d))) (ν (r c)))) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) where
  orderly d := by
    have h := hν.clause5 (r d) (D.grade d.1)
      (by rw [gTop_of_le (hK d)]; exact le_top) (D.grade d.1) le_rfl
    rwa [← hr.orderly d] at h
  locality c := by
    rcases hc c with hs | hl
    · exact map_capped_locality
        (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
        (p := fun d => r (CellScheme.below.incl c d))
        (fun d => d.2.2) (hK c) hs (hr.orderly c).symm (hr.locality c) hν
    · exact hl
  availability d c hs hg := by
    obtain ⟨e, he, hde⟩ := hr.availability d c hs hg
    exact ⟨e, he, hν.mono hde⟩

end VaughtConjecture.Knight.SharpWitnessComposition
