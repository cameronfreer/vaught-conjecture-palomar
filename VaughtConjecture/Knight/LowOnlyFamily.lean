/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyCommonRoot

/-! # The gate-free LOW family on two original legal cofaces

Complete vectors retain all future occurrences. The only extra scalar field is
the cutoff. No receiving `Ref`, gate, shadow synchronization, or output scheme is
used. The common root is transported by its literal occurrence and row identities.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

/-- The actual original-row and donor-display data of the LOW-only family. -/
structure Family (P C : SemScheme n) (K : ℕ) where
  root : CommonRoot P C
  gap : SourceGap C K
  p : Cell P.scheme → ExtOrd
  p_lawful : RespectsSemantics P.rows p
  top_grade : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K
  root_sub : root.B ⊆ C.scheme.scope gap.c
  root_gap : ∀ (a : P.scheme.below (root.A, root.A.card)) (ht : p a.1 = ⊤),
    gap.h < C.rows.E gap.c ⟨(root.face a).1,
      ⟨(root.face a).2.1.trans root_sub,
        (root.grade a).symm.trans_le ((top_grade a.1 ht).trans_eq gap.c_grade.symm)⟩⟩

/-- Complete original vectors and the free cutoff; there is no gate field. -/
structure State (P C : SemScheme n) where
  u : Cell P.scheme → ExtOrd
  v : Cell C.scheme → ExtOrd
  b : ExtOrd

namespace State

def lowerP (S : State P C) (j : ℕ) (d : P.scheme.below (effC n j)) : ExtOrd := S.u d.1
def lowerC (S : State P C) (j : ℕ) (d : C.scheme.below (effC n j)) : ExtOrd := S.v d.1

def replace (S : State P C) {j : ℕ} (u : P.scheme.below (effC n j) → ExtOrd)
    (v : C.scheme.below (effC n j) → ExtOrd) (b : ExtOrd) : State P C :=
  ⟨completeAt S.u u, completeAt S.v v, b⟩

theorem replace_lowerP (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : (S.replace u v b).lowerP j = u := funext (completeAt_present S.u u)

theorem replace_lowerC (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : (S.replace u v b).lowerC j = v := funext (completeAt_present S.v v)

def CapEq (γ : ExtOrd) (S S' : State P C) : Prop :=
  (∀ d, min (S'.u d) γ = min (S.u d) γ) ∧
  (∀ d, min (S'.v d) γ = min (S.v d) γ) ∧ min S'.b γ = min S.b γ

def FutureEq (j : ℕ) (S S' : State P C) : Prop :=
  (∀ d, j < P.scheme.grade d → S'.u d = S.u d) ∧
  (∀ d, j < C.scheme.grade d → S'.v d = S.v d)

theorem replace_future (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : S.FutureEq j (S.replace u v b) :=
  ⟨completeAt_future S.u u, completeAt_future S.v v⟩

theorem replace_caps (S : State P C) {j : ℕ}
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    {b γ : ExtOrd} (hu : ∀ d, min (u d) γ = min (S.lowerP j d) γ)
    (hv : ∀ d, min (v d) γ = min (S.lowerC j d) γ) (hb : min b γ = min S.b γ) :
    S.CapEq γ (S.replace u v b) :=
  ⟨completeAt_cap S.u hu, completeAt_cap S.v hv, hb⟩

end State

namespace Family

variable (F : Family P C K)

def maximum (S : State P C) : ExtOrd := nonTopMax (fun d => F.p d = ⊤) S.u

/-- Lawfulness through the current grade, with future fields retained at grade one. -/
structure Source (j : ℕ) (S : State P C) : Prop where
  lawfulP : RespectsSemanticsBelow P.rows (effC n j) (S.lowerP j)
  lawfulC : RespectsSemanticsBelow C.rows (effC n j) (S.lowerC j)
  shared : F.root.Shared S.u S.v
  futureP : ∀ d, j < P.scheme.grade d → SelfVis 1 (S.u d)
  futureC : ∀ d, j < C.scheme.grade d → SelfVis 1 (S.v d)

structure Admissible (j : ℕ) (S : State P C) : Prop extends F.Source j S where
  cutoff : SelfVis (min j K) S.b
  low : ∀ hj : K ≤ j, F.maximum S < S.b → ∀ d, F.p d = ⊤ →
    max S.b (F.gap.eC hj (S.lowerC j)) ≤ S.u d

theorem Source.replace {j : ℕ} {S : State P C} (hS : F.Source j S)
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) (b : ExtOrd)
    (hface : ∀ a : P.scheme.below (faceIndex F.root.A j),
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) :
    F.Source j (S.replace u v b) where
  lawfulP := completeAt_respects S.u hu
  lawfulC := completeAt_respects S.v hv
  shared := F.root.shared_complete hS.shared u v hface
  futureP d hd := by
    rw [show (S.replace u v b).u d = S.u d from completeAt_future _ _ _ hd]
    exact hS.futureP d hd
  futureC d hd := by
    rw [show (S.replace u v b).v d = S.v d from completeAt_future _ _ _ hd]
    exact hS.futureC d hd

/-- First install only the prescribed root in the opposite original scheme. -/
theorem Source.install_private {j : ℕ} {S : State P C} (hS : F.Source j S)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ u, F.Source j (S.replace u v (min S.b γ)) ∧
      (∀ d, min (u d) γ = min (S.lowerP j d) γ) := by
  obtain ⟨u, hu, hcap, hface⟩ := F.root.installP hS.lawfulP hv hγ (fun a => by
    rw [hag]
    exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a))
  exact ⟨u, hS.replace F hu hv _ hface, hcap⟩

theorem Source.install_donor {j : ℕ} {S : State P C} (hS : F.Source j S)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ v, F.Source j (S.replace u v (min S.b γ)) ∧
      (∀ d, min (v d) γ = min (S.lowerC j d) γ) := by
  obtain ⟨v, hv, hcap, hface⟩ := F.root.installC hS.lawfulC hu hγ (fun a => by
    rw [hag]
    exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a).symm)
  exact ⟨v, hS.replace F hu hv _ (fun a => (hface a).symm), hcap⟩

theorem frontier_cap {j : ℕ} (hj : K ≤ j) {v v' : C.scheme.below (effC n j) → ExtOrd}
    {γ : ExtOrd} (hγ : SelfVis K γ) (hag : ∀ d, min (v' d) γ = min (v d) γ) :
    min (F.gap.eC hj v') γ = min (F.gap.eC hj v) γ := by
  unfold SourceGap.eC
  rw [← F.gap.e_min hγ, ← F.gap.e_min hγ]
  congr 1
  exact funext (fun d => hag (CellScheme.below.mono (F.gap.domLe hj) d))

theorem frontier_le_root {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    (a : P.scheme.below (faceIndex F.root.A j)) (ht : F.p a.1 = ⊤) :
    F.gap.eC hj v ≤ v (CellScheme.below.mono (faceIndex_le F.root.B j)
      (F.root.faceAt j a)) :=
  F.gap.e_le_of_gap (F.gap.lowD_respects hj hv) _ (F.root_gap (F.root.fullP a) ht)

end Family
end
end VaughtConjecture.Knight.LowOnly
