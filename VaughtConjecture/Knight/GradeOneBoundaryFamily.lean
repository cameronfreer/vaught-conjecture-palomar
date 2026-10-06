/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneSelectedSections

/-! # The finite normalized family of an actual grade-one boundary

No abstract order-closure or section-supply contract is assumed. A
bottom-reflecting finite interpolation transports the actual semantics,
including the higher-threshold source-block conditions. The family is the
finite set of lawful, rank-normalized boundary profiles.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneBoundaryFamily

open Transform Value ExtOrd SlotControllerFamily
open FullRowLifting NormalizedProfileFamily

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

local notation "rankCode" => NormalizedProfileFamily.code

theorem bottom_respects : RespectsSemantics sem (fun _ => ⊥) :=
  RespectsSemantics.bot sem

/-- Normalization preserves lawfulness for arbitrary actual grade-one rows.
This does not infer full order-closure or erase an inherited bottom pattern. -/
theorem normalize_respects (hg : ∀ d : Cell D, D.grade d = 1)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics sem (fun d => value (rankCode p d)) := by
  let ν := orderInterpolate p (fun d => value (rankCode p d))
  have hread : ∀ d, ν (p d) = value (rankCode p d) :=
    orderInterpolate_read
      (fun d e h => value_mono ((code_order p d e).mpr h))
      (fun d h => by rw [(code_zero p d).mpr h]; rfl)
  have hv : ∀ d, SelfVis 1 (p d) := fun d => hg d ▸ (hp.orderly d).symm
  have hb : ∀ x, ν x = ⊥ ↔ x = ⊥ := orderInterpolate_bottom_iff
    (fun d h => (value_code_bot p d).mp h)
  have hr := map_respects_of_bounded_reflecting
    (orderInterpolate_bounded hv (fun _ => value_visible _)) hb
    (fun d : D.below (A, 1) => (hg d.1).le) (hp.toBelow (A, 1))
  have hwhole := hr.toRespects
    (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), (hg d).le⟩)
  change RespectsSemantics sem (fun d => ν (p d)) at hwhole
  simpa only [hread] using hwhole

/-- Every family member is an actual respecting normalized boundary profile. -/
def Profile := {p : Cell D → Fin (D.card + 1) //
  RespectsSemantics sem (fun d => value (p d).val) ∧
    ∀ d, rankCode (fun e => value (p e).val) d = (p d).val}

instance : Finite (Profile sem) := by unfold Profile; infer_instance
noncomputable instance : Fintype (Profile sem) := Fintype.ofFinite (Profile sem)

def levels (q : Profile sem) (d : Cell D) : ℕ := (q.val d).val

theorem levels_bound (q : Profile sem) (d : Cell D) : levels sem q d ≤ D.card :=
  Nat.le_of_lt_succ (q.val d).isLt

theorem profile_card_le : Fintype.card (Profile sem) ≤ (D.card + 1) ^ D.card := by
  have h := Fintype.card_le_of_injective (fun p : Profile sem => p.val) Subtype.val_injective
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

noncomputable def encode (hg : ∀ d : Cell D, D.grade d = 1)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) : Profile sem :=
  ⟨fun d => ⟨rankCode p d, by simpa using Nat.lt_succ_of_le (code_le p d)⟩,
    normalize_respects sem hg hp, code_idempotent p⟩

theorem levels_encode (hg : ∀ d : Cell D, D.grade d = 1)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    levels sem (encode sem hg hp) = rankCode p := rfl

theorem nonempty (hg : ∀ d : Cell D, D.grade d = 1) : Nonempty (Profile sem) :=
  ⟨encode sem hg (bottom_respects sem)⟩

/-- A whole selected section on the explicit boundary-plus-family inventory.
This already includes all new-controller localities and availability. Literal
old-owner lawfulness is supplied by the actual prescribed input, not by an
assumed completion. The geometric installation is performed separately. -/
theorem selected_joint (hg : ∀ d : Cell D, D.grade d = 1)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) {C : ExtOrd}
    (hC : SelfVis 1 C) (hbound : ∀ d, p d ≤ C) :
    FiniteProfileControllers.Joint (D.card + 1) (levels sem)
      (GradeOneSelectedSections.selected (levels sem) p C) := by
  have h := GradeOneSelectedSections.selected_joint
    (fun q d => (levels_bound sem q d).trans (by simp))
    (fun d => hg d ▸ (hp.orderly d).symm) hC hbound (encode sem hg hp) (levels_encode sem hg hp)
  simpa only [Fintype.card_fin] using h

end VaughtConjecture.Knight.GradeOneBoundaryFamily
