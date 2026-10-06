/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPrivateFibre

/-! # The gate-free donor-prescribed LOW fibre

After original-root installation, an excessive private frontier is released at
the comparison cap. The shielding inequality is derived from the complete
donor maximum, not assumed as a repair input.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CappedDonor.Ref.LowRef

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Release specialized to the actual common-root occurrences. -/
theorem release_root {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) (hbot : γ ≠ ⊥) (he : γ < F.gap.eC hj v)
    (hshield : ∀ a : P.scheme.below (faceIndex F.root.A j), F.p a.1 ≠ ⊤ →
      v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) < γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      (∀ a : P.scheme.below (faceIndex F.root.A j),
        v' (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) =
          v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) ∧
      F.gap.eC hj v' = γ := by
  let T (d : Cell C.scheme) : Prop :=
    ∃ a : P.scheme.below (F.root.A, F.root.A.card), (F.root.face a).1 = d ∧ F.p a.1 = ⊤
  have ht : ∀ a : C.scheme.below (faceIndex F.root.B j), T a.1 → C.scheme.grade a.1 ≤ K := by
    rintro a ⟨b, hb, ht⟩
    rw [← hb, ← F.root.grade]
    exact F.top_grade b.1 ht
  have hgap : ∀ (a : C.scheme.below (faceIndex F.root.B K))
      (ha : GradedLe (C.scheme.cell a.1) (C.scheme.cell F.gap.c)),
      T a.1 → F.gap.h < C.rows.E F.gap.c ⟨a.1, ha⟩ := by
    rintro a ha ⟨b, hb, ht⟩
    have heq : (⟨a.1, ha⟩ : F.gap.Dom) = ⟨(F.root.face b).1,
        ⟨(F.root.face b).2.1.trans F.root_sub,
          (F.root.grade b).symm.trans_le
            ((F.top_grade b.1 ht).trans_eq F.gap.c_grade.symm)⟩⟩ := Subtype.ext hb.symm
    rw [heq]
    exact F.root_gap b ht
  have hs : ∀ a : C.scheme.below (faceIndex F.root.B j), ¬ T a.1 →
      v (CellScheme.below.mono (faceIndex_le F.root.B j) a) < γ := by
    intro a ha
    have hn : F.p ((F.root.faceAt j).symm a).1 ≠ ⊤ := by
      intro ht
      apply ha
      refine ⟨F.root.fullP ((F.root.faceAt j).symm a), ?_, ht⟩
      exact congrArg Subtype.val ((F.root.faceAt j).apply_symm_apply a)
    simpa only [Equiv.apply_symm_apply] using hshield ((F.root.faceAt j).symm a) hn
  obtain ⟨v', hv', hface, hcap, -, -, he'⟩ := F.gap.exists_release hj hv hγ hbot he
    F.root.B_mem F.root_sub T ht hgap hs
  exact ⟨v', hv', hcap, fun a => hface (F.root.faceAt j a), he'⟩

/-- The active-grade donor fibre constructs the released private vector. -/
theorem donor_active {j : ℕ} (hj : K ≤ j) {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  have hface0 : ∀ a : P.scheme.below (faceIndex F.root.A j),
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) := by
    intro a
    have h := F.root.shared_at hQ.shared a
    change (S.replace u v _).lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
      (S.replace u v _).lowerC j
        (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) at h
    simpa only [State.replace_lowerP, State.replace_lowerC] using h
  let Q := S.replace u v (min S.b γ)
  have hcap : S.CapEq γ Q := S.replace_caps hag hvcap (clipped_cutoff_cap _ _)
  have hbvis : SelfVis K (min S.b γ) :=
    selfVis_min (by simpa only [min_eq_right hj] using hS.cutoff) (F.cap_visible hj hγ)
  have hfloor : min (max (min S.b γ) (F.gap.eC hj v)) γ =
      min (max S.b (F.gap.eC hj (S.lowerC j))) γ :=
    floor_min (clipped_cutoff_cap _ _) (F.frontier_cap hj (F.cap_visible hj hγ) hvcap)
  by_cases hact : F.maximum Q < min S.b γ ∧ γ < F.gap.eC hj v
  · obtain ⟨hm, he⟩ := hact
    obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm
    have hγfloor : γ ≤ max S.b (F.gap.eC hj (S.lowerC j)) := by
      rw [min_eq_right (he.le.trans (le_max_right _ _))] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    have hbot : γ ≠ ⊥ := ne_bot_of_gt ((bot_le.trans_lt hm).trans_le (min_le_right _ _))
    obtain ⟨v', hv', hv'cap, hface', he'⟩ := F.release_root hj
      (by simpa only [State.replace_lowerC] using hQ.lawfulC) hγ hbot he (fun a ha => by
        rw [← hface0]
        have h := ((le_nonTopMax Q.u ha).trans_lt hm).trans_le (min_le_right _ _)
        change Q.lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) < γ at h
        simpa only [Q, State.replace_lowerP] using h)
    have hcap' : ∀ d, min (v' d) γ = min (S.lowerC j d) γ :=
      fun d => (hv'cap d).trans (hvcap d)
    refine ⟨S.replace u v' (min S.b γ),
      ⟨hS.toSource.replace F hu hv' _ (fun a => (hface0 a).trans (hface' a).symm), ?_, ?_⟩,
      S.replace_lowerP _ _ _, S.replace_caps hag hcap' (clipped_cutoff_cap _ _),
      S.replace_future _ _ _⟩
    · change SelfVis (min j K) (min S.b γ)
      simpa only [min_eq_right hj] using hbvis
    · intro _ _ d hd
      change max (min S.b γ) (F.gap.eC _ ((S.replace u v' _).lowerC j)) ≤
        completeAt S.u u d
      rw [State.replace_lowerC, he', max_eq_right (min_le_right _ _),
        completeAt_present S.u u ⟨d, F.top_present hj hd⟩]
      exact le_of_capAgree_of_le (hag _).symm (hγfloor.trans (hS.low hj hmold d hd))
  · refine ⟨Q, ⟨hQ, ?_, ?_⟩, S.replace_lowerP _ _ _, hcap, S.replace_future _ _ _⟩
    · change SelfVis (min j K) (min S.b γ)
      simpa only [min_eq_right hj] using hbvis
    · intro _ hm d hd
      have hm' : F.maximum Q < min S.b γ := hm
      obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm'
      have hη : max (min S.b γ) (F.gap.eC hj v) ≤ γ :=
        max_le (min_le_right _ _) (not_lt.mp (fun h => hact ⟨hm', h⟩))
      change max (min S.b γ) (F.gap.eC _ (Q.lowerC j)) ≤ Q.u d
      rw [show Q.lowerC j = v from S.replace_lowerC _ _ _]
      calc
        max (min S.b γ) (F.gap.eC hj v)
            = min (max (min S.b γ) (F.gap.eC hj v)) γ := (min_eq_left hη).symm
        _ = min (max S.b (F.gap.eC hj (S.lowerC j))) γ := hfloor
        _ ≤ min (S.u d) γ := min_le_min_right _ (hS.low hj hmold d hd)
        _ = min (Q.u d) γ := (hcap.1 d).symm
        _ ≤ Q.u d := min_le_left _ _

end
end VaughtConjecture.Knight.LowOnly.Family
