/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFamily

/-! # The gate-free private-prescribed LOW fibre

Root installation and retargeting are constructed on the original legal donor.
The complete non-top maximum includes future fields. No repaired state,
alignment, or output bountifulness is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CappedDonor.Ref.LowRef

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

include F in
theorem cap_visible {j : ℕ} (hj : K ≤ j) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) : SelfVis K γ := hγ.mono (le_min hj F.gap.K_le)

theorem top_present {j : ℕ} (hj : K ≤ j) {d : Cell P.scheme} (hd : F.p d = ⊤) :
    GradedLe (P.scheme.cell d) (effC n j) :=
  ⟨Finset.subset_univ _, le_min ((F.top_grade d hd).trans hj) (gradeC_le d)⟩

/-- The active-grade private fibre, including top comparison cap. -/
theorem private_active {j : ℕ} (hj : K ≤ j) {S : State P C}
    (hS : F.Admissible j S) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
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
  have hcap : S.CapEq γ Q := S.replace_caps hucap hag (clipped_cutoff_cap _ _)
  have hbvis : SelfVis K (min S.b γ) :=
    selfVis_min (by simpa only [min_eq_right hj] using hS.cutoff) (F.cap_visible hj hγ)
  have hfloor : min (max (min S.b γ) (F.gap.eC hj v)) γ =
      min (max S.b (F.gap.eC hj (S.lowerC j))) γ :=
    floor_min (clipped_cutoff_cap _ _) (F.frontier_cap hj (F.cap_visible hj hγ) hag)
  by_cases hact : F.maximum Q < min S.b γ ∧ γ < max (min S.b γ) (F.gap.eC hj v)
  · obtain ⟨hm, hη⟩ := hact
    obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm
    have hlow := hS.low hj hmold
    have hγfloor : γ ≤ max S.b (F.gap.eC hj (S.lowerC j)) := by
      rw [min_eq_right hη.le] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    have htopγ : ∀ d : P.scheme.below (effC n j), F.p d.1 = ⊤ → γ ≤ u d := by
      intro d hd
      exact le_of_capAgree_of_le (hucap d).symm (hγfloor.trans (hlow d.1 hd))
    have hRD : RetargetData (p := F.p) (K := K) u (min S.b γ)
        (max (min S.b γ) (F.gap.eC hj v)) :=
      ⟨by simpa only [State.replace_lowerP] using hQ.lawfulP,
        hbvis, bot_lt_iff_ne_bot.mpr (fun h => not_lt_bot (h ▸ hm)),
        (fun d hd => by
          have h := (le_nonTopMax Q.u hd).trans_lt hm
          simpa only [Q, State.replace, completeAt_present] using h),
        (fun d hd => (min_le_right _ _).trans (htopγ d hd)),
        TopSupport.selfVis_max_of hbvis (F.gap.e_selfVis (F.gap.lowD_respects hj hv)),
        le_max_left _ _⟩
    obtain ⟨u', hu', hnon, htop, hface⟩ := hRD.exists_retarget_restore
      F.p_lawful F.gap.K_pos (F.gap.K_pos.trans_le F.gap.K_le) hj F.top_grade
      F.root.A_mem ((F.root.respects_iff _).mp (hv.mono (faceIndex_le F.root.B j)))
      (fun a _ => (hface0 a).symm)
      (fun a ha => max_le
        ((min_le_right _ _).trans
          ((htopγ (CellScheme.below.mono (faceIndex_le F.root.A j) a) ha).trans_eq (hface0 a)))
        (F.frontier_le_root hj hv a ha))
    have hcap' : ∀ d, min (u' d) γ = min (S.lowerP j d) γ := by
      intro d
      by_cases hd : F.p d.1 = ⊤
      · change min (u' d) γ = min (S.u d.1) γ
        rw [min_eq_right (hη.le.trans (htop d hd)),
          min_eq_right (hγfloor.trans (hlow d.1 hd))]
      · rw [hnon d hd, hucap d]
    refine ⟨S.replace u' v (min S.b γ),
      ⟨hS.toSource.replace F hu' hv _ hface, ?_, ?_⟩,
      S.replace_lowerC _ _ _, S.replace_caps hcap' hag (clipped_cutoff_cap _ _),
      S.replace_future _ _ _⟩
    · change SelfVis (min j K) (min S.b γ)
      simpa only [min_eq_right hj] using hbvis
    · intro _ _ d hd
      change max (min S.b γ) (F.gap.eC _ ((S.replace u' v _).lowerC j)) ≤
        completeAt S.u u' d
      rw [State.replace_lowerC, completeAt_present S.u u' ⟨d, F.top_present hj hd⟩]
      exact htop _ hd
  · refine ⟨Q, ⟨hQ, ?_, ?_⟩, S.replace_lowerC _ _ _, hcap, S.replace_future _ _ _⟩
    · change SelfVis (min j K) (min S.b γ)
      simpa only [min_eq_right hj] using hbvis
    · intro _ hm d hd
      have hm' : F.maximum Q < min S.b γ := hm
      obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm'
      have hη : max (min S.b γ) (F.gap.eC hj v) ≤ γ :=
        not_lt.mp (fun h => hact ⟨hm', h⟩)
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
