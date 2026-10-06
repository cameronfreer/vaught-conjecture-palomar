/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyGradeOneSource
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # Positive-cap private lifting on the padded LOW grade-one layer

The old-boundary interpretation and occurrence map are explicit inputs. No
physical source lawfulness, source cut, replacement anchor, alignment, output
lawfulness or predecessor lift is supplied. Actual installed ladder lawfulness
is derived from the original-boundary interpretation. This module makes no
claim about higher layers or bottom-cap supply.

The rank-table endgame follows `ReceivingGradeOneActiveLift`, specialized here
to the LOW birth-grade catalogue and the actual `RelativeLadderLayer` rows.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : ∀ d, D.scope d ≠ A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))
  (incl : C.scheme.below (effC n 1) → D.below (A, 1))
  (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d,
    S.profile (field (incl d).1) = S.v d.1)

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "E" => rows D sem hA field (F.fields 1) hproper
local notation "H" => rungs (X := Field P C)
local instance : Fintype (C.scheme.below (effC n 1)) := Fintype.ofFinite _

def privateAt (d : C.scheme.below (effC n 1)) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

include hfield in
theorem anchor_private (a : F.Anchor 1) (d : C.scheme.below (effC n 1)) :
    F.fields 1 a (field (incl d).1) = a.val (.inr (.inl d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change a.val (field (incl d).1) = a.val (.inr (.inl d.1))
  rw [← he]
  exact hfield S hs d

def leafSource (a : F.Anchor 1) (d : Cell L) : ExtOrd :=
  image D hA field (F.fields 1) a (SupportLadderRows.source H) d

theorem leafSource_eq (a : F.Anchor 1) (d : Cell L) :
    leafSource F D hA field a d = ladderRow D hA field (F.fields 1)
      (SupportLadderRows.leaf (Nat.succ_pos _) a) d := by
  simp only [leafSource, ladderRow]
  rfl

include hfield in
theorem leafSource_private (a : F.Anchor 1) (d : C.scheme.below (effC n 1)) :
    leafSource F D hA field a (privateAt F D hA incl d).1 =
      SupportLadderRows.source H (fieldRank a.val (.inr (.inl d.1))) := by
  simp only [leafSource, privateAt, image, rankIndex_old, ranks, fieldRank,
    anchor_private F D field incl hfield a d]
  rfl

include hboundary in
theorem leafSource_lawful (a : F.Anchor 1) :
    RespectsSemanticsBelow E (A, 1) (fun d => leafSource F D hA field a d.1) := by
  simp only [leafSource_eq]
  apply ladder_respects D sem hA field (F.fields 1) hproper _ _
  intro b
  obtain ⟨S, hs, he⟩ := b.property.2
  have hv : (fun d : D.below (A, 1) => F.fields 1 b (field d.1)) =
      (fun d => S.profile (field d.1)) := funext (fun d => (congrFun he _).symm)
  exact hv ▸ hboundary S hs

include hboundary hfield in
/-- Arbitrary-input active lifting. All replacement/source data are constructed;
the hypotheses describe only the original boundary and the actual input query. -/
theorem private_active_lift
    {p : C.scheme.below (effC n 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (privateAt F D hA incl d)) γ = min (p d) γ)
    (c : C.scheme.below (effC n 1)) (hactive : γ < p c) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  classical
  let Z := (zero : State P C).normalize 1
  have hz := F.normalize_admissible (by decide : 1 ≤ 1) (F.zero_admissible 1)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory (Field P C) 1 :=
    normalize_inventory 1 (fun d => by cases d with
      | inl d => exact bot_ne_top
      | inr d => cases d <;> exact bot_ne_top)
  let seed : F.Anchor 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart D sem hA field (F.fields 1) hproper seed hq hγ
  have hread' (d) : σ (leafSource F D hA field a d.1) = min (q d) γ := by
    rw [leafSource_eq]; exact hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank a.val (.inr (.inl d.1))))) γ =
      min (p d) γ := by
    rw [← leafSource_private F D hA field incl hfield a d,
      hread', min_assoc, min_self]
    exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ :=
    F.exists_private_rank_repair a hσ hp hγ hpos hpr c hactive
  let δ := grid 1 B
  let k := next (values a.val) δ
  let f : ℕ → ExtOrd := fun i => σ (SupportLadderRows.source H i)
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfv (i) : SelfVis 1 (f i) :=
    CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have hfieldc : δ ≤ a.val (.inr (.inl c.1)) := by
    apply not_lt.mp
    intro hh
    have hl := (hcut (.inr (.inl c.1))).mp hh
    have he := hpr c
    rw [min_eq_left hl.le, min_eq_right hactive.le] at he
    exact hl.ne he
  have hcmem : a.val (.inr (.inl c.1)) ∈ values a.val :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values a.val).card := by
    apply le_trans _ (rank_le_card _ (a.val (.inr (.inl c.1))))
    apply not_lt.mp
    intro h
    exact ((rank_lt_next hcmem).mp h).not_ge hfieldc
  have hkpos : 0 < k := Nat.succ_pos _
  have hkbound : k ≤ H := hkc.trans ((values_card_le a.val).trans (Nat.le_succ _))
  have hab : FiniteProfileControllers.Agree (fieldRank a.val) (fieldRank b.val) k :=
    fieldRank_agreement (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) hpref
  have hlow (i) (hi : i < k) : f i < γ := by
    by_cases hz : i = 0
    · rw [hz, hf0]; exact hpos
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank a.val
      (Nat.pos_of_ne_zero hz) (hi.le.trans hkc)
    have hdb : a.val d ≠ ⊥ := by
      intro he
      have hr : fieldRank a.val d = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values _)]
      exact hz (hd.symm.trans hr)
    have hr : fieldRank a.val d < next (values a.val) δ := hd ▸ hi
    have hl := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mp hr
    simpa only [hd] using (hcut d).mp hl
  have hreach : γ ≤ f k := by
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank a.val hkpos hkc
    apply not_lt.mp
    intro hl
    have hlt : a.val d < δ := (hcut d).mpr (by simpa only [hd] using hl)
    have hdb : a.val d ≠ ⊥ := by
      intro he
      have hr : fieldRank a.val d = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values _)]
      have := hd.symm.trans hr
      omega
    have hr := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mpr hlt
    change fieldRank a.val d < k at hr
    rw [show fieldRank a.val d = k from hd] at hr
    exact (lt_irrefl k) hr
  have hpvis (d : C.scheme.below (effC n 1)) : SelfVis 1 (p d) := by
    have hg : C.scheme.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans (min_le_left _ _)) (C.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  have horder (d e : C.scheme.below (effC n 1))
      (h : fieldRank b.val (.inr (.inl d.1)) ≤ fieldRank b.val (.inr (.inl e.1))) : p d ≤ p e := by
    rw [← hνread d, ← hνread e]
    apply hν.mono
    by_contra hn
    have hh := not_le.mp hn
    have hm : b.val (.inr (.inl d.1)) ∈ values b.val :=
      mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩
    exact (rank_strict hm hh).not_ge h
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := ReceivingRankLift.exists_table
    (fun d : C.scheme.below (effC n 1) => fieldRank a.val (.inr (.inl d.1)))
    (fun d : C.scheme.below (effC n 1) => fieldRank b.val (.inr (.inl d.1))) p f
    hkpos hf hf0 hfv hpvis hγ hlow hreach (fun d => hab (.inr (.inl d.1))) hpr horder
  obtain ⟨τ, hτ, hτread⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : (L).below (A, 1)) :
      min (τ (leafSource F D hA field b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H (rankIndex D hA field (F.fields 1) b d.1))) γ = _
    rw [hτread _ (rankIndex_bound D hA field (F.fields 1) b d.1), ← hread' d]
    change min (g _) γ = f _
    have hc := FiniteProfileControllers.le_cut hkbound hab
    have hh := rankIndex_agreement D hA field (F.fields 1) a b d.1
    change min (rankIndex D hA field (F.fields 1) a d.1)
      (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) =
      min (rankIndex D hA field (F.fields 1) b d.1)
      (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) at hh
    by_cases hia : rankIndex D hA field (F.fields 1) a d.1 < k
    · have he : rankIndex D hA field (F.fields 1) b d.1 =
          rankIndex D hA field (F.fields 1) a d.1 := by omega
      rw [he, hglow _ hia, min_eq_left (hlow _ hia).le]
    · have hib : k ≤ rankIndex D hA field (F.fields 1) b d.1 := by omega
      rw [min_eq_right (hgreach.trans (hg hib))]
      have hle : γ ≤ f (rankIndex D hA field (F.fields 1) a d.1) :=
        hreach.trans (hf (not_lt.mp hia))
      have hbound : f (rankIndex D hA field (F.fields 1) a d.1) ≤ γ := by
        change σ (leafSource F D hA field a d.1) ≤ γ
        rw [hread']; exact min_le_right _ _
      exact le_antisymm hle hbound
  refine ⟨fun d => τ (leafSource F D hA field b d.1),
    map_respects_of_positive_cap_agreement
      (leafSource_lawful F D sem hA field hproper hboundary b) hq
      (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps, ?_, hcaps⟩
  intro d
  exact (congrArg τ (leafSource_private F D hA field incl hfield b d)).trans
    ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d))

include hboundary hfield in
/-- Every positive visible cap, including top; the inactive case is just the
lawful capped ambient, with the literal prescription pinned by its cap. -/
theorem private_positive_lift
    {p : C.scheme.below (effC n 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (privateAt F D hA incl d)) γ = min (p d) γ) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  classical
  by_cases hsmall : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hsmall d)),
      fun _ => by rw [min_assoc, min_self]⟩
  · obtain ⟨c, hc⟩ := not_forall.mp hsmall
    exact private_active_lift F D sem hA field hproper hboundary incl hfield
      hp hq hγ hpos hag c (not_le.mp hc)

end
end VaughtConjecture.Knight.LowOnly.Family
