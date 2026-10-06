/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthBaseSupply
public import VaughtConjecture.Knight.GrowthGradeOneSource
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # All-cap original-face lifting on the growth padded base

The rank-table endgame of `LowOnlyGradeOneLift` is reused on the growth
catalogue. Both public endpoints construct their source repair from the
arbitrary physical query; the donor endpoint uses the pre-activation fibre.
Caps are proved at every occurrence before positive-cap transport is applied.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "L" => scheme I X hA
local notation "E" => semantics I X hA hB hC
local notation "H" => rungs (X := Field I.right.scheme I.left.scheme)

def source (a : Catalogue X 1) (d : Cell L) : ExtOrd :=
  image I.boundary hA (field I) (fields I X) a (SupportLadderRows.source H) d

theorem source_eq (a : Catalogue X 1) (d : Cell L) :
    source I X hA a d = ladderRow I.boundary hA (field I) (fields I X)
      (SupportLadderRows.leaf (Nat.succ_pos _) a) d := rfl

include T in
theorem source_lawful (a : Catalogue X 1) :
    RespectsSemanticsBelow E (A, 1) (fun d => source I X hA a d.1) := by
  simp only [source_eq]
  exact ladder_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
    (anchor_lawful I X T) _

section Face
variable {s : ℕ} (O : SemScheme s)
  (incl : O.scheme.below (Finset.univ, 1) → I.boundary.below (A, 1))
  (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
  (hfield : ∀ a : Catalogue X 1, ∀ d, a.val (field I (incl d).1) = a.val (pick d.1))

local instance : Fintype (O.scheme.below (Finset.univ, 1)) := Fintype.ofFinite _

include hfield in
theorem source_face (a : Catalogue X 1) (d : O.scheme.below (Finset.univ, 1)) :
    source I X hA a (oldAt I X hA (incl d)).1 =
      SupportLadderRows.source H (fieldRank a.val (pick d.1)) := by
  simp only [source, oldAt, image, rankIndex_old, ranks, fieldRank, fields, hfield a d]

include T hfield in
private theorem face_active_lift
    (repair : ∀ (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}, Witness (gTop 1) σ →
      ∀ {p : O.scheme.below (Finset.univ, 1) → ExtOrd},
      RespectsSemanticsBelow O.rows (Finset.univ, 1) p →
      ∀ {γ : ExtOrd}, SelfVis 1 γ → ⊥ < γ →
      (∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ = min (p d) γ) →
      ∀ c, γ < p c →
      ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
        BoundedMap 1 ν ∧
        (∀ f, a.val f < grid 1 B ↔ σ (SupportLadderRows.source H (fieldRank a.val f)) < γ) ∧
        (∀ d, ν (b.val (pick d.1)) = p d) ∧
        ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B))
    {p : O.scheme.below (Finset.univ, 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (oldAt I X hA (incl d))) γ = min (p d) γ)
    (c : O.scheme.below (Finset.univ, 1)) (hactive : γ < p c) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (oldAt I X hA (incl d)) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  classical
  let Z := (zero : State I.right.scheme I.left.scheme).normalize 1
  have hz := normalize_admitted X (by decide : 1 ≤ 1) (zero_admitted X 1)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory
      (Field I.right.scheme I.left.scheme) 1 :=
    normalize_inventory 1 (fun d => by cases d <;> exact bot_ne_top)
  let seed : Catalogue X 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart I.boundary I.rows hA (field I) (fields I X) (proper I hB hC) seed hq hγ
  have hread' (d) : σ (source I X hA a d.1) = min (q d) γ := by
    rw [source_eq]; exact hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ =
      min (p d) γ := by
    rw [← source_face I X hA O incl pick hfield a d,
      hread', min_assoc, min_self]
    exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ :=
    repair a hσ hp hγ hpos hpr c hactive
  let δ := grid 1 B
  let k := next (values a.val) δ
  let f : ℕ → ExtOrd := fun i => σ (SupportLadderRows.source H i)
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfv (i) : SelfVis 1 (f i) :=
    CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have hfieldc : δ ≤ a.val (pick c.1) := by
    apply not_lt.mp
    intro hh
    have hl := (hcut (pick c.1)).mp hh
    have he := hpr c
    rw [min_eq_left hl.le, min_eq_right hactive.le] at he
    exact hl.ne he
  have hcmem : a.val (pick c.1) ∈ values a.val :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values a.val).card := by
    apply le_trans _ (rank_le_card _ (a.val (pick c.1)))
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
  have hpvis (d : O.scheme.below (Finset.univ, 1)) : SelfVis 1 (p d) := by
    have hg : O.scheme.grade d.1 = 1 :=
      le_antisymm d.2.2 (O.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  have horder (d e : O.scheme.below (Finset.univ, 1))
      (h : fieldRank b.val (pick d.1) ≤ fieldRank b.val (pick e.1)) : p d ≤ p e := by
    rw [← hνread d, ← hνread e]
    apply hν.mono
    by_contra hn
    have hh := not_le.mp hn
    have hm : b.val (pick d.1) ∈ values b.val :=
      mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩
    exact (rank_strict hm hh).not_ge h
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := ReceivingRankLift.exists_table
    (fun d : O.scheme.below (Finset.univ, 1) => fieldRank a.val (pick d.1))
    (fun d : O.scheme.below (Finset.univ, 1) => fieldRank b.val (pick d.1)) p f
    hkpos hf hf0 hfv hpvis hγ hlow hreach (fun d => hab (pick d.1)) hpr horder
  obtain ⟨τ, hτ, hτread⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : (L).below (A, 1)) :
      min (τ (source I X hA b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H
      (rankIndex I.boundary hA (field I) (fields I X) b d.1))) γ = _
    rw [hτread _ (rankIndex_bound I.boundary hA (field I) (fields I X) b d.1), ← hread' d]
    change min (g _) γ = f _
    have hc := FiniteProfileControllers.le_cut hkbound hab
    have hh := rankIndex_agreement I.boundary hA (field I) (fields I X) a b d.1
    change min (rankIndex I.boundary hA (field I) (fields I X) a d.1)
      (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) =
      min (rankIndex I.boundary hA (field I) (fields I X) b d.1)
      (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) at hh
    by_cases hia : rankIndex I.boundary hA (field I) (fields I X) a d.1 < k
    · have he : rankIndex I.boundary hA (field I) (fields I X) b d.1 =
          rankIndex I.boundary hA (field I) (fields I X) a d.1 := by omega
      rw [he, hglow _ hia, min_eq_left (hlow _ hia).le]
    · have hib : k ≤ rankIndex I.boundary hA (field I) (fields I X) b d.1 := by omega
      rw [min_eq_right (hgreach.trans (hg hib))]
      have hle : γ ≤ f (rankIndex I.boundary hA (field I) (fields I X) a d.1) :=
        hreach.trans (hf (not_lt.mp hia))
      have hbound : f (rankIndex I.boundary hA (field I) (fields I X) a d.1) ≤ γ := by
        change σ (source I X hA a d.1) ≤ γ
        rw [hread']; exact min_le_right _ _
      exact le_antisymm hle hbound
  refine ⟨fun d => τ (source I X hA b d.1),
    map_respects_of_positive_cap_agreement
      (source_lawful I X T hA hB hC b) hq
      (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps, ?_, hcaps⟩
  intro d
  exact (congrArg τ (source_face I X hA O incl pick hfield b d)).trans
    ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d))

end Face

include T in
theorem private_lift
    {p : I.right.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (privateAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt I X hA d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := private_bottom_supply I X T hA hB hC hp
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hi d)),
      fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  apply face_active_lift I X T hA hB hC I.right (privateIncl I) Sum.inl
    (fun a d => ?_) (exists_private_rank_repair X T) hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) hag c (not_le.mp hc)
  obtain ⟨S, hs, he⟩ := a.property.2
  rw [← he]
  exact field_private I X T hs d.1

include T in
theorem donor_lift (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := donor_bottom_supply I X T hA hB hC hN hp
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hi d)),
      fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  apply face_active_lift I X T hA hB hC I.left (donorIncl I) Sum.inr
    (fun a d => ?_) (exists_donor_rank_repair X T hN) hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) hag c (not_le.mp hc)
  obtain ⟨S, _, he⟩ := a.property.2
  rw [← he]
  exact field_donor I S d.1

include T in
/-- The intended strict donor-arity geometry discharges pre-activation. -/
theorem donor_lift_of_arity (hsmall : n + 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ :=
  donor_lift I X T hA hB hC ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall)
    hp hq hγ hag

end
end VaughtConjecture.Knight.GrowthOrderedBase
