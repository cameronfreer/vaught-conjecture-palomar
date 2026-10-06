/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRecursiveCharts

/-! # Constructed catalogue coverage for recursive LOW rendering

Downward admission keeps the complete source vector, including crossing and
future fields. Normalizing at the lower grade therefore constructs an actual
member of that grade's fixed catalogue. The base rank match and the ceiling
leaf at every retained higher grade are consequences, not coverage premises.

Original fields are read literally, so their lawful restrictions are inherited
without composing witnesses on long original rows. These are numerical master
vectors: scope placement and the physical availability and lifting ledgers are
not asserted here. No upward admission or cross-grade rendering equality is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyRecursiveCoverage
open Transform Value ExtOrd CappedDonor LowOnly
open PairedSlotEncoding PairedSlotComparison RecursiveRungRendering RecursiveRungLocality
open LowOnlyRecursiveCharts
noncomputable section
variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

/-- The same complete state is admitted at every lower cutoff. Crossing fields
are one-visible by their old lawfulness, not by a new source-family assumption. -/
theorem admissible_down {i j : ℕ} (hj : 1 ≤ j) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) : F.Admissible i S where
  lawfulP := hS.lawfulP.mono (CappedDonor.Ref.effC_mono hij)
  lawfulC := hS.lawfulC.mono (CappedDonor.Ref.effC_mono hij)
  shared := hS.shared
  futureP d _ := profile_visible_one F hj hS (.inl d)
  futureC d _ := profile_visible_one F hj hS (.inr (.inl d))
  cutoff := selfVis_mono hS.cutoff (min_le_min_right K hij)
  low hKi hm d hd := hS.low (hKi.trans hij) hm d hd

/-- Canonical normalization at a lower grade lands in the existing catalogue. -/
def normalizedAnchor {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) : F.Anchor i :=
  ⟨(S.normalize i).profile, LowOnly.Family.normalize_inventory i hp,
    S.normalize i, F.normalize_admissible hi (admissible_down F (hi.trans hij) hij hS), rfl⟩

theorem normalizedAnchor_fields {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) :
    F.fields i (normalizedAnchor F hi hij hS hp) = normalize i S.profile :=
  funext (State.profile_normalize i S)

/-- The grade-one catalogue contains the rank profile of every proper admitted
source, even when its numerical fields were born at higher grades. -/
theorem base_rank_match {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) :
    ranks F (normalizedAnchor F le_rfl hj hS hp) =
      LadderScalarRendering.fieldRank S.profile := by
  unfold ranks
  rw [normalizedAnchor_fields]
  exact funext (ReceivingCatalogueRanks.fieldRank_normalize 1 S.profile hp)

/-- Actual base lawfulness, with the matching anchor now constructed. -/
theorem base_lawful (n : ℕ) {S : State P C} (hS : F.Admissible (n + 1) S)
    (hp : ∀ d, S.profile d ≠ ⊤) {G : Finset ExtOrd} {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hh : SelfVis (n + 1) h)
    (hb : ∀ d, S.profile d ≤ h) :
    RungOnlyLadder.Lawful (ranks F)
      (fun v => renderAux (ranks F) F.fields n S.profile G h (baseAt n v)) :=
  render_base_lawful (ranks F) F.fields n (normalizedAnchor F le_rfl (by omega) hS hp)
    (base_rank_match F (by omega) hS hp) hp (profile_visible_one F (by omega) hS) hG hh hb

/-- A named spare tip in the unchanged grade-one catalogue reads the ceiling. -/
theorem base_ceiling (n : ℕ) {S : State P C} (hS : F.Admissible (n + 1) S)
    (hp : ∀ d, S.profile d ≠ ⊤) {G : Finset ExtOrd} {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (n + 1) z) (hh : SelfVis (n + 1) h)
    (hb : ∀ d, S.profile d ≤ h) :
    ∃ a : F.Anchor 1,
      renderAux (ranks F) F.fields n S.profile G h
        (baseAt n (a, Fin.last (Fintype.card (Field P C)))) = h :=
  ⟨normalizedAnchor F le_rfl (by omega) hS hp,
    render_base_ceiling (ranks F) F.fields n _
      (base_rank_match F (by omega) hS hp) hp hG hh hb⟩

/-- Every retained higher birth grade has an actual ceiling leaf. In a later
call the leaf is selected from the normalized lower call, not from an assumed
equality with an independently rendered section. -/
theorem inherited_leaf_ceiling (n t : ℕ) {S : State P C}
    (hS : F.Admissible (n + t + 2) S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (n + t + 2) z) (hh : SelfVis (n + t + 2) h)
    (hb : ∀ d, S.profile d ≤ h) :
    ∃ a : F.Anchor (n + 2),
      render (ranks F) F.fields (n + 1 + t) S.profile G h
        (raise t (.inr (.inr a))) = h := by
  induction t generalizing S G h with
  | zero =>
    let a := normalizedAnchor F (by omega : 1 ≤ n + 2) le_rfl hS hp
    refine ⟨a, ?_⟩
    change renderAux (ranks F) F.fields (n + 1) S.profile G h (.inr a) = h
    exact
      render_leaf_ceiling (ranks F) F.fields n a
        (normalizedAnchor_fields F (by omega) le_rfl hS hp) hh hb
  | succ t ih =>
    have hj : n + (t + 1) + 2 = n + 1 + t + 2 := by omega
    have hS' : F.Admissible (n + 1 + t + 2) S := hj ▸ hS
    have hG' : ∀ z ∈ G, SelfVis (n + 1 + t + 2) z := hj ▸ hG
    have hh' : SelfVis (n + 1 + t + 2) h := hj ▸ hh
    let T := S.normalize (n + 1 + t + 2)
    have hT := F.normalize_admissible (by omega : 1 ≤ n + 1 + t + 2) hS'
    have hmem := LowOnly.Family.normalize_inventory (n + 1 + t + 2) hp
    have hproper : ∀ d, T.profile d ≠ ⊤ := hmem.2
    have hbound : ∀ d, T.profile d ≤ ceiling (Field P C) (n + 1 + t + 2) :=
      anchor_bound F (⟨T.profile, hmem, T, hT, rfl⟩ : F.Anchor (n + 1 + t + 2))
    obtain ⟨a, ha⟩ := ih (admissible_down F (by omega) (by omega) hT) hproper
      (G := grid (Field P C) (n + 1 + t + 2))
      (h := ceiling (Field P C) (n + 1 + t + 2))
      (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega)) hbound
    refine ⟨a, ?_⟩
    rw [render_raise_succ (ranks F) F.fields (n := n + 1) t hp hG' hh']
    have hprofile : T.profile = normalize (n + 1 + t + 2) S.profile :=
      funext (State.profile_normalize _ S)
    rw [← hprofile, ha]
    exact decode_reserved_ceiling hh' hb

/-- The birth grade of an auxiliary in the fixed recursive inventory. -/
def auxGrade : (n : ℕ) → Aux (Field P C) (F.Anchor 1) F.Anchor n → ℕ
  | 0, _ => 1
  | n + 1, .inl d => auxGrade n d
  | n + 1, .inr _ => n + 2

theorem raiseAux_grade {n : ℕ} (t : ℕ)
    (d : Aux (Field P C) (F.Anchor 1) F.Anchor n) :
    auxGrade F (n + t) (raiseAux t d) = auxGrade F n d := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem baseAt_grade (n : ℕ) (d : Base (Field P C) (F.Anchor 1)) :
    auxGrade F n (baseAt n d) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Every present positive grade has a ceiling occurrence. This supplies the
numerical witness for availability; actual scope membership is still separate. -/
theorem ceiling_at_grade (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    {S : State P C} (hS : F.Admissible (n + 1) S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hh : SelfVis (n + 1) h) (hb : ∀ d, S.profile d ≤ h) :
    ∃ a : Aux (Field P C) (F.Anchor 1) F.Anchor n,
      auxGrade F n a = k ∧ renderAux (ranks F) F.fields n S.profile G h a = h := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · obtain ⟨a, ha⟩ := base_ceiling F n hS hp hG hh hb
    exact ⟨baseAt n (a, Fin.last (Fintype.card (Field P C))), baseAt_grade F n _, ha⟩
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ n by omega)
    have he : k + 1 + t + 1 = k + t + 2 := by omega
    obtain ⟨a, ha⟩ := inherited_leaf_ceiling F k t (he ▸ hS) hp (he ▸ hG) (he ▸ hh) hb
    refine ⟨raiseAux t (.inr a), ?_, ha⟩
    exact raiseAux_grade F (n := k + 1) t (.inr a)

/-- A constructed same-grade auxiliary dominates any chosen master coordinate.
No matching anchor or ceiling-leaf premise is passed by the caller. -/
theorem exists_dominating_at_grade (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1)
    {S : State P C} (hS : F.Admissible (n + 1) S) (hp : ∀ d, S.profile d ≠ ⊤)
    {G : Finset ExtOrd} {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis (n + 1) z)
    (hh : SelfVis (n + 1) h) (hb : ∀ d, S.profile d ≤ h)
    (d : Point (Field P C) (F.Anchor 1) F.Anchor n) :
    ∃ a : Aux (Field P C) (F.Anchor 1) F.Anchor n, auxGrade F n a = k ∧
      render (ranks F) F.fields n S.profile G h d ≤
        renderAux (ranks F) F.fields n S.profile G h a := by
  obtain ⟨a, hgrade, ha⟩ := ceiling_at_grade F n k hk hkn hS hp hG hh hb
  refine ⟨a, hgrade, ?_⟩
  rw [ha]
  cases d with
  | inl d => exact hb d
  | inr d => exact renderAux_bound (ranks F) F.fields n hh hb d

/-- Literal original-field columns retain donor lawfulness at every lower grade.
This includes long rows; no decoding-composition premise is used. -/
theorem donor_respects (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) {S : State P C}
    (hS : F.Admissible (n + 1) S) (G : Finset ExtOrd) (h : ExtOrd) :
    RespectsSemanticsBelow P.rows (effC m i)
      (fun d => render (ranks F) F.fields n S.profile G h (.inl (.inl d.1))) :=
  hS.lawfulP.mono (CappedDonor.Ref.effC_mono hi)

/-- The private restriction is likewise the original lawful section, literally. -/
theorem private_respects (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) {S : State P C}
    (hS : F.Admissible (n + 1) S) (G : Finset ExtOrd) (h : ExtOrd) :
    RespectsSemanticsBelow C.rows (effC m i)
      (fun d => render (ranks F) F.fields n S.profile G h (.inl (.inr (.inl d.1)))) :=
  hS.lawfulC.mono (CappedDonor.Ref.effC_mono hi)

end
end VaughtConjecture.Knight.LowOnlyRecursiveCoverage
