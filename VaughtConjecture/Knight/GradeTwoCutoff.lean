/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoAvailability
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.FiniteCutoffBound
public import VaughtConjecture.Knight.RowReadback

/-! # The two-level tower: the intended section and the cutoff forcing at a controller

**Part one of the acceptance test — the intended section exists.**  Every level-two member `m`
extends to a labelling respecting the whole tower semantics: its own row on the lower set of
its cell, `⊥` above grade two (`section_of_member`, by the full-scope zero extension of
`Knight/FullScopeZeroExtension.lean`).  The section carries the member's base labels literally
(`section_old`) and reads the member's cell at its cap (`section_self`).  A coded display —
context labels and requested labels in the alphabet at grade two, respecting the base, under a
cap — is a member, so its intended section exists.

**Part two — the forcing at a controller.**  At any cell `Sig` of any scheme whose row satisfies
the cutoff bound for reference data on its lower set, a respecting labelling that activates
`Sig` **above the cap** — `s Sig ≠ ⊥` and `s cap ≤ s Sig` — and carries the proper reference
`β + j` at the representative reads the request at least `β`: `truncExt β (s req) = ⊤`
(`readback_at_controller`: locality at `Sig` transports the bound, `CutoffBound.readback_top`
finishes).  On the tower, the display member's cell is such a controller (`tower_readback`).

**What this does not yet give.**  A respecting labelling may activate the display's cell *below*
the cap, `⊥ < s Sig < s cap`, and rely on another level-two member for availability; then the
transported bound is capped at `s Sig` and the request is forced only above `min β (s Sig)`.
Forcing it for every activating labelling requires every member dominating the cap to be
cutoff-correct — the correctness thinning of Def. 8.3.2 on this tower, carried out through the
family predicate in `Knight/GradeTwoForcing.lean` (`tower_readback_of_availability`); the thinned
family's bountifulness (§§9.1, 9.4–9.6) is not proved.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-! ## The forcing at a controller, for any scheme -/

/-- **Readback at a cutoff-correct controller.**  If the row of `Sig` satisfies the cutoff bound
for reference data on its lower set whose trigger is `Sig` itself, then every respecting labelling
activating `Sig` above the cap, with the proper reference `β + j` at the representative under the
cap, reads the request at least `β`. -/
theorem readback_at_controller {D : CellScheme A} {sem : Semantics D} {s : Cell D → ExtOrd}
    (hs : RespectsSemantics sem s) (Sig : Cell D)
    (R : FiniteReferenceData (D.below (D.cell Sig)) (fun d => D.grade d.1))
    (hrow : R.CutoffBound (sem.E Sig)) (htrigger : R.trigger.1 = Sig) (hSig : s Sig ≠ ⊥)
    (hcap : s R.cap.1 ≤ s Sig) {r : FiniteRequest (D.below (D.cell Sig))} (hr : r ∈ R.requests)
    (h0 : r.offset = 0) {β : Ordinal.{0}} (hβ : limitPart β = β) {j : ℕ} (hj : j < R.N)
    (href : s (R.rep r.block).1 = ofOrd (β + j)) (hcapβ : ofOrd β ≤ s R.cap.1)
    (hrepcap : s (R.rep r.block).1 ≤ s R.cap.1) :
    truncExt β (s r.cell.1) = ⊤ := by
  have hc : R.CutoffBound (fun d => min (s d.1) (s Sig)) := hrow.transport (hs.locality Sig)
  have key := hc.readback_top (by rw [htrigger, min_self]; exact hSig) hr h0 hβ hj
    (by rw [min_eq_left (hrepcap.trans hcap), href])
    (by rw [min_eq_left hcap]; exact hcapβ)
  exact truncExt_eq_top_of_ge ((truncExt_eq_top_iff.mp key).trans (min_le_left _ _))

/-- Transport of respect along an equality of graded indices. -/
theorem RespectsSemanticsBelow.castIndex {D : CellScheme A} {sem : Semantics D}
    {BJ BJ' : Finset ι × ℕ} (h : BJ = BJ') {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow sem BJ' (fun d => r ⟨d.1, h ▸ d.2⟩) := by
  subst h
  exact hr

/-! ## The tower -/

variable {D₀ : CellScheme A} (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P

omit hI hproper in
/-- The cell of a level-two member. -/
noncomputable def memberCell (m : Member sem₀ I 2 P) : Cell (tower sem₀ I M P hAk) :=
  NEW (idx sem₀ I M P (Sum.inr (Sum.inl m)))

omit hAk hI hproper in
theorem memOf_memberCell (m : Member sem₀ I 2 P) :
    MEM (idx sem₀ I M P (Sum.inr (Sum.inl m))) = Sum.inr (Sum.inl m) :=
  memOf_idx _ _ _ _ _

omit hI hproper in
theorem cell_memberCell (m : Member sem₀ I 2 P) : Tcell (memberCell sem₀ I M P hAk m) = (A, 2) := by
  unfold memberCell
  rw [addFull.cell_new, level_idx]
  rfl

/-- **The row of a level-two member on the lower set of `(A, 2)`.** -/
noncomputable def memberRow (m : Member sem₀ I 2 P) : Tbelow (A, 2) → ExtOrd :=
  fun d => SE (memberCell sem₀ I M P hAk m) ⟨d.1, (cell_memberCell sem₀ I M P hAk m).symm ▸ d.2⟩

theorem memberRow_respects (m : Member sem₀ I 2 P) :
    RespectsSemanticsBelow (towerSem sem₀ I M P hAk hI hproper) (A, 2)
      (memberRow sem₀ I M P hAk hI hproper m) :=
  (respects_new sem₀ I M P hAk hI hproper _).castIndex (cell_memberCell sem₀ I M P hAk m)

/-- **The intended section**: the member's row, `⊥` above grade two. -/
noncomputable def section' (m : Member sem₀ I 2 P) : Cell (tower sem₀ I M P hAk) → ExtOrd :=
  CellScheme.zeroAbove (memberRow sem₀ I M P hAk hI hproper m)

/-- **Part one of the acceptance test: the intended section respects the tower semantics.** -/
theorem section_of_member (m : Member sem₀ I 2 P) :
    RespectsSemantics (towerSem sem₀ I M P hAk hI hproper) (section' sem₀ I M P hAk hI hproper m) :=
  (memberRow_respects sem₀ I M P hAk hI hproper m).zeroAbove

/-- The section carries the member's base labels literally. -/
theorem section_old (m : Member sem₀ I 2 P) (b : Cell D₀) (hb : D₀.grade b ≤ 2) :
    section' sem₀ I M P hAk hI hproper m (OLD b) = m.F ⟨b, hb⟩ := by
  have hmem : GradedLe (Tcell (OLD b)) (A, 2) := by
    rw [addFull.cell_old]
    exact ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan b), hb⟩
  have h1 : section' sem₀ I M P hAk hI hproper m (OLD b) =
      memberRow sem₀ I M P hAk hI hproper m ⟨OLD b, hmem⟩ :=
    CellScheme.zeroAbove_low _ ⟨OLD b, hmem⟩
  rw [h1]
  unfold memberRow memberCell
  refine (E_new_old sem₀ I M P hAk hI hproper _ b (by rw [level_idx]; exact hb) _).trans ?_
  exact newRow_two_old sem₀ I M P hI (memOf_memberCell sem₀ I M P m) b _

/-- The section reads the member's own cell at its cap. -/
theorem section_self (m : Member sem₀ I 2 P) :
    section' sem₀ I M P hAk hI hproper m (memberCell sem₀ I M P hAk m) = m.γ := by
  have hmem : GradedLe (Tcell (memberCell sem₀ I M P hAk m)) (A, 2) := by
    rw [cell_memberCell]; exact GradedLe.refl _
  have h1 : section' sem₀ I M P hAk hI hproper m (memberCell sem₀ I M P hAk m) =
      memberRow sem₀ I M P hAk hI hproper m ⟨memberCell sem₀ I M P hAk m, hmem⟩ :=
    CellScheme.zeroAbove_low _ ⟨memberCell sem₀ I M P hAk m, hmem⟩
  rw [h1]
  unfold memberRow
  exact E_self_two sem₀ I M P hAk hI hproper (memOf_memberCell sem₀ I M P m)

/-- The section is `⊥` above grade two. -/
theorem section_high (m : Member sem₀ I 2 P) (d : Cell (tower sem₀ I M P hAk))
    (hd : ¬ (tower sem₀ I M P hAk).grade d ≤ 2) : section' sem₀ I M P hAk hI hproper m d = ⊥ :=
  CellScheme.zeroAbove_high _ hd

/-! ## The forcing on the tower -/

omit hI hproper in
/-- A base cell of grade `≤ 2` as a cell of the lower set of a level-two member's cell. -/
noncomputable def baseBelow (m : Member sem₀ I 2 P) (b : Cell D₀) (hb : D₀.grade b ≤ 2) :
    Tbelow (Tcell (memberCell sem₀ I M P hAk m)) :=
  ⟨OLD b, by
    rw [cell_memberCell, addFull.cell_old]
    exact ⟨D₀.isPlan.subset_of_mem (D₀.scope_mem_plan b), hb⟩⟩

omit hI hproper in
/-- The member's cell as a cell of its own lower set. -/
noncomputable def selfBelow (m : Member sem₀ I 2 P) :
    Tbelow (Tcell (memberCell sem₀ I M P hAk m)) :=
  ⟨memberCell sem₀ I M P hAk m, GradedLe.refl _⟩

/-- The row of the display member at a base cell is the display's label. -/
theorem E_memberCell_base (m : Member sem₀ I 2 P) (b : Cell D₀) (hb : D₀.grade b ≤ 2) :
    SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m b hb) = m.F ⟨b, hb⟩ := by
  unfold baseBelow memberCell
  refine (E_new_old sem₀ I M P hAk hI hproper _ b (by rw [level_idx]; exact hb) _).trans ?_
  exact newRow_two_old sem₀ I M P hI (memOf_memberCell sem₀ I M P m) b _

/-- The row of the display member at its own cell is its cap. -/
theorem E_memberCell_self (m : Member sem₀ I 2 P) :
    SE (memberCell sem₀ I M P hAk m) (selfBelow sem₀ I M P hAk m) = m.γ :=
  E_self_two sem₀ I M P hAk hI hproper (memOf_memberCell sem₀ I M P m)

omit hI hproper in
/-- **The one-reference data** on the lower set of the display member's cell: threshold two, the
cap `c` (a base cell of grade two), the trigger the member's own cell, the representative `ρ`
at every block, and one request at the cell `q`, block `β`, offset zero. -/
noncomputable def oneReference (m : Member sem₀ I 2 P) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) (β : Ordinal.{0}) :
    FiniteReferenceData (Tbelow (Tcell (memberCell sem₀ I M P hAk m)))
      (fun d => (tower sem₀ I M P hAk).grade d.1) where
  N := 2
  cap := baseBelow sem₀ I M P hAk m c hc.le
  cap_grade := by
    change (tower sem₀ I M P hAk).grade (OLD c) = 2
    rw [addFull.grade_old]; exact hc
  trigger := selfBelow sem₀ I M P hAk m
  rep _ := baseBelow sem₀ I M P hAk m ρ hρ
  requests := [⟨baseBelow sem₀ I M P hAk m q hq, β, 0⟩]
  req_grade_le r hr := by
    rw [List.mem_singleton] at hr
    subst hr
    change (tower sem₀ I M P hAk).grade (OLD q) ≤ 2
    rw [addFull.grade_old]; exact hq
  rep_grade_le _ _ := by
    change (tower sem₀ I M P hAk).grade (OLD ρ) ≤ 2
    rw [addFull.grade_old]; exact hρ
  offset_lt r hr := by
    rw [List.mem_singleton] at hr
    subst hr
    exact two_pos

/-- **The display member's row satisfies the cutoff bound** when its representative carries the
proper reference `β + j`, `j < 2`, under a cap at least `β`, and its request is at least `β`. -/
theorem cutoffBound_memberCell (m : Member sem₀ I 2 P) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) {β : Ordinal.{0}} (hβ : limitPart β = β)
    {j : ℕ} (hj : j < 2) (hmρ : m.F ⟨ρ, hρ⟩ = ofOrd (β + j)) (hmc : ofOrd β ≤ m.F ⟨c, hc.le⟩)
    (hmq : ofOrd β ≤ m.F ⟨q, hq⟩) :
    (oneReference sem₀ I M P hAk m c ρ q hc hρ hq β).CutoffBound
      (SE (memberCell sem₀ I M P hAk m)) := by
  intro _ r hr
  have hr' : r = ⟨baseBelow sem₀ I M P hAk m q hq, β, 0⟩ := List.mem_singleton.mp hr
  subst hr'
  change min (extVisibilityReplace
        (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m ρ hρ)) 2 0)
      (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m c hc.le)) ≤
    min (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m q hq))
      (SE (memberCell sem₀ I M P hAk m) (baseBelow sem₀ I M P hAk m c hc.le))
  rw [E_memberCell_base, E_memberCell_base, E_memberCell_base, hmρ, extVisibilityReplace_rep hβ hj,
    Nat.cast_zero, add_zero, min_eq_left hmc]
  exact le_min hmq hmc

/-- **Part two of the acceptance test, at the display's controller**: every respecting labelling
of the tower that activates the display member's cell above the cap and carries the context's
reference labels reads the request at least `β`. -/
theorem tower_readback (m : Member sem₀ I 2 P) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
    (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2) {β : Ordinal.{0}} (hβ : limitPart β = β)
    {j : ℕ} (hj : j < 2) (hmρ : m.F ⟨ρ, hρ⟩ = ofOrd (β + j)) (hmc : ofOrd β ≤ m.F ⟨c, hc.le⟩)
    (hmq : ofOrd β ≤ m.F ⟨q, hq⟩) {s : Cell (tower sem₀ I M P hAk) → ExtOrd}
    (hs : RespectsSemantics (towerSem sem₀ I M P hAk hI hproper) s)
    (hSig : s (memberCell sem₀ I M P hAk m) ≠ ⊥)
    (hcap : s (OLD c) ≤ s (memberCell sem₀ I M P hAk m))
    (hsρ : s (OLD ρ) = ofOrd (β + j)) (hsc : ofOrd β ≤ s (OLD c)) (hρc : s (OLD ρ) ≤ s (OLD c)) :
    truncExt β (s (OLD q)) = ⊤ :=
  readback_at_controller hs (memberCell sem₀ I M P hAk m)
    (oneReference sem₀ I M P hAk m c ρ q hc hρ hq β)
    (cutoffBound_memberCell sem₀ I M P hAk hI hproper m c ρ q hc hρ hq hβ hj hmρ hmc hmq) rfl hSig
    hcap (List.mem_singleton_self _) rfl hβ hj hsρ hsc hρc

end VaughtConjecture.Knight
