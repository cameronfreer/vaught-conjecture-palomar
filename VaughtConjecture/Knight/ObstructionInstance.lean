/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowCapCompletion
public import VaughtConjecture.Knight.MixedReferenceEntailment

/-! # The high-fresh obstruction on an actual legal finite type

The reviewer's task (2026-09-16): test the remaining obstruction concretely — an actual legal
finite type satisfying the three inequalities of `lowCap_obstruction`, keeping realization
inside an intended receiver as a separate obligation; conclude neither that every high fresh
prescription fails nor that the general extension problem is refuted.

**The scheme-level donor construction.**  `lowCap_obstruction` is stated for a mixed donor of a
reference context, which carries a realization.  The construction it concerns needs only a
scheme with semantics, a donor cell `o`, a representative `r` below it and an offset:
`donorSource` (the donor's row plus the replacement of its reading of `r`) and `DonorSection`
(a faithful capped target with prescribed old labels and a fixed fresh label).  For a mixed
donor these are definitionally its `mixedSource` and `SimultaneousSection`
(`MixedDonor.mixedSource_eq_donorSource`).  The readback equation (`donorSection_capped`) and
the obstruction (`donorSection_obstruction`) are proved at this level with the same proofs.

**The instance.**  The repaired coupled domain `semSchemeR` (four points, unconditional) with
the mixed display `display κ κ'` (a respecting labelling for every `γ₀ ≤ κ ≤ κ'` self-visible at
grade three; extended by bottom it is the stage type `MixedReferenceCofaces.extension`) has:

* the donor `U_S` at `(univ, 2)`, the unique cell there (`eq_U_S_of_cell`);
* the prescribed sub-index `({0,1,2}, 2)`, the index of `s₀old`, a proper sub-index of the
  donor's, whose display value is `κ`;
* a representative `r` at `({1}, 1)` inside it (completeness), a proper cell, whose display
  value is `v₀ = ω + 1`: block `ω`, offset `1 < 2`, so it is a lawful representative at the
  donor's grade for every requested offset at most `2`;
* the inequalities `v₀ < κ` and `extVisibilityReplace v₀ 2 off < κ` for every offset
  `off ≤ 2`, since both sides are below `γ₀ = ω + 4 ≤ κ`.

Hence for every fresh label `φ ≥ κ` — in particular the display's own high value `κ'` or `⊤` —
**no lawful completion of the display's restriction to `({0,1,2}, 2)` forms a donor section
with the literal fresh label `φ`** (`concrete_obstruction`).  The prescribed section is the
restriction of a respecting labelling, hence lawful; the donor and representative satisfy the
mixed-donor data (`v₀ ≤ κ'` for the cap requirement).

**What this does and does not show.**  It exhibits actual lawful inputs — a legal finite type,
a lawful section of an actual sub-index, a lawful representative, a fixed fresh label above the
cap — for which the one-donor construction at `U_S` admits no completion.  It concerns this
donor row: the display's own value at the fresh cell, and any other extension of the domain,
are not addressed.  Realization of `semSchemeR` inside an intended receiver, and the reference
context that would make `U_S` a `MixedDonor` there, remain separate obligations.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## The donor construction at scheme level -/

section Generic

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} (sem : Semantics D)

/-- **The donor row with a fresh reading**: the donor's row on its lower domain, and at the
fresh cell the replacement at the donor's grade of its reading of the representative. -/
noncomputable def donorSource (o : Cell D) (r : D.below (D.cell o)) (off : ℕ) :
    D.below (D.cell o) ⊕ Unit → ExtOrd :=
  Sum.elim (sem.E o) (fun _ => extVisibilityReplace (sem.E o r) (D.grade o) off)

/-- **A donor section**: prescribed old labels `p` and a fixed fresh label `φ` as a faithful
capped target of the donor row, the fresh cell at grade `g₀`. -/
def DonorSection (o : Cell D) (r : D.below (D.cell o)) (off g₀ : ℕ)
    (p : D.below (D.cell o) → ExtOrd) (φ : ExtOrd) : Prop :=
  TransformsTo (Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ => g₀))
    (donorSource sem o r off)
    (fun x => min (Sum.elim p (fun _ => φ) x) (p ⟨o, GradedLe.refl _⟩))

variable {sem}

/-- **The readback equation**: a donor section reads the fresh cell, capped at the donor, as
the replacement of its capped value at the representative. -/
theorem donorSection_capped {o : Cell D} {r : D.below (D.cell o)} {off g₀ : ℕ}
    (hoff : off ≤ D.grade o) (hg₀ : g₀ ≤ D.grade o) {p : D.below (D.cell o) → ExtOrd}
    {φ : ExtOrd} (hvis : SelfVis (D.grade o) (p ⟨o, GradedLe.refl _⟩))
    (h : DonorSection sem o r off g₀ p φ) :
    min φ (p ⟨o, GradedLe.refl _⟩) =
      extVisibilityReplace (min (p r) (p ⟨o, GradedLe.refl _⟩)) (D.grade o) off := by
  have hmax : ∀ x : D.below (D.cell o) ⊕ Unit,
      Sum.elim (fun d : D.below (D.cell o) => D.grade d.1) (fun _ : Unit => g₀) x ≤
        D.grade o := by
    intro x
    rcases x with d | u
    · exact d.2.2
    · exact hg₀
  obtain ⟨τ, hτ, -, hread⟩ : ∃ τ : ExtOrd → ExtOrd, Witness (gTop (D.grade o)) τ ∧
      (∀ x, τ x ≤ p ⟨o, GradedLe.refl _⟩) ∧
      ∀ d, τ (donorSource sem o r off d) =
        min (Sum.elim p (fun _ => φ) d) (p ⟨o, GradedLe.refl _⟩) :=
    exists_bounded_exact_capped_witness (p := Sum.elim p (fun _ => φ))
      (c := Sum.inl ⟨o, GradedLe.refl _⟩) hmax hvis (by unfold DonorSection at h; exact h)
  have hnew := hread (Sum.inr ())
  have href := hread (Sum.inl r)
  change τ (extVisibilityReplace (sem.E o r) (D.grade o) off) = min φ _ at hnew
  change τ (sem.E o r) = min (p r) _ at href
  rw [hτ.clause5 _ (D.grade o) (by rw [gTop_of_le le_rfl]; exact le_top) _ hoff, href] at hnew
  exact hnew.symm

/-- **The obstruction at scheme level**: with the donor unique at its index and the
representative inside a prescribed sub-index, a prescribed same-grade cell read strictly above
the prescribed representative value and its replacement, with the fresh label at least that
cell, admits no lawful completion forming a donor section. -/
theorem donorSection_obstruction {o : Cell D} {r : D.below (D.cell o)} {off g₀ : ℕ}
    (hoff : off ≤ D.grade o) (hg₀ : g₀ ≤ D.grade o)
    {CI : Finset ι × ℕ} (hle : GradedLe CI (D.cell o))
    (huniq : ∀ w : D.below (D.cell o), D.cell w.1 = D.cell o → w.1 = o)
    (hr : GradedLe (D.cell r.1) CI) (d : D.below CI) (hd : D.grade d.1 = D.grade o)
    (p : D.below CI → ExtOrd) (φ : ExtOrd)
    (h1 : p ⟨r.1, hr⟩ < p d)
    (h2 : extVisibilityReplace (p ⟨r.1, hr⟩) (D.grade o) off < p d) (h3 : p d ≤ φ) :
    ¬ ∃ p' : D.below (D.cell o) → ExtOrd, RespectsSemanticsBelow sem (D.cell o) p' ∧
      (∀ e : D.below CI, p' (CellScheme.below.mono hle e) = p e) ∧
      DonorSection sem o r off g₀ p' φ := by
  rintro ⟨p', hp', hres, hs⟩
  have hcrit := donorSection_capped hoff hg₀ (hp'.orderly ⟨o, GradedLe.refl _⟩).symm hs
  have hrep' : p' r = p ⟨r.1, hr⟩ := by
    have h := hres ⟨r.1, hr⟩
    rwa [show CellScheme.below.mono hle ⟨r.1, hr⟩ = r from Subtype.ext rfl] at h
  have hod : p d ≤ p' ⟨o, GradedLe.refl _⟩ := by
    obtain ⟨Xi, hXi, hle'⟩ := hp'.availability (CellScheme.below.mono hle d)
      ⟨o, GradedLe.refl _⟩ (d.2.trans hle).1 hd
    have hXi' : Xi = ⟨o, GradedLe.refl _⟩ := Subtype.ext (huniq Xi hXi)
    rw [hXi', hres d] at hle'
    exact hle'
  have hlt : p' r < p' ⟨o, GradedLe.refl _⟩ := by rw [hrep']; exact h1.trans_le hod
  rw [min_eq_left hlt.le, hrep'] at hcrit
  have hge : p d ≤ min φ (p' ⟨o, GradedLe.refl _⟩) := le_min h3 hod
  rw [hcrit] at hge
  exact absurd h2 (not_lt.mpr hge)

end Generic

/-- A mixed donor's row is the scheme-level donor row. -/
theorem ReferenceContext.MixedDonor.mixedSource_eq_donorSource {M : Type*} {α : LimitStage}
    {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest}
    {C : ReferenceContext R t reqs} {i : Fin reqs.length} (D : C.MixedDonor i) :
    D.mixedSource = donorSource C.p₀.scheme.rows D.cell D.rep reqs[i.val].offset :=
  rfl

/-! ## The instance on the repaired coupled domain -/

namespace ObstructionInstance

open MixedReferenceEntailment

/-- The prescribed sub-index: the index of `s₀old`, a proper sub-index of the donor's. -/
theorem s₀old_ne_U_S : D₂.cell s₀old ≠ D₂.cell U_S := by
  intro h
  have hs : D₂.scope s₀old = Finset.univ := (congrArg Prod.fst (h.trans cell_U_S))
  rw [scope_s₀old] at hs
  exact absurd (hs ▸ Finset.mem_univ (3 : Fin 4)) (by decide)

/-- The donor is unique at its index. -/
theorem U_S_unique (w : D₂.below (D₂.cell U_S)) (hw : D₂.cell w.1 = D₂.cell U_S) : w.1 = U_S :=
  eq_U_S_of_cell (hw.trans cell_U_S)

/-- A representative at `({1}, 1)` exists (completeness). -/
theorem exists_rep : ∃ x : Cell D₂, D₂.cell x = ({1}, 1) := by
  apply D₂_complete
  refine Plan.mem_gradedPlan.mpr ⟨?_, Nat.one_pos, by simp⟩
  rw [D₂_plan]
  decide

/-- The representative lies inside the prescribed sub-index. -/
theorem rep_below_s₀old {x : Cell D₂} (hx : D₂.cell x = ({1}, 1)) :
    GradedLe (D₂.cell x) (D₂.cell s₀old) := by
  rw [hx]
  refine ⟨?_, ?_⟩
  · change ({1} : Finset (Fin 4)) ⊆ D₂.scope s₀old
    rw [scope_s₀old]; decide
  · change 1 ≤ D₂.grade s₀old
    rw [grade_s₀old]; decide

/-- The display reads the prescribed grade-two cell as `κ`. -/
theorem display_s₀old (κ κ' : ExtOrd) (hle : κ ≤ κ') :
    display κ κ' ⟨s₀old, mems₀old₃⟩ = κ := by
  rw [(shape κ κ' hle).at_s₀old, min_eq_left hle]

/-- The display reads the representative as `v₀`. -/
theorem display_rep (κ κ' : ExtOrd) (hle : κ ≤ κ') {x : Cell D₂} (hx : D₂.cell x = ({1}, 1))
    (hmem : GradedLe (D₂.cell x) (Finset.univ, 3)) : display κ κ' ⟨x, hmem⟩ = v₀ := by
  rw [(shape κ κ' hle).at_proper ⟨x, hmem⟩ (isProper_of_cell_singleton x 1 hx)]
  have hg : D₂.grade x = 1 := congrArg Prod.snd hx
  rw [hg]
  exact ite_eq_right (by decide)

/-- `v₀ < κ` for every `κ ≥ γ₀`. -/
theorem v₀_lt_of_cap {κ : ExtOrd} (hκ : γ₀ ≤ κ) : v₀ < κ := by
  refine lt_of_lt_of_le ?_ hκ
  unfold v₀ γ₀
  rw [ofOrd_lt_ofOrd]
  exact add_lt_add_right (Nat.cast_lt.mpr (by decide : 1 < 4)) _

/-- The replacement of `v₀` at grade two with any offset at most two is below every `κ ≥ γ₀`. -/
theorem replace_v₀_lt_of_cap {κ : ExtOrd} (hκ : γ₀ ≤ κ) {off : ℕ} (hoff : off ≤ 2) :
    extVisibilityReplace v₀ 2 off < κ := by
  refine lt_of_lt_of_le ?_ hκ
  unfold v₀ γ₀
  rw [extVisibilityReplace_rep (limitPart_omega0_mul _) (by decide : 1 < 2), ofOrd_lt_ofOrd]
  exact add_lt_add_right (Nat.cast_lt.mpr (by omega : off < 4)) _

/-- The display's cap requirement at the donor: `v₀ ≤ κ'`. -/
theorem v₀_le_donor {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ') : v₀ ≤ κ' :=
  ((v₀_lt_of_cap hκ).le).trans hle

/-- **The obstruction on an actual legal finite type.**  On the repaired coupled domain with the
mixed display, for the donor `U_S`, a representative at `({1}, 1)`, any requested offset at most
two, any fresh grade at most two, and any fresh label at least `κ`: the display's restriction
to `({0,1,2}, 2)` is a lawful section, and no lawful completion of it forms a donor section
with that fresh label. -/
theorem concrete_obstruction {κ κ' : ExtOrd} (hκ : γ₀ ≤ κ) (hle : κ ≤ κ')
    (hvκ : SelfVis 3 κ) (hvκ' : SelfVis 3 κ') {off : ℕ} (hoff : off ≤ 2) {g₀ : ℕ} (hg₀ : g₀ ≤ 2)
    {φ : ExtOrd} (hφ : κ ≤ φ) :
    ∃ r : D₂.below (D₂.cell U_S), D₂.cell r.1 = ({1}, 1) ∧
      RespectsSemanticsBelow rowsR (D₂.cell s₀old)
        (fun e => display κ κ' (CellScheme.below.mono mems₀old₃ e)) ∧
      ¬ ∃ p' : D₂.below (D₂.cell U_S) → ExtOrd,
        RespectsSemanticsBelow rowsR (D₂.cell U_S) p' ∧
        (∀ e : D₂.below (D₂.cell s₀old), p' (CellScheme.below.mono s₀old_below_U_S e) =
          display κ κ' (CellScheme.below.mono mems₀old₃ e)) ∧
        DonorSection rowsR U_S r off g₀ p' φ := by
  obtain ⟨x, hx⟩ := exists_rep
  have hxU : GradedLe (D₂.cell x) (D₂.cell U_S) := (rep_below_s₀old hx).trans s₀old_below_U_S
  refine ⟨⟨x, hxU⟩, hx, (display_respects hκ hle hvκ hvκ').mono mems₀old₃, ?_⟩
  have hK : D₂.grade U_S = 2 := congrArg Prod.snd cell_U_S
  have hoff' : off ≤ D₂.grade U_S := by rw [hK]; exact hoff
  have hg₀' : g₀ ≤ D₂.grade U_S := by rw [hK]; exact hg₀
  refine donorSection_obstruction hoff' hg₀' s₀old_below_U_S U_S_unique (rep_below_s₀old hx)
    ⟨s₀old, GradedLe.refl _⟩ (by rw [grade_s₀old, hK]) _ φ ?_ ?_ ?_
  · change display κ κ' ⟨x, _⟩ < display κ κ' ⟨s₀old, _⟩
    rw [display_rep κ κ' hle hx, display_s₀old κ κ' hle]
    exact v₀_lt_of_cap hκ
  · change extVisibilityReplace (display κ κ' ⟨x, _⟩) (D₂.grade U_S) off <
      display κ κ' ⟨s₀old, _⟩
    rw [display_rep κ κ' hle hx, display_s₀old κ κ' hle, hK]
    exact replace_v₀_lt_of_cap hκ hoff
  · change display κ κ' ⟨s₀old, _⟩ ≤ φ
    rw [display_s₀old κ κ' hle]
    exact hφ

end ObstructionInstance

end VaughtConjecture.Knight
