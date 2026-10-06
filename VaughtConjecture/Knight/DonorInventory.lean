/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NestedDonors

/-! # Classifying the remaining indices of the actual inventory for a donor-based domain

The reviewer's task (2026-09-15, V-C item 1): for each remaining mixed index of the actual
inventory, establish whether an admissible donor exists, whether a mute row is lawful, or
whether another construction is required — accounting for scopes missing the representative
and for the bottom readings larger owners owe mute cells — before assembling the complete
donor-based extension.  This module supplies the classification and the incidence facts each
bucket rests on; the assembly itself is not here.

**The buckets** at a remaining index `(B ∪ {fresh}, j)`, `B` its old face (`oldFace`):
* **Top**: `j` is the size of the whole scope.  No same-grade cell of the inventory lies
  inside it except itself (`top_grade_only_self`), so a mute row is lawful on its own lower
  set (`respectsBelow_bot`) and availability toward it needs nothing; the price is that every
  larger owner must read it as `⊥` (`mute_incoming_iff`).
* **Donor**: an old cell at `(B, j)` with the representative in its lower domain, offsets
  admissible, and the representative's label at most the donor's — an `IndexDonor`, a
  `MixedDonor` at exactly that index.  Its row is the donor's (`MixedDonor.mixedSource`); the
  incidence of an old cell below it is the receiver's **own consistency at the donor**
  (`old_to_donor_locality`: no recoding is involved), the incidence of the fresh cell is a
  one-cell transformation from the request's own source (`transformsTo_const_of_selfVis`),
  and nested donors are `nested_transformsTo`.
* **Other**: a same-grade old requester exists inside `B` (so a mute row is not lawful —
  `mute_unlawful_of_requester`), but no index donor is admissible: either no old cell sits at
  `(B, j)`, or the representative is outside every such cell's lower domain (a scope missing
  the representative), or an offset condition fails.  `DonorCovered` is the explicit
  restriction on the receiver context and request that this bucket is empty.

**Not here**: the assembled semantics and its consistency, coding and selected labelling.
`DonorCovered` is one necessary condition for it, not an assembly theorem: `Knight/DonorAudit.lean`
records the further obligations (the fresh requester, the grade-one rows, source-row
availability across upper donors).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

/-! ## A one-cell transformation from any nonbottom source -/

/-- **Any nonbottom source reaches any label self-visible at the cell's grade** on a one-cell
family: the fresh cell's own row imposes no constraint on the reading a larger owner gives it,
beyond visibility. -/
theorem transformsTo_const_of_selfVis {k : ℕ} {e x : ExtOrd} (he : e ≠ ⊥) (hx : SelfVis k x) :
    TransformsTo (fun _ : Unit => k) (fun _ => e) (fun _ => x) := by
  by_cases hx0 : x = ⊥
  · subst hx0
    exact TransformsTo.to_bot _
  refine ⟨fun n => if n ≤ k then x else ⊥, fun y => if y = ⊥ then ⊥ else x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega
  · intro m
    dsimp only
    split_ifs with h
    · exact (hx.mono h).symm
    · exact (extVisibilityReplace_bot _ _).symm
  · exact ite_eq_left rfl
  · intro y y' hyy'
    dsimp only
    by_cases hy : y = ⊥
    · rw [ite_eq_left hy]
      exact bot_le
    · have hy' : y' ≠ ⊥ := fun h => hy (le_antisymm (h ▸ hyy') bot_le)
      rw [ite_eq_right hy, ite_eq_right hy']
  · intro α kk hle i hi
    dsimp only at hle ⊢
    by_cases hα : α = ⊥
    · subst hα
      rw [extVisibilityReplace_bot, ite_eq_left rfl, extVisibilityReplace_bot]
    · rw [ite_eq_right hα] at hle
      have hkk : kk ≤ k := by
        by_contra hcon
        rw [ite_eq_right hcon] at hle
        exact hx0 (le_antisymm hle bot_le)
      have hα' : extVisibilityReplace α kk i ≠ ⊥ := by
        rcases ExtOrd.cases α with rfl | rfl | ⟨a, rfl⟩
        · exact absurd rfl hα
        · rw [extVisibilityReplace_top]
          exact top_ne_bot
        · rw [extVisibilityReplace_ofOrd]
          exact ofOrd_ne_bot _
      rw [ite_eq_right hα', ite_eq_right hα, evr_eq_self_of_selfVis (hx.mono hkk)]
  · intro u
    dsimp only
    rw [ite_eq_right he, ite_eq_left le_rfl, min_self]

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

/-! ## The old face of an index and the index donor -/

/-- The old face of a scope on the enlarged points: the old points it contains. -/
def oldFace (S : Finset (Fin (C.m + 1))) : Finset (Fin C.m) :=
  Finset.univ.filter fun x => Fin.castSucc x ∈ S

theorem mem_oldFace {S : Finset (Fin (C.m + 1))} {x : Fin C.m} :
    x ∈ oldFace (C := C) S ↔ Fin.castSucc x ∈ S := by
  simp [oldFace]

variable (C) in
/-- **An index donor**: a mixed donor sitting at exactly the old face and grade of a remaining
index. -/
structure IndexDonor (S : Finset (Fin (C.m + 1))) (j : ℕ) extends MixedDonor C i where
  /-- The donor sits at the old face of the index, at its grade. -/
  at_index : C.p₀.scheme.scheme.cell cell = (oldFace (C := C) S, j)

/-- **A same-grade old requester makes a mute row unlawful**: a nonbottom old cell of the
index's grade inside its old face must be dominated at the index under any respecting
labelling, so the index's cell cannot carry `⊥` there. -/
theorem mute_unlawful_of_requester {j : ℕ} (d : Cell C.p₀.scheme.scheme)
    (hne : C.p₀.label d ≠ ⊥) {q : Cell C.p₀.scheme.scheme → ExtOrd}
    (hq : q d = C.p₀.label d) (hmute : ∀ Xi, C.p₀.scheme.scheme.grade Xi = j →
      C.p₀.scheme.scheme.scope d ⊆ C.p₀.scheme.scheme.scope Xi → q Xi = ⊥)
    (Xi : Cell C.p₀.scheme.scheme) (hXi : C.p₀.scheme.scheme.grade Xi = j)
    (hs : C.p₀.scheme.scheme.scope d ⊆ C.p₀.scheme.scheme.scope Xi) :
    ¬ q d ≤ q Xi := by
  rw [hmute Xi hXi hs, hq]
  exact fun h => hne (le_antisymm h bot_le)

/-! ## The incidences a donor row rests on -/

/-- **Old-to-donor locality needs no recoding**: an old cell below the donor transforms to the
donor's row capped at its reading of that cell — the receiver's own consistency at the
donor. -/
theorem old_to_donor_locality (D : C.MixedDonor i) (d : D.Old) :
    TransformsTo (fun x : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell d.1) =>
        C.p₀.scheme.scheme.grade x.1)
      (C.p₀.scheme.rows.E d.1)
      (fun x => min (D.mixedSource (Sum.inl (CellScheme.below.incl d x)))
        (D.mixedSource (Sum.inl d))) :=
  (C.p₀.scheme.consistent D.cell).locality d

/-- **Fresh-to-donor locality**: the request's own source at the fresh cell transforms to the
donor row's fresh reading whenever that reading is self-visible at the fresh cell's grade. -/
theorem fresh_to_donor_locality (D : C.MixedDonor i) {e : ExtOrd} (he : e ≠ ⊥) {k : ℕ}
    (hx : SelfVis k (D.mixedSource (Sum.inr ()))) :
    TransformsTo (fun _ : Unit => k) (fun _ => e) (fun _ => D.mixedSource (Sum.inr ())) :=
  transformsTo_const_of_selfVis he hx

/-- The donor row's fresh reading is self-visible at every grade at most the requested offset:
it is a code with the requested offset as finite part. -/
theorem fresh_reading_selfVis (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (D : C.MixedDonor i) {k : ℕ} (hk : k ≤ reqs[i.val].offset) :
    SelfVis k (D.mixedSource (Sum.inr ())) := by
  obtain ⟨b, hb⟩ := D.mixedSource_fresh_code hblocks
  rw [hb, selfVis_ofOrd_iff, finitePart_mul_add]
  exact hk

/-! ## The explicit restriction -/

variable (C) in
/-- **Donor coverage**: every remaining index of the plan with a same-grade old requester inside
its old face admits an index donor — the explicit restriction on the receiver context and the
request under which a complete donor-based extension can be assembled.  Indices without a
same-grade requester may be mute (`top_grade_only_self` covers the top-grade ones). -/
def DonorCovered (Rp : Finset (Finset (Fin (C.m + 1)))) : Prop :=
  ∀ S ∈ Rp, ∀ j : ℕ, Fin.last C.m ∈ S →
    (∃ d : Cell C.p₀.scheme.scheme, C.p₀.scheme.scheme.grade d = j ∧
      C.p₀.scheme.scheme.scope d ⊆ oldFace (C := C) S ∧ C.p₀.label d ≠ ⊥) →
    Nonempty (C.IndexDonor (i := i) S j)

end ReferenceContext

end VaughtConjecture.Knight
