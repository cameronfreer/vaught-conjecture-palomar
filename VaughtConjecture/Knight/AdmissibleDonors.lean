/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DonorFamilyCoverage
public import VaughtConjecture.Knight.DonorAudit

/-! # Admissible donors and the diagonal-coverage condition

The reviewer's task (2026-09-15, item 1): reuse the row-dependent coverage criterion
(`DonorFamilyCoverage`, ported) rather than reproving finite maximization; define admissibility
of a donor cell from the actual scope, representative, offset, fresh-source and cap
requirements; at the smallest supported mixed-index configuration prove the diagonal-coverage
condition or identify a controller whose diagonal cannot be covered; keep witnesses
row-dependent; transport successful old-source coverage to the actual copied occurrences,
keeping fresh-requester availability separate.

**Admissibility** (`Admissible`).  An old cell `o` is admissible for request `i` at fresh grade
`g₀` when the representative's scope lies in `o`'s and its grade at most `o`'s (the actual
scope and representative), the representative's offset is below `o`'s grade and the requested
offset at most it (offset), the representative's label is at most `o`'s (cap), and the fresh
source `o` would carry — the visibility replacement at `o`'s grade of `o`'s reading of the
representative — is compatible with every same-grade old reading of `o`'s row: an old cell of
grade `g₀` read with the very same source must carry, capped at `o`, the same output as the
requested value (the reviewer's correction: equal sources are forbidden only when the required
same-grade capped outputs differ).  The last clause is not an extra assumption: every mixed
donor satisfies it, because the donor's own exact witness reads that source as the requested
value (`MixedDonor.fresh_compat`).  Hence `Admissible` is exactly "cell of a `MixedDonor`"
(`admissible_iff`), and admissible cells have grade at least two.

**Coverage.**  The pool at an index is the admissible cells below it (`pool`).  The reviewer's
diagonal test then reads: at every old controller `c` below the index, an admissible cell at
`c`'s own index is read by `c` at least as high as `c` reads itself.

* `diagonalCover_of_admissible`: where every controller at a needed index is itself admissible,
  the condition holds with the row-dependent witness `c` itself.
* `not_covered_of_grade_one`, `not_covered_of_scope`, `not_covered_of_reading_below`: three
  kinds of controller whose diagonal no admissible family covers — a grade-one controller
  (no admissible cell has grade one), a controller whose scope misses the representative's
  scope (no admissible cell shares its index), and a non-admissible controller reading every
  admissible coindexed cell strictly below its own diagonal.
* **The smallest configuration** — one mixed donor `D` and its lower domain: the donor's own
  face carries a grade-one controller (`MixedDonor.exists_grade_one_below`, by completeness), so
  the unrestricted family never covers the donor's lower domain
  (`MixedDonor.not_diagonalCover_pool`).  Coverage must be targeted away from such indices; the
  grade-one mixed cells are served by the recoded mixed rows, not by donors (`LowLayerTests`).
* `diagonalCover_targeted_iff`: after targeting the indices where admissibility is geometrically
  possible (`IndexAdmissible`), the residual condition is exact and finite: every controller
  there whose label is below the representative's must read some coindexed cell of label at
  least the representative's at least as high as its own diagonal.  This is a condition on the
  receiver's rows; it is neither proved nor refuted here for all contexts.

**Transport** (`MixedDonor.covers_castAdd`).  Successful coverage of the donor's old lower
domain transports to the copied occurrences in the request inventory: for copied old requester
and target of equal grade with nested scopes, an admissible copied cell at the target's index
is read at least as high by the donor's mixed row.  Only the copied old cells are covered; the
fresh requester's availability toward the mixed indices is a separate obligation, not
addressed by this transport.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd DonorFamily

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} {i : Fin reqs.length}

/-! ## Admissibility -/

variable (C i) in
/-- **An admissible donor cell** for request `i`, fresh cell of grade `g₀`: the actual scope,
representative, offset, cap and fresh-source requirements. -/
structure Admissible (g₀ : ℕ) (o : Cell C.p₀.scheme.scheme) : Prop where
  /-- The representative's scope lies in the cell's. -/
  scope_rep : C.p₀.scheme.scheme.scope (C.repBase reqs[i.val].block) ⊆ C.p₀.scheme.scheme.scope o
  /-- The representative's grade is at most the cell's. -/
  grade_rep : C.p₀.scheme.scheme.grade (C.repBase reqs[i.val].block) ≤ C.p₀.scheme.scheme.grade o
  /-- The representative's offset is below the cell's grade. -/
  rep_off_lt : C.repOff reqs[i.val].block < C.p₀.scheme.scheme.grade o
  /-- The requested offset is at most the cell's grade. -/
  offset_le : reqs[i.val].offset ≤ C.p₀.scheme.scheme.grade o
  /-- The representative's label is at most the cell's (the cap requirement). -/
  rep_le_label : C.p₀.label (C.repBase reqs[i.val].block) ≤ C.p₀.label o
  /-- The fresh source is compatible with every same-grade old reading: an old cell of the
  fresh grade read with the same source carries the requested value's capped output. -/
  fresh_compat : ∀ d : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell o),
    C.p₀.scheme.scheme.grade d.1 = g₀ →
    C.p₀.scheme.rows.E o d = extVisibilityReplace
      (C.p₀.scheme.rows.E o ⟨C.repBase reqs[i.val].block, ⟨scope_rep, grade_rep⟩⟩)
      (C.p₀.scheme.scheme.grade o) reqs[i.val].offset →
    min (C.p₀.label d.1) (C.p₀.label o) = min (ofOrd reqs[i.val].value) (C.p₀.label o)

/-- An admissible cell is a mixed donor. -/
def Admissible.toMixedDonor {g₀ : ℕ} {o : Cell C.p₀.scheme.scheme} (h : C.Admissible i g₀ o) :
    C.MixedDonor i :=
  ⟨o, ⟨h.scope_rep, h.grade_rep⟩, h.rep_off_lt, h.offset_le, h.rep_le_label⟩

theorem Admissible.toMixedDonor_cell {g₀ : ℕ} {o : Cell C.p₀.scheme.scheme}
    (h : C.Admissible i g₀ o) : h.toMixedDonor.cell = o :=
  rfl

/-- **The fresh source is compatible with every old reading of the donor's row**: a cell read
with the fresh source carries, capped at the donor, exactly the requested value — the donor's
own exact witness reads that source as the request.  No grade condition is needed. -/
theorem MixedDonor.fresh_compat (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (D : C.MixedDonor i) (d : D.Old)
    (hsrc : C.p₀.scheme.rows.E D.cell d = D.mixedSource (Sum.inr ())) :
    min (C.p₀.label d.1) (C.p₀.label D.cell) =
      min (ofOrd reqs[i.val].value) (C.p₀.label D.cell) := by
  obtain ⟨τ, hτ, -, hread⟩ := D.exists_exact_witness
  rw [← hread d, hsrc, D.fresh_readback hblocks hτ hread, min_eq_left (D.request_le_donor hblocks)]

/-- **Every mixed donor is admissible** at every fresh grade. -/
theorem MixedDonor.admissible (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
    (D : C.MixedDonor i) (g₀ : ℕ) : C.Admissible i g₀ D.cell where
  scope_rep := D.rep_le.1
  grade_rep := D.rep_le.2
  rep_off_lt := D.rep_off_lt
  offset_le := D.offset_le
  rep_le_label := D.rep_le_label
  fresh_compat d _ hsrc := D.fresh_compat hblocks d hsrc

/-- **Admissibility is exactly being a mixed donor's cell.** -/
theorem admissible_iff (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ)
    (o : Cell C.p₀.scheme.scheme) :
    C.Admissible i g₀ o ↔ ∃ D : C.MixedDonor i, D.cell = o :=
  ⟨fun h => ⟨h.toMixedDonor, rfl⟩, fun ⟨D, hD⟩ => hD ▸ D.admissible hblocks g₀⟩

/-- Admissible cells have grade at least two. -/
theorem Admissible.two_le_grade (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) {g₀ : ℕ}
    {o : Cell C.p₀.scheme.scheme} (h : C.Admissible i g₀ o) : 2 ≤ C.p₀.scheme.scheme.grade o :=
  two_le_grade_of_mixedDonor hblocks h.toMixedDonor

variable (C i) in
/-- **Geometric admissibility of an index**: the scope, representative and offset requirements,
which depend on the index alone. -/
def IndexAdmissible (BJ : Finset (Fin C.m) × ℕ) : Prop :=
  C.p₀.scheme.scheme.scope (C.repBase reqs[i.val].block) ⊆ BJ.1 ∧
    C.p₀.scheme.scheme.grade (C.repBase reqs[i.val].block) ≤ BJ.2 ∧
    C.repOff reqs[i.val].block < BJ.2 ∧ reqs[i.val].offset ≤ BJ.2

/-- At a geometrically admissible index, a cell is admissible exactly when its label is at
least the representative's. -/
theorem admissible_iff_rep_le_label (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ)
    {o : Cell C.p₀.scheme.scheme} (hgeo : C.IndexAdmissible i (C.p₀.scheme.scheme.cell o)) :
    C.Admissible i g₀ o ↔ C.p₀.label (C.repBase reqs[i.val].block) ≤ C.p₀.label o :=
  ⟨fun h => h.rep_le_label, fun h =>
    (MixedDonor.mk (C := C) (i := i) o ⟨hgeo.1, hgeo.2.1⟩ hgeo.2.2.1 hgeo.2.2.2 h).admissible
      hblocks g₀⟩

/-- At a geometrically admissible index, non-admissibility is exactly a label below the
representative's. -/
theorem not_admissible_iff (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ)
    {o : Cell C.p₀.scheme.scheme} (hgeo : C.IndexAdmissible i (C.p₀.scheme.scheme.cell o)) :
    ¬ C.Admissible i g₀ o ↔ C.p₀.label o < C.p₀.label (C.repBase reqs[i.val].block) := by
  rw [admissible_iff_rep_le_label hblocks g₀ hgeo, not_le]

/-! ## The admissible pool and the diagonal test -/

variable (C i) in
/-- The admissible pool below an index. -/
def pool (g₀ : ℕ) (BJ : Finset (Fin C.m) × ℕ) (w : C.p₀.scheme.scheme.below BJ) : Prop :=
  C.Admissible i g₀ w.1

/-- **Coverage where every needed controller is admissible**: the row-dependent witness is the
controller itself. -/
theorem diagonalCover_of_admissible (g₀ : ℕ) {BJ : Finset (Fin C.m) × ℕ}
    (needs : Finset (Fin C.m) × ℕ → Prop)
    (h : ∀ c : C.p₀.scheme.scheme.below BJ, needs (C.p₀.scheme.scheme.cell c.1) →
      C.Admissible i g₀ c.1) :
    DiagonalCover C.p₀.scheme.rows BJ (Targeted needs (C.pool i g₀ BJ)) :=
  fun c => ⟨⟨c.1, GradedLe.refl _⟩, rfl, fun hn => h c hn, le_rfl⟩

/-- **A grade-one controller's diagonal cannot be covered**: no admissible cell has grade one. -/
theorem not_covered_of_grade_one (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ)
    {BJ : Finset (Fin C.m) × ℕ} (c : C.p₀.scheme.scheme.below BJ)
    (hc : C.p₀.scheme.scheme.grade c.1 = 1) :
    ¬ ∃ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 ∧
        C.pool i g₀ BJ (CellScheme.below.incl c w) ∧
        C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ C.p₀.scheme.rows.E c.1 w := by
  rintro ⟨w, hw, ha, -⟩
  have h2 := Admissible.two_le_grade hblocks ha
  have hg : C.p₀.scheme.scheme.grade w.1 = C.p₀.scheme.scheme.grade c.1 := congrArg Prod.snd hw
  change 2 ≤ C.p₀.scheme.scheme.grade w.1 at h2
  omega

/-- **A controller whose scope misses the representative's cannot be covered**: no admissible
cell shares its index. -/
theorem not_covered_of_scope (g₀ : ℕ) {BJ : Finset (Fin C.m) × ℕ}
    (c : C.p₀.scheme.scheme.below BJ)
    (hc : ¬ C.p₀.scheme.scheme.scope (C.repBase reqs[i.val].block) ⊆
      C.p₀.scheme.scheme.scope c.1) :
    ¬ ∃ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 ∧
        C.pool i g₀ BJ (CellScheme.below.incl c w) ∧
        C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ C.p₀.scheme.rows.E c.1 w := by
  rintro ⟨w, hw, ha, -⟩
  apply hc
  have hs : C.p₀.scheme.scheme.scope w.1 = C.p₀.scheme.scheme.scope c.1 := congrArg Prod.fst hw
  rw [← hs]
  exact ha.scope_rep

/-- **A controller reading every admissible coindexed cell strictly below its diagonal cannot
be covered** (such a controller is not admissible itself, since it reads itself as its
diagonal). -/
theorem not_covered_of_reading_below (g₀ : ℕ) {BJ : Finset (Fin C.m) × ℕ}
    (c : C.p₀.scheme.scheme.below BJ)
    (hlow : ∀ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 → C.Admissible i g₀ w.1 →
        C.p₀.scheme.rows.E c.1 w < C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩) :
    ¬ ∃ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
      C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 ∧
        C.pool i g₀ BJ (CellScheme.below.incl c w) ∧
        C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ C.p₀.scheme.rows.E c.1 w := by
  rintro ⟨w, hw, ha, hle⟩
  exact absurd hle (not_le.mpr (hlow w hw ha))

/-- **The residual condition after targeting the geometrically admissible indices**: every
controller there whose label is below the representative's must read some coindexed cell of
label at least the representative's at least as high as its own diagonal. -/
theorem diagonalCover_targeted_iff (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ)
    (BJ : Finset (Fin C.m) × ℕ) :
    DiagonalCover C.p₀.scheme.rows BJ (Targeted (C.IndexAdmissible i) (C.pool i g₀ BJ)) ↔
      ∀ c : C.p₀.scheme.scheme.below BJ, C.IndexAdmissible i (C.p₀.scheme.scheme.cell c.1) →
        C.p₀.label c.1 < C.p₀.label (C.repBase reqs[i.val].block) →
        ∃ w : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1),
          C.p₀.scheme.scheme.cell w.1 = C.p₀.scheme.scheme.cell c.1 ∧
            C.p₀.label (C.repBase reqs[i.val].block) ≤ C.p₀.label w.1 ∧
            C.p₀.scheme.rows.E c.1 ⟨c.1, GradedLe.refl _⟩ ≤ C.p₀.scheme.rows.E c.1 w := by
  rw [diagonal_targeted_iff]
  constructor
  · intro h c hgeo _
    obtain ⟨w, hw, ha, hr⟩ := h c hgeo
    exact ⟨w, hw, ha.rep_le_label, hr⟩
  · intro h c hgeo
    by_cases hlt : C.p₀.label c.1 < C.p₀.label (C.repBase reqs[i.val].block)
    · obtain ⟨w, hw, hlab, hr⟩ := h c hgeo hlt
      have hgeo' : C.IndexAdmissible i (C.p₀.scheme.scheme.cell w.1) := by rw [hw]; exact hgeo
      exact ⟨w, hw, (admissible_iff_rep_le_label hblocks g₀ hgeo').mpr hlab, hr⟩
    · exact ⟨⟨c.1, GradedLe.refl _⟩, rfl,
        (admissible_iff_rep_le_label hblocks g₀ hgeo).mpr (not_lt.mp hlt), le_rfl⟩

/-! ## The smallest configuration: one donor and its lower domain -/

namespace MixedDonor

variable (D : C.MixedDonor i)

/-- **The donor's own face carries a grade-one controller** (completeness of the receiver's
scheme at the graded index `(scope D, 1)`). -/
theorem exists_grade_one_below : ∃ c : D.Old, C.p₀.scheme.scheme.grade c.1 = 1 := by
  have hmem : (C.p₀.scheme.scheme.scope D.cell, 1) ∈ Plan.gradedPlan C.p₀.scheme.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨C.p₀.scheme.scheme.scope_mem_plan D.cell, Nat.one_pos,
      (C.p₀.scheme.scheme.grade_pos D.cell).trans_le (C.p₀.scheme.scheme.grade_le_card_scope _)⟩
  obtain ⟨c, hc⟩ := C.p₀.scheme.complete _ hmem
  have hs := congrArg Prod.fst hc
  have hg := congrArg Prod.snd hc
  change C.p₀.scheme.scheme.scope c = C.p₀.scheme.scheme.scope D.cell at hs
  change C.p₀.scheme.scheme.grade c = 1 at hg
  refine ⟨⟨c, ?_⟩, hg⟩
  refine ⟨?_, ?_⟩
  · change C.p₀.scheme.scheme.scope c ⊆ C.p₀.scheme.scheme.scope D.cell
    rw [hs]
  · change C.p₀.scheme.scheme.grade c ≤ C.p₀.scheme.scheme.grade D.cell
    rw [hg]
    exact C.p₀.scheme.scheme.grade_pos D.cell

/-- **The unrestricted admissible family never covers a donor's lower domain**: the grade-one
controller on the donor's face has no admissible coindexed cell. -/
theorem not_diagonalCover_pool (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block) (g₀ : ℕ) :
    ¬ DiagonalCover C.p₀.scheme.rows (C.p₀.scheme.scheme.cell D.cell)
      (C.pool i g₀ (C.p₀.scheme.scheme.cell D.cell)) := by
  intro h
  obtain ⟨c, hc⟩ := D.exists_grade_one_below
  exact not_covered_of_grade_one hblocks g₀ c hc (h c)

/-! ## Transport to the copied occurrences -/

variable {Y : CellScheme (ι := Fin (n + 1)) Finset.univ}
  {Rp : Finset (Finset (Fin (C.m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
    Y.plan.image (Finset.image (onePointProj C.proj))}

/-- **Old-source coverage transports to the copied occurrences**: if the donor's row covers its
old lower domain with the admissible pool, then for copied old cells of equal grade with nested
scopes there is an admissible copied cell at the target's index read at least as high by the
donor's mixed row.  The fresh requester is not covered by this transport. -/
theorem covers_castAdd (g₀ : ℕ)
    (hcov : Covers (C.p₀.scheme.rows.E D.cell) (C.pool i g₀ (C.p₀.scheme.scheme.cell D.cell)))
    (d e : D.Old)
    (hs : (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).scope (Fin.castAdd _ d.1) ⊆
      (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).scope (Fin.castAdd _ e.1))
    (hg : (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).grade (Fin.castAdd _ d.1) =
      (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).grade (Fin.castAdd _ e.1)) :
    ∃ w : D.Old,
      (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).cell (Fin.castAdd _ w.1) =
        (requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB).cell (Fin.castAdd _ e.1) ∧
      C.Admissible i g₀ w.1 ∧ D.mixedSource (Sum.inl d) ≤ D.mixedSource (Sum.inl w) := by
  rw [scope_castAdd_subset_iff'] at hs
  rw [grade_castAdd, grade_castAdd] at hg
  obtain ⟨w, hw, ha, hle⟩ := hcov d e hs hg
  refine ⟨w, ?_, ha, hle⟩
  unfold requestInventory
  rw [extendOneWith_cell_castAdd, extendOneWith_cell_castAdd, hw]

end MixedDonor

end ReferenceContext

end VaughtConjecture.Knight
