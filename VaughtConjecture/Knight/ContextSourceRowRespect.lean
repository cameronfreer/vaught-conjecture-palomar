/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ContextSourceRow
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.CodedWitness

/-! # The candidate controller row respects the inherited rows

The first unsupported obligation of `Knight/ContextSourceRow.lean` — that the candidate
controller row `sourceRow` be a transformation target of every inherited row of the context —
is discharged here, **without transitivity of `⇒`**, by the keyed capped recoding of
`Knight/CappedLocalityRecoding.lean` and the Cap Lemma: the recoding is
`codeLabel x = min (encT x) capCode` (`codeLabel_eq_cap`), every context label is keyed
(`keyed_label`), so the coded ambient locality `coded_locality_S` transports each inherited
row's locality to the recoded labels and the Cap Lemma caps it at the cap code
(`inherited_locality`).  With orderliness and inherited availability
(`codeLabel_le`: the recoding is monotone on keyed labels) this is respect of the base rows
through grade `N` (`inherited_respectsBase`, `RespectsBase`).  The threshold `N` is arbitrary.

**Provenance.**  Ported verbatim, with attribution, from the reviewer's checked standalone
diagnostic `context-source-row-review.lean` (2026-09-14) on PR #460 at `feb6b4b`; standard
axioms only.  No new carrier, no mixed rows and no bountifulness is asserted.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight.ContextSourceRow

open AmalgamationPlan Transform Value ExtOrd

universe w
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M} {n : ℕ}
  {t : Fin n ↪ M} {r : BlockRequest} (C : ReferenceContext R t [r])

theorem codeLabel_eq_cap (x : ExtOrd) :
    codeLabel C x =
      min (encT C.N (vals C) x)
        (ofOrd (capCode C.N (vals C))) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (min_eq_left bot_le).symm
  · exact (min_eq_right le_top).symm
  · exact (min_eq_left (ofOrd_le_ofOrd.mpr
      (code_le_capCode C.N (vals C) v))).symm

theorem keyed_label (d : Cell C.p₀.scheme.scheme) :
    Keyed C.N (vals C) (C.p₀.label d) := by
  rcases ExtOrd.cases (C.p₀.label d) with hb | ht | ⟨v, hv⟩
  · rw [hb]; exact keyed_bot _ _
  · rw [ht]; exact keyed_top _ _
  · rw [hv]
    exact keyed_of_mem _ _ (mem_vals_of_label C hv)

theorem inherited_locality
    (c : {d : Cell C.p₀.scheme.scheme // C.p₀.scheme.scheme.grade d ≤ C.N}) :
    TransformsTo
      (fun d : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1) =>
        C.p₀.scheme.scheme.grade d.1)
      (C.p₀.scheme.rows.E c.1)
      (fun d => min
        (sourceRow C (Sum.inl ⟨d.1, d.2.2.trans c.2⟩))
        (sourceRow C (Sum.inl c))) := by
  classical
  let _ : Fintype (C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1)) :=
    Fintype.ofFinite _
  have hc := coded_locality_S
    (fun d : C.p₀.scheme.scheme.below (C.p₀.scheme.scheme.cell c.1) =>
      C.p₀.scheme.scheme.grade d.1)
    (C.p₀.scheme.rows.E c.1) (fun d => C.p₀.label d.1)
    ⟨c.1, GradedLe.refl _⟩
    (fun d => d.2.2) (fun d => (C.p₀.respects.orderly d.1).symm)
    (C.p₀.respects.locality c.1) c.2 (vals C)
    (fun d => keyed_min _ _ (keyed_label C d.1) (keyed_label C c.1))
  have ht := hc.cap (fun d => d.2.2.trans c.2)
    (capCode_selfVis C.N (vals C))
  convert ht using 1
  funext d
  dsimp only [sourceRow, actual]
  rw [codeLabel_eq_cap, codeLabel_eq_cap,
    encT_min_keyed _ _ (keyed_label C d.1) (keyed_label C c.1),
    min_min_min_comm, min_self]

theorem codeLabel_le {x y : ExtOrd}
    (hx : Keyed C.N (vals C) x)
    (hy : Keyed C.N (vals C) y) (hxy : x ≤ y) :
    codeLabel C x ≤ codeLabel C y := by
  rw [codeLabel_eq_cap, codeLabel_eq_cap]
  exact min_le_min (encT_le_keyed _ _ hx hy hxy) le_rfl

theorem inherited_respectsBase :
    RespectsBase C.p₀.scheme.rows C.N
      (fun d => sourceRow C (Sum.inl d)) where
  orderly d := by
    change SelfVis (C.p₀.scheme.scheme.grade d.1)
      (codeLabel C (C.p₀.label d.1))
    rcases hl : C.p₀.label d.1 with _ | _ | v
    · exact selfVis_bot _
    · exact (capCode_selfVis _ _).mono d.2
    · exact code_selfVis _ _
        (grade_le_finitePart_of_label C.p₀ d.1 hl) d.2
  locality c := inherited_locality C c
  availability d e hs hg := by
    obtain ⟨f, hf, hle⟩ := C.p₀.respects.availability d.1 e.1 hs hg
    have hfn : C.p₀.scheme.scheme.grade f ≤ C.N := by
      unfold CellScheme.grade
      rw [hf]
      exact e.2
    exact ⟨⟨f, hfn⟩, hf, codeLabel_le C (keyed_label C d.1) (keyed_label C f) hle⟩

end VaughtConjecture.Knight.ContextSourceRow
