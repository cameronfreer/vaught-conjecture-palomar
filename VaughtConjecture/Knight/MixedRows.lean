/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MixedOwnValues
public import VaughtConjecture.Knight.CrossGradeRecoding
public import VaughtConjecture.Knight.PartialSections
public import VaughtConjecture.Knight.MixedIndexConstraints

/-! # The mixed rows over the actual context: consistency from the recodings

The reviewer's assignment (2026-09-15, V-C item 2): use the cross-grade recoding to assemble
the actual mixed rows and prove consistency, with one common inventory of values including the
newly assigned own values, no independently chosen codebook, and the threshold `N` arbitrary.

**The rows.**  On the cell inventory over the actual context, the rows are those prescribed by
both faces (`prescribedRows`: the context's rows on old cells, the request's rows on fresh
cells) with, at every remaining-index cell of grade `j`, **the recoding at grade `j` of the
full labelling** on its lower set (`recode j S ∘ fullLabel`; `mixedRows`).  The value set `S`
is the set of all label values of both faces; the own values introduce nothing new
(`fullLabel_eq_or`), so every label is keyed and one codebook serves all rows.

**Proved.**  The rows are coded (`mixedRows_isCoded`) and **consistent** (`mixedRows_isConsistent`,
Def. 2.5.12): the old rows and the fresh rows respect their lower sets by transport of the
context's and the request's consistency along the lower-set equivalences; a recoded row is
orderly, respects locality at every cell below it — at an old cell by the inherited locality
through the recoding (`coded_locality_recode`, the fixed-key coded locality and the Cap Lemma,
as in `Knight/ContextSourceRowRespect.lean`), at a fresh cell likewise from the request's
locality, at a lower remaining-index cell by the **cross-grade recoding transformation**
(`crossGrade_transformsTo_capped`) — and satisfies availability by the own values
(`fullLabel_availability`) and the monotonicity of the recoding on keyed labels.  The full
labelling **respects the rows** (`fullLabel_respects`): it keeps the context's and the
request's labels literally, decodes each recoded row (`recode_transformsTo`), and is available.

**Not proved.**  Bountifulness (Def. 2.5.14) of these rows — the field that would make them a
`SemScheme` — is not attempted here; it is the reviewer's item 3.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

/-! ## The recoding at a grade, generically -/

section Recode

variable (l : ℕ) (S : Finset Ordinal.{0})

/-- The recoding of a label at grade `l` over the value set `S`: `⊤` as the cap code. -/
noncomputable def recode (x : ExtOrd) : ExtOrd := min (encT l S x) (ofOrd (capCode l S))

theorem recode_bot : recode l S ⊥ = ⊥ := by
  unfold recode
  rw [encT_bot]
  exact min_eq_left bot_le

theorem recode_top : recode l S ⊤ = ofOrd (capCode l S) := by
  unfold recode
  rw [encT_top]
  exact min_eq_right le_top

theorem recode_ofOrd (v : Ordinal.{0}) : recode l S (ofOrd v) = ofOrd (code l S v) := by
  unfold recode
  rw [encT_ofOrd, encOrdK_eq_code]
  exact min_eq_left (ofOrd_le_ofOrd.mpr (code_le_capCode l S v))

/-- The recoding is coded at its grade. -/
theorem recode_isCoded (x : ExtOrd) : IsCodedLabel l (recode l S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · rw [recode_bot]; exact Or.inl rfl
  · rw [recode_top]; exact capCode_isCoded l S
  · rw [recode_ofOrd]; exact code_isCoded l S v

/-- The recoding of a label self-visible at `a ≤ l` is self-visible at `a`. -/
theorem recode_selfVis {a : ℕ} {x : ExtOrd} (hx : SelfVis a x) (hal : a ≤ l) :
    SelfVis a (recode l S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · rw [recode_bot]; exact selfVis_bot a
  · rw [recode_top]; exact (capCode_selfVis l S).mono hal
  · rw [recode_ofOrd]; exact code_selfVis l S (selfVis_ofOrd_iff.mp hx) hal

/-- The recoding is monotone on keyed labels. -/
theorem recode_le {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) (hxy : x ≤ y) :
    recode l S x ≤ recode l S y :=
  min_le_min (encT_le_keyed l S hx hy hxy) le_rfl

/-- The recoding preserves minima of keyed labels. -/
theorem recode_min_keyed {x y : ExtOrd} (hx : Keyed l S x) (hy : Keyed l S y) :
    recode l S (min x y) = min (recode l S x) (recode l S y) := by
  unfold recode
  rw [encT_min_keyed l S hx hy, min_min_min_comm, min_self]

/-- The recoding decodes to the label at every cell of grade `≤ l`, capped at any `ρ`
self-visible at `l`. -/
theorem recode_transformsTo {D : Type*} (grade : D → ℕ) (hgr : ∀ d, grade d ≤ l) (p : D → ExtOrd)
    (hp : ∀ d, p d = ⊥ ∨ p d = ⊤ ∨ ∃ v ∈ S, p d = ofOrd v) {ρ : ExtOrd} (hρ : SelfVis l ρ) :
    TransformsTo grade (fun d => recode l S (p d)) (fun d => min (p d) ρ) := by
  have h := transformsTo_of_shift l S ⊤ grade (extVisibilityReplace_top _ _) (fun _ _ => le_top)
    (fun d => recode l S (p d)) hρ
  convert h using 1
  funext d
  rw [ite_eq_left (hgr d)]
  congr 1
  rcases hp d with h | h | ⟨v, hv, h⟩ <;> rw [h]
  · rw [recode_bot, shift_bot]
  · rw [recode_top, shift_capCode]
  · rw [recode_ofOrd, shift_code l S ⊤ hv]

/-- **Inherited locality through the recoding**: a row local toward a labelling capped at a
cell `c` of grade `≤ l` is local toward the recoding at `l` of that labelling capped at the
recoding of `p c`, when the labels are keyed. -/
theorem coded_locality_recode {D : Type*} [Finite D] (grade : D → ℕ) (E p : D → ExtOrd) (c : D)
    (hmax : ∀ d, grade d ≤ grade c) (hordp : ∀ d, SelfVis (grade d) (p d))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) (hl : grade c ≤ l)
    (hS : ∀ d, Keyed l S (p d)) :
    TransformsTo grade E (fun d => min (recode l S (p d)) (recode l S (p c))) := by
  classical
  let _ : Fintype D := Fintype.ofFinite D
  have hc := coded_locality_S grade E p c hmax hordp hloc hl S
    (fun d => keyed_min l S (hS d) (hS c))
  have ht := hc.cap (fun d => (hmax d).trans hl) (capCode_selfVis l S)
  convert ht using 1
  funext d
  rw [← recode_min_keyed l S (hS d) (hS c)]
  rfl

end Recode

/-! ## The inventory over the actual context -/

section Inventory

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (hvX : Finset.univ.image e ∈ X.plan) (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
  (hroot : X.restrictFace e hvX = Y.restrictFace Fin.castSuccEmb hvY)
  (rowsX : Semantics X) (rowsY : Semantics Y) (labX : Cell X → ExtOrd) (labY : Cell Y → ExtOrd)

/-- **The common value set**: every ordinal label of either face. -/
noncomputable def faceVals : Finset Ordinal.{0} :=
  (Finset.univ.biUnion fun d : Cell X => ContextSourceRow.ordSet (labX d)) ∪
    (Finset.univ.biUnion fun c : Cell Y => ContextSourceRow.ordSet (labY c))

theorem mem_faceVals_X {d : Cell X} {v : Ordinal.{0}} (h : labX d = ofOrd v) :
    v ∈ faceVals labX labY :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, by
    rw [h]; exact Finset.mem_singleton_self v⟩)

theorem mem_faceVals_Y {c : Cell Y} {v : Ordinal.{0}} (h : labY c = ofOrd v) :
    v ∈ faceVals labX labY :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, by
    rw [h]; exact Finset.mem_singleton_self v⟩)

/-- Labels in the value set, `⊥` or `⊤`. -/
def InVals (S : Finset Ordinal.{0}) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ x = ⊤ ∨ ∃ v ∈ S, x = ofOrd v

theorem InVals.keyed {S : Finset Ordinal.{0}} {x : ExtOrd} (h : InVals S x) (l : ℕ) :
    Keyed l S x := by
  rcases h with rfl | rfl | ⟨v, hv, rfl⟩
  · exact keyed_bot l S
  · exact keyed_top l S
  · exact keyed_of_mem l S hv

theorem inVals_labX (d : Cell X) : InVals (faceVals labX labY) (labX d) := by
  rcases ExtOrd.cases (labX d) with h | h | ⟨v, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨v, mem_faceVals_X labX labY h, h⟩)

theorem inVals_labY (c : Cell Y) : InVals (faceVals labX labY) (labY c) := by
  rcases ExtOrd.cases (labY c) with h | h | ⟨v, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨v, mem_faceVals_Y labX labY h, h⟩)

/-- The full labelling takes values in the common value set: the own values add nothing. -/
theorem inVals_fullLabel (d : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    InVals (faceVals labX labY) (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d) := by
  rcases fullLabel_eq_or (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d with h | ⟨i, h⟩ | ⟨c, h⟩
  · exact Or.inl h
  · rw [h]; exact inVals_labX labX labY i
  · rw [h]; exact inVals_labY labX labY c

/-! ### The rows -/

/-- **The row of a remaining-index cell**: the recoding at its grade of the full labelling. -/
noncomputable def mixedCtrl (b : OutsideIndex e Rp)
    (d : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))) : ExtOrd :=
  recode b.1.2 (faceVals labX labY) (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d.1)

variable (hX : ∀ d, SelfVis (X.grade d) (labX d)) (hY : ∀ c, SelfVis (Y.grade c) (labY c))

theorem grade_le_of_below_outside {b : OutsideIndex e Rp}
    (d : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))) :
    (requestInventory X Y e Rp hR hRA hRB).grade d.1 ≤ b.1.2 :=
  calc (requestInventory X Y e Rp hR hRA hRB).grade d.1
      = ((requestInventory X Y e Rp hR hRA hRB).cell d.1).2 := rfl
    _ ≤ ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)).2 := d.2.2
    _ = b.1.2 := congrArg Prod.snd (cell_outsideCell b)

include hX hY in
theorem mixedCtrl_orderly (b : OutsideIndex e Rp) :
    IsOrderly (fun d : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
        (requestInventory X Y e Rp hR hRA hRB).grade d.1) (mixedCtrl labX labY b) :=
  fun d => (recode_selfVis _ _ (fullLabel_selfVis labX labY hX hY d.1)
    (grade_le_of_below_outside d)).symm

/-- **The mixed rows**: both faces' rows, and the recoded full labelling at every remaining
index. -/
noncomputable def mixedRows : Semantics (requestInventory X Y e Rp hR hRA hRB) :=
  prescribedRows hvX hvY hroot rowsX rowsY (mixedCtrl labX labY) (mixedCtrl_orderly labX labY hX hY)

theorem mixedRows_outside (b : OutsideIndex e Rp) (d) :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX hY).E
        (outsideCell b) d =
      recode b.1.2 (faceVals labX labY)
        (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d.1) :=
  prescribedRows_outside hvX hvY hroot rowsX rowsY _ (b := b) d

theorem mixedRows_old (i : Cell X) (d' : X.below (X.cell i)) (h) :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX hY).E
      (Fin.castAdd _ i) ⟨Fin.castAdd _ d'.1, h⟩ = rowsX.E i d' :=
  prescribedRows_old hvX hvY hroot rowsX rowsY _ i d' h

theorem mixedRows_fresh (c : FreshReq Y) (d' : Y.below (Y.cell c.1)) (h) :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX hY).E
      (freshCell c) ⟨reqCell hvX hvY hroot d'.1, h⟩ = rowsY.E c.1 d' :=
  prescribedRows_fresh hvX hvY hroot rowsX rowsY _ c d' h

/-! ### Every cell is old, an identified request cell, or a remaining-index cell -/

variable (hfresh : ∀ c : Cell Y, Fin.last n ∈ Y.scope c)

theorem scope_reqCell (c : Cell Y) :
    (requestInventory X Y e Rp hR hRA hRB).scope (reqCell hvX hvY hroot c) =
      (Y.scope c).image (onePointProj e) :=
  congrArg Prod.fst (cell_reqCell hvX hvY hroot c)

theorem inv_cases (s : Cell (requestInventory X Y e Rp hR hRA hRB)) :
    (∃ i : Cell X, s = Fin.castAdd _ i) ∨ (∃ c : Cell Y, s = reqCell hvX hvY hroot c) ∨
      ∃ b, s = outsideCell b := by
  rcases requestInventory_cases s with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨c.1, by rw [reqCell_of_last hvX hvY hroot c.2]⟩)
  · exact Or.inr (Or.inr ⟨b, rfl⟩)

include hfresh in
theorem mixedRows_reqCell (c : Cell Y) (d' : Y.below (Y.cell c)) (h) :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX hY).E
      (reqCell hvX hvY hroot c) ⟨reqCell hvX hvY hroot d'.1, h⟩ = rowsY.E c d' := by
  have hg : GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot d'.1))
      ((requestInventory X Y e Rp hR hRA hRB).cell (freshCell ⟨c, hfresh c⟩)) := by
    rw [← reqCell_of_last hvX hvY hroot (hfresh c)]
    exact h
  rw [Semantics.E_congr _ (reqCell_of_last hvX hvY hroot (hfresh c)) (hd := hg) rfl]
  exact mixedRows_fresh (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY
    hX hY ⟨c, hfresh c⟩ d' _

/-! ### Consistency on a face, transported -/

/-- **Transport of a respecting section of a face** into the inventory along an embedding of
cells with lower-set equivalences. -/
theorem respectsBelow_of_face_section {ι₀ : Type*} [DecidableEq ι₀] {A₀ : Finset ι₀}
    {Z : CellScheme A₀} (rowsZ : Semantics Z)
    (sem : Semantics (requestInventory X Y e Rp hR hRA hRB))
    (emb : Cell Z → Cell (requestInventory X Y e Rp hR hRA hRB))
    (eqv : ∀ i, Z.below (Z.cell i) ≃ (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (emb i)))
    (heqv : ∀ i d, (eqv i d).1 = emb d.1)
    (hgrade : ∀ i, (requestInventory X Y e Rp hR hRA hRB).grade (emb i) = Z.grade i)
    (hscope : ∀ i j, (requestInventory X Y e Rp hR hRA hRB).scope (emb i) ⊆
      (requestInventory X Y e Rp hR hRA hRB).scope (emb j) ↔ Z.scope i ⊆ Z.scope j)
    (hrows : ∀ i d, sem.E (emb i) (eqv i d) = rowsZ.E i d) (i : Cell Z)
    {q : Z.below (Z.cell i) → ExtOrd} (hq : RespectsSemanticsBelow rowsZ (Z.cell i) q) :
    RespectsSemanticsBelow sem ((requestInventory X Y e Rp hR hRA hRB).cell (emb i))
      (fun a => q ((eqv i).symm a)) :=
  RespectsSemanticsBelow.of_equiv (sem := rowsZ) (sem' := sem) (eqv i).symm
    (fun a => by
      obtain ⟨d, rfl⟩ := (eqv i).surjective a
      rw [Equiv.symm_apply_apply, heqv]
      exact hgrade d.1)
    (fun a b => by
      obtain ⟨d, rfl⟩ := (eqv i).surjective a
      obtain ⟨d', rfl⟩ := (eqv i).surjective b
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, heqv, heqv]
      exact hscope d.1 d'.1)
    (fun Sig d hd => by
      obtain ⟨Sig', rfl⟩ := (eqv i).surjective Sig
      have hS : (eqv i Sig').1 = emb Sig'.1 := heqv i Sig'
      have hd2 : GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell d.1)
          ((requestInventory X Y e Rp hR hRA hRB).cell (emb Sig'.1)) :=
        Eq.mp (congrArg (fun x => GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell d.1)
          ((requestInventory X Y e Rp hR hRA hRB).cell x)) hS) d.2
      obtain ⟨d', hd'⟩ := (eqv Sig'.1).surjective ⟨d.1, hd2⟩
      have hd1' : d.1 = (eqv Sig'.1 d').1 := (congrArg Subtype.val hd').symm
      have hd1 : d.1 = emb d'.1 := hd1'.trans (heqv Sig'.1 d')
      have hsub : (⟨d.1, d.2.trans (eqv i Sig').2⟩ :
          (requestInventory X Y e Rp hR hRA hRB).below
            ((requestInventory X Y e Rp hR hRA hRB).cell (emb i))) =
          eqv i ⟨d'.1, d'.2.trans Sig'.2⟩ :=
        Subtype.ext (hd1.trans (heqv i ⟨d'.1, d'.2.trans Sig'.2⟩).symm)
      have hab : Sig'.1 = ((eqv i).symm (eqv i Sig')).1 := by rw [Equiv.symm_apply_apply]
      have hcd : d'.1 = ((eqv i).symm ⟨d.1, d.2.trans (eqv i Sig').2⟩).1 :=
        (congrArg Subtype.val ((eqv i).symm_apply_apply ⟨d'.1, d'.2.trans Sig'.2⟩)).symm.trans
          (congrArg (fun x => ((eqv i).symm x).1) hsub.symm)
      calc sem.E (eqv i Sig').1 d
          = sem.E (emb Sig'.1) (eqv Sig'.1 d') :=
            Semantics.E_congr sem hS (hc := d.2) (hd := (eqv Sig'.1 d').2) hd1'
        _ = rowsZ.E Sig'.1 d' := hrows Sig'.1 d'
        _ = _ := Semantics.E_congr rowsZ hab (hc := d'.2) (hd := hd) hcd)
    hq

/-- **Transport of a face's consistency** into the inventory along an embedding of cells with
lower-set equivalences. -/
theorem respectsBelow_of_face {ι₀ : Type*} [DecidableEq ι₀] {A₀ : Finset ι₀}
    {Z : CellScheme A₀} (rowsZ : Semantics Z) (hZ : rowsZ.IsConsistent)
    (sem : Semantics (requestInventory X Y e Rp hR hRA hRB))
    (emb : Cell Z → Cell (requestInventory X Y e Rp hR hRA hRB))
    (eqv : ∀ i, Z.below (Z.cell i) ≃ (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (emb i)))
    (heqv : ∀ i d, (eqv i d).1 = emb d.1)
    (hgrade : ∀ i, (requestInventory X Y e Rp hR hRA hRB).grade (emb i) = Z.grade i)
    (hscope : ∀ i j, (requestInventory X Y e Rp hR hRA hRB).scope (emb i) ⊆
      (requestInventory X Y e Rp hR hRA hRB).scope (emb j) ↔ Z.scope i ⊆ Z.scope j)
    (hrows : ∀ i d, sem.E (emb i) (eqv i d) = rowsZ.E i d) (i : Cell Z) :
    RespectsSemanticsBelow sem ((requestInventory X Y e Rp hR hRA hRB).cell (emb i))
      (sem.E (emb i)) := by
  have key := respectsBelow_of_face_section rowsZ sem emb eqv heqv hgrade hscope hrows i (hZ i)
  convert key using 1
  funext a
  obtain ⟨d, rfl⟩ := (eqv i).surjective a
  rw [Equiv.symm_apply_apply, hrows]

/-! ### Consistency at the old and the request cells -/

variable (hXres : RespectsSemantics rowsX labX) (hYres : RespectsSemantics rowsY labY)
  (hXcons : rowsX.IsConsistent) (hYcons : rowsY.IsConsistent)

theorem scope_castAdd_subset_iff' (i j : Cell X) :
    (requestInventory X Y e Rp hR hRA hRB).scope (Fin.castAdd _ i) ⊆
        (requestInventory X Y e Rp hR hRA hRB).scope (Fin.castAdd _ j) ↔
      X.scope i ⊆ X.scope j := by
  unfold requestInventory
  rw [extendOneWith_scope_castAdd, extendOneWith_scope_castAdd]
  exact Finset.image_subset_image_iff Fin.castSuccEmb.injective

theorem scope_reqCell_subset_iff' (c c' : Cell Y) :
    (requestInventory X Y e Rp hR hRA hRB).scope (reqCell hvX hvY hroot c) ⊆
        (requestInventory X Y e Rp hR hRA hRB).scope (reqCell hvX hvY hroot c') ↔
      Y.scope c ⊆ Y.scope c' := by
  rw [scope_reqCell, scope_reqCell]
  exact Finset.image_subset_image_iff (onePointProj e).injective

include hXcons in
/-- The old rows respect their lower sets (the context's consistency, transported). -/
theorem mixedRows_respects_old (i : Cell X) :
    RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX
      rowsY labX labY hX hY) ((requestInventory X Y e Rp hR hRA hRB).cell (Fin.castAdd _ i))
      ((mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
        hY).E (Fin.castAdd _ i)) :=
  respectsBelow_of_face rowsX hXcons _ (Fin.castAdd _) oldBelowEquiv (fun _ _ => rfl)
    grade_castAdd scope_castAdd_subset_iff'
    (fun i d => mixedRows_old (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
      labX labY hX hY i d _) i

include hYcons hfresh in
/-- The request's rows respect their lower sets (the request's consistency, transported). -/
theorem mixedRows_respects_req (c : Cell Y) :
    RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX
      rowsY labX labY hX hY)
      ((requestInventory X Y e Rp hR hRA hRB).cell (reqCell hvX hvY hroot c))
      ((mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
        hY).E (reqCell hvX hvY hroot c)) :=
  respectsBelow_of_face rowsY hYcons _ (reqCell hvX hvY hroot) (reqBelowEquiv hvX hvY hroot)
    (fun _ _ => rfl) (grade_reqCell hvX hvY hroot) (scope_reqCell_subset_iff' hvX hvY hroot)
    (fun c d => mixedRows_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
      labX labY hX hY hfresh c d _) c

/-! ### Consistency at the remaining-index cells -/

theorem fullLabel_reqCell (c : Cell Y) (hc : Fin.last n ∈ Y.scope c) :
    fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY (reqCell hvX hvY hroot c) =
      labY c := by
  rw [reqCell_of_last hvX hvY hroot hc]
  exact fullLabel_freshCell labX labY ⟨c, hc⟩

theorem grade_le_of_below_outside' {b : OutsideIndex e Rp}
    {s : Cell (requestInventory X Y e Rp hR hRA hRB)}
    (hs : GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell s)
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))) :
    (requestInventory X Y e Rp hR hRA hRB).grade s ≤ b.1.2 :=
  grade_le_of_below_outside ⟨s, hs⟩

variable (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e)

include hXres hYres hfresh hn in
/-- **The recoded rows respect their lower sets**: locality at an old cell by the inherited
locality through the recoding, at a request cell likewise, at a lower remaining-index cell by
the cross-grade recoding transformation; availability by the own values. -/
theorem mixedRows_respects_outside (b : OutsideIndex e Rp) :
    RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX
      rowsY labX labY hX hY) ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))
      ((mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
        hY).E (outsideCell b)) where
  orderly := (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY
    hX hY).orderly (outsideCell b)
  locality Sig := by
    obtain ⟨s, hs⟩ := Sig
    rcases inv_cases hvX hvY hroot s with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b', rfl⟩
    · -- an old cell: the context's locality through the recoding
      have hj : X.grade i ≤ b.1.2 := by
        have := grade_le_of_below_outside' hs
        rwa [grade_castAdd] at this
      have base := coded_locality_recode b.1.2 (faceVals labX labY)
        (fun d : X.below (X.cell i) => X.grade d.1) (rowsX.E i) (fun d => labX d.1)
        ⟨i, GradedLe.refl _⟩ (fun d => d.2.2) (fun d => hX d.1) (hXres.locality i) hj
        (fun d => (inVals_labX labX labY d.1).keyed _)
      have key := base.reindex (oldBelowEquiv (Y := Y) (e := e) (hR := hR) (hRA := hRA)
        (hRB := hRB) i).symm
      refine transformsTo_congr ?_ ?_ ?_ key
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        change X.grade ((oldBelowEquiv i).symm (oldBelowEquiv i d')).1 =
          (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d'.1)
        rw [Equiv.symm_apply_apply, grade_castAdd]
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        change rowsX.E i ((oldBelowEquiv i).symm (oldBelowEquiv i d')) = _
        rw [Equiv.symm_apply_apply]
        exact (mixedRows_old (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX
          labY hX hY i d' _).symm
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        dsimp only [Function.comp]
        have h1 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          (CellScheme.below.incl ⟨Fin.castAdd _ i, hs⟩ (oldBelowEquiv i d'))
        have h2 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          ⟨Fin.castAdd _ i, hs⟩
        refine Eq.trans ?_ (congrArg₂ min h1 h2).symm
        change min (recode _ _ (labX ((oldBelowEquiv i).symm (oldBelowEquiv i d')).1))
          (recode _ _ (labX i)) = min (recode _ _ (fullLabel labX labY (Fin.castAdd _ d'.1)))
          (recode _ _ (fullLabel labX labY (Fin.castAdd _ i)))
        rw [Equiv.symm_apply_apply, fullLabel_castAdd, fullLabel_castAdd]
    · -- a request cell: the request's locality through the recoding
      have hj : Y.grade c ≤ b.1.2 := by
        have := grade_le_of_below_outside' hs
        rwa [grade_reqCell] at this
      have base := coded_locality_recode b.1.2 (faceVals labX labY)
        (fun d : Y.below (Y.cell c) => Y.grade d.1) (rowsY.E c) (fun d => labY d.1)
        ⟨c, GradedLe.refl _⟩ (fun d => d.2.2) (fun d => hY d.1) (hYres.locality c) hj
        (fun d => (inVals_labY labX labY d.1).keyed _)
      have key := base.reindex (reqBelowEquiv (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot
        c).symm
      refine transformsTo_congr ?_ ?_ ?_ key
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        change Y.grade ((reqBelowEquiv hvX hvY hroot c).symm (reqBelowEquiv hvX hvY hroot c d')).1 =
          (requestInventory X Y e Rp hR hRA hRB).grade (reqCell hvX hvY hroot d'.1)
        rw [Equiv.symm_apply_apply, grade_reqCell]
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        change rowsY.E c ((reqBelowEquiv hvX hvY hroot c).symm
          (reqBelowEquiv hvX hvY hroot c d')) = _
        rw [Equiv.symm_apply_apply]
        exact (mixedRows_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
          labX labY hX hY hfresh c d' _).symm
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        dsimp only [Function.comp]
        have h1 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          (CellScheme.below.incl ⟨reqCell hvX hvY hroot c, hs⟩ (reqBelowEquiv hvX hvY hroot c d'))
        have h2 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          ⟨reqCell hvX hvY hroot c, hs⟩
        refine Eq.trans ?_ (congrArg₂ min h1 h2).symm
        change min (recode _ _ (labY ((reqBelowEquiv hvX hvY hroot c).symm
            (reqBelowEquiv hvX hvY hroot c d')).1)) (recode _ _ (labY c)) =
          min (recode _ _ (fullLabel labX labY (reqCell hvX hvY hroot d'.1)))
            (recode _ _ (fullLabel labX labY (reqCell hvX hvY hroot c)))
        rw [Equiv.symm_apply_apply, fullLabel_reqCell hvX hvY hroot labX labY _ (hfresh _),
          fullLabel_reqCell hvX hvY hroot labX labY _ (hfresh _)]
    · -- a lower remaining-index cell: the cross-grade recoding transformation
      have hjj' : b'.1.2 ≤ b.1.2 := by
        have := grade_le_of_below_outside' hs
        rwa [grade_outsideCell] at this
      have hρ : SelfVis b'.1.2 (recode b.1.2 (faceVals labX labY)
          (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY (outsideCell b'))) := by
        refine recode_selfVis _ _ ?_ hjj'
        have := fullLabel_selfVis (hR := hR) (hRA := hRA) (hRB := hRB) labX labY hX hY
          (outsideCell b')
        rwa [grade_outsideCell] at this
      have base := crossGrade_transformsTo_capped b.1.2 b'.1.2 (faceVals labX labY)
        (fun d : (requestInventory X Y e Rp hR hRA hRB).below
          ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b')) =>
            (requestInventory X Y e Rp hR hRA hRB).grade d.1) hjj'
        (fun d => grade_le_of_below_outside d)
        (fun d => fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d.1)
        (fun d => inVals_fullLabel labX labY d.1) hρ
      refine transformsTo_congr rfl ?_ ?_ base
      · funext d
        simp only [mixedRows_outside]
        rfl
      · funext d
        have h1 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          (CellScheme.below.incl ⟨outsideCell b', hs⟩ d)
        have h2 := mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b
          ⟨outsideCell b', hs⟩
        exact (congrArg₂ min h1 h2).symm
  availability Sig Xi₀ hs' hg' := by
    obtain ⟨Xi, hXi, hle⟩ := fullLabel_availability labX labY hn hXres.availability
      hYres.availability Sig.1 Xi₀.1 hs' hg'
    have hmem : GradedLe ((requestInventory X Y e Rp hR hRA hRB).cell Xi)
        ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) := by
      rw [hXi]; exact Xi₀.2
    refine ⟨⟨Xi, hmem⟩, hXi, ?_⟩
    calc _ = recode b.1.2 (faceVals labX labY) (fullLabel labX labY Sig.1) :=
          mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b Sig
      _ ≤ recode b.1.2 (faceVals labX labY) (fullLabel labX labY Xi) :=
          recode_le _ _ ((inVals_fullLabel labX labY _).keyed _)
            ((inVals_fullLabel labX labY _).keyed _) hle
      _ = _ := (mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b ⟨Xi, hmem⟩).symm

/-! ### The assembled properties -/

include hXres hYres hXcons hYcons hfresh hn in
/-- **The mixed rows are consistent** (Def. 2.5.12). -/
theorem mixedRows_isConsistent :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
      hY).IsConsistent := by
  intro Sig
  rcases inv_cases hvX hvY hroot Sig with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · exact mixedRows_respects_old hvX hvY hroot rowsX rowsY labX labY hX hY hXcons i
  · exact mixedRows_respects_req hvX hvY hroot rowsX rowsY labX labY hX hY hfresh hYcons c
  · exact mixedRows_respects_outside hvX hvY hroot rowsX rowsY labX labY hX hY hfresh hXres hYres
      hn b

include hfresh in
/-- **The mixed rows are coded.** -/
theorem mixedRows_isCoded (hXc : rowsX.IsCoded) (hYc : rowsY.IsCoded) :
    (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
      hY).IsCoded := by
  intro Sig d
  rcases inv_cases hvX hvY hroot Sig with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
  · obtain ⟨d', rfl⟩ := (oldBelowEquiv (Y := Y) (e := e) (hR := hR) (hRA := hRA) (hRB := hRB)
      i).surjective d
    rw [grade_castAdd]
    exact (mixedRows_old (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY
      hX hY i d' _) ▸ hXc i d'
  · obtain ⟨d', rfl⟩ := (reqBelowEquiv (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot
      c).surjective d
    rw [grade_reqCell]
    exact (mixedRows_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX
      labY hX hY hfresh c d' _) ▸ hYc c d'
  · rw [mixedRows_outside, grade_outsideCell]
    exact recode_isCoded _ _ _

include hXres hYres hfresh hn in
/-- **The full labelling respects the mixed rows**: it keeps the context's and the request's
labels literally, decodes every recoded row, and is available. -/
theorem fullLabel_respects :
    RespectsSemantics (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
      labX labY hX hY) (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY) where
  orderly d := (fullLabel_selfVis labX labY hX hY d).symm
  locality Sig := by
    rcases inv_cases hvX hvY hroot Sig with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b, rfl⟩
    · have key := (hXres.locality i).reindex (oldBelowEquiv (Y := Y) (e := e) (hR := hR)
        (hRA := hRA) (hRB := hRB) i).symm
      refine transformsTo_congr ?_ ?_ ?_ key
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        change X.grade ((oldBelowEquiv i).symm (oldBelowEquiv i d')).1 =
          (requestInventory X Y e Rp hR hRA hRB).grade (Fin.castAdd _ d'.1)
        rw [Equiv.symm_apply_apply, grade_castAdd]
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        change rowsX.E i ((oldBelowEquiv i).symm (oldBelowEquiv i d')) = _
        rw [Equiv.symm_apply_apply]
        exact (mixedRows_old (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX
          labY hX hY i d' _).symm
      · funext d
        obtain ⟨d', rfl⟩ := (oldBelowEquiv i).surjective d
        dsimp only [Function.comp]
        change min (labX ((oldBelowEquiv i).symm (oldBelowEquiv i d')).1) (labX i) =
          min (fullLabel labX labY (Fin.castAdd _ d'.1)) (fullLabel labX labY (Fin.castAdd _ i))
        rw [Equiv.symm_apply_apply, fullLabel_castAdd, fullLabel_castAdd]
    · have key := (hYres.locality c).reindex (reqBelowEquiv (hR := hR) (hRA := hRA) (hRB := hRB)
        hvX hvY hroot c).symm
      refine transformsTo_congr ?_ ?_ ?_ key
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        change Y.grade ((reqBelowEquiv hvX hvY hroot c).symm (reqBelowEquiv hvX hvY hroot c d')).1 =
          (requestInventory X Y e Rp hR hRA hRB).grade (reqCell hvX hvY hroot d'.1)
        rw [Equiv.symm_apply_apply, grade_reqCell]
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        change rowsY.E c ((reqBelowEquiv hvX hvY hroot c).symm
          (reqBelowEquiv hvX hvY hroot c d')) = _
        rw [Equiv.symm_apply_apply]
        exact (mixedRows_reqCell (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY
          labX labY hX hY hfresh c d' _).symm
      · funext d
        obtain ⟨d', rfl⟩ := (reqBelowEquiv hvX hvY hroot c).surjective d
        dsimp only [Function.comp]
        change min (labY ((reqBelowEquiv hvX hvY hroot c).symm
            (reqBelowEquiv hvX hvY hroot c d')).1) (labY c) =
          min (fullLabel labX labY (reqCell hvX hvY hroot d'.1))
            (fullLabel labX labY (reqCell hvX hvY hroot c))
        rw [Equiv.symm_apply_apply, fullLabel_reqCell hvX hvY hroot labX labY _ (hfresh _),
          fullLabel_reqCell hvX hvY hroot labX labY _ (hfresh _)]
    · have hρ : SelfVis b.1.2 (fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY
          (outsideCell b)) := by
        have := fullLabel_selfVis (hR := hR) (hRA := hRA) (hRB := hRB) labX labY hX hY
          (outsideCell b)
        rwa [grade_outsideCell] at this
      have base := recode_transformsTo b.1.2 (faceVals labX labY)
        (fun d : (requestInventory X Y e Rp hR hRA hRB).below
          ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) =>
            (requestInventory X Y e Rp hR hRA hRB).grade d.1)
        (fun d => grade_le_of_below_outside d)
        (fun d => fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d.1)
        (fun d => inVals_fullLabel labX labY d.1) hρ
      refine transformsTo_congr rfl ?_ rfl base
      funext d
      simp only [mixedRows_outside]
  availability := fullLabel_availability labX labY hn hXres.availability hYres.availability

/-! ### The first bountifulness obligation: what the recoded rows force -/

/-- A cell at the graded index of a remaining-index cell is that cell. -/
theorem eq_outsideCell_of_cell_eq {b : OutsideIndex e Rp}
    {Xi : Cell (requestInventory X Y e Rp hR hRA hRB)}
    (h : (requestInventory X Y e Rp hR hRA hRB).cell Xi =
      (requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) :
    Xi = outsideCell b := by
  have hs : (requestInventory X Y e Rp hR hRA hRB).scope Xi =
      (requestInventory X Y e Rp hR hRA hRB).scope (outsideCell b) := congrArg Prod.fst h
  rcases requestInventory_cases Xi with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨b', rfl⟩
  · exfalso
    have hlast : Fin.last m ∈ (requestInventory X Y e Rp hR hRA hRB).scope (outsideCell b) := by
      rw [scope_outsideCell]; exact (Finset.mem_filter.mp b.2).2.1
    rw [← hs] at hlast
    unfold requestInventory at hlast
    rw [extendOneWith_scope_castAdd] at hlast
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hlast
    exact Fin.castSucc_ne_last x hx
  · exfalso
    apply scope_outsideCell_not_subset b
    rw [← hs]
    exact scope_freshCell_subset c
  · rw [cell_outsideCell, cell_outsideCell] at h
    rw [Subtype.ext h]

include hX hY in
/-- **The recoded controller identifies what the full labelling identifies**: under any
respecting labelling of the lower set of a remaining-index cell, two same-grade cells below it
with equal full labels carry equal labels capped at the cell. -/
theorem capped_eq_of_fullLabel_eq (b : OutsideIndex e Rp)
    {q' : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)) → ExtOrd}
    (hq : RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot
      rowsX rowsY labX labY hX hY) ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))
      q')
    (d₁ d₂ : (requestInventory X Y e Rp hR hRA hRB).below
      ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)))
    (hF : fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d₁.1 =
      fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d₂.1)
    (hgr : (requestInventory X Y e Rp hR hRA hRB).grade d₁.1 =
      (requestInventory X Y e Rp hR hRA hRB).grade d₂.1) :
    min (q' d₁) (q' ⟨outsideCell b, GradedLe.refl _⟩) =
      min (q' d₂) (q' ⟨outsideCell b, GradedLe.refl _⟩) := by
  have hrow : (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX
      labY hX hY).E (outsideCell b) d₁ =
      (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
        hY).E (outsideCell b) d₂ := by
    rw [mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b d₁,
      mixedRows_outside hvX hvY hroot rowsX rowsY labX labY hX hY b d₂, hF]
  exact hq.capped_eq_of_row_eq' ⟨outsideCell b, GradedLe.refl _⟩ d₁ d₂ hrow hgr

/-- The constantly-`⊥` labelling respects every semantics on every lower set. -/
theorem respectsBelow_bot {ι₀ : Type*} [DecidableEq ι₀] {A₀ : Finset ι₀} {D₀ : CellScheme A₀}
    (sem : Semantics D₀) (BJ : Finset ι₀ × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => (⊥ : ExtOrd)) :=
  RespectsSemanticsBelow.bot sem BJ

include hX hY in
/-- **Bottom-cap completion fails for a separating lawful section**: if some respecting
labelling `p` of a lower set below a remaining-index cell separates two same-grade cells that
the full labelling identifies, strictly below its own value at a cell of the remaining cell's
index, then the mixed rows are **not bountiful** — the bottom-cap instance from that lower set
into the remaining cell's has no completion.  This is the first bountifulness obligation, and
the recoded rows fail it exactly when the inherited rows admit such a section. -/
theorem not_bountiful_of_separating (b : OutsideIndex e Rp) {CI : Finset (Fin (m + 1)) × ℕ}
    (hCI : CI ∈ Plan.gradedPlan (requestInventory X Y e Rp hR hRA hRB).plan)
    (hle : GradedLe CI ((requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b)))
    (hne : CI ≠ (requestInventory X Y e Rp hR hRA hRB).cell (outsideCell b))
    {p : (requestInventory X Y e Rp hR hRA hRB).below CI → ExtOrd}
    (hp : RespectsSemanticsBelow (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot
      rowsX rowsY labX labY hX hY) CI p)
    (d₁ d₂ cap : (requestInventory X Y e Rp hR hRA hRB).below CI)
    (hF : fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d₁.1 =
      fullLabel (hR := hR) (hRA := hRA) (hRB := hRB) labX labY d₂.1)
    (hgr : (requestInventory X Y e Rp hR hRA hRB).grade d₁.1 =
      (requestInventory X Y e Rp hR hRA hRB).grade d₂.1)
    (h12 : p d₁ < p d₂) (hcap : p d₁ < p cap)
    (hcs : (requestInventory X Y e Rp hR hRA hRB).scope cap.1 ⊆
      (requestInventory X Y e Rp hR hRA hRB).scope (outsideCell b))
    (hcg : (requestInventory X Y e Rp hR hRA hRB).grade cap.1 =
      (requestInventory X Y e Rp hR hRA hRB).grade (outsideCell b)) :
    ¬ (mixedRows (hR := hR) (hRA := hRA) (hRB := hRB) hvX hvY hroot rowsX rowsY labX labY hX
      hY).IsBountiful := by
  intro hb
  obtain ⟨q', hq', -, hres⟩ := hb CI _ hCI ((requestInventory X Y e Rp hR hRA hRB).cell_mem _)
    hle hne p (fun _ => ⊥) ⊥ hp (respectsBelow_bot _ _) (extVisibilityReplace_bot _ _)
    (fun _ => by rw [min_eq_right bot_le, min_eq_right bot_le])
  have hcapped := capped_eq_of_fullLabel_eq hvX hvY hroot rowsX rowsY labX labY hX hY b hq'
    (CellScheme.below.mono hle d₁) (CellScheme.below.mono hle d₂) hF hgr
  rw [hres, hres] at hcapped
  obtain ⟨Xi, hXi, hXile⟩ := hq'.availability (CellScheme.below.mono hle cap)
    ⟨outsideCell b, GradedLe.refl _⟩ hcs hcg
  have hXi' : Xi = ⟨outsideCell b, GradedLe.refl _⟩ := Subtype.ext (eq_outsideCell_of_cell_eq hXi)
  rw [hXi', hres] at hXile
  have hlt : p d₁ < q' ⟨outsideCell b, GradedLe.refl _⟩ := hcap.trans_le hXile
  rw [min_eq_left hlt.le] at hcapped
  exact absurd hcapped (ne_of_lt (lt_min h12 hlt))

end Inventory

end VaughtConjecture.Knight
