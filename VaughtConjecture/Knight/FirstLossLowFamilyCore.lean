/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FirstLossAcquisitionCore
public import VaughtConjecture.Knight.LowOnlyFibres

/-! # From the first-loss acquisition to the gate-free LOW family

The literal adapter from `FirstLossAcquisition` to KVC's `LowOnly.Family`: the two actual legal
cofaces of the finite-characteristic receiver, their literal common root, the actual owner and
low source, every strict-gap hypothesis, and the admissibility of the actual pair.

* **The private face** is the acquired cover's type restricted to the larger first-loss face
  `g ⌢ c`; **the donor** is the enlarged donor over the smaller face `g`
  (`exists_enlarged_donor`), whose tops have grade at most `K`.  Both are cofaces of the type of
  the smaller face along `Fin.castSuccEmb`.
* **The common root** (`commonRoot_of_cofaces`): two cofaces of one type have a literal common
  root along the initial face — the identification is `CappedDonor.commonFace`, and its grade,
  scope and row identities are derived from the two literal restrictions (rows transport along
  the scheme equalities, `rows_castCell`).  The actual labellings agree on the root
  (`shared_of_cofaces`).
* **The source gap**: the surviving full-scope grade-`K` owner and the lost top, read as cells
  of the private face; the strict gap at the owner is the acquired gap, since the restricted
  rows are the cover's rows.
* **The family**: the donor labelling, its top-grade bound, the root inside the owner's scope,
  and the strict gaps at every root top (retained tops of the smaller face lie below the owner,
  and the acquired gap covers them).
* **Admissibility of the actual pair**: for every cutoff `b` visible at `min j K`, the state
  `(donor labels, private labels, b)` is `Admissible j` — both labellings are lawful through
  every grade, agree on the root, are `1`-visible on future fields (orderliness), and LOW's
  conclusion is met since every designated donor top is literally `⊤`.  Higher-grade proper root
  values are retained literally; nothing is truncated to grade `K`.

No physical receiver is used. -/

@[expose] public section

namespace VaughtConjecture.Knight.FirstLossLowFamily

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace
  AmalgamationPlan CappedDonor

universe w

/-! ## Transport lemmas -/

/-- Rows transport along an equality of schemes. -/
theorem rows_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) (Sig : Cell X.scheme)
    (d : X.scheme.below (X.scheme.cell Sig))
    (hd : GradedLe (Y.scheme.cell (SemScheme.castCell h d.1))
      (Y.scheme.cell (SemScheme.castCell h Sig))) :
    Y.rows.E (SemScheme.castCell h Sig) ⟨SemScheme.castCell h d.1, hd⟩ = X.rows.E Sig d := by
  subst h; rfl

theorem gradedLe_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) {c c' : Cell X.scheme}
    (hc : GradedLe (X.scheme.cell c) (X.scheme.cell c')) :
    GradedLe (Y.scheme.cell (SemScheme.castCell h c))
      (Y.scheme.cell (SemScheme.castCell h c')) := by
  subst h; exact hc

/-- The scope of the image of a transported cell of a literal restriction. -/
theorem scope_toCell_castCell {m n : ℕ} {X : SemScheme n} {f : Fin m ↪ Fin n}
    {hv : Finset.univ.image f ∈ X.scheme.plan} {Z : SemScheme m}
    (h : X.restrictFace f hv = Z) (c : Cell Z.scheme) :
    X.scheme.scope (toCell X.scheme f hv (SemScheme.castCell h.symm c)) =
      (Z.scheme.scope c).image f := by
  subst h
  exact (image_scope_restrictFace X.scheme f hv c).symm

/-- A row entry depends only on the owner and the underlying cell of the argument. -/
theorem E_congr {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) {Sig Sig' : Cell D} (h : Sig = Sig') (d : D.below (D.cell Sig))
    (d' : D.below (D.cell Sig')) (hd : d.1 = d'.1) : sem.E Sig d = sem.E Sig' d' := by
  subst h
  congr 1
  exact Subtype.ext hd

/-! ## The literal common root of two cofaces -/

section CommonRoot

variable {α : Ordinal.{0}} {k : ℕ} {pR : S α k} {P C : S α (k + 1)} (hP : IsCoface pR P)
  (hC : IsCoface pR C)

/-- The root face on `k + 1` points. -/
abbrev rootFace (k : ℕ) : Finset (Fin (k + 1)) := Finset.univ.image Fin.castSuccEmb

/-- The identification of the two copies of the root. -/
noncomputable def faceOf :
    P.scheme.scheme.below (rootFace k, (rootFace k).card) ≃
      C.scheme.scheme.below (rootFace k, (rootFace k).card) :=
  commonFace Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card

/-- The root cell of a root-face cell of the donor. -/
noncomputable def rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    Cell pR.scheme.scheme :=
  SemScheme.castCell hP.extendsDomain.restrict
    ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm a).1

theorem toCell_rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
      (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)) = a.1 :=
  toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
    (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl a

theorem faceOf_val (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    (faceOf hP hC a).1 = toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
      (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a)) :=
  commonFace_val Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card a

theorem scopeP (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    P.scheme.scheme.scope a.1 =
      (pR.scheme.scheme.scope (rootCell hP a)).image Fin.castSuccEmb := by
  rw [← toCell_rootCell hP a]
  exact scope_toCell_castCell hP.extendsDomain.restrict (rootCell hP a)

theorem scopeC (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    C.scheme.scheme.scope (faceOf hP hC a).1 =
      (pR.scheme.scheme.scope (rootCell hP a)).image Fin.castSuccEmb := by
  rw [faceOf_val hP hC a]
  exact scope_toCell_castCell hC.extendsDomain.restrict (rootCell hP a)

/-- The rows of two cofaces agree on the root, through the identification. -/
theorem row_of_cofaces (a : P.scheme.scheme.below (rootFace k, (rootFace k).card))
    (d : P.scheme.scheme.below (P.scheme.scheme.cell a.1))
    (hd : GradedLe (C.scheme.scheme.cell (faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1)
      (C.scheme.scheme.cell (faceOf hP hC a).1)) :
    P.scheme.rows.E a.1 d =
      C.scheme.rows.E (faceOf hP hC a).1 ⟨(faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1, hd⟩ := by
  have hda : P.scheme.scheme.scope d.1 ⊆ rootFace k := d.2.1.trans a.2.1
  obtain ⟨d'', hd''⟩ := exists_toCell_eq (D := P.scheme.scheme) (f := Fin.castSuccEmb)
    (hr := hP.extendsDomain.visible) hda
  -- the argument as a cell of the restricted donor, below the root cell
  have hle : GradedLe (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb
      hP.extendsDomain.visible d''))
      (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
        (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)))) := by
    rw [hd'', toCell_rootCell hP a]
    exact d.2
  have hle' := (gradedLe_restrictFace_iff P.scheme.scheme Fin.castSuccEmb
    hP.extendsDomain.visible).mpr hle
  let dR : pR.scheme.scheme.below (pR.scheme.scheme.cell (rootCell hP a)) :=
    ⟨SemScheme.castCell hP.extendsDomain.restrict d'',
      gradedLe_castCell hP.extendsDomain.restrict hle'⟩
  -- the donor side, read through the root
  have hL : P.scheme.rows.E a.1 d = pR.scheme.rows.E (rootCell hP a) dR := by
    have e1 : P.scheme.rows.E a.1 d = P.scheme.rows.E (toCell P.scheme.scheme Fin.castSuccEmb
        hP.extendsDomain.visible (SemScheme.castCell hP.extendsDomain.restrict.symm
          (rootCell hP a)))
        ⟨toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible d'', hle⟩ :=
      E_congr P.scheme.rows (toCell_rootCell hP a).symm d _ hd''.symm
    have e2 : (P.scheme.restrictFace Fin.castSuccEmb hP.extendsDomain.visible).rows.E
        (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)) ⟨d'', hle'⟩ =
        pR.scheme.rows.E (rootCell hP a) dR :=
      (rows_castCell hP.extendsDomain.restrict _ ⟨d'', hle'⟩
        (gradedLe_castCell hP.extendsDomain.restrict hle')).symm
    exact e1.trans e2
  -- the private side, read through the root
  have hd3 : ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm
      ⟨d.1, d.2.trans a.2⟩).1 = d'' := by
    apply toCell_injective P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
    rw [hd'']
    exact toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
      (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl _
  have hrc : rootCell hP ⟨d.1, d.2.trans a.2⟩ =
      SemScheme.castCell hP.extendsDomain.restrict d'' := by
    unfold rootCell
    rw [hd3]
  have hleC : GradedLe ((C.scheme.restrictFace Fin.castSuccEmb hC.extendsDomain.visible).scheme.cell
      (SemScheme.castCell hC.extendsDomain.restrict.symm dR.1))
      ((C.scheme.restrictFace Fin.castSuccEmb hC.extendsDomain.visible).scheme.cell
        (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))) :=
    gradedLe_castCell hC.extendsDomain.restrict.symm dR.2
  have hR : C.scheme.rows.E (faceOf hP hC a).1 ⟨(faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1, hd⟩ =
      pR.scheme.rows.E (rootCell hP a) dR := by
    have e1 : C.scheme.rows.E (faceOf hP hC a).1 ⟨(faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1, hd⟩ =
        C.scheme.rows.E (toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
          (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a)))
          ⟨toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
            (SemScheme.castCell hC.extendsDomain.restrict.symm dR.1),
            gradedLe_of_restrictFace C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
              hleC⟩ :=
      E_congr C.scheme.rows (faceOf_val hP hC a) _ _ (by
        rw [faceOf_val hP hC ⟨d.1, d.2.trans a.2⟩, hrc])
    have e2 : (C.scheme.restrictFace Fin.castSuccEmb hC.extendsDomain.visible).rows.E
        (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))
        ⟨SemScheme.castCell hC.extendsDomain.restrict.symm dR.1, hleC⟩ =
        pR.scheme.rows.E (rootCell hP a) dR :=
      rows_castCell hC.extendsDomain.restrict.symm (rootCell hP a) dR hleC
    exact e1.trans e2
  exact hL.trans hR.symm

/-- Two cofaces of one type have a literal common root along the initial face. -/
noncomputable def commonRoot_of_cofaces : LowOnly.CommonRoot P.scheme C.scheme where
  A := rootFace k
  B := rootFace k
  A_mem := hP.extendsDomain.visible
  B_mem := hC.extendsDomain.visible
  card := rfl
  face := faceOf hP hC
  grade a := (commonFace_grade Fin.castSuccEmb hP.extendsDomain.visible
    hP.extendsDomain.restrict Fin.castSuccEmb hC.extendsDomain.visible
    hC.extendsDomain.restrict (rootFace k).card a).symm
  scope a b := by rw [scopeP hP a, scopeP hP b, scopeC hP hC a, scopeC hP hC b]
  row := row_of_cofaces hP hC

/-- The labels of two cofaces agree on the common root. -/
theorem shared_of_cofaces : (commonRoot_of_cofaces hP hC).Shared P.label C.label := by
  intro a
  change P.label a.1 = C.label (faceOf hP hC a).1
  have hPl := (typeMap_eq_some_iff_labels Fin.castSuccEmb P pR hP.extendsDomain.visible
    hP.extendsDomain.restrict).mp hP
    (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a))
  have hCl := (typeMap_eq_some_iff_labels Fin.castSuccEmb C pR hC.extendsDomain.visible
    hC.extendsDomain.restrict).mp hC
    (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))
  rw [← toCell_rootCell hP a, faceOf_val hP hC a]
  exact hPl.trans hCl.symm

end CommonRoot

/-! ## The family from the first-loss acquisition -/

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- **The gate-free LOW family from the first-loss acquisition.**  In a model of characteristic
arity `K > 0` without globally rigid cores, over any actual root `t ↦ p` and any legal donor
coface `q` of `p` with tops of grade at most `K`: an actual private context `u ↦ CT` containing
the root, an enlarged donor `Q'` restricting to `q` along the extended root embedding, both
cofaces of one type `pR` along `Fin.castSuccEmb`, and KVC's family `F` on their schemes with the
donor labelling `Q'.label`, the root along the initial face, the owner and low source both `⊤`
in the actual private labelling, and every pair `(Q'.label, CT.label, b)` admissible at every
grade for every cutoff `b` visible at `min j K`. -/
theorem exists_lowOnlyFamily_of_tail (hcons : R.IsExactParentConsistent) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K) (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore R B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : R.eval t = some p) (q : S α.1 (n + 1))
    (hq : IsCoface p q) (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ (k : ℕ) (u : Fin (k + 1) ↪ M) (CT : S α.1 (k + 1)) (e : Fin n ↪ Fin k)
      (pR : S α.1 k) (Q' : S α.1 (k + 1)),
      R.eval u = some CT ∧ (e.trans Fin.castSuccEmb).trans u = t ∧
      IsCoface pR CT ∧ IsCoface pR Q' ∧ typeMap (FixedHeight.extendFace e) Q' = some q ∧
      ∃ F : LowOnly.Family Q'.scheme CT.scheme K,
        F.p = Q'.label ∧ F.root.A = rootFace k ∧ F.root.B = rootFace k ∧
        CT.label F.gap.c = ⊤ ∧ CT.label F.gap.r.1 = ⊤ ∧
        ∀ (j : ℕ) (b : ExtOrd), SelfVis (min j K) b →
          F.Admissible j ⟨Q'.label, CT.label, b⟩ := by
  obtain ⟨m, Cov, Q, hQ, hQK, k, g, c, hc, e, het, hvg, hvg', H, hH, hfull, x, o, hxs, hxtop, hxH,
    hoH, hocell, hxo, hgap⟩ := FirstLossAcquisition.first_loss_of_tail hcons hcoin hKpos hres t p hp
  set g₁ : Fin (k + 1) ↪ Fin m := snoc g c hc with hg₁def
  have hg : Fin.castSuccEmb.trans g₁ = g := castSuccEmb_trans_snoc g c hc
  -- the two face types of the cover: the smaller face `pR`, the larger face `CT`
  set pR : S α.1 k := Q.restrictFace g hvg with hpRdef
  set CT : S α.1 (k + 1) := Q.restrictFace g₁ hvg' with hCTdef
  have hpR : typeMap g Q = some pR := typeMap_eq_some g Q hvg
  have hCT : typeMap g₁ Q = some CT := typeMap_eq_some g₁ Q hvg'
  have hcofCT : IsCoface pR CT := by
    change typeMap Fin.castSuccEmb CT = some pR
    rw [typeMap_trans Fin.castSuccEmb g₁ Q CT hCT, hg]
    exact hpR
  -- the root type is the restriction of `pR` along `e`
  have hep : typeMap e pR = some p := by
    rw [typeMap_trans e g Q pR hpR]
    have h := hcons Cov Q (e.trans g) hQ
    rw [het, hp] at h
    exact h.symm
  have hRtops : ∀ d, pR.label d = ⊤ → pR.scheme.scheme.grade d ≤ K := fun d hd =>
    (FirstLossAcquisition.face_top_grade_le hpR d hd).trans_eq hQK
  -- the enlarged donor
  obtain ⟨Q', hcofQ', hQ'e, hQ'K⟩ :=
    FirstLossAcquisition.exists_enlarged_donor pR e p hep hRtops q hq hqK
  -- the owner and the low source as cells of the private face
  have hos : Q.scheme.scheme.scope o = Finset.univ.image g₁ := congrArg Prod.fst hocell
  have hog : Q.scheme.scheme.grade o = K := congrArg Prod.snd hocell
  obtain ⟨oC, hoC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg')
    (Finset.subset_of_eq hos)
  obtain ⟨xC, hxC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg') hxs
  have hxoC : GradedLe (CT.scheme.scheme.cell xC) (CT.scheme.scheme.cell oC) :=
    (gradedLe_restrictFace_iff Q.scheme.scheme g₁ hvg').mpr (by rw [hoC, hxC]; exact hxo)
  have hoCg : CT.scheme.scheme.grade oC = K := by
    change Q.scheme.scheme.grade (toCell Q.scheme.scheme g₁ hvg' oC) = K
    rw [hoC]; exact hog
  have hb1 := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' hxoC
  have hb2 := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg'
    (GradedLe.refl (CT.scheme.scheme.cell oC))
  let gap : LowOnly.SourceGap CT.scheme K :=
    { c := oC
      c_grade := hoCg
      r := ⟨xC, hxoC⟩
      gap_c := by
        have h := hgap ⟨o, GradedLe.refl _⟩ hoH
        change extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
          ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K <
          Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
            ⟨toCell Q.scheme.scheme g₁ hvg' oC, hb2⟩
        calc extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
              ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K
            = extVisibilityReplace (Q.scheme.rows.E o ⟨x, hxo⟩) K K :=
              congrArg (fun z => extVisibilityReplace z K K)
                (E_congr Q.scheme.rows hoC _ _ hxC)
          _ < Q.scheme.rows.E o ⟨o, GradedLe.refl _⟩ := h
          _ = Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
              ⟨toCell Q.scheme.scheme g₁ hvg' oC, hb2⟩ :=
              (E_congr Q.scheme.rows hoC _ _ hoC).symm }
  -- the common root and the family
  let root := commonRoot_of_cofaces hcofQ' hcofCT
  have hshared : root.Shared Q'.label CT.label := shared_of_cofaces hcofQ' hcofCT
  have hroot_sub : root.B ⊆ CT.scheme.scheme.scope gap.c := by
    intro y _
    change y ∈ Finset.univ.filter (fun j => g₁ j ∈ Q.scheme.scheme.scope
      (toCell Q.scheme.scheme g₁ hvg' oC))
    rw [Finset.mem_filter, hoC, hos]
    exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  -- a root-face cell of the private face, as a cell of the cover, has scope inside `g`
  have hface_scope : ∀ a : Q'.scheme.scheme.below (rootFace k, (rootFace k).card),
      Q.scheme.scheme.scope (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) ⊆
        Finset.univ.image g := by
    intro a
    have him := image_scope_restrictFace Q.scheme.scheme g₁ hvg' (root.face a).1
    rw [← him]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzB : z ∈ rootFace k := (root.face a).2.1 hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzB
    rw [← hg]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hgg₁ : Finset.univ.image g ⊆ Finset.univ.image g₁ := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [← snoc_apply_castSucc g c hc i]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let F : LowOnly.Family Q'.scheme CT.scheme K :=
    { root := root
      gap := gap
      p := Q'.label
      p_lawful := Q'.respects
      top_grade := hQ'K
      root_sub := hroot_sub
      root_gap := by
        intro a ht
        -- the root top is a retained top of the smaller face, below the owner
        have hlab : Q.label (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) = ⊤ := by
          change CT.label (root.face a).1 = ⊤
          rw [← hshared a]
          exact ht
        have hmem : toCell Q.scheme.scheme g₁ hvg' (root.face a).1 ∈ H :=
          hfull _ (hface_scope a) hlab
        have hbelow : GradedLe (Q.scheme.scheme.cell (toCell Q.scheme.scheme g₁ hvg'
            (root.face a).1)) (Q.scheme.scheme.cell o) := by
          rw [hocell]
          refine ⟨(hface_scope a).trans hgg₁, ?_⟩
          change Q.scheme.scheme.grade _ ≤ K
          rw [← hQK]
          exact grade_le_topGrade_of_top hlab
        have h := hgap ⟨_, hbelow⟩ hmem
        have hb3 : GradedLe (CT.scheme.scheme.cell (root.face a).1) (CT.scheme.scheme.cell oC) :=
          ⟨(root.face a).2.1.trans hroot_sub,
            (root.grade a).symm.trans_le ((hQ'K a.1 ht).trans_eq hoCg.symm)⟩
        have hb3' := gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' hb3
        change extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
          ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K <
          Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
            ⟨toCell Q.scheme.scheme g₁ hvg' (root.face a).1, hb3'⟩
        calc extVisibilityReplace (Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
              ⟨toCell Q.scheme.scheme g₁ hvg' xC, hb1⟩) K K
            = extVisibilityReplace (Q.scheme.rows.E o ⟨x, hxo⟩) K K :=
              congrArg (fun z => extVisibilityReplace z K K)
                (E_congr Q.scheme.rows hoC _ _ hxC)
          _ < Q.scheme.rows.E o ⟨_, hbelow⟩ := h
          _ = Q.scheme.rows.E (toCell Q.scheme.scheme g₁ hvg' oC)
              ⟨toCell Q.scheme.scheme g₁ hvg' (root.face a).1, hb3'⟩ :=
              (E_congr Q.scheme.rows hoC _ _ rfl).symm }
  refine ⟨k, g₁.trans Cov, CT, e, pR, Q', ?_, ?_, hcofCT, hcofQ', hQ'e, F, rfl, rfl, rfl,
    ?_, ?_, ?_⟩
  · have h := hcons Cov Q g₁ hQ
    rw [h]
    exact hCT
  · rw [Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc Fin.castSuccEmb, hg,
      ← Function.Embedding.trans_assoc]
    exact het
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' oC) = ⊤
    rw [hoC]
    exact mem_topSet.mp (hH.subset hoH)
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' xC) = ⊤
    rw [hxC]
    exact hxtop
  · intro j b hb
    exact
      { lawfulP := Q'.respects.toBelow _
        lawfulC := CT.respects.toBelow _
        shared := hshared
        futureP := fun d _ => SelfVis.mono (show SelfVis (Q'.scheme.scheme.grade d) (Q'.label d)
          from (Q'.respects.orderly d).symm) (Q'.scheme.scheme.grade_pos d)
        futureC := fun d _ => SelfVis.mono (show SelfVis (CT.scheme.scheme.grade d) (CT.label d)
          from (CT.respects.orderly d).symm) (CT.scheme.scheme.grade_pos d)
        cutoff := hb
        low := fun _ _ d hd => by
          have hd' : Q'.label d = ⊤ := hd
          exact le_top.trans_eq hd'.symm }

end VaughtConjecture.Knight.FirstLossLowFamily
