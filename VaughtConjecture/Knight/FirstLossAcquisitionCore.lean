/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopSupportRigidCoreCap
public import VaughtConjecture.Knight.TopGradeStableCore
public import VaughtConjecture.Knight.ExpansionUniqueness
public import VaughtConjecture.Knight.CanonicalCoatomFiniteSupply
public import VaughtConjecture.Knight.CoatomFaceLift
public import VaughtConjecture.Knight.CappedDonorFace

/-! # The first-loss acquisition at finite characteristic

The acquisition step of the finite-characteristic residual receiver (newapproach17 new34 §1,
newapproach18 new40 §3), from the residual property of `TopSupportRigidCore`: in an exactly
consistent realization with a constant top-grade tail `K > 0`
and without globally rigid cores, over **any** actual root,

* the root is enlarged to an actual context `B⁺` past which every labelled cover has top grade
  exactly `K` (the explicit coinitial-tail hypothesis); `B⁺` carries a full-scope
  grade-`K` top;
* the residual property supplies an actual cover of `B⁺` with a proper admissible top support
  `H` containing every top of the `B⁺`-face;
* a maximal full visible face above the `B⁺`-face has an immediate nonfull superface,
  giving a **first loss**: consecutive visible
  faces `g ⊂ g ⌢ c` with every top of the `g`-face in `H` and some top `x` of the `g ⌢ c`-face
  outside `H` (`exists_adjacent_loss`, with the `exists_first_loss` compatibility wrapper);
* top availability from the protected grade-`K` top supplies a **surviving full-scope grade-`K`
  owner** `o ∈ H` of the larger face (completeness gives the full-scope grade-`K` index), and
  finite characteristic bounds the grade of the lost top by `K`, so it lies in `o`'s lower
  domain; source separation then gives the **strict source gaps**
  `evr (E o x) K K < E o a` for every retained top `a` below `o`, `o` itself and every top of
  the smaller face included (`first_loss`).

Separately, the donor is **enlarged over the larger root** by the constructed ordinary coatom
supplier and its pinned-coface consumer (`FixedHeight.pinnedCofaceLift` with
`CanonicalCoatomSupply.supply`), and the tops it introduces above grade `K` are **removed** by
the uniform lowering at a cap visible at the enlarged arity: the set of tops of grade at most
`K` is an admissible support (`admissible_gradeTrunc`, new41 §5), so the lowering is lawful,
retains the root literally and restricts to the original donor exactly (`exists_enlarged_donor`).

No physical receiver or realization covering is used or asserted. The tail is eventual
constancy above every starting context, not merely frequent occurrences. -/

@[expose] public section

namespace VaughtConjecture.Knight.FirstLossAcquisition

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace
  AmalgamationPlan

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-! ## Grade truncation of admissible supports -/

/-- **Grade truncation preserves admissibility**: the tops of grade at most `K` in an admissible
support form an admissible support (availability preserves the grade; an omitted top below a
retained owner of grade at most `K` has grade at most `K`, so it was already omitted). -/
theorem admissible_gradeTrunc {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {P : Cell D → ExtOrd} {H : Set (Cell D)} (hH : Admissible sem P H)
    (K : ℕ) : Admissible sem P {d | d ∈ H ∧ D.grade d ≤ K} where
  subset d hd := hH.subset hd.1
  available := by
    intro d hd Xi₀ hsc hgr
    obtain ⟨Xi, hcell, hXi⟩ := hH.available d hd.1 Xi₀ hsc hgr
    refine ⟨Xi, hcell, hXi, ?_⟩
    have hg : D.grade Xi = D.grade Xi₀ := congrArg Prod.snd hcell
    rw [hg, ← hgr]
    exact hd.2
  separated := by
    intro c hc a ha d hdtop hdH
    exact hH.separated c hc.1 a ha.1 d hdtop fun hdmem => hdH ⟨hdmem, d.2.2.trans hc.2⟩

/-! ## Adjacent loss at a maximal full visible face -/

/-- The support `H` is **full on the face `f`**: every top cell of the cover's type whose scope
lies in the face is in `H`. -/
def Full {m : ℕ} (Q : S α.1 m) (H : Set (Cell Q.scheme.scheme)) {n : ℕ} (f : Fin n ↪ Fin m) :
    Prop :=
  ∀ x : Cell Q.scheme.scheme, Q.scheme.scheme.scope x ⊆ Finset.univ.image f → Q.label x = ⊤ →
    x ∈ H

/-! A maximal full face gives the required adjacent loss without choosing a chain. -/

/-- An adjacent full/nonfull pair above the protected root, chosen by finite maximality. -/
theorem exists_adjacent_loss {α : LimitStage} {m n : ℕ} (Q : S α.1 m)
    {H : Set (Cell Q.scheme.scheme)} (hsub : H ⊆ topSet Q.label)
    (hne : H ≠ topSet Q.label) (f : Fin n ↪ Fin m)
    (hvis : Finset.univ.image f ∈ Q.scheme.scheme.plan) (hfull : Full Q H f) :
    ∃ (k : ℕ) (g : Fin k ↪ Fin m) (c : Fin m) (hc : c ∉ Set.range g) (e : Fin n ↪ Fin k),
      e.trans g = f ∧ Finset.univ.image g ∈ Q.scheme.scheme.plan ∧
      Finset.univ.image (snoc g c hc) ∈ Q.scheme.scheme.plan ∧
      Full Q H g ∧ ¬ Full Q H (snoc g c hc) := by
  classical
  let faces : Finset (Finset (Fin m)) := Finset.univ.filter fun B =>
    B ∈ Q.scheme.scheme.plan ∧ ∃ (k : ℕ) (g : Fin k ↪ Fin m) (e : Fin n ↪ Fin k),
      e.trans g = f ∧ Finset.univ.image g = B ∧ Full Q H g
  have hinit : Finset.univ.image f ∈ faces := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hvis, n, f, Function.Embedding.refl _,
      Function.Embedding.refl_trans _, rfl, hfull⟩
  obtain ⟨B, hB, hmax⟩ := faces.exists_max_image Finset.card ⟨_, hinit⟩
  obtain ⟨hBvis, k, g, e, he, hBimage, hBg⟩ := (Finset.mem_filter.mp hB).2
  subst B
  have hneB : Finset.univ.image g ≠ (Finset.univ : Finset (Fin m)) := by
    intro h
    apply hne
    apply Set.Subset.antisymm hsub
    intro d hd
    exact hBg d (by rw [h]; exact Finset.subset_univ _) hd
  obtain ⟨C, hC, hsubC, hcardC⟩ :=
    Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hBvis hneB
  obtain ⟨c, hcC, hcB⟩ := Finset.exists_of_ssubset hsubC
  have hc : c ∉ Set.range g := by
    rintro ⟨i, rfl⟩
    exact hcB (Finset.mem_image_of_mem g (Finset.mem_univ i))
  have hCeq : C = insert c (Finset.univ.image g) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hcC hsubC.subset
    · rw [Finset.card_insert_of_notMem hcB, hcardC]
  have himage : Finset.univ.image (snoc g c hc) = C := by
    rw [image_snoc_univ, hCeq]
  refine ⟨k, g, c, hc, e, he, hBvis, himage ▸ hC, hBg, ?_⟩
  intro hfullC
  have hCmem : C ∈ faces := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hC, k + 1, snoc g c hc, e.trans Fin.castSuccEmb,
      ?_, himage, hfullC⟩
    rw [Function.Embedding.trans_assoc, castSuccEmb_trans_snoc, he]
  have hle := hmax C hCmem
  omega


/-- **The first loss**: for a proper support `H` full on a visible face `f`, a saturated chain of
visible faces above `f` contains consecutive faces `g ⊂ g ⌢ c` with `H` full on `g` and not full
on `g ⌢ c`. -/
theorem exists_first_loss {m : ℕ} (Q : S α.1 m) {H : Set (Cell Q.scheme.scheme)}
    (hsub : H ⊆ topSet Q.label) (hne : H ≠ topSet Q.label) (r : ℕ) :
    ∀ {n : ℕ} (f : Fin n ↪ Fin m), n + r = m → Finset.univ.image f ∈ Q.scheme.scheme.plan →
      Full Q H f →
      ∃ (k : ℕ) (g : Fin k ↪ Fin m) (c : Fin m) (hc : c ∉ Set.range g) (e : Fin n ↪ Fin k),
        e.trans g = f ∧ Finset.univ.image g ∈ Q.scheme.scheme.plan ∧
        Finset.univ.image (snoc g c hc) ∈ Q.scheme.scheme.plan ∧
        Full Q H g ∧ ¬ Full Q H (snoc g c hc) := by
  intro n f _ hvis hfull
  exact exists_adjacent_loss Q hsub hne f hvis hfull

/-- The tops of a visible face of a type have grade at most the type's top grade. -/
theorem face_top_grade_le {m n : ℕ} {Q : S α.1 m} {f : Fin n ↪ Fin m} {p : S α.1 n}
    (h : typeMap f Q = some p) (d : Cell p.scheme.scheme) (hd : p.label d = ⊤) :
    p.scheme.scheme.grade d ≤ Q.topGrade := by
  have hv : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
    (typeMap_isSome_iff f Q).mp (by rw [h]; rfl)
  have hs : Q.scheme.restrictFace f hv = p.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some f Q hv).symm.trans h))
  have hl := (typeMap_eq_some_iff_labels f Q p hv hs).mp h (SemScheme.castCell hs.symm d)
  have htop : Q.label (toCell Q.scheme.scheme f hv (SemScheme.castCell hs.symm d)) = ⊤ := by
    rw [hl]; exact hd
  have hg : (Q.scheme.restrictFace f hv).scheme.grade (SemScheme.castCell hs.symm d) ≤
      Q.topGrade := grade_le_topGrade_of_top htop
  rw [CappedDonor.castCell_grade hs.symm d] at hg
  exact hg

/-! ## The first-loss acquisition -/

/-- **The first-loss acquisition.**  In a model of characteristic arity `K > 0` without globally
rigid cores, over any actual root `t ↦ p`: an actual cover `C ↦ Q` of top grade `K` containing
the root, an admissible top support `H` of `Q`, consecutive visible faces `g ⊂ g ⌢ c` of the
cover above the root, with `H` full on `g` and a lost top `x` of the larger face outside `H`, a
surviving full-scope grade-`K` owner `o ∈ H` of the larger face, the lost top in `o`'s lower
domain, and the strict source gaps `evr (E o x) K K < E o a` at every retained top `a` below
`o`. -/
theorem first_loss_of_tail (hcons : R.IsExactParentConsistent) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K)
    (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore R B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : R.eval t = some p) :
    ∃ (m : ℕ) (C : Fin m ↪ M) (Q : S α.1 m), R.eval C = some Q ∧ Q.topGrade = K ∧
      ∃ (k : ℕ) (g : Fin k ↪ Fin m) (c : Fin m) (hc : c ∉ Set.range g) (e : Fin n ↪ Fin k),
        (e.trans g).trans C = t ∧
        Finset.univ.image g ∈ Q.scheme.scheme.plan ∧
        Finset.univ.image (snoc g c hc) ∈ Q.scheme.scheme.plan ∧
        ∃ H : Set (Cell Q.scheme.scheme), Admissible Q.scheme.rows Q.label H ∧
          Full Q H g ∧
          ∃ (x o : Cell Q.scheme.scheme),
            Q.scheme.scheme.scope x ⊆ Finset.univ.image (snoc g c hc) ∧ Q.label x = ⊤ ∧
            x ∉ H ∧ o ∈ H ∧ Q.scheme.scheme.cell o = (Finset.univ.image (snoc g c hc), K) ∧
            ∃ hxo : GradedLe (Q.scheme.scheme.cell x) (Q.scheme.scheme.cell o),
              ∀ a : Q.scheme.scheme.below (Q.scheme.scheme.cell o), a.1 ∈ H →
                extVisibilityReplace (Q.scheme.rows.E o ⟨x, hxo⟩) K K < Q.scheme.rows.E o a := by
  -- the context past which every cover has top grade `K`
  let x₀ : LabelledExt R := ⟨n, t, p, hp⟩
  obtain ⟨y, hxy, hy⟩ := hcoin x₀
  have hyK : y.type.topGrade = K := hy (le_refl y)
  -- the flexible cover of that context
  obtain ⟨m, C, Q, hQ, e, he, H, hH, htops, hne⟩ :=
    TopSupportRigidCore.exists_flexible_cover_of_not_rigidCore (hres y.tuple)
  have htyp : typeMap e Q = some y.type := by
    have h := hcons C Q e hQ
    rw [he, y.eval_eq] at h
    exact h.symm
  have hyz : y ≤ (⟨m, C, Q, hQ⟩ : LabelledExt R) := ⟨e, he, htyp⟩
  have hQK : Q.topGrade = K := hy hyz
  have hve : Finset.univ.image e ∈ Q.scheme.scheme.plan :=
    (typeMap_isSome_iff e Q).mp (by rw [htyp]; rfl)
  have hse : Q.scheme.restrictFace e hve = y.type.scheme :=
    congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some e Q hve).symm.trans htyp))
  -- maximality supplies the adjacent loss above the context face
  obtain ⟨k, g, c, hc, e', he', hvg, hvg', hfull, hnot⟩ :=
    exists_adjacent_loss Q hH.subset hne e hve htops
  obtain ⟨f₀, hf₀, -⟩ := hxy
  refine ⟨m, C, Q, hQ, hQK, k, g, c, hc, f₀.trans e', ?_, hvg, hvg', H, hH, hfull, ?_⟩
  · rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
      ← Function.Embedding.trans_assoc e' g C, he', he]
    exact hf₀
  -- the lost top
  obtain ⟨x, hxs, hxtop, hxH⟩ : ∃ x : Cell Q.scheme.scheme,
      Q.scheme.scheme.scope x ⊆ Finset.univ.image (snoc g c hc) ∧ Q.label x = ⊤ ∧ x ∉ H := by
    by_contra hall
    apply hnot
    intro x hx hxt
    by_contra hxH
    exact hall ⟨x, hx, hxt, hxH⟩
  -- the protected grade-`K` top of the context, as a cell of the cover
  obtain ⟨Θ, hΘs, hΘg, hΘt⟩ := exists_topCell_of_topGrade_pos y.type (by rw [hyK]; exact hKpos)
  set a₀ : Cell Q.scheme.scheme :=
    toCell Q.scheme.scheme e hve (SemScheme.castCell hse.symm Θ) with ha₀def
  have ha₀t : Q.label a₀ = ⊤ := by
    rw [ha₀def, (typeMap_eq_some_iff_labels e Q y.type hve hse).mp htyp]
    exact hΘt
  have ha₀g : Q.scheme.scheme.grade a₀ = K := by
    have h : (Q.scheme.restrictFace e hve).scheme.grade (SemScheme.castCell hse.symm Θ) = K := by
      rw [CappedDonor.castCell_grade hse.symm Θ, hΘg, hyK]
    exact h
  have heg : Finset.univ.image e ⊆ Finset.univ.image g := by
    rw [← he']
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem g (Finset.mem_univ _)
  have hgg' : Finset.univ.image g ⊆ Finset.univ.image (snoc g c hc) := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [← snoc_apply_castSucc g c hc i]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have ha₀s : Q.scheme.scheme.scope a₀ ⊆ Finset.univ.image g :=
    (scope_toCell_subset (D := Q.scheme.scheme) e hve _).trans heg
  have ha₀H : a₀ ∈ H := hfull a₀ ha₀s ha₀t
  -- the full-scope grade-`K` index of the larger face is occupied, and a surviving owner there
  have hKcard : K ≤ (Finset.univ.image (snoc g c hc)).card := by
    rw [← ha₀g]
    exact (CellScheme.grade_le_card_scope _ a₀).trans
      (Finset.card_le_card (ha₀s.trans hgg'))
  obtain ⟨Xi₀, hXi₀⟩ := Q.scheme.complete (Finset.univ.image (snoc g c hc), K)
    (Plan.mem_gradedPlan.mpr ⟨hvg', hKpos, hKcard⟩)
  have hXi₀s : Q.scheme.scheme.scope Xi₀ = Finset.univ.image (snoc g c hc) :=
    congrArg Prod.fst hXi₀
  have hXi₀g : Q.scheme.scheme.grade Xi₀ = K := congrArg Prod.snd hXi₀
  obtain ⟨o, hocell, hoH⟩ := hH.available a₀ ha₀H Xi₀
    (by rw [hXi₀s]; exact ha₀s.trans hgg') (by rw [ha₀g, hXi₀g])
  have hocell' : Q.scheme.scheme.cell o = (Finset.univ.image (snoc g c hc), K) :=
    hocell.trans hXi₀
  -- the lost top lies in the owner's lower domain
  have hxo : GradedLe (Q.scheme.scheme.cell x) (Q.scheme.scheme.cell o) := by
    rw [hocell']
    refine ⟨hxs, ?_⟩
    change Q.scheme.scheme.grade x ≤ K
    rw [← hQK]
    exact grade_le_topGrade_of_top hxtop
  refine ⟨x, o, hxs, hxtop, hxH, hoH, hocell', hxo, fun a ha => ?_⟩
  have hog : Q.scheme.scheme.grade o = K := congrArg Prod.snd hocell'
  have hsep := hH.separated o hoH a ha ⟨x, hxo⟩ hxtop hxH
  rwa [hog] at hsep

/-! ## Donor enlargement over the larger root, with the high tops removed -/

/-- **Donor enlargement.**  A legal donor coface `q` of the public root `p`, with tops of grade at
most `K`, enlarges over a larger root `pR ⊇ p` (its tops of grade at most `K`) to a coface `Q`
of `pR` restricting to `q` along `extendFace e`, all of whose tops have grade at most `K`: the
pinned-coface consumer of the constructed coatom supplier enlarges the donor, and the uniform
lowering at a cap visible at the enlarged arity removes the tops above `K`, the support of tops
of grade at most `K` being admissible. -/
theorem exists_enlarged_donor {n k : ℕ} (pR : S α.1 k) (e : Fin n ↪ Fin k) (p : S α.1 n)
    (hep : typeMap e pR = some p) {K : ℕ}
    (hR : ∀ d, pR.label d = ⊤ → pR.scheme.scheme.grade d ≤ K)
    (q : S α.1 (n + 1)) (hq : IsCoface p q)
    (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ Q : S α.1 (k + 1), IsCoface pR Q ∧ typeMap (FixedHeight.extendFace e) Q = some q ∧
      ∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K := by
  have hnk : n ≤ k := by
    have := Fintype.card_le_of_embedding e
    simpa only [Fintype.card_fin] using this
  obtain ⟨Q₀, hQ₀cof, hQ₀e⟩ := FixedHeight.pinnedCofaceLift (CanonicalCoatomSupply.supply α.2)
    (k - n) (by omega) pR e p hep q hq
  -- the tops of grade at most `K`, an admissible support
  let HK : Set (Cell Q₀.scheme.scheme) :=
    {d | d ∈ topSet Q₀.label ∧ Q₀.scheme.scheme.grade d ≤ K}
  have hHK : Admissible Q₀.scheme.rows Q₀.label HK :=
    admissible_gradeTrunc (admissible_of_respects Q₀.respects fun _ _ => rfl) K
  -- the cap: visible at `k + 1`, above every proper label of `Q₀`
  obtain ⟨b, hb, _, hβ, hβgt⟩ := Q₀.exists_lawful_cutoff α.2.pos (k + 1)
  -- the root's tops have grade at most `K`, so they are retained
  have hroot : rootTops hQ₀cof ⊆ HK := by
    rintro c ⟨d, rfl, hd⟩
    refine ⟨hd, ?_⟩
    have h1 : (Q₀.scheme.restrictFace Fin.castSuccEmb hQ₀cof.extendsDomain.visible).scheme.grade
        (SemScheme.castCell hQ₀cof.extendsDomain.restrict.symm d) ≤ K := by
      rw [CappedDonor.castCell_grade]
      apply hR
      rw [← hQ₀cof.label_cellOf d]
      exact hd
    exact h1
  refine ⟨lowerType Q₀ HK hb hβ hβgt hHK, isCoface_lowerType hQ₀cof hb hβ hβgt hHK hroot, ?_, ?_⟩
  · -- the original donor is retained: its tops have grade at most `K`
    have hv' : Finset.univ.image (FixedHeight.extendFace e) ∈ Q₀.scheme.scheme.plan :=
      (typeMap_isSome_iff _ Q₀).mp (by rw [hQ₀e]; rfl)
    have hs' : Q₀.scheme.restrictFace (FixedHeight.extendFace e) hv' = q.scheme :=
      congrArg StageType.scheme (Option.some.inj ((typeMap_eq_some _ Q₀ hv').symm.trans hQ₀e))
    have hlab := (typeMap_eq_some_iff_labels _ Q₀ q hv' hs').mp hQ₀e
    refine (typeMap_eq_some_iff_labels (FixedHeight.extendFace e)
      (lowerType Q₀ HK hb hβ hβgt hHK) q hv' hs').mpr fun i => ?_
    change lower Q₀.label HK _ (toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i) = _
    by_cases htop : Q₀.label (toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i) = ⊤
    · have hmem : toCell Q₀.scheme.scheme (FixedHeight.extendFace e) hv' i ∈ HK := by
        refine ⟨htop, ?_⟩
        have h2 : (Q₀.scheme.restrictFace (FixedHeight.extendFace e) hv').scheme.grade i ≤
            K := by
          rw [← CappedDonor.castCell_grade hs' i]
          apply hqK
          rw [← hlab i]
          exact htop
        exact h2
      rw [lower_of_mem htop hmem]
      exact ((hlab i).symm.trans htop).symm
    · rw [lower_of_ne_top htop]
      exact hlab i
  · intro d hd
    have hmem : d ∈ topSet (lower Q₀.label HK (ofOrd b)) := hd
    rw [topSet_lower hHK.subset (ofOrd_ne_top _)] at hmem
    exact hmem.2

end VaughtConjecture.Knight.FirstLossAcquisition
