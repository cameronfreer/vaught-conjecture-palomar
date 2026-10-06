/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemScheme

/-! # Knight's stage types and horizontal restriction

Ported from Knight-VC `KnightVC/TypeSpace.lean` @ f7c7847d (`TypeSpace`, `S`, `TypeSpace.ext`,
`subsingleton_S0`, `emptyType`, `typeMap`, `typeMap_isSome_of_mem`, `typeMap_id`,
`typeMap_eq_some_of_emb`, `typeMap_comp`, `IsFaceClosed`, `isFaceClosed_iff_plan`,
`not_isFaceClosed_of_arity_ge_three`) and `KnightVC/TypeSpaceCountable.lean` (`countable_S`),
with Knight-VC's `TypeSpace n α` renamed `StageType α n`, its fields renamed to the vocabulary
of `docs/TERMINOLOGY.md` (`dom` → `scheme`, `p` → `label`, `bound` → `label_bound`), the scheme
restriction that Knight-VC inlines into `typeMap` factored out as `CellScheme.restrictFace`
(`Knight.Cell`) / `SemScheme.restrictFace` (`Knight.SemScheme`), and — the content of #88 —
Knight-VC's free, stage-bounded semantic rows (`sem`, `sem_bound`) replaced by the
**associated semantics** of the scheme (`SemScheme`, Def. 2.6.1).

A **stage type** of stage `α` on `n`-tuples (Knight, Def. 3.1.1) is a domain with its
associated semantics on `Fin n` (`SemScheme n`: a cell scheme owning its coded, consistent,
bountiful rows, the scheme complete) together with a labelling `p` of its cells, with every
label **strictly** bounded at stage `α` (`p(Ξ) ∈ {-∞} ∪ α ∪ {∞}`, i.e. `< ofOrd α` or `⊤`)
and `p` respecting the associated semantics in the faithful sense of Def. 2.5.4
(`RespectsSemantics`, locality and availability).  `S α n` is the type of stage types: this
**is** the paper's `S^α_A` (for `A = Fin n`) in record form — Def. 3.1.1 with Def. 2.6.1's
associated semantics, the paper's set-theoretic coding `⌜Ξ⌝` replaced by the scheme owning its
rows (`SemScheme`).  There is no separate row bound and no separate row field: the rows are
`t.scheme.rows`, they are stage-independent, and they are **fixed** under vertical reduction
(`Knight.Reduction`, Def. 3.1.2).  In the paper the stages `α` are limit ordinals (Def. 3.1.1
"α a limit ordinal"); `S α n` is defined for every ordinal, but the `TypeTower` instance
(`Knight.Tower.knightTower`) is indexed by the limit stages, since the faithful transport of
respect under reduction (`RespectsSemantics.truncate`, #89) needs `Order.IsSuccLimit α`.
`S α n` is countable for countable `α` (`countable_S`: countably many domains with associated
semantics, `SemScheme.countable`, times countably many strictly bounded labellings — Prop. 3.1.4
from Prop. 2.6.3(4), not from any row bound), and `S α 0` is a subsingleton.

**Horizontal restriction** (Def. 3.1.5): `typeMap f : S α n → Option (S α m)` restricts a stage
type along `f : Fin m ↪ Fin n`; it is `some (t.restrictFace f hr)` when the range of `f` is a
visible face of the plan (`hr`), and `none` otherwise — partiality is the mathematics, not an
API defect (`docs/DESIGN.md` §4).  `t.restrictFace f hr` is the face restriction of the domain
with its associated semantics (`SemScheme.restrictFace`, Prop. 2.6.3(3)) and the labels of the
visible cells; respect transports faithfully (`RespectsSemantics.restrictFace`, Lemma 2.5.5).
Its laws are the identity law `typeMap_refl` and the conditional composition law `typeMap_trans`
(`typeMap g t = some u → typeMap f u = typeMap (f.trans g) t`); both are instances of the
single characterisation `typeMap_eq_some_of_emb` (Knight-VC's theorem of the same name): a
stage type is the `f`-restriction of `t` as soon as some strictly monotone enumeration of
exactly the `f`-visible cells of `t` matches its plan, cells, labels and rows.  No type of
arity `≥ 3` is face-closed (`not_isFaceClosed_of_arity_ge_three`), since a plan on three or
more points is never the full powerset.

Knight-VC's preservation lemmas `typeMap_bandAwareControlled`, `typeMap_semBounded`,
`typeMap_bandSelfVisible`, `typeMap_semTopImpliesMinTop`, `typeMap_noTop` belong to later
consumers (band control, the one-point transfer) and are not ported here; each is immediate
from `typeMap_eq_some` and the definition of `StageType.restrictFace` (labels and rows are
read off the original type). -/

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open CellScheme.restrictFace (toCell belowMap)

/-- A **stage type** of stage `α` on `n`-tuples — the paper's `S^α_A` in record form (Knight,
Def. 3.1.1 with the associated semantics of Def. 2.6.1; Knight-VC `TypeSpace`): a domain with
its associated semantics on `Fin n` (`SemScheme n`) and a labelling of its cells, **strictly**
bounded at stage `α` (`< ofOrd α` or `⊤`, the paper's `{-∞} ∪ α ∪ {∞}`, matching the strict
`truncExt`, #84), respecting the associated semantics in the faithful sense of Def. 2.5.4.
The rows are `scheme.rows`: stage-independent, and fixed under reduction.  The paper's stages
are limit ordinals; the tower is indexed by them (`Knight.Tower`). -/
structure StageType (α : Ordinal.{0}) (n : ℕ) where
  /-- The domain with its associated semantics (Def. 2.6.1): the cell scheme (Knight's
  "domain" of the type) owning its rows. -/
  scheme : SemScheme n
  /-- The label of each cell. -/
  label : Cell scheme.scheme → ExtOrd
  /-- Labels are strictly bounded at stage `α`: in `{-∞} ∪ α ∪ {∞}` (Def. 3.1.1). -/
  label_bound : ∀ d : Cell scheme.scheme, label d < ExtOrd.ofOrd α ∨ label d = ⊤
  /-- The labelling respects the associated semantics (Def. 2.5.4, faithful: orderliness,
  locality, availability). -/
  respects : RespectsSemantics scheme.rows label

/-- `S α n`: the stage types of stage `α` on `n`-tuples, Knight's `S^α_n`; see `StageType`. -/
abbrev S (α : Ordinal.{0}) (n : ℕ) := StageType α n

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-- Extensionality: two stage types are equal when their domains and labellings agree (`label`
depends on `scheme`, hence `HEq`); the `Prop` fields follow by proof irrelevance. -/
@[ext]
theorem ext {t₁ t₂ : S α n} (h_scheme : t₁.scheme = t₂.scheme)
    (h_label : HEq t₁.label t₂.label) : t₁ = t₂ := by
  obtain ⟨d₁, p₁, _, _⟩ := t₁
  obtain ⟨d₂, p₂, _, _⟩ := t₂
  subst h_scheme
  obtain rfl := eq_of_heq h_label
  rfl

/-- Equality of stage types from their components, with the cells of `t₂` transported along
`Fin.cast` (Knight-VC `typeSpace_eq_of_components`): this avoids `HEq` when the schemes are
only propositionally equal.  The rows are components of the domain (`scheme.rows`). -/
theorem ext_of_components {t₁ t₂ : S α n}
    (h_plan : t₁.scheme.scheme.plan = t₂.scheme.scheme.plan)
    (h_card : t₁.scheme.scheme.card = t₂.scheme.scheme.card)
    (h_cell : ∀ i, t₁.scheme.scheme.cell (Fin.cast h_card.symm i) = t₂.scheme.scheme.cell i)
    (h_label : ∀ i, t₁.label (Fin.cast h_card.symm i) = t₂.label i)
    (h_row : ∀ (Sig : Cell t₂.scheme.scheme)
      (d : t₂.scheme.scheme.below (t₂.scheme.scheme.cell Sig)),
      t₁.scheme.rows.E (Fin.cast h_card.symm Sig)
        ⟨Fin.cast h_card.symm d.1, by rw [h_cell d.1, h_cell Sig]; exact d.2⟩ =
      t₂.scheme.rows.E Sig d) :
    t₁ = t₂ := by
  obtain ⟨⟨⟨P₁, ip₁, c₁, cl₁, cm₁⟩, s₁, _, _, _, _⟩, p₁, b₁, r₁⟩ := t₁
  obtain ⟨⟨⟨P₂, ip₂, c₂, cl₂, cm₂⟩, s₂, _, _, _, _⟩, p₂, b₂, r₂⟩ := t₂
  dsimp only at h_plan h_card h_cell h_label h_row
  subst h_plan h_card
  simp only [Fin.cast_eq_self] at h_cell h_label h_row
  obtain rfl := funext h_cell
  obtain rfl : s₁ = s₂ := Semantics.ext (funext fun Sig => funext fun d => h_row Sig d)
  exact ext rfl (heq_of_eq (funext h_label))

/-! ### The stage types on `0`-tuples -/

/-- The graded plan over `Fin 0` is empty: there is no face of positive size. -/
private theorem gradedPlan_fin0_eq_empty (P : Finset (Finset (Fin 0))) :
    Plan.gradedPlan P = ∅ := by
  ext ⟨B, j⟩
  simp only [Plan.mem_gradedPlan, Plan.MemGraded, Finset.notMem_empty, iff_false, not_and,
    not_le]
  intro _ hj
  simpa [Finset.eq_empty_of_forall_notMem (fun x : Fin 0 => x.elim0) (s := B)] using hj

/-- A scheme over `Fin 0` has no cells. -/
private theorem card_eq_zero_of_fin0 (D : CellScheme (ι := Fin 0) Finset.univ) : D.card = 0 := by
  by_contra h
  have := D.cell_mem ⟨0, Nat.pos_of_ne_zero h⟩
  rw [gradedPlan_fin0_eq_empty] at this
  exact Finset.notMem_empty _ this

/-- The only plan on `Fin 0` is `{∅}`. -/
private theorem plan_eq_of_fin0 {P : Finset (Finset (Fin 0))}
    (h : Plan.IsPlan (Finset.univ : Finset (Fin 0)) P) : P = {∅} := by
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ :=
    Finset.eq_empty_of_forall_notMem (fun x => x.elim0)
  rw [huniv] at h
  ext B
  simp only [Finset.mem_singleton]
  exact ⟨fun hB => Finset.subset_empty.mp (h.subset_of_mem hB), fun hB => hB ▸ h.empty_mem⟩

/-- There is at most one stage type on `0`-tuples at each stage: the scheme has no cells and
the plan is `{∅}`. -/
instance subsingleton_zero : Subsingleton (S α 0) := by
  constructor
  rintro ⟨⟨⟨P₁, ip₁, c₁, cl₁, cm₁⟩, s₁, _, _, _, _⟩, p₁, _, _⟩
    ⟨⟨⟨P₂, ip₂, c₂, cl₂, cm₂⟩, s₂, _, _, _, _⟩, p₂, _, _⟩
  have h1 : c₁ = 0 := card_eq_zero_of_fin0 ⟨P₁, ip₁, c₁, cl₁, cm₁⟩
  have h2 : c₂ = 0 := card_eq_zero_of_fin0 ⟨P₂, ip₂, c₂, cl₂, cm₂⟩
  subst h1 h2
  obtain rfl : P₁ = P₂ := (plan_eq_of_fin0 ip₁).trans (plan_eq_of_fin0 ip₂).symm
  obtain rfl : cl₁ = cl₂ := funext fun d => d.elim0
  obtain rfl : s₁ = s₂ := Semantics.ext (funext fun d => d.elim0)
  obtain rfl : p₁ = p₂ := funext fun d => d.elim0
  rfl

/-! ### The empty type and countability -/

/-- The empty domain with its associated semantics on `Fin 0`: the canonical plan `{∅}` and
no cells.  Coding, consistency and bountifulness are vacuous (no cells); completeness is
vacuous because the graded plan over `Fin 0` is empty (`j ≤ |∅| = 0 < j`).  For `n ≥ 1` a
complete scheme must have cells, so there is no empty `SemScheme n`. -/
noncomputable def emptySemScheme : SemScheme 0 where
  scheme :=
    { plan := Plan.canonicalPlan (Finset.univ : Finset (Fin 0))
      isPlan := Plan.isPlan_canonicalPlan _
      card := 0
      cell := fun d => d.elim0
      cell_mem := fun d => d.elim0 }
  rows := { E := fun Sig => Sig.elim0, orderly := fun Sig => Sig.elim0 }
  rows_coded Sig := Sig.elim0
  consistent Sig := Sig.elim0
  bountiful _ BJ _ _ _ _ _ _ _ _ _ _ _ :=
    ⟨fun d => d.1.elim0, ⟨fun d => d.1.elim0, fun d => d.1.elim0, fun d _ _ _ => d.1.elim0⟩,
      fun d => d.1.elim0, fun d => d.1.elim0⟩
  complete BJ hBJ := by
    rw [gradedPlan_fin0_eq_empty] at hBJ
    exact absurd hBJ (Finset.notMem_empty _)

/-- The empty stage type on `0`-tuples at any stage: the empty domain, no labels (the unique
element of `S α 0`, `subsingleton_zero`). -/
noncomputable def emptyType : S α 0 where
  scheme := emptySemScheme
  label := fun d => d.elim0
  label_bound := fun d => d.elim0
  respects :=
    { orderly := fun d => d.elim0, locality := fun Sig => Sig.elim0,
      availability := fun Sig => Sig.elim0 }

/-- `S α n` is countable when `α` is countable (Knight, Prop. 3.1.4): a stage type is its
domain with associated semantics — countably many (`SemScheme.countable`, Prop. 2.6.3(4), from
countably many coded schemes) — together with finitely many labels in the countable set of
labels strictly bounded at `α` (`ExtOrd.countable_bounded_lt`).  No row bound is involved. -/
theorem countable_S (hα : α.card ≤ Cardinal.aleph0) (n : ℕ) : Countable (S α n) := by
  have := ExtOrd.countable_bounded_lt hα
  let B := {x : ExtOrd // x < ExtOrd.ofOrd α ∨ x = ⊤}
  let g : S α n → Σ X : SemScheme n, (Cell X.scheme → B) :=
    fun t => ⟨t.scheme, fun i => ⟨t.label i, t.label_bound i⟩⟩
  have hinj : Function.Injective g := by
    rintro ⟨d₁, p₁, _, _⟩ ⟨d₂, p₂, _, _⟩ h
    obtain rfl : d₁ = d₂ := congrArg Sigma.fst h
    rw [Sigma.mk.injEq, heq_eq_eq] at h
    obtain rfl : p₁ = p₂ := funext fun i => congrArg Subtype.val (congrFun h.2 i)
    rfl
  exact hinj.countable

/-! ### Horizontal restriction -/

/-- The restriction of a stage type to a visible face (Knight, Def. 3.1.5; the `some` branch
of Knight-VC `typeMap`): the face restriction of the domain with its associated semantics
(`SemScheme.restrictFace`: the restricted scheme, the rows read at the underlying visible
cells) and the labels of the visible cells; respect transports faithfully
(`RespectsSemantics.restrictFace`). -/
noncomputable def restrictFace (t : S α n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan) : S α m where
  scheme := t.scheme.restrictFace f hr
  label i := t.label (toCell t.scheme.scheme f hr i)
  label_bound i := t.label_bound (toCell t.scheme.scheme f hr i)
  respects := t.respects.restrictFace f hr

@[simp] theorem restrictFace_scheme (t : S α n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan) :
    (t.restrictFace f hr).scheme = t.scheme.restrictFace f hr := rfl

@[simp] theorem restrictFace_label (t : S α n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan)
    (i : Cell (t.scheme.scheme.restrictFace f hr)) :
    (t.restrictFace f hr).label i = t.label (toCell t.scheme.scheme f hr i) := rfl

@[simp] theorem restrictFace_rows_E (t : S α n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan)
    (Sig : Cell (t.scheme.scheme.restrictFace f hr))
    (d : (t.scheme.scheme.restrictFace f hr).below
      ((t.scheme.scheme.restrictFace f hr).cell Sig)) :
    (t.restrictFace f hr).scheme.rows.E Sig d =
      t.scheme.rows.E (toCell t.scheme.scheme f hr Sig) (belowMap t.scheme.scheme f hr Sig d) :=
  rfl

end StageType

open StageType

variable {α : Ordinal.{0}} {k m n : ℕ}

/-- **Horizontal restriction** `S^α f` (Knight, Def. 3.1.5; Knight-VC `typeMap`): the partial
restriction of a stage type along `f : Fin m ↪ Fin n`, defined exactly when the range of `f` is
a visible face of its plan.  This is the `pull` of the Knight `TypeTower` instance. -/
noncomputable def typeMap (f : Fin m ↪ Fin n) (t : S α n) : Option (S α m) :=
  if hr : Finset.univ.image f ∈ t.scheme.scheme.plan then some (t.restrictFace f hr) else none

theorem typeMap_eq_some (f : Fin m ↪ Fin n) (t : S α n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan) :
    typeMap f t = some (t.restrictFace f hr) :=
  dite_eq_left hr

theorem typeMap_eq_none (f : Fin m ↪ Fin n) (t : S α n)
    (hr : Finset.univ.image f ∉ t.scheme.scheme.plan) : typeMap f t = none :=
  dite_eq_right hr

/-- `typeMap f t` is defined exactly when the range of `f` is a visible face of the plan. -/
theorem typeMap_isSome_iff (f : Fin m ↪ Fin n) (t : S α n) :
    (typeMap f t).isSome ↔ Finset.univ.image f ∈ t.scheme.scheme.plan := by
  by_cases hr : Finset.univ.image f ∈ t.scheme.scheme.plan
  · simp [typeMap_eq_some f t hr, hr]
  · simp [typeMap_eq_none f t hr, hr]

theorem typeMap_isSome_of_mem (f : Fin m ↪ Fin n) (t : S α n)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan) : (typeMap f t).isSome :=
  (typeMap_isSome_iff f t).mpr hr

/-- The characterisation of restriction (Knight-VC `typeMap_eq_some_of_emb`): `q` is the
`f`-restriction of `t` as soon as a strictly monotone `emb` enumerates exactly the `f`-visible
cells of `t` and the plan, cells, labels and rows of `q` are those of `t` read through `emb`.
The identity and composition laws below are instances. -/
theorem typeMap_eq_some_of_emb (f : Fin m ↪ Fin n) (t : S α n) (q : S α m)
    (hr : Finset.univ.image f ∈ t.scheme.scheme.plan)
    (emb : Cell q.scheme.scheme → Cell t.scheme.scheme) (emb_mono : StrictMono emb)
    (emb_visible : ∀ c, t.scheme.scheme.scope (emb c) ⊆ Finset.univ.image f)
    (visible_emb : ∀ d, t.scheme.scheme.scope d ⊆ Finset.univ.image f → ∃ c, emb c = d)
    (hplan : (t.scheme.scheme.restrictFace f hr).plan = q.scheme.scheme.plan)
    (hcell : ∀ c, t.scheme.scheme.pullCell f (emb c) = q.scheme.scheme.cell c)
    (hlabel : ∀ c, t.label (emb c) = q.label c)
    (hrow : ∀ (Sig : Cell q.scheme.scheme) (d : q.scheme.scheme.below (q.scheme.scheme.cell Sig))
      (d' : t.scheme.scheme.below (t.scheme.scheme.cell (emb Sig))),
      d'.1 = emb d.1 → t.scheme.rows.E (emb Sig) d' = q.scheme.rows.E Sig d) :
    typeMap f t = some q := by
  rw [typeMap_eq_some f t hr]
  congr 1
  have hcard : (t.restrictFace f hr).scheme.scheme.card = q.scheme.scheme.card :=
    CellScheme.restrictFace.card_restrictFace_of_emb t.scheme.scheme f hr emb_mono emb_visible
      visible_emb
  have hei : ∀ c, toCell t.scheme.scheme f hr (Fin.cast hcard.symm c) = emb c :=
    CellScheme.restrictFace.toCell_cast_eq_of_emb t.scheme.scheme f hr emb_mono emb_visible hcard
  refine ext_of_components hplan hcard (fun c => ?_) (fun c => ?_) (fun Sig d => ?_)
  · change t.scheme.scheme.pullCell f (toCell t.scheme.scheme f hr (Fin.cast hcard.symm c)) = _
    rw [hei c]; exact hcell c
  · change t.label (toCell t.scheme.scheme f hr (Fin.cast hcard.symm c)) = _
    rw [hei c]; exact hlabel c
  · have hgl : GradedLe (t.scheme.scheme.cell (emb d.1)) (t.scheme.scheme.cell (emb Sig)) :=
      (CellScheme.gradedLe_pullCell_iff t.scheme.scheme f (emb_visible d.1)).mp
        (by rw [hcell d.1, hcell Sig]; exact d.2)
    exact (t.scheme.rows.E_congr (hei Sig) (hei d.1)).trans (hrow Sig d ⟨emb d.1, hgl⟩ rfl)

/-- The identity law of restriction (Knight-VC `typeMap_id`): every face of `Fin n` visible
through the identity is visible, and the restriction along the identity is the type itself. -/
theorem typeMap_refl (t : S α n) : typeMap (Function.Embedding.refl (Fin n)) t = some t := by
  have hrng : Finset.univ.image (Function.Embedding.refl (Fin n)) = Finset.univ := by
    simp [Function.Embedding.coe_refl]
  have hr : Finset.univ.image (Function.Embedding.refl (Fin n)) ∈ t.scheme.scheme.plan := by
    rw [hrng]; exact t.scheme.scheme.isPlan.domain_mem
  refine typeMap_eq_some_of_emb _ t t hr id strictMono_id
    (fun c => by rw [hrng]; exact Finset.subset_univ _) (fun d _ => ⟨d, rfl⟩) ?_ ?_ (fun _ => rfl)
    (fun Sig d d' hd => congrArg _ (Subtype.ext hd))
  · exact Option.some_injective _
      ((CellScheme.pullbackPlan_eq_restrictFace_plan _ _ hr).symm.trans
        (Plan.pullbackPlan_refl t.scheme.scheme.isPlan))
  · intro c
    refine Prod.ext ?_ rfl
    ext i
    simp [CellScheme.pullCell]

/-- **Conditional composition** of restrictions (Knight-VC `typeMap_comp`; Knight, Lemma 3.1.6
style): if restricting `t` along `g` is defined and gives `u`, then restricting `u` further
along `f` agrees — including definedness — with restricting `t` along the composite
`f.trans g`.  Nothing is asserted when the intermediate face is invisible; this is the
`pull_trans` law of `TypeTower`. -/
theorem typeMap_trans (f : Fin k ↪ Fin m) (g : Fin m ↪ Fin n) (t : S α n) (u : S α m)
    (hu : typeMap g t = some u) : typeMap f u = typeMap (f.trans g) t := by
  have hg : Finset.univ.image g ∈ t.scheme.scheme.plan :=
    (typeMap_isSome_iff g t).mp (by rw [hu]; rfl)
  rw [typeMap_eq_some g t hg, Option.some.injEq] at hu
  subst hu
  have hguard : Finset.univ.image f ∈ (t.scheme.scheme.restrictFace g hg).plan ↔
      Finset.univ.image (f.trans g) ∈ t.scheme.scheme.plan := by
    rw [CellScheme.mem_restrictFace_plan, Finset.image_image]; rfl
  by_cases hfg : Finset.univ.image (f.trans g) ∈ t.scheme.scheme.plan
  · have hf : Finset.univ.image f ∈ (t.scheme.scheme.restrictFace g hg).plan := hguard.mpr hfg
    rw [typeMap_eq_some f _ hf]
    symm
    refine typeMap_eq_some_of_emb (f.trans g) t _ hfg
      (fun c => toCell t.scheme.scheme g hg (toCell (t.scheme.scheme.restrictFace g hg) f hf c))
      ((CellScheme.restrictFace.toCell_strictMono _ _ _).comp
        (CellScheme.restrictFace.toCell_strictMono _ _ _))
      ?_ ?_ ?_ ?_ (fun _ => rfl) ?_
    · -- the composite enumeration lands in the `f.trans g`-visible cells
      intro c x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp
        (CellScheme.restrictFace.scope_toCell_subset t.scheme.scheme g hg
          (toCell (t.scheme.scheme.restrictFace g hg) f hf c) hx)
      have hy : y ∈ (t.scheme.scheme.restrictFace g hg).scope
          (toCell (t.scheme.scheme.restrictFace g hg) f hf c) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp
        (CellScheme.restrictFace.scope_toCell_subset (t.scheme.scheme.restrictFace g hg) f hf c
          hy)
      exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
    · -- and exhausts them
      intro d hd
      have hdg : t.scheme.scheme.scope d ⊆ Finset.univ.image g := fun x hx => by
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (hd hx)
        exact Finset.mem_image.mpr ⟨f z, Finset.mem_univ _, rfl⟩
      obtain ⟨c₁, rfl⟩ := CellScheme.restrictFace.exists_toCell_eq t.scheme.scheme g hg hdg
      have hc₁ : (t.scheme.scheme.restrictFace g hg).scope c₁ ⊆ Finset.univ.image f :=
        fun y hy => by
          obtain ⟨z, -, hz⟩ := Finset.mem_image.mp (hd (Finset.mem_filter.mp hy).2)
          exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, g.injective hz⟩
      obtain ⟨c, rfl⟩ :=
        CellScheme.restrictFace.exists_toCell_eq (t.scheme.scheme.restrictFace g hg) f hf hc₁
      exact ⟨c, rfl⟩
    · -- plans: conditional composition of pullback plans
      exact Option.some_injective _
        ((CellScheme.pullbackPlan_eq_restrictFace_plan _ _ hfg).symm.trans
          ((Plan.pullbackPlan_trans f g
            (CellScheme.pullbackPlan_eq_restrictFace_plan t.scheme.scheme g hg)).symm.trans
            (CellScheme.pullbackPlan_eq_restrictFace_plan (t.scheme.scheme.restrictFace g hg) f
              hf)))
    · -- cells: pulling back twice is pulling back along the composite
      intro c
      change _ = (t.scheme.scheme.restrictFace g hg).pullCell f
        (toCell (t.scheme.scheme.restrictFace g hg) f hf c)
      refine Prod.ext ?_ rfl
      ext j
      simp [CellScheme.pullCell]
    · -- rows
      intro Sig d d' hd
      exact t.scheme.rows.E_congr rfl hd
  · have hf : Finset.univ.image f ∉ (t.scheme.scheme.restrictFace g hg).plan :=
      fun h => hfg (hguard.mp h)
    rw [typeMap_eq_none f _ hf, typeMap_eq_none _ t hfg]

/-! ### Face closure -/

/-- A stage type is **face-closed** if its restriction along every injection is defined
(Knight-VC `IsFaceClosed`). -/
def IsFaceClosed (t : S α n) : Prop :=
  ∀ (m : ℕ) (f : Fin m ↪ Fin n), (typeMap f t).isSome

/-- Face closure says exactly that every face of `Fin n` is visible. -/
theorem isFaceClosed_iff_plan (t : S α n) :
    IsFaceClosed t ↔
      ∀ (m : ℕ) (f : Fin m ↪ Fin n), Finset.univ.image f ∈ t.scheme.scheme.plan :=
  forall₂_congr fun _ f => typeMap_isSome_iff f t

/-- No stage type of arity `≥ 3` is face-closed: a plan on three or more points is never the
full powerset (`Plan.isPlan_ne_powerset`), yet face closure forces every subset to be visible.
(Knight-VC `not_isFaceClosed_of_arity_ge_three`.) -/
theorem not_isFaceClosed_of_arity_ge_three (hn : 3 ≤ n) (t : S α n) : ¬ IsFaceClosed t := by
  intro hfc
  have hplan := (isFaceClosed_iff_plan t).mp hfc
  have hfull : t.scheme.scheme.plan = (Finset.univ : Finset (Fin n)).powerset := by
    ext B
    refine ⟨fun hB => Finset.mem_powerset.mpr (t.scheme.scheme.isPlan.subset_of_mem hB),
      fun _ => ?_⟩
    have himg : (Finset.univ : Finset (Fin B.card)).image (B.orderEmbOfFin rfl).toEmbedding = B :=
      by simp
    rw [← himg]
    exact hplan _ _
  exact Plan.isPlan_ne_powerset (by rw [Finset.card_univ, Fintype.card_fin]; exact hn)
    t.scheme.scheme.isPlan hfull

end VaughtConjecture.Knight
