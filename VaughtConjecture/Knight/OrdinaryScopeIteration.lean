/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryRawScope
public import VaughtConjecture.Knight.OrderedScopeObligations

/-! # Coherent iteration of ordinary proper scopes

The state records already completed targets. The successor derives the raw
local producer's premises from those targets, constructs its rows, and installs
them in the same ambient inventory. No local operator is an input to the step.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryScopeIteration
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}
variable (sem₀ : Semantics D₀) (F₀ : Finset (Finset ι)) (N : ℕ)
variable (G : Finset ExtOrd) (θ : ExtOrd)

/-- An actual partial carrier, its completed-target ledger, and its renderer.
`initial`, `step`, and finite iteration below construct these records. -/
structure State (F : Finset (Finset ι)) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = D₀.plan
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  original : Cell D₀ ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = D₀.cell d
  row : ∀ (c : Cell D₀) (d : D₀.below (D₀.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = sem₀.E c d
  exhaustive : ∀ d, carrier.scope d ∈ F₀ → ∃ c, original c = d
  occupied : ∀ d, carrier.scope d ∈ F
  initial_le : F₀ ⊆ F
  scopes : F ⊆ D₀.plan
  proper : A ∉ F
  closed : ∀ B ∈ F, ∀ C ∈ D₀.plan, C ⊆ B → C ∈ F
  complete : ∀ J ∈ Plan.gradedPlan D₀.plan, J.1 ∈ F → ∃ d, carrier.cell d = J
  lifts : ∀ I J, I ∈ Plan.gradedPlan D₀.plan → J ∈ Plan.gradedPlan D₀.plan → J.1 ∈ F →
    (h : GradedLe I J) → CappedLift rows h
  classification : OrderedScopeRelocation.OwnerClassification rows original
  mute : ∀ c, carrier.grade c = (carrier.scope c).card → carrier.scope c ∉ F₀ →
    rows.E c ⟨c, GradedLe.refl _⟩ = ⊥
  render : ∀ {p : Cell D₀ → ExtOrd}, RespectsSemantics sem₀ p → (∀ d, p d ≤ θ) →
    Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d,
    render hp hb (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ),
    RespectsSemantics rows (render hp hb)
  bound : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d, render hp hb d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) d,
    Supported N (G : Set ExtOrd) p (render hp hb d)
  agreement : ∀ {p q} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ)
    (hq : RespectsSemantics sem₀ q) (hqb : ∀ d, q d ≤ θ) {γ}, γ ∈ G → γ ≤ θ →
    Agree p q γ → Agree (render hp hb) (render hq hqb) γ

variable {sem₀ F₀ N G θ} {F : Finset (Finset ι)}
variable (X : State sem₀ F₀ N G θ F) {B : Finset ι}
variable (hB : B ∈ D₀.plan) (hnew : B ∉ F)
variable (hready : ∀ C ∈ D₀.plan, C ⊂ B → C ∈ F)

include hB hnew in
theorem separated : OrderedScopeRelocation.Separated (D := X.carrier) (B := B) := by
  intro d hd
  exact hnew (X.closed _ (X.occupied d) B hB hd)

def restricted := ScopeBoundary.scheme X.carrier B (X.plan.symm ▸ hB)
def restrictedRows := ScopeBoundary.rows X.carrier B (X.plan.symm ▸ hB) X.rows

include hnew hready in
theorem ready : OrdinaryRawScope.Ready (restrictedRows X hB) where
  proper d := by
    intro he
    exact separated X hB hnew (ScopeBoundary.toCell X.carrier B (X.plan.symm ▸ hB) d)
      (subset_of_eq he.symm)
  consistent := ScopeBoundary.consistent _ _ _ _ X.consistent
  coded := ScopeBoundary.coded _ _ _ _ X.coded
  complete J hJ hJB := by
    have hm := Plan.mem_gradedPlan.mp hJ
    have hmem : J.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
    have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
    have hd := hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩)
    obtain ⟨d, hd⟩ := X.complete J (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩) hd
    have hs : X.carrier.scope d ⊆ B := by change (X.carrier.cell d).1 ⊆ B; rwa [hd]
    obtain ⟨e, he⟩ := ScopeBoundary.exhaustive X.carrier B (X.plan.symm ▸ hB) hs
    exact ⟨e, (congrArg X.carrier.cell he).trans hd⟩
  lifts I J hI hJ hJB h := by
    have hm := Plan.mem_gradedPlan.mp hJ
    have hmem : J.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hm.1).1
    have hsub := Finset.mem_powerset.mp (Finset.mem_inter.mp hm.1).2
    have hdone := hready J.1 hmem (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJB⟩)
    have hi := Plan.mem_gradedPlan.mp hI
    have himem : I.1 ∈ D₀.plan := X.plan ▸ (Finset.mem_inter.mp hi.1).1
    have hb := X.lifts I J (Plan.mem_gradedPlan.mpr ⟨himem, hi.2⟩)
      (Plan.mem_gradedPlan.mpr ⟨hmem, hm.2⟩) hdone h
    let eJ := ScopeBoundary.belowEquiv X.carrier B (X.plan.symm ▸ hB) J hsub
    let eI := ScopeBoundary.belowEquiv X.carrier B (X.plan.symm ▸ hB) I (h.1.trans hsub)
    intro p q γ hp hq hγ hc
    exact bountiful_of_equiv h h eJ eI (fun _ => rfl)
      (ScopeBoundary.respects_iff _ _ _ _ _ _) (ScopeBoundary.respects_iff _ _ _ _ _ _)
      hb rfl p q γ hp hq hγ hc

variable (k : ℕ) (hk : 0 < k) (hcard : B.card = k + 1)

/-- The next operator is produced on the current carrier's literal restriction. -/
def localOperator : OrdinaryScopeOperator.Core (restrictedRows X hB) (k + 1) :=
  (OrdinaryRawScope.build _ (ready X hB hnew hready) k hk hcard).finish hk hcard

theorem local_complete : (localOperator X hB hnew hready k hk hcard).carrier.IsComplete :=
  (OrdinaryRawScope.build _ (ready X hB hnew hready) k hk hcard).finish_complete hk hcard

theorem local_highest_inactive
    {p : Cell (localOperator X hB hnew hready k hk hcard).carrier → ExtOrd}
    (hp : RespectsSemantics (localOperator X hB hnew hready k hk hcard).rows p)
    (d : Cell (localOperator X hB hnew hready k hk hcard).carrier)
    (hd : (localOperator X hB hnew hready k hk hcard).carrier.grade d = k + 1) : p d = ⊥ :=
  (OrdinaryRawScope.build _ (ready X hB hnew hready) k hk hcard).finish_highest_inactive
    hk hcard hp d hd

/-- Execute one new scope on the actual ambient carrier. All local lifting and
selected-section premises are derived above from the completed-target ledger. -/
def step (hBA : B ≠ A) (hN : k + 1 ≤ N)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G) :
    State sem₀ F₀ N G θ (insert B F) := by
  classical
  let hBX : B ∈ X.carrier.plan := X.plan.symm ▸ hB
  let L := localOperator X hB hnew hready k hk hcard
  let sep := separated X hB hnew
  let K := OrderedScopeRelocation.carrier X.rows hBX L
  let ss := OrderedScopeRelocation.rows X.rows hBX L sep
  let l := OrderedScopeRelocation.old X.rows hBX L
  let r := OrderedScopeRelocation.localCell X.rows hBX L
  have hg : ∀ z ∈ G, SelfVis (k + 1) z := fun z hz => selfVis_mono (hG z hz) hN
  have hθ' : SelfVis (k + 1) θ := selfVis_mono hθ hN
  let render' {p : Cell D₀ → ExtOrd} (hp : RespectsSemantics sem₀ p) (hb : ∀ d, p d ≤ θ) :=
    OrderedScopeRelocation.render X.rows hBX L (X.lawful hp hb)
      (fun d => ne_top_of_le_ne_top htθ (X.bound hp hb d)) G θ
  refine {
    carrier := K
    rows := ss
    plan := X.plan
    consistent := OrderedScopeRelocation.consistent X.rows hBX L sep X.consistent
    coded := OrderedScopeRelocation.coded X.rows hBX L sep X.coded
    original := X.original.trans (OrderEmbedding.ofStrictMono l
      (OrderedScopeRelocation.old_order X.rows hBX L))
    index := fun d => (OrderedScopeRelocation.old_index X.rows hBX L _).trans (X.index d)
    row := fun c d => (OrderedScopeRelocation.row_old X.rows hBX L sep (X.original c)
      ⟨X.original d.1, by rw [X.index, X.index]; exact d.2⟩).trans (X.row c d)
    exhaustive := ?_
    occupied := ?_
    initial_le := fun _ h => Finset.mem_insert_of_mem (X.initial_le h)
    scopes := by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hB
      · exact X.scopes hC
    proper := by simpa only [Finset.mem_insert, not_or] using And.intro hBA.symm X.proper
    closed := ?_
    complete := ?_
    lifts := ?_
    classification := OrderedScopeRelocation.ownerClassification X.rows hBX L sep
      X.original X.classification
    mute := ?_
    render := render'
    readback := ?_
    lawful := fun hp hb => OrderedScopeRelocation.render_lawful X.rows hBX L sep
      (X.lawful hp hb) _ hg hθ'
    bound := fun hp hb => OrderedScopeRelocation.render_bound X.rows hBX L
      (X.lawful hp hb) _ hg hθ' (X.bound hp hb)
    support := fun hp hb => OrderedScopeRelocation.render_supported X.rows hBX L
      (X.lawful hp hb) _ hN hG hθ' hθG (X.support hp hb)
    agreement := by
      intro p q hp hb hq hqb γ hγ hγθ he
      exact OrderedScopeRelocation.render_agreement X.rows hBX L
        (X.lawful hp hb) _ (X.lawful hq hqb) _ hg hθ' hγ hγθ
        (X.agreement hp hb hq hqb hγ hγθ he)
  }
  · intro z hz
    rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨d, rfl⟩ | hd
    · have hd : X.carrier.scope d ∈ F₀ := by
        simpa only [K, CellScheme.scope, OrderedScopeRelocation.old_index X.rows hBX L] using hz
      obtain ⟨e, rfl⟩ := X.exhaustive d hd
      exact ⟨e, rfl⟩
    · exact False.elim (hnew (X.initial_le (hd ▸ hz)))
  · intro z
    rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨d, rfl⟩ | hd
    · change (OrderedScopeRelocation.carrier X.rows hBX L).scope _ ∈ insert B F
      simpa only [CellScheme.scope, OrderedScopeRelocation.old_index X.rows hBX L] using
        (Finset.mem_insert_of_mem (X.occupied d) : X.carrier.scope d ∈ insert B F)
    · exact hd ▸ Finset.mem_insert_self B F
  · intro C hC T hT hTC
    rcases Finset.mem_insert.mp hC with hCB | hC
    · rw [hCB] at hTC
      by_cases he : T = B
      · exact he ▸ Finset.mem_insert_self B F
      · exact Finset.mem_insert_of_mem (hready T hT (Finset.ssubset_iff_subset_ne.mpr ⟨hTC, he⟩))
    · exact Finset.mem_insert_of_mem (X.closed C hC T hT hTC)
  · intro J hJ hJF
    rcases Finset.mem_insert.mp hJF with hJB | hJF
    · have hm := Plan.mem_gradedPlan.mp hJ
      have hJL : J ∈ Plan.gradedPlan L.carrier.plan := by
        rw [L.plan]
        exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
          ⟨X.plan.symm ▸ hm.1, Finset.mem_powerset.mpr (subset_of_eq hJB)⟩, hm.2⟩
      obtain ⟨d, hd⟩ := local_complete X hB hnew hready k hk hcard J hJL
      exact ⟨r d, (OrderedScopeRelocation.local_index X.rows hBX L d).trans hd⟩
    · obtain ⟨d, hd⟩ := X.complete J hJ hJF
      exact ⟨l d, (OrderedScopeRelocation.old_index X.rows hBX L d).trans hd⟩
  · intro I J hI hJ hJF h
    rcases Finset.mem_insert.mp hJF with hJB | hJF
    · exact OrderedScopeRelocation.local_lift X.rows hBX L sep h
        (X.plan.symm ▸ hI) (X.plan.symm ▸ hJ) (subset_of_eq hJB)
    · exact OrderedScopeRelocation.old_lift X.rows hBX L sep h
        (fun hBJ => hnew (X.closed _ hJF B hB hBJ)) (X.lifts I J hI hJ hJF h)
  · intro z hz hn
    rcases OrderedScopeRelocation.classify X.rows hBX L z with ⟨c, rfl⟩ | hc
    · have hg : X.carrier.grade c = (X.carrier.scope c).card := by
        simpa only [K, CellScheme.scope, CellScheme.grade,
          OrderedScopeRelocation.old_index X.rows hBX L] using hz
      have hn' : X.carrier.scope c ∉ F₀ := by
        simpa only [K, CellScheme.scope, OrderedScopeRelocation.old_index X.rows hBX L] using hn
      exact (OrderedScopeRelocation.row_old X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
        (X.mute c hg hn')
    · obtain ⟨c, rfl⟩ := OrderedScopeRelocation.local_exhaustive X.rows hBX L z (subset_of_eq hc)
      have hg : L.carrier.grade c = k + 1 := by
        have hh := hz.trans (congrArg Finset.card hc)
        simpa only [K, CellScheme.grade, OrderedScopeRelocation.local_index X.rows hBX L,
          hcard] using hh
      exact (OrderedScopeRelocation.row_local X.rows hBX L sep c ⟨c, GradedLe.refl _⟩).trans
        (OrdinaryRawScope.completed_highest_row
          (OrdinaryRawScope.build _ (ready X hB hnew hready) k hk hcard) hk hcard c hg _)
  · intro p hp hb d
    exact (OrderedScopeRelocation.render_old X.rows hBX L (X.lawful hp hb) _ _).trans
      (X.readback hp hb d)

end

noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (F₀ : Finset (Finset ι)) (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd)

def initial (hs : sem.IsConsistent) (hc : sem.IsCoded)
    (hocc : ∀ d, D.scope d ∈ F₀) (hscopes : F₀ ⊆ D.plan) (hproper : A ∉ F₀)
    (hclosed : ∀ B ∈ F₀, ∀ C ∈ D.plan, C ⊆ B → C ∈ F₀)
    (hcomplete : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ∈ F₀ → ∃ d, D.cell d = J)
    (hlift : ∀ I J, I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan → J.1 ∈ F₀ →
      (h : GradedLe I J) → CappedLift sem h) : State sem F₀ N G θ F₀ where
  carrier := D
  rows := sem
  plan := rfl
  consistent := hs
  coded := hc
  original := (OrderIso.refl (Cell D)).toOrderEmbedding
  index _ := rfl
  row _ _ := rfl
  exhaustive d _ := ⟨d, rfl⟩
  occupied := hocc
  initial_le := Finset.Subset.refl _
  scopes := hscopes
  proper := hproper
  closed := hclosed
  complete := hcomplete
  lifts := hlift
  classification := OrderedScopeRelocation.ownerClassification_initial sem
  mute c _ hn := (hn (hocc c)).elim
  render {p} _ _ := p
  readback _ _ _ := rfl
  lawful hp _ := hp
  bound _ hb := hb
  support _ _ := supported_field N (G : Set ExtOrd) _
  agreement := by
    intro p q hp hb hq hqb γ hγ hγθ he
    exact he

variable {sem F₀ N G θ}

/-- Execute the finite iteration. A least-cardinality missing scope has all
proper lower scopes completed, so the successor above supplies its own input.
No list of local operators or separately chosen legal facets is assumed. -/
theorem exists_completed
    (hN : ∀ B ∈ D.plan, B ≠ A → B.card ≤ N)
    (hsmall : ∀ B ∈ D.plan, B.card ≤ 1 → B ∈ F₀)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G)
    {F : Finset (Finset ι)} (X : State sem F₀ N G θ F) :
    ∃ F', Nonempty (State sem F₀ N G θ F') ∧ ∀ B ∈ D.plan, B ≠ A → B ∈ F' := by
  classical
  suffices ∀ n, ∀ (F : Finset (Finset ι)), (D.plan \ insert A F).card = n →
      State sem F₀ N G θ F →
      ∃ F', Nonempty (State sem F₀ N G θ F') ∧ ∀ B ∈ D.plan, B ≠ A → B ∈ F' by
    exact this _ F rfl X
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn X
    by_cases hempty : (D.plan \ insert A F).Nonempty
    · obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image (D.plan \ insert A F) Finset.card hempty
      have hBp := (Finset.mem_sdiff.mp hB).1
      have hBA : B ≠ A := fun he => (Finset.mem_sdiff.mp hB).2 (he ▸ Finset.mem_insert_self A F)
      have hnew : B ∉ F := fun hf => (Finset.mem_sdiff.mp hB).2 (Finset.mem_insert_of_mem hf)
      have hready : ∀ C ∈ D.plan, C ⊂ B → C ∈ F := by
        intro C hC hCB
        by_contra hc
        have hCA : C ≠ A := by
          intro he
          have hsub := D.isPlan.subset_of_mem hBp
          have hlt := Finset.card_lt_card hCB
          have hle := Finset.card_le_card hsub
          subst C
          omega
        have hcm : C ∈ D.plan \ insert A F :=
          Finset.mem_sdiff.mpr ⟨hC, by simp only [Finset.mem_insert, not_or]; exact ⟨hCA, hc⟩⟩
        exact (not_le_of_gt (Finset.card_lt_card hCB)) (hmin C hcm)
      have htwo : 2 ≤ B.card := by
        by_contra hh
        exact hnew (X.initial_le (hsmall B hBp (by omega)))
      let k := B.card - 1
      have hk : 0 < k := by dsimp [k]; omega
      have hcard : B.card = k + 1 := by dsimp [k]; omega
      let Y := step X hBp hnew hready k hk hcard hBA (hcard ▸ hN B hBp hBA)
        hG hθ htθ hθG
      have hlt : (D.plan \ insert A (insert B F)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨?_, ?_⟩
        · intro C hC
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hC ⊢
          exact ⟨hC.1, hC.2.1, hC.2.2.2⟩
        · intro he
          have hm := he.symm ▸ hB
          simp only [Finset.mem_sdiff, Finset.mem_insert, true_or, or_true, not_true_eq_false,
            and_false] at hm
      exact ih _ hlt _ rfl Y
    · refine ⟨F, ⟨X⟩, ?_⟩
      intro B hB hBA
      by_contra hf
      exact hempty ⟨B, Finset.mem_sdiff.mpr
        ⟨hB, by simp only [Finset.mem_insert, not_or]; exact ⟨hBA, hf⟩⟩⟩

end
end VaughtConjecture.Knight.OrdinaryScopeIteration
