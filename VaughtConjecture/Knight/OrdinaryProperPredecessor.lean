/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeIteration

/-! # Constructing all proper scopes from the actual legal inputs

The initial ledger is the union of the two literal input faces. The finite
iteration constructs every other proper scope on that same ordered inventory.
The full ambient scope is deliberately not completed here.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryProperPredecessor
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open OrdinaryScopeIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

def initialScopes : Finset (Finset ι) := I.boundary.plan.filter (fun S => S ⊆ B ∨ S ⊆ C)

theorem mem_initial {S : Finset ι} : S ∈ initialScopes I ↔ S ∈ R ∧ (S ⊆ B ∨ S ⊆ C) :=
  Finset.mem_filter

theorem initial_occupied (d : Cell I.boundary) : I.boundary.scope d ∈ initialScopes I :=
  mem_initial I |>.mpr ⟨I.boundary.scope_mem_plan d,
    (I.occupied_iff (I.boundary.cell_mem d)).mp ⟨d, rfl⟩⟩

variable (hBA : B ≠ A) (hCA : C ≠ A)

include hBA hCA in
theorem initial_proper : A ∉ initialScopes I := by
  intro h
  rcases (mem_initial I |>.mp h).2 with hb | hc
  · exact hBA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.left_mem I)) hb)
  · exact hCA (Finset.Subset.antisymm
      (I.isPlan.subset_of_mem (WholeDonorOrdinaryLift.right_mem I)) hc)

variable (N : ℕ) (G : Finset ExtOrd) (θ : ExtOrd)

/-- Every premise of the initial iteration state follows from input legality. -/
def seed : State I.rows (initialScopes I) N G θ (initialScopes I) :=
  initial I.rows (initialScopes I) N G θ I.consistent I.coded (initial_occupied I)
    (fun _ h => (mem_initial I |>.mp h).1) (initial_proper I hBA hCA)
    (by
      intro S hS T hT ht
      refine (mem_initial I).mpr ⟨hT, ?_⟩
      exact (mem_initial I |>.mp hS).2.imp ht.trans ht.trans)
    (fun J hJ h => (I.occupied_iff hJ).mpr (mem_initial I |>.mp h).2)
    (by
      intro CI BJ hCI hBJ hscope h
      by_cases he : CI = BJ
      · subst BJ; exact lift_refl
      · exact I.inherited_lift hCI hBJ h he (mem_initial I |>.mp hscope).2)

theorem small_scopes (hunion : A = B ∪ C) {S : Finset ι}
    (hS : S ∈ R) (hcard : S.card ≤ 1) : S ∈ initialScopes I := by
  refine (mem_initial I).mpr ⟨hS, ?_⟩
  by_cases hs : S.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hxa := I.isPlan.subset_of_mem hS hx
    rw [hunion, Finset.mem_union] at hxa
    have he : ∀ y ∈ S, y = x := fun y hy => Finset.card_le_one.mp hcard y hy x hx
    exact hxa.imp (fun h y hy => he y hy ▸ h) (fun h y hy => he y hy ▸ h)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hs ▸ Finset.empty_subset B)

/-- This record is inhabited by `construct`, not an assumed local-operator
interface. All proper targets have been constructed and have unrestricted lifts. -/
structure Completed where
  scopes : Finset (Finset ι)
  state : State I.rows (initialScopes I) N G θ scopes
  done : ∀ S ∈ R, S ≠ A → S ∈ scopes

def construct (hunion : A = B ∪ C) (hcard : A.card = N + 1)
    (hG : ∀ z ∈ G, SelfVis N z) (hθ : SelfVis N θ) (htθ : θ ≠ ⊤) (hθG : θ ∈ G) :
    Completed I N G θ := by
  let hx := exists_completed
    (D := I.boundary) (sem := I.rows) (F₀ := initialScopes I) (N := N) (G := G) (θ := θ)
    (by
      intro S hS hSA
      have hs := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨I.isPlan.subset_of_mem hS, hSA⟩)
      omega)
    (fun _ hS hc => small_scopes I hunion hS hc)
    hG hθ htθ hθG (seed I hBA hCA N G θ)
  exact ⟨Classical.choose hx, Classical.choice (Classical.choose_spec hx).1,
    (Classical.choose_spec hx).2⟩

variable {N G θ} (X : Completed I N G θ)

theorem proper (d : Cell X.state.carrier) : X.state.carrier.scope d ≠ A := by
  intro he
  have hm := X.state.occupied d
  rw [he] at hm
  exact X.state.proper hm

theorem complete {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hJA : J.1 ≠ A) :
    ∃ d, X.state.carrier.cell d = J :=
  X.state.complete J hJ (X.done J.1 (Plan.mem_gradedPlan.mp hJ).1 hJA)

theorem lifts : CanonicalCoatomBountiful.OldLifts X.state.rows := by
  intro CI BJ hCI hBJ hJA h
  rw [X.state.plan] at hCI hBJ
  exact X.state.lifts CI BJ hCI hBJ (X.done BJ.1 (Plan.mem_gradedPlan.mp hBJ).1 hJA) h

theorem ready : OrdinaryRawScope.Ready X.state.rows where
  proper := proper I X
  consistent := X.state.consistent
  coded := X.state.coded
  lifts := lifts I X
  complete _ hJ hJA := complete I X (by rwa [X.state.plan] at hJ) hJA

/-- Every literal initial face survives all later scope completions. -/
def face {T : Finset ι} {D : CellScheme T} {sem : Semantics D}
    (E : ExactSemanticFace sem I.rows) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace sem X.state.rows where
  map := E.map.trans X.state.original.toEmbedding
  index d := (X.state.index (E.map d)).trans (E.index d)
  exhaustive d hd := by
    have hm : X.state.carrier.scope d ∈ initialScopes I := by
      refine (mem_initial I).mpr ⟨?_, hT.imp hd.trans hd.trans⟩
      have hp := X.state.carrier.scope_mem_plan d
      rwa [X.state.plan] at hp
    obtain ⟨e, rfl⟩ := X.state.exhaustive d hm
    have hs : I.boundary.scope e ⊆ T := by
      simpa only [CellScheme.scope, X.state.index] using hd
    obtain ⟨c, rfl⟩ := E.exhaustive e hs
    exact ⟨c, rfl⟩
  row c d := (X.state.row (E.map c) (E.belowMap c d)).trans (E.row c d)

def leftFace : ExactSemanticFace I.leftRows X.state.rows :=
  face I X I.leftFace (Or.inl (Finset.Subset.refl B))

def rightFace : ExactSemanticFace I.rightRows X.state.rows :=
  face I X I.rightFace (Or.inr (Finset.Subset.refl C))

theorem left_order : StrictMono (leftFace I X).map :=
  X.state.original.strictMono.comp I.left_order

theorem right_order : StrictMono (rightFace I X).map :=
  X.state.original.strictMono.comp I.right_order

/-- Newly completed grade-N proper owners are mute; the private face is
excluded explicitly, while its actual grade-N owners remain in the inventory. -/
theorem nonprivate_mute (hcard : A.card = N + 1) (hB : B.card = N) (hC : C.card < N)
    (d : Cell X.state.carrier) (hg : X.state.carrier.grade d = N)
    (hd : X.state.carrier.scope d ≠ B) : X.state.rows.E d ⟨d, GradedLe.refl _⟩ = ⊥ := by
  have hs := X.state.carrier.isPlan.subset_of_mem (X.state.carrier.scope_mem_plan d)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, proper I X d⟩)
  have hge := X.state.carrier.grade_le_card_scope d
  have hsize : (X.state.carrier.scope d).card = N := by omega
  apply X.state.mute d (hg.trans hsize.symm)
  intro hi
  rcases (mem_initial I |>.mp hi).2 with hl | hr
  · exact hd (Finset.eq_of_subset_of_card_le hl (hB.trans_le hsize.ge))
  · have := Finset.card_le_card hr
    omega

end
end VaughtConjecture.Knight.OrdinaryProperPredecessor
