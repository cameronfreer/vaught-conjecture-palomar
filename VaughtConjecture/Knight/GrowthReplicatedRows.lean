/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationLifting
public import VaughtConjecture.Knight.GrowthPaddedInstallation

/-! # The actual growth rows on every mixed scope

Instantiate scope replication on the constructed one-scope growth layers.
The catalogue and the full padded grade-one base are unchanged. Every mixed
scope receives each eligible full-scope prototype, with actual enlarged rows.
Consistency, coding, selected lawfulness, prefix agreement and support are
derived. Original faces remain literal and ordered. Completeness through the
installed height no longer assumes that proper scopes lie in an original face.
This does not yet prove arbitrary mixed-section extension or bountifulness.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthReplicatedRows
open AmalgamationPlan Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration ScopeReplicationCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}
  {k : ℕ} (P : Layer I X attach hA hB hC k)

/-- Every proper old owner lies inside an original face. This concerns
occupied cells, not a two-face cover of the whole plan. -/
theorem proper_covered (c : Cell P.carrier) (hc : P.carrier.scope c ≠ A) :
    P.carrier.scope c ⊆ B ∨ P.carrier.scope c ⊆ C := by
  rcases P.cases c with ⟨d, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) d with
      ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hi := (P.base_index (RelativeLadderLayer.old I.boundary (by omega) e)).trans
        (RelativeLadderLayer.old_index I.boundary (by omega) e)
      have he := (I.occupied_iff (I.boundary.cell_mem e)).mp ⟨e, rfl⟩
      simpa only [CellScheme.scope, hi] using he
    · exact (hc ((congrArg Prod.fst (P.base_index _)).trans
        (congrArg Prod.fst (RelativeLadderLayer.added_index I.boundary (by omega) v)))).elim
  · exact (hc hs).elim

abbrev carrier := ScopeReplicationCarrier.scheme P.carrier B C
abbrev old := ScopeReplicationCarrier.old P.carrier B C
abbrev erase := ScopeReplicationCarrier.erase P.carrier B C

def rows : Semantics (carrier P) :=
  ScopeReplicationSemantics.rows P.carrier B C (proper_covered P) P.rows

theorem consistent : (rows P).IsConsistent :=
  ScopeReplicationSemantics.consistent P.carrier B C (proper_covered P) P.rows P.consistent

theorem coded (hp : P.rows.IsCoded) : (rows P).IsCoded := by
  intro c d
  change IsCodedLabel ((carrier P).grade c) (P.rows.E (erase P c) _)
  rw [← ScopeReplicationCarrier.erase_grade P.carrier B C c]
  exact hp _ _

theorem inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (rows P).E (old P c)
      ⟨old P d.1, by rw [old_index, old_index]; exact d.2⟩ = P.rows.E c d :=
  ScopeReplicationSemantics.inherited_row P.carrier B C (proper_covered P) P.rows c d

def render {j : ℕ} (hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) (G : Finset ExtOrd) (H : ExtOrd) :
    Cell (carrier P) → ExtOrd := P.render hj S hS hp G H ∘ erase P

theorem render_lawful {j : ℕ} (hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hb : ∀ f, S.profile f ≤ H) :
    RespectsSemanticsBelow (rows P) (A, j) (fun d => render P hj S hS hp G H d.1) := by
  apply ScopeReplicationSemantics.duplicateBelow_respects P.carrier B C (proper_covered P)
    P.rows (K := (A, j))
      (fun d => ⟨P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan _),
        (ScopeReplicationCarrier.erase_grade P.carrier B C d.1).le.trans d.2.2⟩)
      (P.lawful hj S hS hp hG hH hb)

theorem render_prefix {j : ℕ} (hj : k ≤ j) (S T : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hT : Admitted X j T)
    (hp : ∀ f, S.profile f ≠ ⊤) (ht : ∀ f, T.profile f ≠ ⊤) {G H h}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hh : h ∈ G) (hb : h ≤ H)
    (hag : SourcePrefixRows.Agree S.profile T.profile h) :
    SourcePrefixRows.Agree (render P hj S hS hp G H) (render P hj T hT ht G H) h :=
  fun d => P.agreement hj S T hS hT hp ht hG hH hh hb hag (erase P d)

theorem render_supported {j : ℕ} (hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) {G : Finset ExtOrd} {H : ExtOrd}
    {l : ℕ} (hl : k ≤ l) (hH : H ∈ G) (d : Cell (carrier P)) :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile (render P hj S hS hp G H d) :=
  P.supported hj S hS hp hl hH (erase P d)

def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE P.rows) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows P) :=
  ScopeReplicationSemantics.face P.carrier B C (proper_covered P) P.rows F hT

theorem copy_eq {V : Finset ι × ℕ} {p : (carrier P).below V → ExtOrd}
    (hp : RespectsSemanticsBelow (rows P) V p) (a b : (carrier P).below V)
    (hs : (carrier P).scope a.1 ⊆ (carrier P).scope b.1) (he : erase P a.1 = erase P b.1) :
    p a = p b :=
  ScopeReplicationSemantics.copy_eq P.carrier B C (proper_covered P) P.rows hp a b hs he

/-- Replication consumes the single-scope lift, not a selected rendering or
an assumed extension of the replicated ambient. -/
theorem lift_to_full {U : Finset ι × ℕ} {j : ℕ} (h : GradedLe U (A, j))
    (hside : U.1 ⊆ B ∨ U.1 ⊆ C) (hl : CoatomBoundaryExtension.CappedLift P.rows h) :
    CoatomBoundaryExtension.CappedLift (rows P) h :=
  ScopeReplicationLifting.lift_to_full P.carrier B C (proper_covered P) P.rows h hside hl

section Constructed
variable (I X attach hA hB hC) (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev built := build I X attach hA hB hC t ht

theorem build_consistent : (rows (built I X attach hA hB hC t ht)).IsConsistent :=
  consistent _

theorem build_coded : (rows (built I X attach hA hB hC t ht)).IsCoded :=
  coded _ (GrowthPaddedInstallation.build_coded I X attach hA hB hC t ht)

def donorFace : ExactSemanticFace I.leftRows (rows (built I X attach hA hB hC t ht)) :=
  face _ (GrowthPaddedInstallation.donorFace I X attach hA hB hC t ht) (Or.inl le_rfl)

def privateFace : ExactSemanticFace I.rightRows (rows (built I X attach hA hB hC t ht)) :=
  face _ (GrowthPaddedInstallation.privateFace I X attach hA hB hC t ht) (Or.inr le_rfl)

theorem donor_order : StrictMono (donorFace I X attach hA hB hC t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.donor_order I X attach hA hB hC t ht)

theorem private_order : StrictMono (privateFace I X attach hA hB hC t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.private_order I X attach hA hB hC t ht)

/-- All actual plan scopes, mixed ones included, are occupied through the
installed height. No two-face coverage hypothesis remains. -/
theorem complete_through {V : Finset ι × ℕ} (hV : V ∈ Plan.gradedPlan R)
    (hv : V.2 ≤ t + 2) :
    ∃ d, (carrier (built I X attach hA hB hC t ht)).cell d = V := by
  classical
  let P := built I X attach hA hB hC t ht
  by_cases hside : V.1 ⊆ B ∨ V.1 ⊆ C
  · obtain ⟨d, hd⟩ := (I.occupied_iff hV).mpr hside
    refine ⟨old P (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d)), ?_⟩
    exact (old_index _ B C _).trans ((P.base_index _).trans
      ((RelativeLadderLayer.old_index I.boundary (by omega) d).trans hd))
  · obtain ⟨c, hc⟩ := GrowthPaddedInstallation.full_occupied I X attach hA hB hC t ht
      V.2 (Plan.mem_gradedPlan.mp hV).2.1 hv
    have hs : P.carrier.scope c = A := congrArg Prod.fst hc
    have hg := congrArg Prod.snd hc
    change P.carrier.grade c = V.2 at hg
    have hm : V.1 = A ∨ Mixed B C V.1 := Or.inr
      ⟨fun h => hside (Or.inl h), fun h => hside (Or.inr h)⟩
    have hplan : V.1 ∈ P.carrier.plan := by
      rw [GrowthPaddedIteration.build_plan]; exact (Plan.mem_gradedPlan.mp hV).1
    refine ⟨atScope P.carrier B C V.1 hplan hm c hs
      (hg ▸ (Plan.mem_gradedPlan.mp hV).2.2), ?_⟩
    exact (atScope_index P.carrier B C _ _ _ _ _ _).trans (by rw [hg])

end Constructed

/-- At full installed height every graded-plan index is occupied, including
all mixed scopes. This is completeness, not bountifulness. -/
theorem complete :
    (carrier (built I X attach hA hB hC (A.card - 2) (by omega))).IsComplete := by
  intro V hV
  have hp : (carrier (built I X attach hA hB hC (A.card - 2) (by omega))).plan = R :=
    GrowthPaddedIteration.build_plan I X attach hA hB hC (A.card - 2) (by omega)
  have hV' : V ∈ Plan.gradedPlan R := by rwa [hp] at hV
  have hg := (Plan.mem_gradedPlan.mp hV').2.2
  have hs := I.boundary.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1
  have hc := Finset.card_le_card hs
  exact complete_through I X attach hA hB hC (A.card - 2) (by omega) hV' (by omega)

/-- Targets inside either literal original face use that face's existing
bountifulness, with no mixed-target extension premise. -/
theorem inherited_lift (t : ℕ) (ht : t + 2 ≤ A.card) {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CoatomBoundaryExtension.CappedLift (rows (built I X attach hA hB hC t ht)) h := by
  by_cases he : U = V
  · subst V; exact CoatomBoundaryExtension.lift_refl
  rcases hv with hb | hc
  · exact (donorFace I X attach hA hB hC t ht).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace I X attach hA hB hC t ht).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end
end VaughtConjecture.Knight.GrowthReplicatedRows
