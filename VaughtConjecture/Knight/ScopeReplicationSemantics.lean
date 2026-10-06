/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationCarrier
public import VaughtConjecture.Knight.ExactSemanticFace

/-! # Actual rows and lawful duplication across mixed scopes

The rows are pulled back along prototype erasure. Locality reuses the same
faithful witness on the enlarged domain; availability relocates the original
witness to the actual target scope. This proves consistency without any mixed
lifting or arbitrary-section extension premise. Only original proper owners
retain an entire lower domain. Full-scope owners retain their old columns.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ScopeReplicationSemantics
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

def rows : Semantics (scheme D B C) where
  E c d := sem.E (erase D B C c) (belowErase D B C hcover c d)
  orderly c d := by
    change sem.E _ _ = extVisibilityReplace (sem.E _ _)
      ((scheme D B C).grade d.1) ((scheme D B C).grade d.1)
    rw [← erase_grade]
    exact sem.orderly _ _

theorem row_eq (c : Cell (scheme D B C))
    (d : (scheme D B C).below ((scheme D B C).cell c)) :
    (rows D B C hcover sem).E c d = sem.E (erase D B C c) (belowErase D B C hcover c d) :=
  rfl

/-- Every old source column is literal, even when the owner's new lower domain
contains additional copies. -/
theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D B C hcover sem).E (old D B C c)
      ⟨old D B C d.1, by rw [old_index, old_index]; exact d.2⟩ = sem.E c d := by
  change sem.E _ _ = _
  exact sem.E_congr (erase_old D B C c) (erase_old D B C d.1)

/-- Lawful pullback to an actual lower domain. Its erased coordinates must lie
in the supplied original domain; no completeness or extension is assumed. -/
theorem duplicateBelow_respects {J K : Finset ι × ℕ}
    (hdom : ∀ d : (scheme D B C).below J, GradedLe (D.cell (erase D B C d.1)) K)
    {p : D.below K → ExtOrd} (hp : RespectsSemanticsBelow sem K p) :
    RespectsSemanticsBelow (rows D B C hcover sem) J
      (fun d => p ⟨erase D B C d.1, hdom d⟩) where
  orderly d := by
    change p _ = extVisibilityReplace (p _) ((scheme D B C).grade d.1)
      ((scheme D B C).grade d.1)
    rw [← erase_grade]
    exact hp.orderly _
  locality c := by
    have ht := (hp.locality ⟨erase D B C c.1, hdom c⟩).reindex
      (belowErase D B C hcover c.1)
    exact transformsTo_congr (funext fun d => erase_grade D B C d.1) rfl rfl ht
  availability c t hs hg := by
    have he := erase_le D B C hcover (d := c.1) (c := t.1) ⟨hs, hg.le⟩
    have heg : D.grade (erase D B C c.1) = D.grade (erase D B C t.1) := by
      rw [erase_grade, erase_grade]; exact hg
    obtain ⟨w, hw, hle⟩ := hp.availability
      ⟨erase D B C c.1, hdom c⟩ ⟨erase D B C t.1, hdom t⟩ he.1 heg
    obtain ⟨z, hz, hez⟩ := exists_at_index D B C t.1 w.1 hw
    refine ⟨⟨z, hz ▸ t.2⟩, hz, ?_⟩
    have hsub : (⟨erase D B C z, hdom ⟨z, hz ▸ t.2⟩⟩ : D.below K) = w :=
      Subtype.ext hez
    simpa only [hsub] using hle

/-- Duplication of any lawful whole section is lawful, including long source
rows, literal top and unsynchronized auxiliary values. -/
theorem duplicate_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D B C hcover sem) (p ∘ erase D B C) := by
  have hd (d : (scheme D B C).below (A, A.card)) :
      GradedLe (D.cell (erase D B C d.1)) (A, A.card) :=
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _),
      (D.grade_le_card_scope _).trans
        (Finset.card_le_card (D.isPlan.subset_of_mem (D.scope_mem_plan _)))⟩
  exact (duplicateBelow_respects D B C hcover sem hd (hp.toBelow (A, A.card))).toRespects
    (fun d => ⟨(scheme D B C).isPlan.subset_of_mem ((scheme D B C).scope_mem_plan d),
      ((scheme D B C).grade_le_card_scope d).trans
        (Finset.card_le_card ((scheme D B C).isPlan.subset_of_mem
          ((scheme D B C).scope_mem_plan d)))⟩)

/-- Consistency of the installed replicated rows is constructed, independently
of any lifting theorem. -/
theorem consistent (hc : sem.IsConsistent) : (rows D B C hcover sem).IsConsistent := by
  intro c
  exact duplicateBelow_respects D B C hcover sem
    (fun d => erase_le D B C hcover d.2) (hc (erase D B C c))

/-- Restriction to the retained single-copy occurrences is lawful. Availability
witnesses at old indices cannot be newly appended copies. -/
theorem restrict_respects {J : Finset ι × ℕ}
    {p : (scheme D B C).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) J p) :
    RespectsSemanticsBelow sem J (p ∘ oldBelow D B C J) where
  orderly d := by
    simpa only [Function.comp_apply, CellScheme.grade, oldBelow, old_index]
      using hp.orderly (oldBelow D B C J d)
  locality c := by
    have ht := (hp.locality (oldBelow D B C J c)).reindex
      (fun d : D.below (D.cell c.1) =>
        (⟨old D B C d.1, by rw [old_index, old_index]; exact d.2⟩ :
          (scheme D B C).below ((scheme D B C).cell (old D B C c.1))))
    exact transformsTo_congr
      (funext fun d => congrArg Prod.snd (old_index D B C d.1))
      (funext fun d => inherited_row D B C hcover sem c.1 d) rfl ht
  availability c t hs hg := by
    obtain ⟨w, hw, hle⟩ := hp.availability (oldBelow D B C J c) (oldBelow D B C J t)
      (by simpa only [CellScheme.scope, oldBelow, old_index] using hs)
      (by simpa only [CellScheme.grade, oldBelow, old_index] using hg)
    obtain ⟨z, hz⟩ := old_index_exhaustive D B C hcover t.1 w.1
      (hw.trans (old_index D B C t.1))
    have hzJ : GradedLe (D.cell z) J := by rw [← old_index D B C z, hz]; exact w.2
    refine ⟨⟨z, hzJ⟩, ?_, ?_⟩
    · exact (old_index D B C z).symm.trans (hz ▸ hw.trans (old_index D B C t.1))
    · have he : oldBelow D B C J ⟨z, hzJ⟩ = w := Subtype.ext hz
      change p (oldBelow D B C J c) ≤ p (oldBelow D B C J ⟨z, hzJ⟩)
      rw [he]
      exact hle

/-- An arbitrary lawful section assigns the same value to nested copies of
one prototype. This uses actual locality and availability, not a renderer or
any synchronization/admission hypothesis. -/
theorem copy_eq {J : Finset ι × ℕ} {p : (scheme D B C).below J → ExtOrd}
    (hp : RespectsSemanticsBelow (rows D B C hcover sem) J p)
    (a b : (scheme D B C).below J)
    (hs : (scheme D B C).scope a.1 ⊆ (scheme D B C).scope b.1)
    (he : erase D B C a.1 = erase D B C b.1) : p a = p b := by
  have hg : (scheme D B C).grade a.1 = (scheme D B C).grade b.1 :=
    (erase_grade D B C a.1).symm.trans
      ((congrArg D.grade he).trans (erase_grade D B C b.1))
  have hw : ∃ w : (scheme D B C).below J,
      (scheme D B C).cell w.1 = (scheme D B C).cell b.1 ∧ p a ≤ p w ∧ p b ≤ p w := by
    rcases le_total (p a) (p b) with h | h
    · exact ⟨b, rfl, h, le_rfl⟩
    · obtain ⟨w, hi, hv⟩ := hp.availability a b hs hg
      exact ⟨w, hi, hv, h.trans hv⟩
  obtain ⟨w, hi, ha, hb⟩ := hw
  let da : (scheme D B C).below ((scheme D B C).cell w.1) :=
    ⟨a.1, hi ▸ (show GradedLe ((scheme D B C).cell a.1) ((scheme D B C).cell b.1)
      from ⟨hs, hg.le⟩)⟩
  let db : (scheme D B C).below ((scheme D B C).cell w.1) :=
    ⟨b.1, hi ▸ GradedLe.refl _⟩
  have hrow : (rows D B C hcover sem).E w.1 da = (rows D B C hcover sem).E w.1 db :=
    sem.E_congr rfl he
  obtain ⟨g, σ, _, _, _, _, _, hread⟩ := hp.locality w
  have hval : min (p a) (p w) = min (p b) (p w) := by
    calc
      _ = min (σ ((rows D B C hcover sem).E w.1 da))
          (g ((scheme D B C).grade a.1)) := hread da
      _ = min (σ ((rows D B C hcover sem).E w.1 db))
          (g ((scheme D B C).grade b.1)) := by rw [hrow, hg]
      _ = _ := (hread db).symm
  simpa only [min_eq_left ha, min_eq_left hb] using hval

/-- Any literal original face contained in either side remains occurrence-exact. -/
def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE sem) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows D B C hcover sem) where
  map := F.map.trans ⟨old D B C, (old_order D B C).injective⟩
  index d := (old_index D B C (F.map d)).trans (F.index d)
  exhaustive z hz := by
    rcases cases D B C z with ⟨d, rfl⟩ | ⟨p, rfl⟩
    · obtain ⟨e, he⟩ := F.exhaustive d (by
        simpa only [CellScheme.scope, old_index] using hz)
      exact ⟨e, congrArg (old D B C) he⟩
    · have hs : p.1.1.1 ⊆ T := by
        simpa only [CellScheme.scope, added_index] using hz
      exact (hT.elim (fun h => p.2.2.1.1 (hs.trans h))
        (fun h => p.2.2.1.2 (hs.trans h))).elim
  row c d := (inherited_row D B C hcover sem (F.map c)
    ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩).trans (F.row c d)

end
end VaughtConjecture.Knight.ScopeReplicationSemantics
