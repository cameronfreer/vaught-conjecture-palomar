/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorAdmission
public import VaughtConjecture.Knight.ReceivingCatalogueSources

/-! # Admission and the actual canonical receiving catalogue

V-C's scalar `SourceAdmitted` and KVC's catalogue use the same complete field
inventory, including the stored cutoff. Catalogue membership is exactly scalar
admission plus a proper canonical fixed point. Restriction and normalization
produce lower-grade catalogue members, not upper-grade replacements.

The admission module is ported unchanged from V-C's `cf78464`. These adapters
change neither the fixed catalogue nor any physical row.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingCatalogueAdmission
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingSupportedRepair
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  (L : R.LowRef K)

/-- The two lane definitions coincide, with canonicality and properness explicit. -/
theorem mem_catalogue_iff {j : ℕ} {a : TField P C → ExtOrd} :
    a ∈ Catalogue (j := j) L ↔
      a ∈ CanonicalPairedProfiles.inventory (TField P C) j ∧ L.SourceAdmitted j a := Iff.rfl

/-- Scalar normalization is a catalogue member only when literal tops are
excluded; terminal properization remains a separate producer. -/
theorem normalize_mem {j : ℕ} (hj : 1 ≤ j) {a : TField P C → ExtOrd}
    (ha : L.SourceAdmitted j a) (hp : ∀ f, a f ≠ ⊤) :
    PairedSlotEncoding.normalize j a ∈ Catalogue (j := j) L :=
  (mem_catalogue_iff L).mpr
    ⟨CanonicalPairedProfiles.normalize_mem_inventory _ _ hp, ha.normalize L hj⟩

/-- A higher catalogue supplies a lower admitted profile with every field
retained before normalization. This implication has no upward converse here. -/
theorem restrict_admitted {i j : ℕ} (hij : i ≤ j) {a : TField P C → ExtOrd}
    (ha : a ∈ Catalogue (j := j) L) : L.SourceAdmitted i a :=
  ((mem_catalogue_iff L).mp ha).2.restrict L hij

/-- Downward normalization lands in the actual lower canonical catalogue.
Properness is derived from the original catalogue rather than added as a premise. -/
theorem restrict_normalize_mem {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {a : TField P C → ExtOrd} (ha : a ∈ Catalogue (j := j) L) :
    PairedSlotEncoding.normalize i a ∈ Catalogue (j := i) L :=
  normalize_mem L hi (restrict_admitted L hij ha) ha.1.2

/-- The frozen carrier's grade-two controller has a constructed grade-one
catalogue image. No grade-one repair is promoted back to a grade-two controller. -/
theorem controller_predecessor (a : ReceivingCatalogueSources.Controller L) :
    PairedSlotEncoding.normalize 1 a.val ∈ Catalogue (j := 1) L :=
  restrict_normalize_mem L le_rfl (by omega) a.property

end
end VaughtConjecture.Knight.ReceivingCatalogueAdmission
