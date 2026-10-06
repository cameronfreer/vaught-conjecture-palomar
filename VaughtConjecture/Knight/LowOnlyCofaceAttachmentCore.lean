/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedReceivingCore
public import VaughtConjecture.Knight.FirstLossLowFamilyCore
public import VaughtConjecture.Knight.CoatomBoundaryPresentation

/-! # Exact LOW receiving for two cofaces of a literal root

Construct the ordered boundary, two-coface plan, coverage, and common-root
occurrence receipt from the actual coface equations. The family uses the
literal common-root identification. No mixed scopes are added.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyCofaceAttachment
open TypeTower StageType KnightRealization Value ExtOrd CappedDonor LowOnly
open CellScheme.restrictFace FirstLossLowFamily AmalgamationPlan
noncomputable section
universe w

/-- The scheme-equality cast in the generic face map is the canonical
restriction occurrence, with no re-enumeration. -/
theorem faceMap_eq {m n : ℕ} (D : SemScheme n) (Q : SemScheme m)
    (f : Fin m ↪ Fin n) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (h : D.restrictFace f hv = Q) (d : Cell Q.scheme) :
    SemSchemeBoundaryInput.faceMap D Q f hv h d =
      toCell D.scheme f hv (SemScheme.castCell h.symm d) := by
  subst Q
  rfl

variable {α : LimitStage} {k K : ℕ} {p : StageType α.1 k}
  {P C : StageType α.1 (k + 1)} (hP : IsCoface p P) (hC : IsCoface p C)

def pair (k : ℕ) : CoatomPair k := CoatomPair.step Fin.castSuccEmb

def data : CoatomBoundaryPresentation.Data (pair k) where
  left := P.scheme
  right := C.scheme
  common := p.scheme
  visibleLeft := hP.extendsDomain.visible
  visibleRight := hC.extendsDomain.visible
  faceLeft := hP.extendsDomain.restrict
  faceRight := hC.extendsDomain.restrict

local notation "D" => data hP hC
local notation "s" => CoatomBoundaryPresentation.Data.step (data hP hC)

/-- The same ordered input in the general whole-boundary interface. -/
def input : WholeDonorBoundary.Input Finset.univ
    (Finset.univ.erase (s).a) (Finset.univ.erase (s).b) (s).plan k (k + 1) (k + 1) where
  isPlan := AmalgamatedBoundaryPlan.isPlan s
  left := P.scheme
  right := C.scheme
  common := p.scheme
  placeLeft := (pair k).f₁
  placeRight := (pair k).f₂
  imageLeft := (D).input.imageLeft
  imageRight := (D).input.imageRight
  commonLeft := Fin.castSuccEmb
  commonRight := Fin.castSuccEmb
  visibleLeft := hP.extendsDomain.visible
  visibleRight := hC.extendsDomain.visible
  faceLeft := hP.extendsDomain.restrict
  faceRight := hC.extendsDomain.restrict
  commute := (pair k).comm
  intersection := (D).input.intersection
  planLeft := (AmalgamatedBoundaryPlan.restrict_left s).trans (D).input.planLeft.symm
  planRight := (AmalgamatedBoundaryPlan.restrict_right s).trans (D).input.planRight.symm

local notation "I" => input hP hC

theorem root_receipt (F : LowOnly.Family P.scheme C.scheme K)
    (hF : F.root = commonRoot_of_cofaces hP hC) :
    ∀ i : Cell (I).common.scheme,
      ∃ a : (I).left.scheme.below (F.root.A, F.root.A.card),
        a.1 = (I).shared.f i ∧ (F.root.face a).1 = (I).shared.g i := by
  intro i
  have hrootcard : (rootFace k).card = k := by
    simp only [rootFace, Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
      Finset.card_univ, Fintype.card_fin]
  have hleft := faceMap_eq P.scheme p.scheme Fin.castSuccEmb
    hP.extendsDomain.visible hP.extendsDomain.restrict i
  have hright := faceMap_eq C.scheme p.scheme Fin.castSuccEmb
    hC.extendsDomain.visible hC.extendsDomain.restrict i
  let a : P.scheme.scheme.below (rootFace k, (rootFace k).card) :=
    ⟨(I).shared.f i, by
      change GradedLe (P.scheme.scheme.cell
        (SemSchemeBoundaryInput.faceMap P.scheme p.scheme Fin.castSuccEmb
          hP.extendsDomain.visible hP.extendsDomain.restrict i)) _
      have hi := SemSchemeBoundaryInput.faceMap_index P.scheme p.scheme Fin.castSuccEmb
        hP.extendsDomain.visible hP.extendsDomain.restrict i
      have hg : GradedLe ((p.scheme.scheme.scope i).image Fin.castSuccEmb,
          p.scheme.scheme.grade i) (rootFace k, (rootFace k).card) :=
        ⟨Finset.image_subset_image (Finset.subset_univ _),
          (FiniteCoverReceiving.grade_le_points p.scheme i).trans_eq hrootcard.symm⟩
      exact hi.symm ▸ hg⟩
  have hi : FirstLossLowFamily.rootCell hP a = i := by
    have h := (toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible).injective
      ((toCell_rootCell hP a).trans hleft)
    exact congrArg (SemScheme.castCell hP.extendsDomain.restrict) h
  rw [hF]
  refine ⟨a, rfl, ?_⟩
  change (faceOf hP hC a).1 = (I).shared.g i
  rw [faceOf_val, hi]
  exact hright.symm

theorem left_proper : Finset.univ.erase (s).a ⊂ (Finset.univ : Finset (Fin (k + 2))) :=
  Finset.erase_ssubset (s).ha

theorem right_proper : Finset.univ.erase (s).b ⊂ (Finset.univ : Finset (Fin (k + 2))) :=
  Finset.erase_ssubset (s).hb

theorem coverage : ∀ T ∈ (s).plan, T ≠ Finset.univ →
    T ⊆ Finset.univ.erase (s).a ∨ T ⊆ Finset.univ.erase (s).b :=
  LowOnlyPaddedPairLift.cover_two_cofaces s rfl rfl rfl

/-- Reidentify the root with its literal coface map. The old family's actual
shared labels ensure that its strict gaps cover every actual private root
top, regardless of which occurrence identification it originally exported. -/
def rebase (F : LowOnly.Family P.scheme C.scheme K)
    (hB : F.root.B = rootFace k) (hp : F.p = P.label)
    (hshared : F.root.Shared F.p C.label) : LowOnly.Family P.scheme C.scheme K where
  root := commonRoot_of_cofaces hP hC
  gap := F.gap
  p := F.p
  p_lawful := F.p_lawful
  top_grade := F.top_grade
  root_sub := by
    change rootFace k ⊆ C.scheme.scheme.scope F.gap.c
    exact hB ▸ F.root_sub
  root_gap := by
    intro a ha
    have htop : C.label ((commonRoot_of_cofaces hP hC).face a).1 = ⊤ :=
      (shared_of_cofaces hP hC a).symm.trans ((congrFun hp a.1).symm.trans ha)
    let b : C.scheme.scheme.below (F.root.B, F.root.B.card) :=
      ⟨((commonRoot_of_cofaces hP hC).face a).1, by
        rw [hB]
        exact ((commonRoot_of_cofaces hP hC).face a).2⟩
    let a₀ := F.root.face.symm b
    have harg : (F.root.face a₀).1 = ((commonRoot_of_cofaces hP hC).face a).1 :=
      congrArg Subtype.val (F.root.face.apply_symm_apply b)
    have ht₀ : F.p a₀.1 = ⊤ :=
      (hshared a₀).trans ((congrArg C.label harg).trans htop)
    exact (F.root_gap a₀ ht₀).trans_eq
      (congrArg (C.scheme.rows.E F.gap.c) (Subtype.ext harg))

/-- A supplied LOW family over two cofaces yields an actual copy of the donor
over their common root. The cutoff, physical scheme, and readback are derived. -/
theorem receive_of_receiving {M : Type w} {W : KnightRealization α M} (hcons :
    W.IsExactParentConsistent)
    (hFC : FiniteCutReceiving W)
    (u : Fin (k + 1) ↪ M) (hu : W.eval u = some C)
    (F : LowOnly.Family P.scheme C.scheme K)
    (hF : F.root = commonRoot_of_cofaces hP hC) (hp : F.p = P.label)
    (hc : C.label F.gap.c = ⊤) (hr : C.label F.gap.r.1 = ⊤) :
    ∃ t : Fin (k + 1) ↪ M,
      W.eval t = some P ∧ Fin.castSuccEmb.trans t = Fin.castSuccEmb.trans u := by
  have hs : F.root.Shared F.p C.label := by
    rw [hF, hp]
    exact shared_of_cofaces hP hC
  obtain ⟨v, pD, -, heval, htuple, heq, hlabel⟩ :=
    LowOnlyPaddedModelReceiving.receive_of_shared_of_receiving (I) F (root_receipt hP hC F hF)
      (by simp) (left_proper hP hC) (right_proper hP hC) (coverage hP hC)
      hcons hFC u C hu rfl hs hc hr (fun d hd => by
        rw [hp] at hd ⊢
        exact (P.label_bound d).resolve_right hd)
  have htype : pD = P := by
    apply StageType.eq_of_label heq
    intro d
    exact ((hlabel (SemScheme.castCell heq.symm d)).trans (congrFun hp _)).trans
      (congrArg P.label (SemScheme.castCell_castCell_symm heq d))
  exact ⟨(I).placeLeft.trans v, htype ▸ heval, htuple⟩

include hP hC in
/-- The exported acquisition data suffice: only the private root scope and
actual shared labels are needed, not equality of the hidden face map. -/
theorem receive_of_shared_of_receiving {M : Type w} {W : KnightRealization α M} (hcons :
    W.IsExactParentConsistent)
    (hFC : FiniteCutReceiving W)
    (u : Fin (k + 1) ↪ M) (hu : W.eval u = some C)
    (F : LowOnly.Family P.scheme C.scheme K)
    (hB : F.root.B = rootFace k) (hp : F.p = P.label)
    (hshared : F.root.Shared F.p C.label)
    (hc : C.label F.gap.c = ⊤) (hr : C.label F.gap.r.1 = ⊤) :
    ∃ t : Fin (k + 1) ↪ M,
      W.eval t = some P ∧ Fin.castSuccEmb.trans t = Fin.castSuccEmb.trans u :=
  receive_of_receiving hP hC hcons hFC u hu (rebase hP hC F hB hp hshared) rfl hp hc hr

end
end VaughtConjecture.Knight.LowOnlyCofaceAttachment
