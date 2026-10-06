/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedLegalCertificate
public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.LowOnlyActualState

/-! # Cap-native exact receiving from the constructed LOW certificate

Finite-cover receiving installs an approximation to the lawful whole display
over an actual private tuple. The private labels stay literal by consistency;
the two physical separator readings then force the donor labels exactly.

The family, its ordered two-face attachment, and an active state with a cutoff
below the stage are explicit inputs. The finished display is truncated once;
its auxiliary labels need no stage bounds. The historical bounded-state API
is retained as a wrapper. No exact-receiving or physical-probe hypothesis is used.
The target supplies only exact consistency and finite-cut receiving, not realization covering.
Finite geometric coverage of the attachment remains explicit. The first-loss acquisition and
its rootwise attachment are separate adapters.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedModelReceiving
open TypeTower StageType KnightRealization Value ExtOrd CappedDonor LowOnly
open CellScheme.restrictFace
noncomputable section
universe w
variable {l m n K : ℕ} {B C : Finset (Fin l)} {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

local notation "E" => LowOnlyPaddedLegal.semScheme I F hroot hA hB hC hcover
local notation "donor" => LowOnlyPaddedLegal.donor I F hroot hA hB hC hcover
local notation "priv" => LowOnlyPaddedLegal.privateFace I F hroot hA hB hC hcover

include hroot hA hB hC hcover in
/-- Receive from a raw certificate by truncating the finished lawful display.
Only the cutoff is bounded by the stage; the actual private face remains literal.
The separator certificate, not cap cancellation alone, recovers donor tops. -/
theorem receive_raw_of_receiving {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b)
    (hb : S.b < ofOrd α.1)
    (u : Fin n ↪ M) (pC : StageType α.1 n) (hu : W.eval u = some pC)
    (hCs : pC.scheme = I.right)
    (hCv : ∀ d, pC.label d = S.v (SemScheme.castCell hCs d)) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left,
        ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  obtain ⟨w, hw, -, hwp, -, hread⟩ :=
    LowOnlyPaddedLegalCertificate.exists_supported_certificate I F hroot hA hB hC hcover
      hS hdonor hc hr hactive
  let Q : StageType α.1 l := ofRespects α.2 E w hw
  have hvC := LowOnlyPaddedLegal.private_visible I F hroot hA hB hC hcover
  have hsC := LowOnlyPaddedLegal.restrict_private I F hroot hA hB hC hcover
  have hoccC (d : Cell I.right.scheme) :
      toCell (E).scheme I.placeRight hvC (SemScheme.castCell hsC.symm d) = (priv).map d :=
    LowOnlyPaddedLegal.private_occurrence I F hroot hA hB hC hcover d
  have hp : typeMap I.placeRight Q = some pC := by
    apply (typeMap_eq_some_iff_labels I.placeRight Q pC hvC (hsC.trans hCs.symm)).mpr
    change ∀ i : Cell ((E).restrictFace I.placeRight hvC).scheme,
      truncExt α.1 (w (toCell (E).scheme I.placeRight hvC i)) =
        pC.label (SemScheme.castCell (hsC.trans hCs.symm) i)
    intro i
    have hi := hoccC (SemScheme.castCell hsC i)
    simp only [SemScheme.castCell_castCell_symm] at hi
    change truncExt α.1 (w (toCell (E).scheme I.placeRight hvC i)) = _
    rw [(congrArg w hi).trans ((hwp _).trans
      (hCv (SemScheme.castCell (hsC.trans hCs.symm) i)).symm)]
    exact truncExt_id_of_bound (pC.label_bound _)
  obtain ⟨v, Q', hv, hev, hq, hcap⟩ :=
    FiniteCoverReceiving.finiteCoverReceiving_of_receiving hcons hFC Q I.placeRight u pC hp hu S.b
      (lt_of_le_of_lt bot_le hactive) hb
  let q : Cell (E).scheme → ExtOrd := fun d => Q'.label (SemScheme.castCell hq.symm d)
  have hqLaw : RespectsSemantics (E).rows q := respects_castCell hq Q'.respects
  let T : StageType α.1 l := ⟨E, q, fun d => Q'.label_bound _, hqLaw⟩
  have hQT : Q' = T := StageType.eq_of_label hq (fun _ => rfl)
  rw [hQT] at hev
  have hprivate : typeMap I.placeRight T = some pC := by
    have h := hcons v T I.placeRight hev
    rw [hv, hu] at h
    exact h.symm
  have hretain : ∀ d, q ((priv).map d) = S.v d := by
    intro d
    have h := (typeMap_eq_some_iff_labels I.placeRight T pC hvC
      (hsC.trans hCs.symm)).mp hprivate (SemScheme.castCell hsC.symm d)
    rw [hoccC d, hCv] at h
    exact h
  have hcaps : ∀ d, min (q d) S.b = min (w d) S.b := by
    intro d
    have he := hcap (SemScheme.castCell hq.symm d)
    change min (q d) S.b = min (truncExt α.1 (w d)) S.b at he
    exact he.trans (FiniteCoverReceiving.min_truncExt_of_lt hb (w d))
  have hdon : ∀ d, q ((donor).map d) = F.p d := hread q hqLaw hretain S.b hactive hcaps
  have hvD := LowOnlyPaddedLegal.donor_visible I F hroot hA hB hC hcover
  have hsD := LowOnlyPaddedLegal.restrict_donor I F hroot hA hB hC hcover
  refine ⟨v, T.restrictFace I.placeLeft hvD, hv, ?_, ?_, hsD, ?_⟩
  · rw [hcons v T I.placeLeft hev]
    exact typeMap_eq_some I.placeLeft T hvD
  · rw [← Function.Embedding.trans_assoc, I.commute, Function.Embedding.trans_assoc, hv]
  · intro d
    have hocc := LowOnlyPaddedLegal.donor_occurrence I F hroot hA hB hC hcover
      (SemScheme.castCell hsD d)
    change q (toCell (E).scheme I.placeLeft hvD d) = _
    have hd := hdon (SemScheme.castCell hsD d)
    rw [← hocc] at hd
    exact hd

include hroot hA hB hC hcover in
/-- The actual donor tuple is on the exact input scheme and has every donor
label literally, including top. It shares the literal common root with the
given private tuple. -/
theorem receive_of_receiving {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b)
    (hb : S.b < ofOrd α.1)
    (hbound : ∀ f, S.profile f ≠ ⊤ → S.profile f < ofOrd α.1)
    (u : Fin n ↪ M) (pC : StageType α.1 n) (hu : W.eval u = some pC)
    (hCs : pC.scheme = I.right)
    (hCv : ∀ d, pC.label d = S.v (SemScheme.castCell hCs d)) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left,
        ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  have _ := hbound -- Retained for compatibility; raw receiving does not need it.
  exact receive_raw_of_receiving I F hroot hA hB hC hcover hcons hFC
    hS hdonor hc hr hactive hb u pC hu hCs hCv

include hroot hA hB hC hcover in
/-- Exact receiving from the actual private tuple and a lawful donor sharing
its root. The active state and cutoff are constructed, not supplied. -/
theorem receive_of_shared_of_receiving {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) (u : Fin n ↪ M) (pC :
      StageType α.1 n)
    (hu : W.eval u = some pC) (hCs : pC.scheme = I.right)
    (hshared : F.root.Shared F.p (fun d => pC.label (SemScheme.castCell hCs.symm d)))
    (hc : pC.label (SemScheme.castCell hCs.symm F.gap.c) = ⊤)
    (hr : pC.label (SemScheme.castCell hCs.symm F.gap.r.1) = ⊤)
    (hpbound : ∀ d, F.p d ≠ ⊤ → F.p d < ofOrd α.1) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left,
        ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  let v : Cell I.right.scheme → ExtOrd := fun d => pC.label (SemScheme.castCell hCs.symm d)
  have hv : RespectsSemantics I.right.rows v := respects_castCell hCs pC.respects
  obtain ⟨b, hb, hadm, hactive, _hbound⟩ := LowOnlyActualState.exists_active F v hv hshared
    hpbound (fun d hd => (pC.label_bound _).resolve_right hd)
  exact receive_raw_of_receiving I F hroot hA hB hC hcover hcons hFC
    (S := ⟨F.p, v, b⟩) (hadm _) rfl hc hr hactive hb u pC hu hCs (fun _ => rfl)

end
end VaughtConjecture.Knight.LowOnlyPaddedModelReceiving
