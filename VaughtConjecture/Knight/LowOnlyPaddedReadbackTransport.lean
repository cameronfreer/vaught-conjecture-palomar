/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedRestriction
public import VaughtConjecture.Knight.LowOnlyPaddedRankReadback
public import VaughtConjecture.Knight.LowOnlyPaddedTwoReadback

/-! # Native LOW readback retained through later installed layers

Actual occurrence maps and literal inherited rows transfer the three native
readback cases to arbitrary whole lawful sections of later carriers. These
are not identities between renderings at different construction grades.
The physical separator and the two private top receipts remain explicit.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedRestriction
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n)

section Rank
variable (F : LowOnly.Family I.left I.right 1)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  {k : ℕ} (P : Layer I F hroot hA hB hC k)

theorem rank_readback {S : State I.left I.right}
    (hlt : LowSeparator.donorMax (LowSeparator.donorField F) S.profile < S.b)
    {qs qt : F.Anchor 1}
    (hqs : RelativeLadderLayer.ranks (F.fields 1) qs = LadderScalarRendering.fieldRank S.profile)
    (hqt : RelativeLadderLayer.ranks (F.fields 1) qt = LadderScalarRendering.fieldRank
      (LowSeparatorRank.rankPartner (LowSeparator.donorField F) LowSeparator.cutoffField S.profile))
    {q : Cell P.carrier → ExtOrd} (hq : RespectsSemantics P.rows q)
    (hsep : q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qt).1) <
      q (P.baseMap (RelativeLadderLayer.leafOccurrence I.boundary (by omega) qs).1))
    (hc : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.c))) = ⊤)
    (hr : q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega)
      (I.rightFace.map F.gap.r.1))) = ⊤)
    (d : I.left.scheme.below (effC n 1)) (hd : F.p d.1 = ⊤) :
    q (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1))) = ⊤ :=
  LowOnlyPaddedRankReadback.donor_top_of_separator I F hroot (by omega) hB hC
    hlt hqs hqt (base_pullback I F hroot hA hB hC P hq) hsep hc hr d hd
end Rank

section Two
variable (F : LowOnly.Family I.left I.right 2)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (r : ℕ) (hheight : 0 + r + 2 ≤ A.card)

abbrev twoAt := belowEquiv I F hroot hA hB hC 0 hA (A, 2) le_rfl r hheight

open LowOnlyPaddedTwoReadback in
theorem two_readback (S : State I.left I.right) (hS : F.Admissible 2 S)
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
    (hlt : LowSeparator.cutoffCut 2 (LowSeparator.donorField F) S.profile < S.b)
    {q : Cell (build I F hroot hA hB hC (0 + r) hheight).carrier → ExtOrd}
    (hq : RespectsSemantics (build I F hroot hA hB hC (0 + r) hheight).rows q)
    (hc : q (twoAt I F hroot hA hB hC r hheight
      (LowOnlyPaddedDecode.privateAt I F hroot hA hB hC (F.gap.cC le_rfl))).1 = ⊤)
    (hr : q (twoAt I F hroot hA hB hC r hheight
      (LowOnlyPaddedDecode.privateAt I F hroot hA hB hC (F.gap.rC le_rfl))).1 = ⊤)
    (hsep : q (twoAt I F hroot hA hB hC r hheight
        (leafAt I F hroot hA hB hC (partnerAnchor I F S hS hcan hlt))).1 <
      q (twoAt I F hroot hA hB hC r hheight
        (leafAt I F hroot hA hB hC (selectedAnchor I F S hS hcan))).1)
    (d : I.left.scheme.below (effC n 2)) (hd : F.p d.1 = ⊤) :
    q (twoAt I F hroot hA hB hC r hheight
      (LowOnlyPaddedDecode.donorAt I F hroot hA hB hC d)).1 = ⊤ :=
  donor_top_of_separator I F hroot hA hB hC S hS hcan hlt
    (whole_pullback I F hroot hA hB hC 0 hA (A, 2) le_rfl r hheight hq) hc hr hsep d hd
end Two

section Higher
variable (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2 + 1))
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (ht : (t + 1) + 2 ≤ A.card) (r : ℕ) (hheight : (t + 1) + r + 2 ≤ A.card)

abbrev higherAt :=
  belowEquiv I F hroot hA hB hC (t + 1) ht (A, t + 2 + 1) le_rfl r hheight

open LowOnlyPaddedStepReadback LowOnlyPaddedStepChart in
theorem higher_readback (S : State I.left I.right) (hS : F.Admissible (t + 2 + 1) S)
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory
      (Field I.left I.right) (t + 2 + 1))
    (hlt : LowSeparator.cutoffCut (t + 2 + 1) (LowSeparator.donorField F) S.profile < S.b)
    {q : Cell (build I F hroot hA hB hC ((t + 1) + r) hheight).carrier → ExtOrd}
    (hq : RespectsSemantics (build I F hroot hA hB hC ((t + 1) + r) hheight).rows q)
    (hc : q (higherAt I t F hroot hA hB hC ht r hheight
      (LowOnlyPaddedStepDecode.privateAt (build I F hroot hA hB hC t (by omega)) ht
        (F.gap.cC le_rfl))).1 = ⊤)
    (hr : q (higherAt I t F hroot hA hB hC ht r hheight
      (LowOnlyPaddedStepDecode.privateAt (build I F hroot hA hB hC t (by omega)) ht
        (F.gap.rC le_rfl))).1 = ⊤)
    (hsep : q (higherAt I t F hroot hA hB hC ht r hheight
        (leafAt (build I F hroot hA hB hC t (by omega)) ht
          (partnerAnchor S hS hcan hlt))).1 <
      q (higherAt I t F hroot hA hB hC ht r hheight
        (leafAt (build I F hroot hA hB hC t (by omega)) ht
          (selectedAnchor S hS hcan))).1)
    (d : Cell I.left.scheme) (hd : F.p d = ⊤) :
    q (higherAt I t F hroot hA hB hC ht r hheight
      (donorTopAt (build I F hroot hA hB hC t (by omega)) ht d hd)).1 = ⊤ :=
  donor_top_of_separator (build I F hroot hA hB hC t (by omega)) (by omega) ht
    S hS hcan hlt
    (whole_pullback I F hroot hA hB hC (t + 1) ht (A, t + 2 + 1) le_rfl r hheight hq)
    hc hr hsep d hd
end Higher

end
end VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport
