/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

/-! # Literal common faces

The face identification of the capped-donor reference data (`CappedDonor.Ref.face`, with its
lawfulness transport `face_respects`) derived from **literal face restrictions**: when the
request scheme `P` restricted along `fP` and the private scheme `C` restricted along `fC` are the
same domain `F` (as `SemScheme`s), the lower sets `(fP[univ], KA)` of `P` and `(fC[univ], KA)`
of `C` are identified through `F` (`commonFace`), and restricted lawfulness transports along the
identification in both directions (`commonFace_respects`), by the existing transport of respect
along a face restriction (`RespectsSemanticsBelow.restrictFace` / `.of_restrictFace`) and the
transport along an equality of domains (`castBelow_respects`).  The underlying cell of the
identification is computed by `commonFace_val`; the identification preserves grades
(`commonFace_grade`) and the identifications at two grades agree on a common cell
(`commonFace_val_congr`), which is what makes it a graded identification of the whole literal
root; labels transport along an equality of stage types by `StageType.label_castCell`. -/

@[expose] public section

namespace VaughtConjecture.Knight

open CellScheme.restrictFace

/-- Labels transport along an equality of stage types. -/
theorem StageType.label_castCell {α : Ordinal.{0}} {n : ℕ} {X Y : S α n} (h : X = Y)
    (c : Cell X.scheme.scheme) :
    Y.label (SemScheme.castCell (congrArg StageType.scheme h) c) = X.label c := by
  subst h; rfl

namespace CappedDonor

/-- Transport of a lower set along an equality of domains. -/
def castBelow {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ) :
    X.scheme.below BJ ≃ Y.scheme.below BJ :=
  Equiv.cast (congrArg (fun Z : SemScheme n => Z.scheme.below BJ) h)

theorem castBelow_val {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ)
    (d : X.scheme.below BJ) : (castBelow h BJ d).1 = SemScheme.castCell h d.1 := by
  subst h; rfl

theorem castBelow_castBelow_symm {n : ℕ} {X Y : SemScheme n} (h : X = Y)
    (BJ : Finset (Fin n) × ℕ) (d : Y.scheme.below BJ) :
    castBelow h BJ (castBelow h.symm BJ d) = d := by
  subst h; rfl

theorem castBelow_symm_castBelow {n : ℕ} {X Y : SemScheme n} (h : X = Y)
    (BJ : Finset (Fin n) × ℕ) (d : X.scheme.below BJ) :
    castBelow h.symm BJ (castBelow h BJ d) = d := by
  subst h; rfl

theorem castBelow_symm {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ) :
    (castBelow h BJ).symm = castBelow h.symm BJ := by
  subst h; rfl

/-- Restricted lawfulness transports along an equality of domains. -/
theorem castBelow_respects {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ)
    (r : Y.scheme.below BJ → ExtOrd) :
    RespectsSemanticsBelow Y.rows BJ r ↔
      RespectsSemanticsBelow X.rows BJ (fun d => r (castBelow h BJ d)) := by
  subst h; exact Iff.rfl

/-- Transport of a cell along an equality of domains keeps its grade. -/
theorem castCell_grade {n : ℕ} {X Y : SemScheme n} (h : X = Y) (c : Cell X.scheme) :
    Y.scheme.grade (SemScheme.castCell h c) = X.scheme.grade c := by
  subst h; rfl

section CommonFace

variable {n nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J} {F : SemScheme n}
  (fP : Fin n ↪ Fin (nP + 1)) (hvP : Finset.univ.image fP ∈ P.scheme.plan)
  (hP : P.restrictFace fP hvP = F)
  (fC : Fin n ↪ Fin J) (hvC : Finset.univ.image fC ∈ C.scheme.plan)
  (hC : C.restrictFace fC hvC = F) (KA : ℕ)

/-- The face bijection on the request side. -/
noncomputable abbrev bP :
    (P.restrictFace fP hvP).scheme.below (Finset.univ, KA) ≃
      P.scheme.below (Finset.univ.image fP, KA) :=
  belowEquiv P.scheme fP hvP (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fP, KA)) rfl

/-- The face bijection on the private side. -/
noncomputable abbrev bC :
    (C.restrictFace fC hvC).scheme.below (Finset.univ, KA) ≃
      C.scheme.below (Finset.univ.image fC, KA) :=
  belowEquiv C.scheme fC hvC (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fC, KA)) rfl

/-- **The identification of the two copies of a literally common face**: through the common
restriction `F`, along the bijections `belowEquiv` of the face restrictions. -/
noncomputable def commonFace :
    P.scheme.below (Finset.univ.image fP, KA) ≃ C.scheme.below (Finset.univ.image fC, KA) :=
  (bP fP hvP KA).symm.trans
    ((castBelow hP (Finset.univ, KA)).trans
      ((castBelow hC.symm (Finset.univ, KA)).trans (bC fC hvC KA)))

theorem commonFace_apply (a : P.scheme.below (Finset.univ.image fP, KA)) :
    commonFace fP hvP hP fC hvC hC KA a =
      bC fC hvC KA (castBelow hC.symm (Finset.univ, KA)
        (castBelow hP (Finset.univ, KA) ((bP fP hvP KA).symm a))) := rfl

theorem commonFace_symm_apply (e : C.scheme.below (Finset.univ.image fC, KA)) :
    (commonFace fP hvP hP fC hvC hC KA).symm e =
      bP fP hvP KA (castBelow hP.symm (Finset.univ, KA)
        (castBelow hC (Finset.univ, KA) ((bC fC hvC KA).symm e))) := by
  simp only [commonFace, Equiv.symm_trans_apply, Equiv.symm_symm, castBelow_symm]

/-- The underlying cell of the identification. -/
theorem commonFace_val (a : P.scheme.below (Finset.univ.image fP, KA)) :
    (commonFace fP hvP hP fC hvC hC KA a).1 =
      toCell C.scheme fC hvC (SemScheme.castCell hC.symm (SemScheme.castCell hP
        ((bP fP hvP KA).symm a).1)) := by
  change (toCell C.scheme fC hvC (castBelow hC.symm (Finset.univ, KA)
    (castBelow hP (Finset.univ, KA) ((bP fP hvP KA).symm a))).1) = _
  rw [castBelow_val, castBelow_val]

/-- The identification preserves grades. -/
theorem commonFace_grade (a : P.scheme.below (Finset.univ.image fP, KA)) :
    C.scheme.grade (commonFace fP hvP hP fC hvC hC KA a).1 = P.scheme.grade a.1 := by
  rw [commonFace_val]
  change (C.restrictFace fC hvC).scheme.grade (SemScheme.castCell hC.symm
    (SemScheme.castCell hP ((bP fP hvP KA).symm a).1)) = _
  rw [castCell_grade, castCell_grade]
  exact congrArg P.scheme.grade (toCell_belowEquiv_symm_val P.scheme fP hvP
    (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fP, KA)) rfl a)

/-- The identifications at two grades agree on a common cell. -/
theorem commonFace_val_congr {KA' : ℕ} (a : P.scheme.below (Finset.univ.image fP, KA))
    (a' : P.scheme.below (Finset.univ.image fP, KA')) (h : a.1 = a'.1) :
    (commonFace fP hvP hP fC hvC hC KA a).1 = (commonFace fP hvP hP fC hvC hC KA' a').1 := by
  have e1 : toCell P.scheme fP hvP ((bP fP hvP KA).symm a).1 = a.1 :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA))
      (BJ := (Finset.univ.image fP, KA)) rfl a
  have e2 : toCell P.scheme fP hvP ((bP fP hvP KA').symm a').1 = a'.1 :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA'))
      (BJ := (Finset.univ.image fP, KA')) rfl a'
  have e : ((bP fP hvP KA).symm a).1 = ((bP fP hvP KA').symm a').1 :=
    toCell_injective P.scheme fP hvP (e1.trans (h.trans e2.symm))
  rw [commonFace_val, commonFace_val, e]

/-- **Restricted lawfulness transports along the identification**, in both directions. -/
theorem commonFace_respects (r : C.scheme.below (Finset.univ.image fC, KA) → ExtOrd) :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, KA) r ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, KA)
        (fun a => r (commonFace fP hvP hP fC hvC hC KA a)) := by
  constructor
  · intro hr
    have h1 := hr.restrictFace (f := fC) (hr := hvC) (BJ' := (Finset.univ, KA)) rfl
    have h2 := (castBelow_respects hC.symm (Finset.univ, KA) _).mp h1
    have h3 := (castBelow_respects hP (Finset.univ, KA) _).mp h2
    have h4 := h3.of_restrictFace (f := fP) (hr := hvP) (BJ' := (Finset.univ, KA)) rfl
    exact h4
  · intro hr
    have h1 : RespectsSemanticsBelow (P.restrictFace fP hvP).rows (Finset.univ, KA)
        (fun d => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA d))) :=
      hr.restrictFace (f := fP) (hr := hvP) (BJ' := (Finset.univ, KA)) rfl
    have e1 : (fun d => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA
        (castBelow hP.symm (Finset.univ, KA) (castBelow hP (Finset.univ, KA) d))))) =
        fun d => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA d)) :=
      funext fun d => by rw [castBelow_symm_castBelow]
    have h2 : RespectsSemanticsBelow F.rows (Finset.univ, KA)
        (fun d => r (commonFace fP hvP hP fC hvC hC KA
          (bP fP hvP KA (castBelow hP.symm (Finset.univ, KA) d)))) := by
      refine (castBelow_respects hP (Finset.univ, KA) _).mpr ?_
      rw [e1]
      exact h1
    have e2 : (fun d => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA
        (castBelow hP.symm (Finset.univ, KA) (castBelow hC (Finset.univ, KA)
          (castBelow hC.symm (Finset.univ, KA) d)))))) =
        fun d => r (commonFace fP hvP hP fC hvC hC KA
          (bP fP hvP KA (castBelow hP.symm (Finset.univ, KA) d))) :=
      funext fun d => by rw [castBelow_castBelow_symm]
    have h3 : RespectsSemanticsBelow (C.restrictFace fC hvC).rows (Finset.univ, KA)
        (fun d => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA
          (castBelow hP.symm (Finset.univ, KA) (castBelow hC (Finset.univ, KA) d))))) := by
      refine (castBelow_respects hC.symm (Finset.univ, KA) _).mpr ?_
      rw [e2]
      exact h2
    have h4 : RespectsSemanticsBelow C.rows (Finset.univ.image fC, KA)
        (fun e => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA
          (castBelow hP.symm (Finset.univ, KA) (castBelow hC (Finset.univ, KA)
            ((bC fC hvC KA).symm e)))))) :=
      h3.of_restrictFace (f := fC) (hr := hvC) (BJ' := (Finset.univ, KA)) rfl
    have he : (fun e => r (commonFace fP hvP hP fC hvC hC KA (bP fP hvP KA
        (castBelow hP.symm (Finset.univ, KA) (castBelow hC (Finset.univ, KA)
          ((bC fC hvC KA).symm e)))))) = r := by
      funext e
      rw [← commonFace_symm_apply fP hvP hP fC hvC hC KA e, Equiv.apply_symm_apply]
    rw [← he]
    exact h4

end CommonFace

end CappedDonor

end VaughtConjecture.Knight
