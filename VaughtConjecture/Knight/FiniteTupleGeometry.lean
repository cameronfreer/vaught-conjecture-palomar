/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import Mathlib.Data.Set.Finite.Range

/-! # Finite tuple and padded-face geometry

Factorization, append embeddings and designated faces, independent of request enumeration
and infinite runs. All occurrence equations retain their original names and definitions. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w} {β : LimitStage}

/-- Factors through an injective tuple are unique. -/
theorem emb_factor_unique {n N : ℕ} {t : Fin n ↪ M} {w : Fin N ↪ M}
    {f g : Fin n ↪ Fin N} (hf : f.trans w = t) (hg : g.trans w = t) : f = g := by
  refine Function.Embedding.ext fun i => w.injective ?_
  have h1 : w (f i) = t i := congrArg (fun e : Fin n ↪ M => e i) hf
  have h2 : w (g i) = t i := congrArg (fun e : Fin n ↪ M => e i) hg
  exact h1.trans h2.symm

/-- A face of a factoring tuple factors through the composite. -/
theorem trans_factor {k n N : ℕ} {t : Fin n ↪ M} {w : Fin N ↪ M} {g : Fin n ↪ Fin N}
    (hg : g.trans w = t) (f : Fin k ↪ Fin n) : (f.trans g).trans w = f.trans t := by
  ext i
  exact congrArg (fun e : Fin n ↪ M => e (f i)) hg

/-- An embedding avoiding the last index factors through the initial segment. -/
theorem exists_factor_castSucc {k n : ℕ} (g : Fin k ↪ Fin (n + 1))
    (hg : Fin.last n ∉ Set.range g) :
    ∃ g₀ : Fin k ↪ Fin n, g = g₀.trans Fin.castSuccEmb := by
  have hne : ∀ i, g i ≠ Fin.last n := fun i h => hg ⟨i, h⟩
  refine ⟨⟨fun i => (g i).castPred (hne i), fun i j hij => ?_⟩, ?_⟩
  · apply g.injective
    have := congrArg Fin.castSucc hij
    simpa [Fin.castSucc_castPred] using this
  · ext i
    exact congrArg Fin.val (Fin.castSucc_castPred (g i) (hne i)).symm

/-- The face of the one-point extension over the face `g` of the base: `extendFace g` maps
`i < n` to `(g i).castSucc` and the new last index to the new last index — the embedding
along which a coface of the master restricts to a coface of the face. -/
def extendFace {n N : ℕ} (g : Fin n ↪ Fin N) : Fin (n + 1) ↪ Fin (N + 1) :=
  ⟨Fin.snoc (fun i => (g i).castSucc) (Fin.last N),
    Fin.snoc_injective_of_injective (Fin.castSucc_injective N |>.comp g.injective)
      (fun ⟨i, hi⟩ => (Fin.castSucc_lt_last (g i)).ne hi)⟩

@[simp] theorem extendFace_castSucc {n N : ℕ} (g : Fin n ↪ Fin N) (i : Fin n) :
    extendFace g (Fin.castSucc i) = (g i).castSucc := by
  simp [extendFace]

@[simp] theorem extendFace_last {n N : ℕ} (g : Fin n ↪ Fin N) :
    extendFace g (Fin.last n) = Fin.last N := by
  simp [extendFace]

/-- The `extendFace` equation on concatenations: extending the master event tuple restricts
along `extendFace g` to the extension of the face tuple. -/
theorem extendFace_trans_snoc {n N : ℕ} (g : Fin n ↪ Fin N) {w : Fin N ↪ M} {y : M}
    (hyw : y ∉ Set.range w) (hyt : y ∉ Set.range (g.trans w)) :
    (extendFace g).trans (snoc w y hyw) = snoc (g.trans w) y hyt := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [snoc]
  | cast i => simp [snoc]

/-- The padded event tuple: the master `w` followed by the fresh block `ys`. -/
def appendEmb {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) : Fin (N + m) ↪ M :=
  ⟨Fin.append w ys, by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left i' =>
        rw [Fin.append_left, Fin.append_left] at hab
        rw [w.injective hab]
      | right j' =>
        rw [Fin.append_left, Fin.append_right] at hab
        exact absurd ⟨i, hab⟩ (hdisj j')
    | right j =>
      induction b using Fin.addCases with
      | left i' =>
        rw [Fin.append_right, Fin.append_left] at hab
        exact absurd ⟨i', hab.symm⟩ (hdisj j)
      | right j' =>
        rw [Fin.append_right, Fin.append_right] at hab
        rw [ys.injective hab]⟩

@[simp] theorem appendEmb_castAdd {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) (i : Fin N) :
    appendEmb w ys hdisj (Fin.castAdd m i) = w i :=
  Fin.append_left _ _ i

@[simp] theorem appendEmb_natAdd {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) (j : Fin m) :
    appendEmb w ys hdisj (Fin.natAdd N j) = ys j :=
  Fin.append_right _ _ j

/-- The master is the initial face of the padded event tuple. -/
theorem castAddEmb_trans_appendEmb {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) :
    (Fin.castAddEmb m).trans (appendEmb w ys hdisj) = w := by
  ext i
  exact appendEmb_castAdd w ys hdisj i

/-- An embedding avoiding the fresh block factors through the initial segment. -/
theorem exists_factor_castAdd {j N m : ℕ} (g : Fin j ↪ Fin (N + m))
    (hg : ∀ i, (g i).val < N) :
    ∃ g₀ : Fin j ↪ Fin N, g = g₀.trans (Fin.castAddEmb m) := by
  refine ⟨⟨fun i => ⟨(g i).val, hg i⟩, fun i i' hii => ?_⟩, ?_⟩
  · have hii' : (⟨(g i).val, hg i⟩ : Fin N) = ⟨(g i').val, hg i'⟩ := hii
    exact g.injective (Fin.ext (congrArg (Fin.val : Fin N → ℕ) hii'))
  · ext i
    rfl

/-- The designated extended face of a `k`-padded one-point master extension: `i < n` goes to
`g i` in the initial block, the new last index to the new last index (the designated
coordinate, AFTER the padding block). -/
def extendFacePad (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) :
    Fin (n + 1) ↪ Fin (N + (k + 1)) where
  toFun := Fin.snoc (fun i => Fin.castAdd (k + 1) (g i)) (Fin.last (N + k))
  inj' := Fin.snoc_injective_of_injective
    (fun a b hab => g.injective
      (Fin.ext (congrArg (Fin.val : Fin (N + (k + 1)) → ℕ) hab)))
    (fun ⟨i, hi⟩ => by
      have h1 : (Fin.castAdd (k + 1) (g i)).val < N := Fin.castAdd_lt _ (g i)
      have hi' : Fin.castAdd (k + 1) (g i) = Fin.last (N + k) := hi
      rw [hi'] at h1
      simp only [Fin.val_last] at h1
      omega)

@[simp] theorem extendFacePad_castSucc (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) (i : Fin n) :
    extendFacePad k g (Fin.castSucc i) = Fin.castAdd (k + 1) (g i) := by
  simp [extendFacePad]

@[simp] theorem extendFacePad_last (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) :
    extendFacePad k g (Fin.last n) = Fin.last (N + k) := by
  simp [extendFacePad]

/-- The old face factors the padded face through the initial segment. -/
theorem castSuccEmb_trans_extendFacePad (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) :
    Fin.castSuccEmb.trans (extendFacePad k g) = g.trans (Fin.castAddEmb (k + 1)) := by
  ext i
  exact congrArg Fin.val (extendFacePad_castSucc k g i)

/-- The padded face of the padded event tuple is the one-point extension of the face tuple
at the designated coordinate. -/
theorem extendFacePad_trans_appendEmb {k n N : ℕ} (g : Fin n ↪ Fin N) {w : Fin N ↪ M}
    {ys : Fin (k + 1) ↪ M} (hdisj : ∀ j, ys j ∉ Set.range w)
    (hyt : ys (Fin.last k) ∉ Set.range (g.trans w)) :
    (extendFacePad k g).trans (appendEmb w ys hdisj) =
      snoc (g.trans w) (ys (Fin.last k)) hyt := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    change appendEmb w ys hdisj (extendFacePad k g (Fin.last n)) = _
    rw [extendFacePad_last]
    have hlast : Fin.last (N + k) = Fin.natAdd N (Fin.last k) := by
      ext
      simp
    rw [hlast, appendEmb_natAdd]
    simp [snoc]
  | cast i =>
    change appendEmb w ys hdisj (extendFacePad k g (Fin.castSucc i)) = _
    rw [extendFacePad_castSucc, appendEmb_castAdd]
    simp [snoc]
/-- Zero padding: `extendFacePad 0` is `extendFace`. -/
theorem extendFacePad_zero {n N : ℕ} (g : Fin n ↪ Fin N) :
    extendFacePad 0 g = extendFace g := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    change (extendFacePad 0 g (Fin.last n)).val = (extendFace g (Fin.last n)).val
    rw [extendFacePad_last, extendFace_last]
    rfl
  | cast i =>
    change (extendFacePad 0 g (Fin.castSucc i)).val = (extendFace g (Fin.castSucc i)).val
    rw [extendFacePad_castSucc, extendFace_castSucc]
    rfl

end FixedHeight
end VaughtConjecture.Knight
