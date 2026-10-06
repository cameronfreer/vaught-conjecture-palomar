/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AnchorStable

/-! # Synchronization after growth, on actual finite contexts

First acquire a cover of sufficiently high top grade, then synchronize its
finite stable labelling. The second operation cannot lose the high top grade.
All receipts concern actual contexts of the original model; no stable model
or physical receiving scheme is assumed.

For hollow models every root top is stable top. The resulting context has a
full-scope top owner above the requested grade and every root top has provisional
value above the requested new-band cutoff. This is the context-selection part
of the proposed hollow-growth receiver, not the receiver itself.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthContextSynchronization
open TypeTower StageType KnightRealization Value ExtOrd
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Finitely many proper stable values admit a common natural new-band bound,
which can be chosen above any prescribed floor. -/
theorem exists_stable_bound {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (L : ℕ) :
    ∃ K : ℕ, L ≤ K ∧ ∀ d : Cell p.scheme.scheme,
      W.stableValue t p d ≠ ⊤ → W.stableValue t p d ≤ ofOrd (α.1 + K) := by
  classical
  have hex : ∀ d : Cell p.scheme.scheme, ∃ k : ℕ,
      W.stableValue t p d ≠ ⊤ → W.stableValue t p d ≤ ofOrd (α.1 + k) := by
    intro d
    by_cases ht : W.stableValue t p d = ⊤
    · exact ⟨0, fun h => (h ht).elim⟩
    have hlt : W.stableValue t p d < ofOrd (α.1 + Ordinal.omega0) :=
      ((W.hasStableValue_stableValue t p d).resolve_right (fun h => ht h.1)).1
    by_cases hlo : ofOrd α.1 ≤ W.stableValue t p d
    · obtain ⟨k, hk⟩ := exists_nat_of_band hlo hlt
      exact ⟨k, fun _ => hk.le⟩
    · exact ⟨0, fun _ => by simpa using (not_le.mp hlo).le⟩
  choose b hb using hex
  refine ⟨max L (Finset.univ.sup b), le_max_left _ _, fun d hd => ?_⟩
  exact (hb d hd).trans (ofOrd_le_ofOrd.mpr (add_le_add_right
    (Nat.cast_le.mpr ((Finset.le_sup (f := b) (Finset.mem_univ d)).trans
      (le_max_right _ _))) _))

/-- Growth first, synchronization second: the final cover retains both the
high top grade and the synchronization receipts for the original exact root. -/
theorem exists_sync_growth (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p) (K L : ℕ) :
    ∃ (y : W.LabelledExt) (f : Fin n ↪ Fin y.arity) (_hf : f.trans y.tuple = t)
      (hpy : typeMap f y.type = some p), K < y.type.topGrade ∧
        ∀ d : Cell p.scheme.scheme,
          (W.stableValue t p d ≠ ⊤ →
            y.type.someProvisionalValue (mapCell hpy d) = W.stableValue t p d) ∧
          (p.label d = ⊤ → W.stableValue t p d = ⊤ →
            ofOrd (α.1 + L) < y.type.someProvisionalValue (mapCell hpy d)) := by
  obtain ⟨x, hxK, e, he, hpx⟩ := hg K ⟨n, t, p, hp⟩
  obtain ⟨y, f, hf, hxy, hsync⟩ :=
    exists_syncCover' hM.consistent hM.covering x.eval_eq L
  have hpy : typeMap (e.trans f) y.type = some p := by
    rw [← typeMap_trans e f y.type x.type hxy]
    exact hpx
  refine ⟨y, e.trans f, ?_, hpy,
    hxK.trans_le (topGrade_le_of_typeMap_eq_some hxy), fun d => ?_⟩
  · rw [Function.Embedding.trans_assoc, hf, he]
  · have hsv := stableValue_mapCell' hM.consistent x.eval_eq he hpx d
    obtain ⟨hproper, htop⟩ := hsync (mapCell hpx d)
    rw [mapCell_trans hxy hpx hpy d]
    constructor
    · intro hd
      rw [hproper (by rwa [hsv]), hsv]
    · intro hd hs
      exact htop (by rw [label_mapCell hpx, hd]) (hsv.trans hs)

/-- In a hollow-growth model the synchronized context has a full-scope
maximal-grade top owner, and every root top lies provisionally above the
requested cutoff. Proper root labels are retained literally. -/
theorem exists_hollow_context (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (hp : W.eval t = some p) (K L : ℕ) :
    ∃ (y : W.LabelledExt) (f : Fin n ↪ Fin y.arity) (_hf : f.trans y.tuple = t)
      (hpy : typeMap f y.type = some p) (c : Cell y.type.scheme.scheme),
      K < y.type.topGrade ∧ y.type.scheme.scheme.scope c = Finset.univ ∧
      y.type.scheme.scheme.grade c = y.type.topGrade ∧ y.type.label c = ⊤ ∧
      (∀ d, p.label d ≠ ⊤ → y.type.someProvisionalValue (mapCell hpy d) = p.label d) ∧
      (∀ d, p.label d = ⊤ →
        ofOrd (α.1 + L) < y.type.someProvisionalValue (mapCell hpy d)) := by
  obtain ⟨y, f, hf, hpy, hK, hs⟩ := exists_sync_growth hM hg t p hp K L
  obtain ⟨c, hcsc, hcgr, hctop⟩ := exists_topCell_of_topGrade_pos y.type
    (lt_of_le_of_lt (Nat.zero_le K) hK)
  refine ⟨y, f, hf, hpy, c, hK, hcsc, hcgr, hctop, ?_, ?_⟩
  · intro d hd
    have hid := stableValue_eq_label_of_hollow hM hh hp d
    exact ((hs d).1 (by rwa [hid])).trans hid
  · intro d hd
    exact (hs d).2 hd ((stableValue_eq_label_of_hollow hM hh hp d).trans hd)

end
end VaughtConjecture.Knight.GrowthContextSynchronization
