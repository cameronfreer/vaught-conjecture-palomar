module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

/-!
# Extending a full-scope lower labelling by bottom

This explicit extension preserves respect for every semantics: lower-grade controllers see
the original labelling, and every higher controller has bottom target. Availability stays
within a grade. No consistency, completeness, or bountifulness assumption is required.
This is a grade extension, not an extension across a proper scope.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {K : ℕ}

namespace CellScheme

/-- A lower labelling at full scope, with bottom at every higher-grade cell. -/
noncomputable def zeroAbove (q : D.below (A, K) → ExtOrd) (d : Cell D) : ExtOrd :=
  if hd : D.grade d ≤ K then
    q ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩ else ⊥

theorem zeroAbove_low (q : D.below (A, K) → ExtOrd) (d : D.below (A, K)) :
    zeroAbove q d.1 = q d := by
  have hd : D.grade d.1 ≤ K := d.2.2
  rw [zeroAbove, dite_of_pos hd]
  rfl

theorem zeroAbove_high (q : D.below (A, K) → ExtOrd) {d : Cell D} (hd : ¬ D.grade d ≤ K) :
    zeroAbove q d = ⊥ := by rw [zeroAbove, dite_of_neg hd]

end CellScheme

/-- Extending a respecting full-scope lower labelling by bottom preserves respect. -/
theorem RespectsSemanticsBelow.zeroAbove {sem : Semantics D} {q : D.below (A, K) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (A, K) q) :
    RespectsSemantics sem (CellScheme.zeroAbove q) := by
  have mem (d : Cell D) (hd : D.grade d ≤ K) : GradedLe (D.cell d) (A, K) :=
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d
    by_cases hd : D.grade d ≤ K
    · rw [CellScheme.zeroAbove_low q ⟨d, mem d hd⟩]
      exact hq.orderly ⟨d, mem d hd⟩
    · rw [CellScheme.zeroAbove_high q hd]
      exact (extVisibilityReplace_bot _ _).symm
  · intro Sig
    by_cases hSig : D.grade Sig ≤ K
    · refine transformsTo_congr rfl rfl ?_ (hq.locality ⟨Sig, mem Sig hSig⟩)
      funext d
      rw [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩,
        CellScheme.zeroAbove_low q ⟨d.1, mem d.1 (d.2.2.trans hSig)⟩]
      rfl
    · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
      funext d
      rw [CellScheme.zeroAbove_high q hSig, min_eq_right bot_le]
  · intro Sig Xi₀ hs hg
    by_cases hSig : D.grade Sig ≤ K
    · have hXi₀ : D.grade Xi₀ ≤ K := hg ▸ hSig
      obtain ⟨Xi, hc, hle⟩ :=
        hq.availability ⟨Sig, mem Sig hSig⟩ ⟨Xi₀, mem Xi₀ hXi₀⟩ hs hg
      refine ⟨Xi.1, hc, ?_⟩
      rw [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩, CellScheme.zeroAbove_low q Xi]
      exact hle
    · exact ⟨Xi₀, rfl, by rw [CellScheme.zeroAbove_high q hSig]; exact bot_le⟩

end VaughtConjecture.Knight
