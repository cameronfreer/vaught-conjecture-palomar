/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryFinalCatalogue
public import VaughtConjecture.Knight.FinalGateChart
public import VaughtConjecture.Knight.CappedDonorCappedReadback

/-! # Capped readback from arbitrary lawful final-layer sections

Availability at the retained private cap chooses an actual installed ceiling
leaf. Its locality gives the whole-coordinate chart; one positive marked node
forces the chosen source's gate positive. Literal private retention then supplies
every cap and representative receipt in V-C's one-chart readback theorem.

Only the **chosen catalogue member** is admitted. The arbitrary physical section
is not assumed synchronized, decoded, or admitted. No LOW clause, anchor,
protected flexibility, or literal-top readback is used. The predecessor's
original occurrence maps and literal source equations remain explicit inputs;
this file does not build the predecessor or prove final-layer bountifulness.

`CappedDonorCappedReadback` is ported unchanged from V-C's `04276e9`.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrdinaryFinalReadback
open Transform Value ExtOrd CappedDonor CappedDonor.Ref OrdinaryFinalCatalogue
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (F : FinalGateLayer.Input D N (Field P C) (OrdinaryFinalCatalogue.Member R))

/-- An inherited occurrence in the final active lower set. -/
abbrev oldAt (d : Cell D) (hd : D.grade d ≤ N) : F.carrier.below (A, N) :=
  ⟨F.old d, by
    rw [F.old_index]
    exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩⟩

variable (req : Cell P.scheme ↪ Cell D) (priv : Cell C.scheme ↪ Cell D)
variable (hreqGrade : ∀ d, D.grade (req d) = P.scheme.grade d)
variable (hprivGrade : ∀ d, D.grade (priv d) = C.scheme.grade d)

abbrev reqAt (d : Cell P.scheme) : F.carrier.below (A, N) :=
  oldAt R F (req d) ((hreqGrade d).trans_le (req_grade_le R d))

abbrev privAt (d : Cell C.scheme) : F.carrier.below (A, N) :=
  oldAt R F (priv d) ((hprivGrade d).trans_le (gradeC_le d))

/-- Capped correctness on **all** donor occurrences follows from the installed
rows, literal private retention, and a single positive physical gate occurrence. -/
theorem capped_readback
    (hfields : ∀ a f, F.fields a f = a.val f) (hgate : F.gate = .gate)
    (hreq : ∀ a d, F.lower a (req d) = a.val (.req d))
    (hpriv : ∀ a d, F.lower a (priv d) = a.val (.priv d))
    {v : F.carrier.below (A, N) → ExtOrd}
    (hv : RespectsSemanticsBelow F.rows (A, N) v)
    (hretain : ∀ d, v (privAt R F priv hprivGrade d) = R.vact d)
    (b : OrdinaryFinalCatalogue.Member R) (hpositive : v (F.addedAt b true) ≠ ⊥)
    (d : Cell P.scheme) :
    min (v (reqAt R F req hreqGrade d)) (R.cut R.vactL) =
      min (R.p d) (R.cut R.vactL) := by
  let c := privAt R F priv hprivGrade R.cap
  have hc : F.carrier.grade c.1 = N :=
    (congrArg Prod.snd (F.old_index (priv R.cap))).trans
      ((hprivGrade R.cap).trans (congrArg Prod.snd R.cap_cell))
  have hpos : v c ≠ ⊥ := by
    rw [hretain]
    exact ne_bot_of_gt R.cap_pos
  obtain ⟨a, hca, hga, τ, hτ, -, hr⟩ := F.exists_active_chart hv c hc hpos b hpositive
  have hm : R.vact R.cap ≤ v (F.addedAt a false) := by
    simpa only [c, hretain] using hca
  obtain ⟨st, hst, -, -, hp⟩ := a.property.2
  have hsu (e : P.scheme.below (effP nP N)) : a.val (.req e.1) = st.u e :=
    (congrFun hp (.req e.1)).symm.trans (profile_present R st (.req e.1))
  have hsv (e : C.scheme.below (effC N N)) : a.val (.priv e.1) = st.v e :=
    (congrFun hp (.priv e.1)).symm.trans (profile_present R st (.priv e.1))
  have hg : st.gate ≠ ⊥ := by
    rw [hgate, hfields] at hga
    have he : a.val .gate = st.gate :=
      (congrFun hp .gate).symm.trans (profile_present R st .gate)
    exact he ▸ hga
  have hu (e : P.scheme.below (effP nP N)) :
      τ (st.u e) = min (v (reqAt R F req hreqGrade e.1)) (v (F.addedAt a false)) := by
    have he := hr (reqAt R F req hreqGrade e.1)
    simpa only [reqAt, oldAt, F.source_old, hreq, hsu] using he
  have hread (e : C.scheme.below (effC N N)) (he : R.vact e.1 ≤ R.vact R.cap) :
      τ (st.v e) = R.vact e.1 := by
    have hr' := hr (privAt R F priv hprivGrade e.1)
    simpa only [privAt, oldAt, F.source_old, hpriv, hsv, hretain,
      min_eq_left (he.trans hm)] using hr'
  exact Ref.capped_readback le_rfl hst le_rfl hτ hm hu
    (hread (R.capC le_rfl) le_rfl)
    (fun i => hread (CellScheme.below.mono (R.capLe le_rfl) (R.lowRef i))
      (R.ref_lt_cap i).le) hg (CappedDonor.Ref.reqCell d (req_grade_le R d))

end
end VaughtConjecture.Knight.OrdinaryFinalReadback
