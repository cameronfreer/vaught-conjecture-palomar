/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryAttachedReceiving
public import VaughtConjecture.Knight.CappedDonorComparisonRequest
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.ExtensionSets
public import VaughtConjecture.Knight.CapObservation

/-! # Finite-cut receiving in a model

The model application of the constructed ordinary receiving probe (the reviewer's integration
checkpoint `6c9493d`, `OrdinaryAttachedReceiving`): **every model satisfies finite-cut receiving**
(`finiteCutReceiving`). One-block readback and the descriptive-set-theoretic consequences remain
in the compatibility/application module `OrdinaryModelReceiving`.

The namespace is unchanged so existing receiving clients retain their theorem names.

The steps, over a realized root `t ↦ p`, a legal one-point candidate `q` over `p` and a requested
proper cutoff `δ = ofOrd ν`:

1. **Reference acquisition above the cutoff and above the threshold floor `3`**
   (`exists_ref_above_cut_min`): an actual private context `u ↦ p₀` of arity `N ≥ 4` containing
   the root literally (`C.proj_ctx`), with the ordinary reference data `Rf`, its literal receipts
   (`J = N`, the block map, the faces, `KA = n`, the literal common face) and `δ < β`, `β` the
   actual cut.
2. **The legal probe** `D := OrdinaryAttachedReceiving.semScheme …`, whose private restriction
   along `Fin.castSuccEmb` is literally `p₀`'s scheme (`private_restrict`), so `D` extends the
   domain of `p₀`; its selected display `r` retains both input labellings and has a named
   grade-`N` gate at `⊤` (`exists_raw_display`); no auxiliary stage bound is needed.
3. **The model's prescribed-bottom-pattern clause** over the private tuple `u` realizes an actual
   coface `q₁` of `p₀` on the scheme `D` with the bottom pattern of `r` on the cells of grade
   `≤ N`.  The gate has grade `N`, so it lies inside the clause's test, and its value in `q₁` is
   nonbottom; `q₁` retains the private labels literally (it is a coface of `p₀`).
4. **Arbitrary-section capped readback** (`readback_below`): `q₁` agrees with the candidate on
   every donor cell below the actual cut, hence below `δ`.
5. **Restriction to the donor face** along `onePointProj e`: the donor tuple of `u ⌢ y` is the
   root tuple with the fresh point (`onePointProj_trans_snoc`), the model's exact parent
   consistency labels it with the restricted type, whose scheme is literally the candidate's
   (`request_restrict`) and whose labels are the installed donor occurrences (`request_toCell`).

No probe-existence interface is introduced: the probe is the constructed scheme, and the model
supplies the coface.  The conclusion is capped agreement, not literal donor tops. -/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryModelReceiving

open TypeTower StageType KnightRealization Value ExtOrd CappedDonor AmalgamationPlan

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- Two stage types with equal domains and labels agreeing through `castCell` are equal
(the statement of `ReadbackReceiver`'s `StageType.ext_of_label`, restated here to keep that
module's imports out of this one). -/
theorem ext_of_label {n : ℕ} {t₁ t₂ : S α.1 n} (hs : t₁.scheme = t₂.scheme)
    (hl : ∀ i, t₁.label i = t₂.label (SemScheme.castCell hs i)) : t₁ = t₂ := by
  obtain ⟨s₂, l₂, hb₂, hr₂⟩ := t₂
  dsimp only at hs
  subst hs
  exact StageType.ext rfl (heq_of_eq (funext fun i => hl i))

/-- Lawfulness transports along an equality of schemes. -/
theorem respects_of_scheme_eq {n : ℕ} {X : SemScheme n} (t : S α.1 n) (h : t.scheme = X) :
    RespectsSemantics X.rows (fun c => t.label (SemScheme.castCell h.symm c)) := by
  obtain ⟨s, l, hb, hr⟩ := t
  dsimp only at h
  subst h
  exact hr

/-- Equal caps at a proper cutoff give equal strict truncations at that cutoff. -/
theorem truncExt_eq_of_min_eq {β : Ordinal.{0}} {x y : ExtOrd}
    (h : min x (ofOrd β) = min y (ofOrd β)) : truncExt β x = truncExt β y :=
  min_eq_min_iff_truncExt_eq.mp h

/-- **Finite-cut receiving from acquired reference data.**  Over a realized root `t ↦ p`, a
candidate `q` on `n + 1` points (its coface relation to `p` is carried by the face receipts and
is not assumed separately), and an actual private context `u ↦ p₀` of arity `J = N ≥ 4` containing
the root along `e`, with ordinary reference data `Rf` for `q`'s scheme over `p₀`'s scheme and
its literal receipts, every cutoff `δ` at most the actual cut is received: some actual coface of
`p` on `q`'s scheme agrees with `q` below `δ`. -/
theorem fc_of_reference (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hp : R.eval t = some p) (q : S α.1 (n + 1))
    {I : Type*} [Fintype I] {N J : ℕ} (hJ : J = N) (hN : 4 ≤ N)
    {u : Fin J ↪ M} {p₀ : S α.1 J} (hu : R.eval u = some p₀)
    (e : Fin n ↪ Fin J) (hut : e.trans u = t)
    (Rf : Ref I n N J q.scheme p₀.scheme) (hRp : Rf.p = q.label) (hRv : Rf.vact = p₀.label)
    (hK : Rf.KA = n) (hA' : Rf.A' = Finset.univ.image e)
    (hA : Rf.A = Finset.univ.image Fin.castSuccEmb)
    (hface : ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
      (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
      (hvC : Finset.univ.image e ∈ p₀.scheme.scheme.plan)
      (hC : p₀.scheme.restrictFace e hvC = p.scheme),
      HEq Rf.face (commonFace Fin.castSuccEmb hvP hP e hvC hC n))
    {δ : ExtOrd} (hδ : δ ≤ Rf.cut Rf.vactL) :
    ∃ (y : M) (hy : y ∉ Set.range t) (q' : S α.1 (n + 1)), R.eval (snoc t y hy) = some q' ∧
      ∃ h : q'.scheme = q.scheme,
        ∀ d, min (q'.label d) δ = min (q.label (SemScheme.castCell h d)) δ := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 4 := ⟨N - 4, by omega⟩
  subst hJ
  subst hut
  obtain ⟨hvP, hP, hvC, hC, hface⟩ := hface
  -- the legal probe and its exact faces
  let D : SemScheme (k + 5) :=
    OrdinaryAttachedReceiving.semScheme p₀.scheme q.scheme p.scheme e hvC hvP hC hP Rf hA hA' hK
      hface
  have hvis := OrdinaryAttachedReceiving.private_visible p₀.scheme q.scheme p.scheme e hvC hvP hC
    hP Rf hA hA' hK hface
  have hres := OrdinaryAttachedReceiving.private_restrict p₀.scheme q.scheme p.scheme e hvC hvP hC
    hP Rf hA hA' hK hface
  have hD : ExtendsDomain p₀ D := ⟨hvis, hres⟩
  -- A raw lawful display suffices for the prescribed-bottom-pattern clause.
  obtain ⟨a, r, hr, -, hrv, hg⟩ := OrdinaryAttachedReceiving.exists_raw_display p₀.scheme q.scheme
    p.scheme e hvC hvP hC hP Rf hA hA' hK hface
  -- the model's prescribed-bottom-pattern clause over the private tuple
  obtain ⟨y, hy, q₁, ⟨h₁, hpat⟩, hcof, hev⟩ := hM.bottomPattern u p₀ hu D hD r hr (fun d => by
    rw [ExtendsDomain.cellOf]
    rw [OrdinaryAttachedReceiving.private_toCell p₀.scheme q.scheme p.scheme e hvC hvP hC hP Rf
      hA hA' hK hface d, hrv d, hRv])
  -- the realized section on the probe
  let qq : Cell D.scheme → ExtOrd := fun c => q₁.label (SemScheme.castCell h₁.symm c)
  have hqq : RespectsSemantics D.rows qq := respects_of_scheme_eq q₁ h₁
  let t' : S α.1 (k + 5) := ⟨D, qq, fun c => q₁.label_bound _, hqq⟩
  have ht' : q₁ = t' := ext_of_label h₁ (fun i => rfl)
  rw [ht'] at hcof hev
  -- literal private retention
  have hretain : ∀ d, qq ((OrdinaryAttachedReceiving.privateFace p₀.scheme q.scheme p.scheme e
      hvC hvP hC hP Rf hA hA' hK hface).map d) = Rf.vact d := by
    intro d
    have key := (typeMap_eq_some_iff_labels Fin.castSuccEmb t' p₀ hvis hres).mp hcof
      (SemScheme.castCell hres.symm d)
    rw [OrdinaryAttachedReceiving.private_toCell p₀.scheme q.scheme p.scheme e hvC hvP hC hP Rf
      hA hA' hK hface d] at key
    rw [hRv]
    exact key
  -- the gate is inside the bottom-pattern test and stays positive
  have hgate : qq (OrdinaryAttachedReceiving.gate p₀.scheme q.scheme p.scheme e hvC hvP hC hP Rf
      hA hA' hK hface a) ≠ ⊥ := by
    intro hb
    have := (hpat ⟨_, Finset.subset_univ _, (OrdinaryAttachedReceiving.gate_grade p₀.scheme
      q.scheme p.scheme e hvC hvP hC hP Rf hA hA' hK hface a).le⟩).mp hb
    rw [hg] at this
    exact top_ne_bot this
  -- capped readback on the donor occurrences
  have hread := fun d => OrdinaryAttachedReceiving.readback_below p₀.scheme q.scheme p.scheme e
    hvC hvP hC hP Rf hA hA' hK hface hqq hretain a hgate hδ d
  -- restriction to the donor face over the root tuple
  have hvreq := OrdinaryAttachedReceiving.request_visible p₀.scheme q.scheme p.scheme e hvC hvP hC
    hP Rf hA hA' hK hface
  have hrreq := OrdinaryAttachedReceiving.request_restrict p₀.scheme q.scheme p.scheme e hvC hvP
    hC hP Rf hA hA' hK hface
  have hy' : y ∉ Set.range (e.trans u) := fun ⟨j, hj⟩ => hy ⟨e j, hj⟩
  refine ⟨y, hy', t'.restrictFace (onePointProj e) hvreq, ?_, hrreq, ?_⟩
  · have h := hM.consistent (snoc u y hy) t' (onePointProj e) hev
    rw [onePointProj_trans_snoc e u y hy hy'] at h
    rw [h]
    exact typeMap_eq_some (onePointProj e) t' hvreq
  · intro d
    have key := hread (SemScheme.castCell hrreq d)
    rw [← OrdinaryAttachedReceiving.request_toCell p₀.scheme q.scheme p.scheme e hvC hvP hC hP Rf
      hA hA' hK hface (SemScheme.castCell hrreq d), hRp] at key
    exact key

/-- **Every model satisfies finite-cut receiving**: reference acquisition above the requested
cutoff and above the threshold floor `3`, then `fc_of_reference`. -/
theorem finiteCutReceiving (hM : R.IsModel) : FiniteCutReceiving R := by
  intro n t p hp P hP δ hδbot hδα
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact absurd hδbot (lt_irrefl _)
    · exact absurd hδα (not_lt.mpr le_top)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  obtain ⟨C, -, Rf, hRp, hRv, -, hK, hA', hA, -, -, -, -, hface, hm, hNmin, -, hlt, -⟩ :=
    exists_ref_above_cut_min hM p hp P hP ν hν 3
  exact fc_of_reference hM hp P hm (by omega) C.eval_ctx C.proj C.proj_ctx Rf hRp hRv hK hA' hA
    hface hlt.le

end VaughtConjecture.Knight.OrdinaryModelReceiving
