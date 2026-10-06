/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PullbackSemantics
public import VaughtConjecture.Knight.WitnessAlgebra
public import VaughtConjecture.Knight.NormalForm

/-! # Witness-level transformation tools: probes, source collapse, truncation, cap, splices

* **Controller probes, ordered.**  From locality at `Sig` with witnesses `(g, σ)`:
  `RespectsSemanticsBelow.probe_ge_of_row_eq` (antitone `g`): equal sources at grades `k ≤ k'`
  give `min (q d') (q Sig) ≤ min (q d) (q Sig)`; a cell whose source is the diagonal's is labelled
  at least `q Sig` (`ge_of_row_eq_diag`).  `probe_le_of_lt` (monotone `σ`): a smaller source
  gives a smaller probe when the larger probe lies strictly below the cap.
* **Source collapse** (`TransformsTo.collapse`): a transformation from `f` also transforms any
  `f'` with `min (f' d) ξ = f d`, for a `K`-visible ordinal cutoff `ξ` above every `f d`
  (witnesses `σ ∘ min (·, ξ)` and `g` truncated to `⊥` above `K`).  A directional source
  precomposition, not transitivity.
* **Witnesses.**  A `Witness g σ` bundles the five clauses of Def. 2.3.9.  `Witness.truncate`
  (`g` set to `⊥` above `K`), `Witness.cap` (the Cap Lemma at the witness level),
  `Witness.raise` (`σ` raised to at least a `K`-visible `c` on the nonbottom fibre above a cutoff
  `ξ` with `K < finitePart ξ`), `Witness.lower` (`σ` lowered to at most `c` on the tail of the
  block of `ξ`, when `σ ≤ c` below `ξ`).  The grade bound and the cutoff visibility are explicit
  hypotheses throughout.

Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Probes
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- **Antitone probe**: equal sources at grades `k ≤ k'` give ordered probes. -/
theorem RespectsSemanticsBelow.probe_ge_of_row_eq (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d d' : D.below (D.cell Sig.1)) (hrow : sem.E Sig.1 d = sem.E Sig.1 d')
    (hgr : D.grade d.1 ≤ D.grade d'.1) :
    min (q (CellScheme.below.incl Sig d')) (q Sig) ≤
      min (q (CellScheme.below.incl Sig d)) (q Sig) := by
  obtain ⟨g, σ, hg_anti, -, -, -, -, heq⟩ := hq.locality Sig
  have h1 := heq d
  have h2 := heq d'
  dsimp only at h1 h2
  rw [h1, h2, hrow]
  apply min_le_min_left
  rcases lt_or_eq_of_le hgr with hlt | heq'
  · exact hg_anti _ _ hlt
  · rw [heq']

/-- A cell whose source is the diagonal's, of grade at most the controller's, is labelled at least
the controller. -/
theorem RespectsSemanticsBelow.ge_of_row_eq_diag (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d : D.below (D.cell Sig.1))
    (hrow : sem.E Sig.1 d = sem.E Sig.1 ⟨Sig.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩)
    (hgr : D.grade d.1 ≤ D.grade Sig.1) : q Sig ≤ q (CellScheme.below.incl Sig d) := by
  have h := hq.probe_ge_of_row_eq Sig d ⟨Sig.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩ hrow hgr
  have e : CellScheme.below.incl Sig ⟨Sig.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩ = Sig :=
    Subtype.ext rfl
  rw [e, min_self] at h
  exact h.trans (min_le_left _ _)

/-- **Monotone probe**: a smaller source gives a smaller probe, when the larger probe lies strictly
below the controller's label. -/
theorem RespectsSemanticsBelow.probe_le_of_lt (hq : RespectsSemanticsBelow sem BJ q)
    (Sig : D.below BJ) (d d' : D.below (D.cell Sig.1)) (hrow : sem.E Sig.1 d ≤ sem.E Sig.1 d')
    (hgr : D.grade d'.1 ≤ D.grade Sig.1)
    (hlt : min (q (CellScheme.below.incl Sig d')) (q Sig) < q Sig) :
    min (q (CellScheme.below.incl Sig d)) (q Sig) ≤
      min (q (CellScheme.below.incl Sig d')) (q Sig) := by
  obtain ⟨g, σ, hg_anti, -, -, hσ_mono, -, heq⟩ := hq.locality Sig
  have h1 := heq d
  have h2 := heq d'
  have h3 := heq ⟨Sig.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩
  dsimp only at h1 h2 h3
  have e : CellScheme.below.incl Sig ⟨Sig.1, ⟨Finset.Subset.refl _, le_rfl⟩⟩ = Sig :=
    Subtype.ext rfl
  rw [e, min_self] at h3
  -- the controller's label is at most `g` at its grade, hence at most `g` at the grade of `d'`
  have hg : g (D.grade Sig.1) ≤ g (D.grade d'.1) := by
    rcases lt_or_eq_of_le hgr with hlt' | heq'
    · exact hg_anti _ _ hlt'
    · rw [heq']
  have hcap : q Sig ≤ g (D.grade d'.1) := h3.symm ▸ (min_le_right _ _).trans hg
  rw [h1, h2]
  rw [h2] at hlt
  -- the larger probe is `σ` of its source
  have hσ' : σ (sem.E Sig.1 d') < g (D.grade d'.1) := by
    by_contra hcon
    rw [not_lt] at hcon
    rw [min_eq_right hcon] at hlt
    exact absurd (lt_of_lt_of_le hlt hcap) (lt_irrefl _)
  rw [min_eq_left hσ'.le]
  exact (min_le_left _ _).trans (hσ_mono hrow)

end Probes

section Collapse


/-- The cutoff is fixed by visibility replacement at thresholds `≤ finitePart ξ`. -/
theorem visReplace_cutoff {ξ : Ordinal.{0}} {k i : ℕ} (hk : k ≤ finitePart ξ) :
    visibilityReplace ξ k i = ξ := by
  unfold visibilityReplace
  rw [ite_eq_right (not_lt.mpr hk)]

/-- **Source collapse.** -/
theorem TransformsTo.collapse {D : Type*} {grade : D → ℕ} {f f' t : D → ExtOrd} {K : ℕ}
    (hK : ∀ d, grade d ≤ K) {ξ : Ordinal.{0}} (hξ : K ≤ finitePart ξ)
    (hf' : ∀ d, min (f' d) (ofOrd ξ) = f d) (h : TransformsTo grade f t) :
    TransformsTo grade f' t := by
  obtain ⟨g, σ, hg_anti, hg_vis, hσ_bot, hσ_mono, hσ5, heq⟩ := h
  refine ⟨fun k => if k ≤ K then g k else ⊥, fun a => σ (min a (ofOrd ξ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with hm hn hn
    · exact hg_anti n m hnm
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs
    · exact hg_vis n
    · exact (extVisibilityReplace_bot n n).symm
  · dsimp only
    rw [min_eq_left bot_le, hσ_bot]
  · intro a b hab
    exact hσ_mono (min_le_min_right _ hab)
  · intro a k hguard i hi
    dsimp only at hguard ⊢
    by_cases hk : k ≤ K
    · rw [ite_eq_left hk] at hguard
      by_cases ha : a ≤ ofOrd ξ
      · rw [min_eq_left ha] at hguard ⊢
        have hle : extVisibilityReplace a k i ≤ ofOrd ξ :=
          extVisReplace_le_of_le ha le_rfl (hk.trans hξ) hi
        rw [min_eq_left hle]
        exact hσ5 a k hguard i hi
      · rw [not_le] at ha
        rw [min_eq_right ha.le] at hguard ⊢
        have hge : ofOrd ξ ≤ extVisibilityReplace a k i := by
          rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
          · exact absurd ha (not_lt.mpr bot_le)
          · rw [extVisibilityReplace_top]; exact le_top
          · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
            exact (visReplace_gt_of_gt (hk.trans hξ) (ofOrd_lt_ofOrd.mp ha)).le
        rw [min_eq_right hge]
        have h5 := hσ5 (ofOrd ξ) k hguard i hi
        rw [extVisibilityReplace_ofOrd, visReplace_cutoff (hk.trans hξ)] at h5
        exact h5
    · rw [ite_eq_right hk] at hguard
      have hbot : σ (min a (ofOrd ξ)) = ⊥ := le_bot_iff.mp hguard
      rw [hbot, extVisibilityReplace_bot]
      apply le_bot_iff.mp
      by_cases ha : a ≤ ofOrd ξ
      · rw [min_eq_left ha] at hbot
        have h5 := hσ5 a k (by rw [hbot]; exact bot_le) i hi
        rw [hbot, extVisibilityReplace_bot] at h5
        calc σ (min (extVisibilityReplace a k i) (ofOrd ξ))
            ≤ σ (extVisibilityReplace a k i) := hσ_mono (min_le_left _ _)
          _ = ⊥ := h5
      · rw [not_le] at ha
        rw [min_eq_right ha.le] at hbot
        calc σ (min (extVisibilityReplace a k i) (ofOrd ξ)) ≤ σ (ofOrd ξ) :=
            hσ_mono (min_le_right _ _)
          _ = ⊥ := hbot
  · intro d
    dsimp only
    rw [ite_eq_left (hK d), hf', heq d]

end Collapse

/-- A label is at most its visibility replacement at its own threshold. -/
theorem le_extVisibilityReplace_self (x : ExtOrd) (k : ℕ) : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact le_rfl
  · exact le_rfl
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    unfold visibilityReplace
    split_ifs with h
    · unfold ordinalReplace
      calc α = limitPart α + ↑(finitePart α) := (decomposition α).symm
        _ ≤ limitPart α + (k : Ordinal) := add_le_add_right (by exact_mod_cast h.le) _
    · exact le_rfl

/-- Visibility replacement below a strict cutoff stays below it (thresholds
`≤ K < finitePart ξ`). -/
theorem extVisReplace_lt_cutoff {ξ : Ordinal.{0}} {K k i : ℕ} (hξ : K < finitePart ξ) (hk : k ≤ K)
    (hi : i ≤ k) {a : ExtOrd} (ha : a < ofOrd ξ) : extVisibilityReplace a k i < ofOrd ξ := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_lt_ofOrd _
  · exact absurd ha (not_lt.mpr le_top)
  · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
    have hα := ofOrd_lt_ofOrd.mp ha
    unfold visibilityReplace
    split_ifs with hfp
    · unfold ordinalReplace
      rcases lt_or_eq_of_le (limitPart_mono hα.le) with hlt | heq
      · have h1 : limitPart (limitPart α + ↑i) < limitPart ξ := by
          rw [limitPart_limitPart_add_nat]; exact hlt
        exact lt_of_lt_of_le (lt_limitPart_of_limitPart_lt h1) (limitPart_le ξ)
      · rw [heq]
        calc limitPart ξ + (i : Ordinal) < limitPart ξ + (finitePart ξ : Ordinal) :=
              add_lt_add_right (Nat.cast_lt.mpr (lt_of_le_of_lt (hi.trans hk) hξ) :
                ((i : ℕ) : Ordinal) < (finitePart ξ : ℕ)) _
          _ = ξ := decomposition ξ
    · exact hα

/-- Visibility replacement above a cutoff stays above it (thresholds `≤ finitePart ξ`). -/
theorem extVisReplace_ge_cutoff {ξ : Ordinal.{0}} {k i : ℕ} (hk : k ≤ finitePart ξ) {a : ExtOrd}
    (ha : ofOrd ξ ≤ a) : ofOrd ξ ≤ extVisibilityReplace a k i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact absurd ha (not_ofOrd_le_bot _)
  · rw [extVisibilityReplace_top]; exact le_top
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    rcases lt_or_eq_of_le (ofOrd_le_ofOrd.mp ha) with hlt | heq
    · exact (visReplace_gt_of_gt hk hlt).le
    · rw [← heq, visReplace_cutoff hk]


theorem limitPart_visibilityReplace (α : Ordinal.{0}) (k i : ℕ) :
    limitPart (visibilityReplace α k i) = limitPart α := by
  unfold visibilityReplace
  split_ifs
  · exact limitPart_limitPart_add_nat α i
  · rfl

/-! ## Splices of the shifter -/

open Classical in
/-- The shifter raised to at least `c` on the nonbottom fibre above the cutoff `ξ`. -/
noncomputable def raiseShifter (σ : ExtOrd → ExtOrd) (ξ : Ordinal.{0}) (c : ExtOrd) :
    ExtOrd → ExtOrd :=
  fun a => if ofOrd ξ ≤ a ∧ σ a ≠ ⊥ then max (σ a) c else σ a

theorem raiseShifter_of_lt {σ : ExtOrd → ExtOrd} {ξ : Ordinal.{0}} {c a : ExtOrd}
    (h : a < ofOrd ξ) : raiseShifter σ ξ c a = σ a := by
  classical
  unfold raiseShifter
  rw [ite_eq_right]
  rintro ⟨h1, -⟩
  exact absurd h (not_lt.mpr h1)

theorem raiseShifter_of_bot {σ : ExtOrd → ExtOrd} {ξ : Ordinal.{0}} {c a : ExtOrd}
    (h : σ a = ⊥) : raiseShifter σ ξ c a = ⊥ := by
  classical
  unfold raiseShifter
  rw [ite_eq_right, h]
  rintro ⟨-, h2⟩
  exact h2 h

theorem raiseShifter_of_ge {σ : ExtOrd → ExtOrd} {ξ : Ordinal.{0}} {c a : ExtOrd}
    (h1 : ofOrd ξ ≤ a) (h2 : σ a ≠ ⊥) : raiseShifter σ ξ c a = max (σ a) c := by
  classical
  unfold raiseShifter
  rw [ite_eq_left ⟨h1, h2⟩]

theorem le_raiseShifter (σ : ExtOrd → ExtOrd) (ξ : Ordinal.{0}) (c a : ExtOrd) :
    σ a ≤ raiseShifter σ ξ c a := by
  classical
  unfold raiseShifter
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- **Raising the shifter above a cutoff** preserves the witness clauses: for thresholds `≤ K` the
orbit of a label stays on its side of the cutoff and the nonbottom fibre is preserved, and
replacement commutes with `max`; for thresholds above `K` the guard `σ a ≤ ⊥` never meets a
raised value. -/
theorem Witness.raise {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) (K : ℕ)
    (hgK : ∀ k, K < k → g k = ⊥) {ξ : Ordinal.{0}} (hξ : K < finitePart ξ) {c : ExtOrd}
    (hc : extVisibilityReplace c K K = c) : Witness g (raiseShifter σ ξ c) where
  anti := hw.anti
  vis := hw.vis
  bot := by rw [raiseShifter_of_lt (bot_lt_ofOrd ξ)]; exact hw.bot
  mono := by
    intro a b hab
    by_cases hσa : σ a = ⊥
    · rw [raiseShifter_of_bot hσa]; exact bot_le
    have hσb : σ b ≠ ⊥ := fun h => hσa (le_bot_iff.mp (h ▸ hw.mono hab))
    by_cases ha : ofOrd ξ ≤ a
    · rw [raiseShifter_of_ge ha hσa, raiseShifter_of_ge (ha.trans hab) hσb]
      exact max_le_max (hw.mono hab) le_rfl
    · rw [not_le] at ha
      rw [raiseShifter_of_lt ha]
      exact (hw.mono hab).trans (le_raiseShifter σ ξ c b)
  clause5 := by
    intro α k hguard i hi
    by_cases hk : k ≤ K
    · by_cases hσ : σ α = ⊥
      · have h5 := hw.clause5 α k (by rw [hσ]; exact bot_le) i hi
        rw [hσ, extVisibilityReplace_bot] at h5
        rw [raiseShifter_of_bot hσ, raiseShifter_of_bot h5, extVisibilityReplace_bot]
      · by_cases hα : ofOrd ξ ≤ α
        · rw [raiseShifter_of_ge hα hσ] at hguard ⊢
          have hg : σ α ≤ g k := (le_max_left _ _).trans hguard
          have h5 := hw.clause5 α k hg i hi
          have hne : σ (extVisibilityReplace α k i) ≠ ⊥ := by
            rw [h5]; exact extVisibilityReplace_ne_bot hσ k i
          rw [raiseShifter_of_ge (extVisReplace_ge_cutoff (hk.trans hξ.le) hα) hne, h5,
            extVisibilityReplace_max _ _ hi,
            extVisReplace_eq_self_of_selfVis (extVisReplace_self_of_le hc hk) i]
        · rw [not_le] at hα
          rw [raiseShifter_of_lt hα] at hguard ⊢
          rw [raiseShifter_of_lt (extVisReplace_lt_cutoff hξ hk hi hα)]
          exact hw.clause5 α k hguard i hi
    · rw [not_le] at hk
      rw [hgK k hk] at hguard
      have hbot : raiseShifter σ ξ c α = ⊥ := le_bot_iff.mp hguard
      have hσ : σ α = ⊥ := le_bot_iff.mp (hbot ▸ le_raiseShifter σ ξ c α)
      have h5 := hw.clause5 α k (by rw [hσ]; exact bot_le) i hi
      rw [hσ, extVisibilityReplace_bot] at h5
      rw [hbot, raiseShifter_of_bot h5, extVisibilityReplace_bot]

/-- Membership in the tail `{α ≥ ξ}` of the block of `ξ`. -/
def InTail (ξ : Ordinal.{0}) (a : ExtOrd) : Prop :=
  ∃ β : Ordinal.{0}, a = ofOrd β ∧ ξ ≤ β ∧ limitPart β = limitPart ξ

open Classical in
/-- The shifter lowered to at most `c` on the tail of the block of `ξ`. -/
noncomputable def lowerShifter (σ : ExtOrd → ExtOrd) (ξ : Ordinal.{0}) (c : ExtOrd) :
    ExtOrd → ExtOrd :=
  fun a => if InTail ξ a then min (σ a) c else σ a

theorem lowerShifter_of_mem {σ : ExtOrd → ExtOrd} {ξ : Ordinal.{0}} {c a : ExtOrd}
    (h : InTail ξ a) :
    lowerShifter σ ξ c a = min (σ a) c := by
  classical
  unfold lowerShifter; rw [ite_eq_left h]
theorem lowerShifter_of_not_mem {σ : ExtOrd → ExtOrd} {ξ : Ordinal.{0}} {c a : ExtOrd}
    (h : ¬ InTail ξ a) : lowerShifter σ ξ c a = σ a := by
  classical
  unfold lowerShifter; rw [ite_eq_right h]
theorem lowerShifter_le (σ : ExtOrd → ExtOrd) (ξ : Ordinal.{0}) (c a : ExtOrd) :
    lowerShifter σ ξ c a ≤ σ a := by
  classical
  unfold lowerShifter; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem not_inTail_of_lt {ξ : Ordinal.{0}} {a : ExtOrd} (h : a < ofOrd ξ) : ¬ InTail ξ a := by
  rintro ⟨β, rfl, hβ, -⟩
  exact absurd (ofOrd_lt_ofOrd.mp h) (not_lt.mpr hβ)
theorem not_inTail_bot (ξ : Ordinal.{0}) : ¬ InTail ξ ⊥ := not_inTail_of_lt (bot_lt_ofOrd ξ)
theorem not_inTail_top (ξ : Ordinal.{0}) : ¬ InTail ξ ⊤ := by
  rintro ⟨β, h, -, -⟩
  exact absurd h.symm (ofOrd_ne_top β)
theorem InTail.ge {ξ : Ordinal.{0}} {a : ExtOrd} (h : InTail ξ a) : ofOrd ξ ≤ a := by
  obtain ⟨β, rfl, hβ, -⟩ := h
  exact ofOrd_le_ofOrd.mpr hβ

/-- Visibility replacement keeps a label's tail membership, in both directions. -/
theorem inTail_extVisReplace_iff {ξ : Ordinal.{0}} {K k i : ℕ} (hξ : K < finitePart ξ) (hk : k ≤ K)
    (hi : i ≤ k) (a : ExtOrd) : InTail ξ (extVisibilityReplace a k i) ↔ InTail ξ a := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd]
    constructor
    · rintro ⟨β, hβ, h1, h2⟩
      have hβ' : visibilityReplace α k i = β := ofOrd_inj.mp hβ
      subst hβ'
      rw [limitPart_visibilityReplace] at h2
      refine ⟨α, rfl, ?_, h2⟩
      by_contra hlt
      rw [not_le] at hlt
      exact absurd (ofOrd_lt_ofOrd.mp (extVisReplace_lt_cutoff hξ hk hi (ofOrd_lt_ofOrd.mpr hlt)))
        (not_lt.mpr h1)
    · rintro ⟨β, hβ, h1, h2⟩
      have hβ' : α = β := ofOrd_inj.mp hβ
      subst hβ'
      refine ⟨visibilityReplace α k i, rfl, ?_, by rw [limitPart_visibilityReplace]; exact h2⟩
      exact ofOrd_le_ofOrd.mp (extVisReplace_ge_cutoff (hk.trans hξ.le) (ofOrd_le_ofOrd.mpr h1))

/-- A label below the block of `ξ`'s tail, but in that block, is below `ξ`. -/
theorem lt_of_not_inTail {ξ β : Ordinal.{0}} (hβ : limitPart β = limitPart ξ)
    (h : ¬ InTail ξ (ofOrd β)) : β < ξ := by
  by_contra hle
  rw [not_lt] at hle
  exact h ⟨β, rfl, hle, hβ⟩

/-- **Lowering the shifter on a block tail** preserves the witness clauses, when the shifter is
already at most `c` below the cutoff. -/
theorem Witness.lower {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) (K : ℕ)
    (hgK : ∀ k, K < k → g k = ⊥) {ξ : Ordinal.{0}} (hξ : K < finitePart ξ) {c : ExtOrd}
    (hc : extVisibilityReplace c K K = c) (hleft : ∀ a, a < ofOrd ξ → σ a ≤ c) :
    Witness g (lowerShifter σ ξ c) where
  anti := hw.anti
  vis := hw.vis
  bot := by rw [lowerShifter_of_not_mem (not_inTail_bot ξ)]; exact hw.bot
  mono := by
    intro a b hab
    by_cases ha : InTail ξ a
    · rw [lowerShifter_of_mem ha]
      by_cases hb : InTail ξ b
      · rw [lowerShifter_of_mem hb]; exact min_le_min_right _ (hw.mono hab)
      · rw [lowerShifter_of_not_mem hb]; exact (min_le_left _ _).trans (hw.mono hab)
    · rw [lowerShifter_of_not_mem ha]
      by_cases hb : InTail ξ b
      · rw [lowerShifter_of_mem hb]
        refine le_min (hw.mono hab) (hleft a ?_)
        -- `a` is not in the tail but lies below `b`, which is in the block of `ξ`
        obtain ⟨β, rfl, hβ, hlp⟩ := hb
        rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
        · exact bot_lt_ofOrd ξ
        · exact absurd (top_le_iff.mp hab) (ofOrd_ne_top β)
        · rw [ofOrd_lt_ofOrd]
          have hαβ := ofOrd_le_ofOrd.mp hab
          by_contra hge
          rw [not_lt] at hge
          apply ha
          refine ⟨α, rfl, hge, le_antisymm ?_ (limitPart_mono hge)⟩
          rw [← hlp]; exact limitPart_mono hαβ
      · rw [lowerShifter_of_not_mem hb]; exact hw.mono hab
  clause5 := by
    intro α k hguard i hi
    by_cases hk : k ≤ K
    · by_cases hα : InTail ξ α
      · -- the tail is fixed by replacement at thresholds `≤ K`
        have hfix : extVisibilityReplace α k i = α := by
          obtain ⟨β, rfl, hβ, hlp⟩ := hα
          rw [extVisibilityReplace_ofOrd]
          congr 1
          unfold visibilityReplace
          rw [ite_eq_right]
          rw [not_lt]
          have : finitePart ξ ≤ finitePart β := by
            have : limitPart ξ + (finitePart ξ : Ordinal) ≤ limitPart ξ + finitePart β := by
              calc limitPart ξ + (finitePart ξ : Ordinal) = ξ := decomposition ξ
                _ ≤ β := hβ
                _ = limitPart β + finitePart β := (decomposition β).symm
                _ = limitPart ξ + finitePart β := by rw [hlp]
            exact_mod_cast (add_le_add_iff_left _).mp this
          omega
        rw [hfix]
        rw [lowerShifter_of_mem hα] at hguard ⊢
        rcases le_total (σ α) c with hσc | hσc
        · rw [min_eq_left hσc] at hguard ⊢
          have h5 := hw.clause5 α k hguard i hi
          rw [hfix] at h5
          exact h5
        · rw [min_eq_right hσc]
          exact (extVisReplace_eq_self_of_selfVis (extVisReplace_self_of_le hc hk) i).symm
      · rw [lowerShifter_of_not_mem hα] at hguard ⊢
        rw [lowerShifter_of_not_mem (fun h => hα ((inTail_extVisReplace_iff hξ hk hi α).mp h))]
        exact hw.clause5 α k hguard i hi
    · rw [not_le] at hk
      rw [hgK k hk] at hguard
      have hbot : lowerShifter σ ξ c α = ⊥ := le_bot_iff.mp hguard
      rw [hbot, extVisibilityReplace_bot]
      apply le_bot_iff.mp
      by_cases hσ : σ α = ⊥
      · have h5 := hw.clause5 α k (by rw [hσ]; exact bot_le) i hi
        rw [hσ, extVisibilityReplace_bot] at h5
        exact (lowerShifter_le σ ξ c _).trans (le_of_eq h5)
      · -- the lowered value is `⊥` only through `c = ⊥`, on the tail
        by_cases hα : InTail ξ α
        · rw [lowerShifter_of_mem hα] at hbot
          have hc0 : c = ⊥ := by
            rcases le_total (σ α) c with h | h
            · rw [min_eq_left h] at hbot; exact absurd hbot hσ
            · rw [min_eq_right h] at hbot; exact hbot
          obtain ⟨β, rfl, hβ, hlp⟩ := hα
          by_cases hb : InTail ξ (extVisibilityReplace (ofOrd β) k i)
          · rw [lowerShifter_of_mem hb, hc0]; exact min_le_right _ _
          · rw [lowerShifter_of_not_mem hb]
            rw [extVisibilityReplace_ofOrd] at hb ⊢
            have hlt : visibilityReplace β k i < ξ :=
              lt_of_not_inTail (by rw [limitPart_visibilityReplace]; exact hlp) hb
            rw [← hc0]
            exact hleft _ (ofOrd_lt_ofOrd.mpr hlt)
        · rw [lowerShifter_of_not_mem hα] at hbot
          exact absurd hbot hσ



end VaughtConjecture.Knight
