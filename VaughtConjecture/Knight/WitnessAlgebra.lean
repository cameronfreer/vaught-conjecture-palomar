/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibilityAlgebra

/-! # Witness algebra before row construction

The five-clause witness, suppressor truncation and capping, the normalized
suppressor and identity, maximum, and exact controller-capped witnesses.
No scheme, installed carrier, catalogue, model, or example is imported.

Declarations retain their names, statements, and proofs (up to lint-only edits)
from `WitnessSplice`, `TwoContextCoupled`, `ControllerPrefixFamily`,
`CappedLocalityRecoding`, and `FreeDiagonal`. Capping keeps its visibility
and controller-grade hypotheses.
Nothing here asserts unrestricted transformation composition.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Witnesses -/

/-- The five clauses of Def. 2.3.9 for a suppressor/shifter pair. -/
structure Witness (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd) : Prop where
  anti : ∀ n m : ℕ, n < m → g m ≤ g n
  vis : ∀ n : ℕ, g n = extVisibilityReplace (g n) n n
  bot : σ ⊥ = ⊥
  mono : Monotone σ
  clause5 : ∀ (α : ExtOrd) (k : ℕ), σ α ≤ g k → ∀ i : ℕ, i ≤ k →
    σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i

theorem Witness.transformsTo {D : Type*} {grade : D → ℕ} {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd}
    (hw : Witness g σ) {f t : D → ExtOrd} (heq : ∀ d, t d = min (σ (f d)) (g (grade d))) :
    TransformsTo grade f t :=
  ⟨g, σ, hw.anti, hw.vis, hw.bot, hw.mono, hw.clause5, heq⟩

theorem TransformsTo.witness {D : Type*} {grade : D → ℕ} {f t : D → ExtOrd}
    (h : TransformsTo grade f t) :
    ∃ (g : ℕ → ExtOrd) (σ : ExtOrd → ExtOrd), Witness g σ ∧
      ∀ d, t d = min (σ (f d)) (g (grade d)) := by
  obtain ⟨g, σ, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨g, σ, ⟨h1, h2, h3, h4, h5⟩, h6⟩

/-- A witness stays a witness for any antitone self-visible suppressor below the old one. -/
theorem Witness.of_le_g {g g' : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ)
    (hle : ∀ k, g' k ≤ g k) (anti : ∀ n m : ℕ, n < m → g' m ≤ g' n)
    (vis : ∀ n : ℕ, g' n = extVisibilityReplace (g' n) n n) : Witness g' σ :=
  ⟨anti, vis, hw.bot, hw.mono, fun α k hg i hi => hw.clause5 α k (hg.trans (hle k)) i hi⟩

/-- The suppressor truncated to `⊥` above `K`. -/
noncomputable def truncG (K : ℕ) (g : ℕ → ExtOrd) : ℕ → ExtOrd := fun k => if k ≤ K then g k else ⊥

theorem truncG_of_le {K : ℕ} {g : ℕ → ExtOrd} {k : ℕ} (h : k ≤ K) : truncG K g k = g k :=
  ite_eq_left h
theorem truncG_of_gt {K : ℕ} {g : ℕ → ExtOrd} {k : ℕ} (h : K < k) : truncG K g k = ⊥ :=
  ite_eq_right (not_le.mpr h)
theorem truncG_le (K : ℕ) (g : ℕ → ExtOrd) (k : ℕ) : truncG K g k ≤ g k := by
  unfold truncG; split_ifs
  · exact le_rfl
  · exact bot_le

theorem Witness.truncate {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) (K : ℕ) :
    Witness (truncG K g) σ :=
  hw.of_le_g (truncG_le K g)
    (fun n m hnm => by
      unfold truncG; split_ifs with hm hn hn
      · exact hw.anti n m hnm
      · omega
      · exact bot_le
      · exact le_rfl)
    (fun n => by
      unfold truncG; split_ifs
      · exact hw.vis n
      · exact (extVisibilityReplace_bot n n).symm)

/-- The suppressor capped by `c` up to `K`, `⊥` above. -/
noncomputable def capG (K : ℕ) (c : ExtOrd) (g : ℕ → ExtOrd) : ℕ → ExtOrd :=
  fun k => if k ≤ K then min (g k) c else ⊥

theorem capG_of_le {K : ℕ} {c : ExtOrd} {g : ℕ → ExtOrd} {k : ℕ} (h : k ≤ K) :
    capG K c g k = min (g k) c := ite_eq_left h

/-- **The Cap Lemma at the witness level.** -/
theorem Witness.cap {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hw : Witness g σ) (K : ℕ) {c : ExtOrd}
    (hc : extVisibilityReplace c K K = c) : Witness (capG K c g) σ :=
  hw.of_le_g
    (fun k => by
      unfold capG; split_ifs
      · exact min_le_left _ _
      · exact bot_le)
    (fun n m hnm => by
      unfold capG; split_ifs with hm hn hn
      · exact min_le_min_right _ (hw.anti n m hnm)
      · omega
      · exact bot_le
      · exact le_rfl)
    (fun n => by
      unfold capG; split_ifs with hn
      · rcases le_total (g n) c with h | h
        · rw [min_eq_left h]; exact hw.vis n
        · rw [min_eq_right h]; exact (extVisReplace_self_of_le hc hn).symm
      · exact (extVisibilityReplace_bot n n).symm)

/-- The suppressor `⊤` at grades `≤ K`, `⊥` above. -/
noncomputable def gTop (K : ℕ) : ℕ → ExtOrd := fun k => if k ≤ K then ⊤ else ⊥

theorem gTop_of_le {K k : ℕ} (h : k ≤ K) : gTop K k = ⊤ := ite_eq_left h
theorem gTop_of_gt {K k : ℕ} (h : K < k) : gTop K k = ⊥ := ite_eq_right (by omega)

theorem witness_id (K : ℕ) : Witness (gTop K) id where
  anti n m h := by
    unfold gTop
    split_ifs <;> first | exact le_rfl | exact bot_le | omega
  vis n := by
    unfold gTop
    split_ifs <;> rfl
  bot := rfl
  mono := monotone_id
  clause5 _ _ _ _ _ := rfl

/-- Pointwise maximum preserves witnesses with the same suppressor. Both guards
follow from the guard on the maximum; neither locality is discarded. -/
theorem Witness.max {g : ℕ → ExtOrd} {σ τ : ExtOrd → ExtOrd}
    (hσ : Witness g σ) (hτ : Witness g τ) : Witness g (fun a => max (σ a) (τ a)) where
  anti := hσ.anti
  vis := hσ.vis
  bot := by rw [hσ.bot, hτ.bot, max_self]
  mono := fun _ _ h => max_le_max (hσ.mono h) (hτ.mono h)
  clause5 := by
    intro a k hk i hi
    rw [hσ.clause5 a k ((le_max_left _ _).trans hk) i hi,
      hτ.clause5 a k ((le_max_right _ _).trans hk) i hi,
      extVisibilityReplace_max _ _ hi]

/-! ## The controller-capped witness -/

section Capped

/-- Replacing back: `(x ⊔⁺ₖ i) ⊔⁺ₖ (fp x) = x` when `x` moves and `i < k`. -/
theorem evr_evr_finitePart {α : Ordinal.{0}} {k i : ℕ} (hfp : finitePart α < k) (hi : i < k) :
    extVisibilityReplace (extVisibilityReplace (ofOrd α) k i) k (finitePart α) = ofOrd α := by
  rw [extVisibilityReplace_of_finitePart_lt hfp,
    extVisibilityReplace_of_finitePart_lt (by rw [finitePart_limitPart_add_nat]; exact hi),
    limitPart_limitPart_add_nat, limitPart_add_finitePart]

variable {D : Type*} (grade : D → ℕ) (E p : D → ExtOrd) (c : D)

/-- **The key step**: at a threshold `k ≤ K` with `cap ≤ g k`, if `σ x` exceeds the cap then
so does `σ` at every replacement of `x` — otherwise `σ`'s clause 5 at the replaced point would
pull `σ x` below the cap. -/
theorem cap_le_of_evr {g : ℕ → ExtOrd} {σ : ExtOrd → ExtOrd} (hσmono : Monotone σ)
    (hσevr : ∀ x k, σ x ≤ g k → ∀ i, i ≤ k →
      σ (extVisibilityReplace x k i) = extVisibilityReplace (σ x) k i)
    {cap : ExtOrd} {k : ℕ} (hvis : SelfVis k cap) (hcap : cap ≤ g k)
    {x : ExtOrd} (hx : cap < σ x) {i : ℕ} (hi : i ≤ k) :
    cap ≤ σ (extVisibilityReplace x k i) := by
  by_contra hlt
  have hlt := not_le.mp hlt
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [extVisibilityReplace_bot] at hlt; exact absurd hx (not_lt.mpr hlt.le)
  · rw [extVisibilityReplace_top] at hlt; exact absurd hx (not_lt.mpr hlt.le)
  · by_cases hfp : finitePart α < k
    · rcases lt_or_eq_of_le hi with hik | hik
      · -- the replaced point is active for `σ`; replace back to `x`
        have hact : σ (extVisibilityReplace (ofOrd α) k i) ≤ g k := hlt.le.trans hcap
        have h5 := hσevr _ k hact (finitePart α) hfp.le
        rw [evr_evr_finitePart hfp hik] at h5
        have : σ (ofOrd α) ≤ cap := by
          rw [h5]; exact extVisibilityReplace_le_of_le_selfVis hfp.le hvis hlt.le
        exact absurd hx (not_lt.mpr this)
      · -- `i = k`: the replacement is above `x`
        have hle : ofOrd α ≤ extVisibilityReplace (ofOrd α) k i := by
          rw [hik, extVisibilityReplace_of_finitePart_lt hfp, ofOrd_le_ofOrd]
          conv_lhs => rw [← limitPart_add_finitePart α]
          exact add_le_add le_rfl (by exact_mod_cast hfp.le)
        exact absurd hx (not_lt.mpr ((hσmono hle).trans hlt.le))
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfp)] at hlt
      exact absurd hx (not_lt.mpr hlt.le)

/-- **The controller-capped witness.**  From an actual locality toward the controller `c` of
maximal grade `K` with a `K`-self-visible nonbottom cap `p c`: a transformation witness whose
shifter is bounded by the cap, **equals the displayed target at every source**, commutes with
every replacement at thresholds `≤ K` unconditionally, and propagates `⊥`. -/
theorem exists_cappedWitness (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
    (hne : p c ≠ ⊥) (hloc : TransformsTo grade E (fun d => min (p d) (p c))) :
    ∃ (g' : ℕ → ExtOrd) (τ : ExtOrd → ExtOrd),
      (∀ n m, n < m → g' m ≤ g' n) ∧ (∀ n, SelfVis n (g' n)) ∧ τ ⊥ = ⊥ ∧ Monotone τ ∧
      (∀ x k, τ x ≤ g' k → ∀ i, i ≤ k →
        τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i) ∧
      (∀ d, min (p d) (p c) = min (τ (E d)) (g' (grade d))) ∧
      (∀ x, τ x ≤ p c) ∧ (∀ d, τ (E d) = min (p d) (p c)) ∧
      (∀ x k i, k ≤ grade c → i ≤ k →
        τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i) ∧
      (∀ x, τ x = ⊥ → ∀ k i, i ≤ k → τ (extVisibilityReplace x k i) = ⊥) := by
  obtain ⟨g, σ, hanti, hgvis, hbot, hmono, hevr, hrow⟩ := hloc
  have hcapg : p c ≤ g (grade c) := by
    have hc := hrow c
    simp only [min_self] at hc
    exact hc.le.trans (min_le_right _ _)
  have hgate : ∀ d, p c ≤ g (grade d) := fun d =>
    hcapg.trans (suppressor_le_of_grade_le hanti (hmax d))
  have hgk : ∀ k, k ≤ grade c → p c ≤ g k := fun k hk =>
    hcapg.trans (suppressor_le_of_grade_le hanti hk)
  -- clause 5 of the capped shifter against the capped suppressor
  have h5 : ∀ x k, min (σ x) (p c) ≤ (if k ≤ grade c then min (g k) (p c) else ⊥) → ∀ i, i ≤ k →
      min (σ (extVisibilityReplace x k i)) (p c) =
        extVisibilityReplace (min (σ x) (p c)) k i := by
    intro x k hact i hi
    split_ifs at hact with hk
    · have hcapk : SelfVis k (p c) := selfVis_mono hvis hk
      rcases le_or_gt (σ x) (p c) with hle | hlt
      · have hτ : min (σ x) (p c) = σ x := min_eq_left hle
        rw [hτ] at hact ⊢
        have hσact : σ x ≤ g k := hact.trans (min_le_left _ _)
        rw [hevr x k hσact i hi, min_eq_left (extVisibilityReplace_le_of_le_selfVis hi hcapk hle)]
      · have hτ : min (σ x) (p c) = p c := min_eq_right hlt.le
        rw [hτ]
        rw [min_eq_right (cap_le_of_evr hmono hevr hcapk (hgk k hk) hlt hi),
          evr_eq_self_of_selfVis hcapk]
    · have hτbot : min (σ x) (p c) = ⊥ := le_bot_iff.mp hact
      have hσbot : σ x = ⊥ := by
        rcases le_total (σ x) (p c) with h | h
        · rwa [min_eq_left h] at hτbot
        · rw [min_eq_right h] at hτbot; exact absurd hτbot hne
      have hσact : σ x ≤ g k := by rw [hσbot]; exact bot_le
      rw [hevr x k hσact i hi, hσbot, extVisibilityReplace_bot, min_eq_left bot_le,
        extVisibilityReplace_bot]
  refine ⟨fun k => if k ≤ grade c then min (g k) (p c) else ⊥, fun x => min (σ x) (p c),
    ?_, ?_, ?_, ?_, h5, ?_, fun _ => min_le_right _ _, ?_, ?_, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with h1 h2 h2
    · exact min_le_min (hanti n m hnm) le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs with h
    · exact selfVis_min (hgvis n).symm (selfVis_mono hvis h)
    · exact selfVis_bot n
  · change min (σ ⊥) (p c) = ⊥
    rw [hbot, min_eq_left bot_le]
  · exact fun _ _ h => min_le_min (hmono h) le_rfl
  · intro d
    have h := hrow d
    simp only at h
    dsimp only
    rw [ite_eq_left (hmax d), min_min_min_comm, min_self, ← h, min_assoc, min_self]
  · intro d
    have h := hrow d
    simp only at h
    change min (σ (E d)) (p c) = min (p d) (p c)
    calc min (σ (E d)) (p c) = min (min (σ (E d)) (g (grade d))) (p c) := by
          rw [min_assoc, min_eq_right (hgate d)]
      _ = min (min (p d) (p c)) (p c) := by rw [h]
      _ = min (p d) (p c) := by rw [min_assoc, min_self]
  · intro x k i hk hi
    apply h5 x k _ i hi
    rw [ite_eq_left hk]
    exact le_min ((min_le_right _ _).trans (hgk k hk)) (min_le_right _ _)
  · intro x hx k i hi
    change min (σ x) (p c) = ⊥ at hx
    change min (σ (extVisibilityReplace x k i)) (p c) = ⊥
    have := h5 x k (by rw [hx]; exact bot_le) i hi
    rw [hx, extVisibilityReplace_bot] at this
    exact this

end Capped

/-- Controller capping retains a global bound as well as exact readback. The common
top/bottom suppressor makes this witness usable with pointwise maximum. -/
theorem exists_bounded_exact_capped_witness {D : Type*} {grade : D → ℕ}
    {E p : D → ExtOrd} {c : D} (hmax : ∀ d, grade d ≤ grade c)
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (grade c)) τ ∧
      (∀ x, τ x ≤ p c) ∧ (∀ d, τ (E d) = min (p d) (p c)) := by
  by_cases hb : p c = ⊥
  · refine ⟨fun _ => ⊥, ?_, fun _ => bot_le, ?_⟩
    · exact ⟨(witness_id _).anti, (witness_id _).vis, rfl, monotone_const,
        by intros; exact (extVisibilityReplace_bot _ _).symm⟩
    · intro d
      simp only [hb, min_bot_right]
  · obtain ⟨_, τ, _, _, hbot, hmono, _, _, hbound, hsrc, hcomm, hprop⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    refine ⟨τ, ⟨(witness_id _).anti, (witness_id _).vis, hbot, hmono, ?_⟩,
      hbound, hsrc⟩
    intro x k hact i hi
    by_cases hk : k ≤ grade c
    · exact hcomm x k i hk hi
    · rw [gTop_of_gt (not_le.mp hk)] at hact
      have hzero := le_bot_iff.mp hact
      rw [hprop x hzero k i hi, hzero, extVisibilityReplace_bot]

end VaughtConjecture.Knight
