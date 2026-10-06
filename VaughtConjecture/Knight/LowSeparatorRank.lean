/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowSeparatorPaired
public import VaughtConjecture.Knight.LadderScalarRendering

/-! # The LOW separator on the rank ladder (grade `K = 1`)

The grade-one regime of newapproach19 new45 §5, kept distinct from the paired-slot regime: the
grade-one base is the actual long rank ladder (`SupportLadderRows`), whose anchors are rank
profiles (`LadderScalarRendering.fieldRank`) and whose spare tips are `SupportLadderRows.leaf`.
No paired-profile leaf is identified with a ladder tip.

* **The rank partner** (`rankPartner`): lower only the cutoff to the non-top maximum `M(s)` and
  re-rank.  Its cutoff rank is `k := rank_s(M(s))` (`rankPartner_cutoff`; `k = 0` for a bottom
  maximum), it agrees with `s`'s rank profile through `k` (`rankPartner_agree`, ties and future
  fields included since ranks are over the complete field type), and the **common rank cut** is
  exactly `k` (`cut_rankPartner`).
* **Strict comparison activates LOW** (`activation_of_cut_lt`, `activation_of_source`): a rank
  profile `a` with `Δ(a, t) < Δ(a, ŝ)` has `Δ(a, t) = k < Δ(a, ŝ)`, so every non-top donor rank
  is at most `k` and the cutoff rank exceeds `k`; for the actual source `a'` with ranks `a`,
  every non-top donor field lies strictly below the cutoff: `M(a') < a' b`.
* **The two-spare-tip separator on the actual ladder** (`ladder_separator`,
  `ladder_readback`): a lawful ladder section reading the partner's tip strictly below `s`'s tip
  is served by one anchor with a positive monotone table (`Lawful.exists_shape`); the tip
  readings are the table at the two common rank cuts, so LOW is active at the serving source,
  and a monotone rank table reading the private owner and low source as `⊤` reads every
  designated donor top as `⊤` (`readout_image`).
* **The selected readings** (`render_tip_partner`, `render_tip_self`): the ceiling-filled
  rendering of `s` reads the partner's tip at `M(s)` and its own tip at the ceiling, a strict
  comparison whenever the ceiling exceeds the cutoff.

The family section instantiates the activation and readback on KVC's `LowOnly.Family` at
`K = 1`.  No physical installation, bountifulness or model application is asserted. -/

@[expose] public section

namespace VaughtConjecture.Knight.LowSeparatorRank

open Transform Value ExtOrd LadderScalarRendering FiniteProfileControllers SupportLadderRows
  LowSeparator

noncomputable section

section Scalar

variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)

/-- The rank partner: only the cutoff is lowered, to the non-top maximum. -/
def rankPartner [DecidableEq X] (s : X → ExtOrd) : X → ExtOrd :=
  Function.update s b (donorMax N s)

theorem rankPartner_apply_self [DecidableEq X] (s : X → ExtOrd) :
    rankPartner N b s b = donorMax N s := Function.update_self b _ s

theorem rankPartner_apply_of_ne [DecidableEq X] (s : X → ExtOrd) {d : X} (hdb : d ≠ b) :
    rankPartner N b s d = s d := Function.update_of_ne hdb _ s

/-- The cutoff rank of the partner: the rank of the non-top maximum in `s`. -/
def rankCut (s : X → ExtOrd) : ℕ := LadderScalarRendering.rank (values s) (donorMax N s)

theorem donorMax_mem_values {s : X → ExtOrd} (hne : donorMax N s ≠ ⊥) :
    donorMax N s ∈ values s := by
  rcases donorMax_cases N s with h | ⟨d, -, hd⟩
  · exact absurd h hne
  · exact mem_values.mpr ⟨hne, d, hd⟩

theorem rankCut_le (s : X → ExtOrd) : rankCut N s ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le s)

variable {s : X → ExtOrd} (hlt : donorMax N s < s b)

include hlt in
theorem sb_mem_values : s b ∈ values s :=
  mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hlt), b, rfl⟩

include hlt in
theorem rankCut_lt_cutoff : rankCut N s < fieldRank s b :=
  rank_strict (sb_mem_values N b hlt) hlt

section Partner

variable [DecidableEq X]

include hlt in
/-- Below the old cutoff, the partner's inventory is `s`'s. -/
theorem values_rankPartner_below :
    ∀ y, y < s b → (y ∈ values (rankPartner N b s) ↔ y ∈ values s) := by
  intro y hy
  rw [mem_values, mem_values]
  constructor
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, ?_⟩
    by_cases hdb : d = b
    · rw [hdb, rankPartner_apply_self N b] at hd
      obtain ⟨_, e, he⟩ := mem_values.mp (donorMax_mem_values N (hd ▸ hz))
      exact ⟨e, he.trans hd⟩
    · rw [rankPartner_apply_of_ne N b s hdb] at hd
      exact ⟨d, hd⟩
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, ?_⟩
    by_cases hdb : d = b
    · subst hdb
      exact absurd (hd ▸ hy) (lt_irrefl _)
    · exact ⟨d, by rw [rankPartner_apply_of_ne N b s hdb]; exact hd⟩

include hlt in
/-- **The partner's cutoff rank is `k`.** -/
theorem rankPartner_cutoff : fieldRank (rankPartner N b s) b = rankCut N s := by
  unfold fieldRank rankCut
  rw [rankPartner_apply_self N b]
  exact rank_congr_below (values_rankPartner_below N b hlt) hlt

include hlt in
/-- **Rank-prefix agreement through `k`**, on every complete field. -/
theorem rankPartner_agree :
    Agree (fieldRank s) (fieldRank (rankPartner N b s)) (rankCut N s) := by
  intro d
  by_cases hdb : d = b
  · rw [hdb, rankPartner_cutoff N b hlt, min_self,
      min_eq_right (rankCut_lt_cutoff N b hlt).le]
  · unfold fieldRank
    rw [rankPartner_apply_of_ne N b s hdb]
    by_cases hsd : s d < s b
    · rw [rank_congr_below (values_rankPartner_below N b hlt) hsd]
    · have h1 : rankCut N s ≤ LadderScalarRendering.rank (values s) (s d) :=
        (rankCut_lt_cutoff N b hlt).le.trans (rank_mono _ (not_lt.mp hsd))
      have h2 : rankCut N s ≤ LadderScalarRendering.rank (values (rankPartner N b s)) (s d) := by
        have h := rank_mono (values (rankPartner N b s)) (hlt.le.trans (not_lt.mp hsd))
        have hk : LadderScalarRendering.rank (values (rankPartner N b s)) (donorMax N s) =
            rankCut N s := by
          have := rankPartner_cutoff N b hlt
          unfold fieldRank at this
          rw [rankPartner_apply_self N b] at this
          exact this
        rw [← hk]
        exact h
      rw [min_eq_right h1, min_eq_right h2]

include hlt in
/-- **The common rank cut is `k`.** -/
theorem cut_rankPartner {H : ℕ} (hH : Fintype.card X ≤ H) :
    cut H (fieldRank s) (fieldRank (rankPartner N b s)) = rankCut N s := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hag := agree_cut H (fieldRank s) (fieldRank (rankPartner N b s)) b
    rw [rankPartner_cutoff N b hlt, min_eq_left hgt.le] at hag
    have h1 := rankCut_lt_cutoff N b hlt
    have : rankCut N s <
        min (fieldRank s b) (cut H (fieldRank s) (fieldRank (rankPartner N b s))) :=
      lt_min h1 hgt
    omega
  · exact le_cut ((rankCut_le N s).trans hH) (rankPartner_agree N b hlt)

include hlt in
/-- The ultrametric identity on rank cuts: a strict comparison pins the partner cut at `k`. -/
theorem cut_rankPartner_eq_of_lt {H : ℕ} (hH : Fintype.card X ≤ H) {a : X → ℕ}
    (h : cut H a (fieldRank (rankPartner N b s)) < cut H a (fieldRank s)) :
    cut H a (fieldRank (rankPartner N b s)) = rankCut N s ∧
      rankCut N s < cut H a (fieldRank s) := by
  have hst := cut_rankPartner N b hlt hH
  have h1 := cut_triangle H a (fieldRank s) (fieldRank (rankPartner N b s))
  have h2 := cut_triangle H (fieldRank s) a (fieldRank (rankPartner N b s))
  rw [hst] at h1 h2
  rw [cut_symm H (fieldRank s) a] at h2
  omega

include hlt in
/-- **Strict comparison activates LOW at the rank level**: every non-top donor rank of the
serving profile is at most `k`, and its cutoff rank exceeds `k`. -/
theorem activation_of_cut_lt {H : ℕ} (hH : Fintype.card X ≤ H) {a : X → ℕ}
    (h : cut H a (fieldRank (rankPartner N b s)) < cut H a (fieldRank s)) :
    (∀ d, N d → a d ≤ rankCut N s) ∧ rankCut N s < a b := by
  obtain ⟨-, hu⟩ := cut_rankPartner_eq_of_lt N b hlt hH h
  have hag := agree_cut H a (fieldRank s)
  refine ⟨fun d hd => ?_, ?_⟩
  · have hsd : fieldRank s d ≤ rankCut N s := rank_mono _ (le_donorMax N s hd)
    have := hag d
    omega
  · have := hag b
    have hb := rankCut_lt_cutoff N b hlt
    omega

end Partner

/-- **Activation at the actual source**: a source whose rank profile has every non-top donor
rank at most `k` and cutoff rank above `k` has its non-top maximum strictly below its cutoff. -/
theorem activation_of_source {k : ℕ} (a : X → ExtOrd)
    (hlow : ∀ d, N d → fieldRank a d ≤ k) (hb : k < fieldRank a b) :
    donorMax N a < a b := by
  have hab : ⊥ < a b := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have : fieldRank a b = 0 := by
      unfold fieldRank
      rw [hz]
      exact rank_bot (bot_not_values a)
    omega
  apply (Finset.sup_lt_iff hab).mpr
  intro d hd
  have hd' : N d := (Finset.mem_filter.mp hd).2
  by_contra hn
  have := rank_mono (values a) (not_lt.mp hn)
  have := hlow d hd'
  unfold fieldRank at *
  omega

end Scalar

/-! ## The two-spare-tip separator on the actual ladder -/

section Ladder

variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)
  {Q : Type*} [Finite Q] {H : ℕ} (profile : Q → X → ℕ)
  (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
  (src : Q → X → ExtOrd) (hsrc : ∀ a, profile a = fieldRank (src a))

include hbound hH hsrc in
/-- **The separator**: a lawful ladder section reading the partner's tip strictly below the
selected anchor's tip is served by an anchor whose source satisfies `M(a') < a' b`. -/
theorem ladder_separator [DecidableEq X] [Nonempty Q] {s : X → ExtOrd} (hlt : donorMax N s < s b)
    (hHX : Fintype.card X ≤ H) {qs qt : Q} (hqs : src qs = s) (hqt : src qt = rankPartner N b s)
    {q : Point H X Q → ExtOrd} (hq : Lawful profile q)
    (hcmp : q (leaf hH qt) < q (leaf hH qs)) :
    ∃ (a : Q) (g : ℕ → ExtOrd), Monotone g ∧ (∀ v, q v = image profile a g v) ∧
      donorMax N (src a) < src a b := by
  obtain ⟨a, g, hg, -, -, he⟩ := hq.exists_shape hbound hH
  refine ⟨a, g, hg, he, ?_⟩
  have hcut : cut H (profile a) (profile qt) < cut H (profile a) (profile qs) := by
    apply lt_of_not_ge
    intro hle
    have := hg hle
    rw [he, he, image, image, index_leaf, index_leaf] at hcmp
    exact absurd hcmp (not_lt.mpr this)
  rw [hsrc qt, hsrc qs, hqt, hqs, hsrc a] at hcut
  obtain ⟨hlow, hb⟩ := activation_of_cut_lt N b hlt hHX hcut
  exact activation_of_source N b (src a) hlow hb

omit [DecidablePred N] in
include hbound hsrc in
/-- **Donor-top readback on the ladder**: for a section rendered by a monotone table on an
anchor whose source satisfies the LOW bound, top readouts at the private owner and low source
force top readouts at every designated donor top. -/
theorem ladder_readback {a : Q} {g : ℕ → ExtOrd} (hg : Monotone g)
    {q : Point H X Q → ExtOrd} (he : ∀ v, q v = image profile a g v)
    {T : X → Prop} {c r : X}
    (hlow : ∀ d, T d → min (src a c) (src a r) ≤ src a d)
    (hc : readout q c = ⊤) (hr : readout q r = ⊤) (d : X) (hd : T d) : readout q d = ⊤ := by
  have hq : q = image profile a g := funext he
  subst hq
  rw [readout_image hbound a hg, hsrc] at hc hr ⊢
  have key : min (src a c) (src a r) ≤ src a d := hlow d hd
  rcases min_choice (src a c) (src a r) with h | h
  · rw [h] at key
    have h1 : g (fieldRank (src a) c) ≤ g (fieldRank (src a) d) := hg (rank_mono _ key)
    rw [hc] at h1
    exact top_le_iff.mp h1
  · rw [h] at key
    have h1 : g (fieldRank (src a) r) ≤ g (fieldRank (src a) d) := hg (rank_mono _ key)
    rw [hr] at h1
    exact top_le_iff.mp h1

end Ladder

/-! ## The selected rendered readings -/

section Selected

variable {X : Type*} [Fintype X] (N : X → Prop) [DecidablePred N] (b : X)
  {Q : Type*} [Finite Q] {H : ℕ} (profile : Q → X → ℕ) (hH : 0 < H)

omit [Finite Q] in
include hH in
/-- The rendering of `s` reads the partner's tip at the non-top maximum. -/
theorem render_tip_partner [DecidableEq X] {s : X → ExtOrd} (hlt : donorMax N s < s b)
    (hHX : Fintype.card X ≤ H) {qs qt : Q} (hqs : profile qs = fieldRank s)
    (hqt : profile qt = fieldRank (rankPartner N b s)) (C : ExtOrd) :
    render profile qs s C (leaf hH qt) = donorMax N s := by
  unfold render
  rw [image, index_leaf, hqs, hqt, cut_rankPartner N b hlt hHX]
  by_cases hM : donorMax N s = ⊥
  · unfold rankCut
    rw [hM, rank_bot (bot_not_values s), level_zero]
  · exact level_rank (donorMax_mem_values N hM) C

omit [DecidablePred N] [Finite Q] in
include hH in
/-- The rendering of `s` reads its own tip at the ceiling. -/
theorem render_tip_self (s : X → ExtOrd) (hHX : Fintype.card X < H) (qs : Q) (C : ExtOrd) :
    render profile qs s C (leaf hH qs) = C := by
  classical
  unfold render
  rw [image, index_leaf, cut_refl, LadderScalarRendering.level,
    ite_eq_left ((values_card_le s).trans_lt hHX)]

end Selected

/-! ## The family instance at `K = 1` -/

section Family

open LowOnly

variable {n : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C 1)

/-- At grade one, the LOW bound of an active admitted state is the plain minimum of the private
owner and low source. -/
theorem low_min_le {A : State P C} (hA : F.Admissible 1 A) (hm : F.maximum A < A.b)
    (d : Cell P.scheme) (hd : F.p d = ⊤) : min (A.v F.gap.c) (A.v F.gap.r.1) ≤ A.u d := by
  have hlow := hA.low le_rfl hm d hd
  change max A.b (min (A.v F.gap.c) (extVisibilityReplace (A.v F.gap.r.1) 1 1)) ≤ A.u d at hlow
  have hvis : SelfVis 1 (A.v F.gap.r.1) := by
    have h := (hA.lawfulC.orderly (CellScheme.below.mono (F.gap.domLe le_rfl) F.gap.r)).symm
    change SelfVis (C.scheme.grade F.gap.r.1) (A.v F.gap.r.1) at h
    exact h.mono (C.scheme.grade_pos _)
  rw [evr_eq_self_of_selfVis hvis] at hlow
  exact (le_max_right _ _).trans hlow

/-- **The rank-ladder separator on the family**: anchors are the rank profiles of admitted
sources; a lawful section reading the partner's tip strictly below the selected tip is served by
an active source, and top readouts at the private owner and low source force top readouts at
every designated donor top. -/
theorem family_ladder_readback {Q : Type*} [Finite Q] [Nonempty Q] {H : ℕ}
    (profile : Q → LowOnly.Field P C → ℕ) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
    (hHX : Fintype.card (LowOnly.Field P C) ≤ H) (src : Q → State P C)
    (hadm : ∀ a, F.Admissible 1 (src a)) (hsrc : ∀ a, profile a = fieldRank (src a).profile)
    {S : State P C} (hlt : donorMax (donorField F) S.profile < S.b) {qs qt : Q}
    (hqs : (src qs).profile = S.profile)
    (hqt : (src qt).profile = rankPartner (donorField F) cutoffField S.profile)
    {q : Point H (LowOnly.Field P C) Q → ExtOrd} (hq : Lawful profile q)
    (hcmp : q (leaf hH qt) < q (leaf hH qs))
    (hc : readout q (Sum.inr (Sum.inl F.gap.c)) = ⊤)
    (hr : readout q (Sum.inr (Sum.inl F.gap.r.1)) = ⊤) (d : Cell P.scheme) (hd : F.p d = ⊤) :
    readout q (Sum.inl d) = ⊤ := by
  obtain ⟨a, g, hg, he, hact⟩ := ladder_separator (donorField F) cutoffField profile hbound hH
    (fun a => (src a).profile) hsrc hlt hHX hqs hqt hq hcmp
  have hm : F.maximum (src a) < (src a).b := by
    rw [maximum_eq_donorMax]
    exact hact
  exact ladder_readback profile hbound (fun a => (src a).profile) hsrc hg he
    (T := fun x => ∃ e, x = Sum.inl e ∧ F.p e = ⊤) (c := Sum.inr (Sum.inl F.gap.c))
    (r := Sum.inr (Sum.inl F.gap.r.1))
    (fun x hx => by
      obtain ⟨e, rfl, he'⟩ := hx
      exact low_min_le F (hadm a) hm e he')
    hc hr (Sum.inl d) ⟨d, rfl, hd⟩

end Family

end

end VaughtConjecture.Knight.LowSeparatorRank
