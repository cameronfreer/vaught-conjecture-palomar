/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderLowerRows

/-! # Ceiling-filled scalar rendering for the support ladder

The distinct positive field values determine their ranks and all occupied
rung values. Every unused positive rung reads the supplied ceiling. The
common rank cut is constructed from the values strictly below the external
cap; it is not an extra receipt assumed of the physical source.

This is the grade-one base of new16's renderer. It does not construct the
higher semantic rows or claim bountifulness of a receiving scheme.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.LadderScalarRendering

open Transform Value ExtOrd
noncomputable section

open Classical in
/-- One-based rank on a finite set of positive values. -/
def rank (S : Finset ExtOrd) (x : ExtOrd) : ℕ := (S.filter (· ≤ x)).card

open Classical in
/-- The occupied initial segment followed by the constant ceiling tail. -/
def level (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if S.card < i then C else (S.filter (fun x => rank S x ≤ i)).sup id

theorem rank_le_card (S : Finset ExtOrd) (x : ExtOrd) : rank S x ≤ S.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_mono (S : Finset ExtOrd) : Monotone (rank S) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (Finset.mem_filter.mp hz).2.trans hxy⟩

theorem rank_strict {S : Finset ExtOrd} {x y : ExtOrd} (hy : y ∈ S) (hxy : x < y) :
    rank S x < rank S y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hxy.le⟩
  · intro he
    have hm : y ∈ S.filter (· ≤ y) := Finset.mem_filter.mpr ⟨hy, le_rfl⟩
    rw [← he] at hm
    exact (not_le_of_gt hxy) (Finset.mem_filter.mp hm).2

theorem rank_pos {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) : 0 < rank S x := by
  classical
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem rank_bot {S : Finset ExtOrd} (hS : ⊥ ∉ S) : rank S ⊥ = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
  exact hS ((le_bot_iff.mp hx) ▸ hxS)

theorem level_zero (S : Finset ExtOrd) (C : ExtOrd) : level S C 0 = ⊥ := by
  classical
  rw [level, ite_eq_right (by omega)]
  have he : S.filter (fun x => rank S x ≤ 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hp := rank_pos (Finset.mem_filter.mp hx).1
    have := (Finset.mem_filter.mp hx).2
    omega
  rw [he, Finset.sup_empty]

theorem level_rank {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) (C : ExtOrd) :
    level S C (rank S x) = x := by
  classical
  rw [level, ite_eq_right (not_lt.mpr (rank_le_card S x))]
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    by_contra hn
    have hs := rank_strict (Finset.mem_filter.mp hy).1 (not_le.mp hn)
    exact not_le_of_gt hs (Finset.mem_filter.mp hy).2
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)

theorem level_le {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) (i : ℕ) :
    level S C i ≤ C := by
  classical
  unfold level
  split_ifs
  · exact le_rfl
  · exact Finset.sup_le (fun x hx => hC x (Finset.mem_filter.mp hx).1)

theorem level_mono {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) :
    Monotone (level S C) := by
  classical
  intro i k hik
  by_cases hk : S.card < k
  · rw [show level S C k = C from ite_eq_left hk]
    exact level_le hC i
  · have hi : ¬S.card < i := by omega
    rw [level, ite_eq_right hi, level, ite_eq_right hk]
    apply Finset.sup_le
    intro x hx
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hik⟩)

theorem level_supported (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) :
    level S C i = ⊥ ∨ level S C i ∈ S ∨ level S C i = C := by
  classical
  unfold level
  split_ifs
  · exact Or.inr (Or.inr rfl)
  · by_cases hn : (S.filter (fun x => rank S x ≤ i)).Nonempty
    · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
      exact Or.inr (Or.inl (he ▸ (Finset.mem_filter.mp hx).1))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty]
      exact Or.inl rfl

theorem rank_min' {S : Finset ExtOrd} (hS : S.Nonempty) : rank S (S.min' hS) = 1 := by
  classical
  have he : S.filter (· ≤ S.min' hS) = {S.min' hS} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (le_antisymm (Finset.mem_filter.mp hx).2
        (Finset.min'_le S x (Finset.mem_filter.mp hx).1))
    · intro hx
      rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨Finset.min'_mem S hS, le_rfl⟩
  rw [rank, he, Finset.card_singleton]

theorem level_pos {S : Finset ExtOrd} {C : ExtOrd} (hS : ⊥ ∉ S)
    (hC : ∀ x ∈ S, x ≤ C) (hpos : C ≠ ⊥) {i : ℕ} (hi : 0 < i) :
    level S C i ≠ ⊥ := by
  classical
  by_cases hn : S.Nonempty
  · have hm := Finset.min'_mem S hn
    have hle : S.min' hn ≤ level S C i := by
      rw [← level_rank hm C, rank_min' hn]
      exact level_mono hC hi
    intro hz
    exact hS ((le_bot_iff.mp (hle.trans_eq hz)) ▸ hm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, level, Finset.card_empty, ite_eq_left hi]
    exact hpos

open Classical in
/-- One more than the number of occupied values strictly below a cap. -/
def next (S : Finset ExtOrd) (h : ExtOrd) : ℕ := (S.filter (· < h)).card + 1

theorem next_le (S : Finset ExtOrd) (h : ExtOrd) : next S h ≤ S.card + 1 := by
  classical
  exact Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1

theorem rank_lt_next {S : Finset ExtOrd} {x h : ExtOrd} (hx : x ∈ S) :
    rank S x < next S h ↔ x < h := by
  classical
  constructor
  · intro hr
    by_contra hn
    have hsub : S.filter (· < h) ⊂ S.filter (· ≤ x) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2.le.trans (not_lt.mp hn)⟩
      · intro he
        have hm : x ∈ S.filter (· ≤ x) := Finset.mem_filter.mpr ⟨hx, le_rfl⟩
        rw [← he] at hm
        exact hn (Finset.mem_filter.mp hm).2
    have hc := Finset.card_lt_card hsub
    dsimp only [rank, next] at hr
    omega
  · intro hxh
    have hc : (S.filter (· ≤ x)).card ≤ (S.filter (· < h)).card := by
      apply Finset.card_le_card
      intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
        (Finset.mem_filter.mp hy).2.trans_lt hxh⟩
    exact Nat.lt_succ_of_le hc

theorem rank_congr_below {S T : Finset ExtOrd} {h x : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) (hx : x < h) : rank S x = rank T x := by
  classical
  unfold rank
  congr 1
  ext y
  simp only [Finset.mem_filter]
  exact and_congr_left (fun hy => hst y (hy.trans_lt hx))

open Classical in
theorem below_eq {S T : Finset ExtOrd} {h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) : S.filter (· < h) = T.filter (· < h) := by
  ext y
  simp only [Finset.mem_filter]
  exact and_congr_left (hst y)

theorem level_agree_below {S T : Finset ExtOrd} {C h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) {i : ℕ} (hi : i < next S h) :
    level S C i = level T C i := by
  classical
  have he := below_eq hst
  have hn : next S h = next T h := congrArg (fun s : Finset ExtOrd => s.card + 1) he
  have hiS : ¬S.card < i := by have := next_le S h; omega
  have hiT : ¬T.card < i := by have := next_le T h; omega
  rw [level, ite_eq_right hiS, level, ite_eq_right hiT]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxS).mp (hr.trans_lt hi)
    exact Finset.mem_filter.mpr ⟨(hst x hxh).mp hxS,
      (rank_congr_below hst hxh) ▸ hr⟩
  · intro hx
    obtain ⟨hxT, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxT).mp (hr.trans_lt (hn ▸ hi))
    exact Finset.mem_filter.mpr ⟨(hst x hxh).mpr hxT,
      (rank_congr_below hst hxh).symm ▸ hr⟩

theorem level_reaches (S : Finset ExtOrd) {C h : ExtOrd} (hh : h ≤ C) :
    h ≤ level S C (next S h) := by
  classical
  by_cases hc : S.card < next S h
  · rw [level, ite_eq_left hc]
    exact hh
  · have hn : (S.filter (h ≤ ·)).Nonempty := by
      by_contra hn
      have he : S.filter (· < h) = S := by
        apply Finset.filter_eq_self.mpr
        intro x hx
        by_contra hnx
        exact hn ⟨x, Finset.mem_filter.mpr ⟨hx, not_lt.mp hnx⟩⟩
      apply hc
      simp only [next, he]
      omega
    let x := (S.filter (h ≤ ·)).min' hn
    have hxm := Finset.min'_mem (S.filter (h ≤ ·)) hn
    have hxS : x ∈ S := (Finset.mem_filter.mp hxm).1
    have hxh : h ≤ x := (Finset.mem_filter.mp hxm).2
    have he : S.filter (· ≤ x) = insert x (S.filter (· < h)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyS, hyx⟩ := Finset.mem_filter.mp hy
        by_cases hyh : y < h
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyS, hyh⟩)
        · exact Finset.mem_insert.mpr (Or.inl (le_antisymm hyx
            (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyS, not_lt.mp hyh⟩))))
      · intro hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_filter.mpr ⟨hxS, le_rfl⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
            (Finset.mem_filter.mp hy).2.le.trans hxh⟩
    have hr : rank S x = next S h := by
      rw [rank, he, Finset.card_insert_of_notMem]
      · rfl
      · intro hx
        exact (not_lt_of_ge hxh) (Finset.mem_filter.mp hx).2
    rw [← hr, level_rank hxS]
    exact hxh

variable {X : Type*} [Fintype X]

open Classical in
def values (p : X → ExtOrd) : Finset ExtOrd := (Finset.univ.image p).erase ⊥

theorem mem_values {p : X → ExtOrd} {x : ExtOrd} :
    x ∈ values p ↔ x ≠ ⊥ ∧ ∃ d, p d = x := by
  classical
  simp only [values, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]

theorem bot_not_values (p : X → ExtOrd) : ⊥ ∉ values p := by
  rw [mem_values]
  simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  classical
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    ((Finset.card_image_le).trans_eq (Finset.card_univ))

def fieldRank (p : X → ExtOrd) (d : X) : ℕ := rank (values p) (p d)

theorem fieldRank_le (p : X → ExtOrd) (d : X) : fieldRank p d ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le p)

theorem field_readback (p : X → ExtOrd) (C : ExtOrd) (d : X) :
    level (values p) C (fieldRank p d) = p d := by
  by_cases hz : p d = ⊥
  · simp only [fieldRank, hz, rank_bot (bot_not_values p), level_zero]
  · exact level_rank (mem_values.mpr ⟨hz, d, rfl⟩) C

theorem values_bound {p : X → ExtOrd} {C : ExtOrd} (hC : ∀ d, p d ≤ C) :
    ∀ x ∈ values p, x ≤ C := by
  intro x hx
  obtain ⟨_, d, rfl⟩ := mem_values.mp hx
  exact hC d

theorem level_visible {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (i : ℕ) : SelfVis 1 (level (values p) C i) := by
  rcases level_supported (values p) C i with hz | hv | hc
  · rw [hz]; exact selfVis_bot 1
  · obtain ⟨_, d, hd⟩ := mem_values.mp hv
    rw [← hd]; exact hp d
  · rw [hc]; exact hC

private theorem eq_of_capped_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by
  rw [min_eq_left hx.le] at he
  by_cases hy : y ≤ h
  · simpa only [min_eq_left hy] using he
  · rw [min_eq_right (not_le.mp hy).le] at he
    exact (ne_of_lt hx he).elim

theorem values_agree_below {p q : X → ExtOrd} {h : ExtOrd}
    (hag : ∀ d, min (p d) h = min (q d) h) :
    ∀ x, x < h → (x ∈ values p ↔ x ∈ values q) := by
  intro x hx
  rw [mem_values, mem_values]
  constructor
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, d, ?_⟩
    exact (eq_of_capped_lt (hag d) (hd ▸ hx)).symm.trans hd
  · rintro ⟨hz, d, hd⟩
    refine ⟨hz, d, ?_⟩
    exact (eq_of_capped_lt (hag d).symm (hd ▸ hx)).symm.trans hd

/-- Capped scalar agreement constructs the common rank prefix. -/
theorem fieldRank_agreement {p q : X → ExtOrd} {h : ExtOrd} (hh : ⊥ < h)
    (hag : ∀ d, min (p d) h = min (q d) h) :
    FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) (next (values p) h) := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  intro d
  by_cases hd : p d < h
  · have he := eq_of_capped_lt (hag d) hd
    exact congrArg (fun n => min n (next (values p) h))
      ((rank_congr_below hs hd).trans (congrArg (rank (values q)) he))
  · have hph : h ≤ p d := not_lt.mp hd
    have hqh : h ≤ q d := by
      have he := hag d
      rw [min_eq_right hph] at he
      exact he.le.trans (min_le_left _ _)
    have hpv : p d ∈ values p := mem_values.mpr ⟨ne_of_gt (hh.trans_le hph), d, rfl⟩
    have hqv : q d ∈ values q := mem_values.mpr ⟨ne_of_gt (hh.trans_le hqh), d, rfl⟩
    have hpr : next (values p) h ≤ fieldRank p d :=
      not_lt.mp (fun hr => hd ((rank_lt_next hpv).mp hr))
    have hqr : next (values p) h ≤ fieldRank q d := by
      rw [hn]
      exact not_lt.mp (fun hr => (not_lt_of_ge hqh) ((rank_lt_next hqv).mp hr))
    rw [min_eq_right hpr, min_eq_right hqr]

/-- Both ladders reach the cap at a constructed common rank and agree
literally at all preceding rungs. No rank-cut hypothesis is supplied. -/
theorem common_rank_cut {p q : X → ExtOrd} {C h : ExtOrd}
    (hh : ⊥ < h) (hC : h ≤ C) (hag : ∀ d, min (p d) h = min (q d) h) :
    ∃ k, 0 < k ∧ k ≤ Fintype.card X + 1 ∧
      FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) k ∧
      h ≤ level (values p) C k ∧ h ≤ level (values q) C k ∧
      ∀ i, i < k → level (values p) C i = level (values q) C i := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  refine ⟨next (values p) h, by unfold next; omega,
    (next_le _ _).trans (Nat.add_le_add_right (values_card_le p) 1),
    fieldRank_agreement hh hag, level_reaches _ hC, ?_, ?_⟩
  · rw [hn]
    exact level_reaches _ hC
  · exact fun _ hi => level_agree_below hs hi

variable {L : ℕ} {Q : Type*} [Finite Q] (profile : Q → X → ℕ)

/-- A selected table section. The anchor's ranks will be identified with
the ranks of the scalar input in the readback and prefix theorems. -/
def render (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    SupportLadderRows.Point L X Q → ExtOrd :=
  SupportLadderRows.image profile a (level (values p) C)

theorem render_lawful (a : Q) {p : X → ExtOrd} {C : ExtOrd}
    (hp : ∀ d, SelfVis 1 (p d)) (hvis : SelfVis 1 C) (hC : ∀ d, p d ≤ C) :
    SupportLadderRows.Lawful profile (render (L := L) profile a p C) := by
  have hb := values_bound hC
  by_cases hz : C = ⊥
  · have he : render (L := L) profile a p C = fun _ => ⊥ := by
      funext v
      exact le_bot_iff.mp ((level_le hb _).trans_eq hz)
    rw [he]
    exact ⟨fun _ => selfVis_bot _, fun _ => by
      simp only [min_self]
      exact TransformsTo.to_bot _⟩
  · exact SupportLadderRows.image_lawful a _ (level_mono hb) (level_zero _ _)
      (level_visible hp hvis) (fun _ hi _ => level_pos (bot_not_values p) hb hz hi)

omit [Finite Q] in
/-- Scalar prefixes determine every physical rung and shadow cap, even
when the profiles reorder or split ties above the cap. -/
theorem render_cap_agreement {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hL : Fintype.card X + 1 ≤ L)
    (ha : ∀ d, profile a d = fieldRank p d) (hb : ∀ d, profile b d = fieldRank q d)
    (hp : ∀ d, p d ≤ C) (hq : ∀ d, q d ≤ C) (hC : h ≤ C)
    (hag : ∀ d, min (p d) h = min (q d) h) (v : SupportLadderRows.Point L X Q) :
    min (render profile a p C v) h = min (render profile b q C v) h := by
  by_cases hz : h = ⊥
  · simp only [hz, min_eq_right bot_le]
  · obtain ⟨k, _, hk, hr, hkp, hkq, he⟩ := common_rank_cut (bot_lt_iff_ne_bot.mpr hz) hC hag
    have hcut : k ≤ FiniteProfileControllers.cut L (profile a) (profile b) := by
      apply FiniteProfileControllers.le_cut (hk.trans hL)
      intro d
      rw [ha d, hb d]
      exact hr d
    exact SupportLadderRows.cap_agreement a b hcut (level (values p) C) (level (values q) C)
      (level_mono (values_bound hp)) (level_mono (values_bound hq)) hkp hkq
      (fun i hi => congrArg (fun x => min x h) (he i hi)) v

end
end VaughtConjecture.Knight.LadderScalarRendering
