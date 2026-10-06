/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotControllerFamily

/-! # Joint controllers for different finite source profiles

Profiles may order the old occurrences differently. Their cross-reading is
the largest natural cut through which they agree literally. Its ultrametric
identity supplies all new/new localities, with separated grade-one source
codes and explicit witnesses. No common old order or transformation
composition is used. Scope geometry and extension supply are separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.FiniteProfileControllers

open Transform Value ExtOrd SlotControllerFamily

variable {X Q : Type*}

def Agree (a b : X → ℕ) (k : ℕ) : Prop := ∀ d, min (a d) k = min (b d) k

theorem Agree.mono {a b : X → ℕ} {k l : ℕ} (h : Agree a b k) (hl : l ≤ k) : Agree a b l := by
  intro d
  have hh := congrArg (fun z => min z l) (h d)
  simpa only [min_assoc, min_eq_right hl] using hh

open Classical in
noncomputable def cut (H : ℕ) (a b : X → ℕ) : ℕ :=
  ((Finset.range (H + 1)).filter (Agree a b)).sup id

theorem cut_le (H : ℕ) (a b : X → ℕ) : cut H a b ≤ H := by
  classical
  apply Finset.sup_le
  intro k hk
  have hh := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  exact Nat.le_of_lt_succ hh

theorem le_cut {H k : ℕ} {a b : X → ℕ} (hk : k ≤ H) (h : Agree a b k) : k ≤ cut H a b := by
  classical
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), h⟩)

theorem agree_cut (H : ℕ) (a b : X → ℕ) : Agree a b (cut H a b) := by
  classical
  have hn : ((Finset.range (H + 1)).filter (Agree a b)).Nonempty :=
    ⟨0, by simp [Agree]⟩
  obtain ⟨k, hk, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  have ha := (Finset.mem_filter.mp hk).2
  change k = cut H a b at he
  exact he ▸ ha

theorem cut_symm (H : ℕ) (a b : X → ℕ) : cut H a b = cut H b a := by
  apply le_antisymm
  · exact le_cut (cut_le H a b) (fun d => (agree_cut H a b d).symm)
  · exact le_cut (cut_le H b a) (fun d => (agree_cut H b a d).symm)

theorem cut_refl (H : ℕ) (a : X → ℕ) : cut H a a = H :=
  le_antisymm (cut_le H a a) (le_cut le_rfl (fun _ => rfl))

theorem cut_triangle (H : ℕ) (a b c : X → ℕ) :
    min (cut H a b) (cut H b c) ≤ cut H a c := by
  apply le_cut ((min_le_left _ _).trans (cut_le H a b))
  intro d
  exact ((agree_cut H a b).mono (min_le_left _ _) d).trans
    ((agree_cut H b c).mono (min_le_right _ _) d)

/-- The exact clipped cross-reading identity, not only a triangle inequality. -/
theorem cross_agreement (H : ℕ) (a b c : X → ℕ) :
    min (cut H a c) (cut H a b) = min (cut H b c) (cut H a b) := by
  have h1 := cut_triangle H a b c
  have h2 := cut_triangle H b a c
  rw [cut_symm H b a] at h2
  omega

noncomputable def index (H : ℕ) (profile : Q → X → ℕ) (q : Q) : X ⊕ Q → ℕ
  | .inl d => profile q d
  | .inr p => cut H (profile q) (profile p)

theorem diagonal (H : ℕ) (profile : Q → X → ℕ) (q : Q) :
    index H profile q (.inr q) = H := cut_refl H _

theorem index_bound {H : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (q : Q) (d : X ⊕ Q) : index H profile q d ≤ H := by
  cases d with
  | inl d => exact hb q d
  | inr p => exact cut_le H _ _

/-- Every occurrence agrees below the actual cross-reading, including all
controller occurrences. This is independent of any shared old source order. -/
theorem index_agreement (H : ℕ) (profile : Q → X → ℕ) (p q : Q) (d : X ⊕ Q) :
    min (index H profile q d) (cut H (profile q) (profile p)) =
      min (index H profile p d) (cut H (profile q) (profile p)) := by
  cases d with
  | inl d => exact agree_cut H (profile q) (profile p) d
  | inr r => exact cross_agreement H (profile q) (profile p) (profile r)

noncomputable def row (H : ℕ) (profile : Q → X → ℕ) (q : Q) (d : X ⊕ Q) : ExtOrd :=
  value (index H profile q d)

def Joint (H : ℕ) (profile : Q → X → ℕ) (p : X ⊕ Q → ExtOrd) : Prop :=
  (∀ d, SelfVis 1 (p d)) ∧
  (∀ q, TransformsTo (fun _ : X ⊕ Q => 1) (row H profile q)
    (fun d => min (p d) (p (.inr q)))) ∧
  ∀ d, ∃ q, p d ≤ p (.inr q)

variable [Finite X] [Finite Q]

/-- Each monotone visible target of any one profile has every controller
locality at its actual cap, with one direct interpolation per controller. -/
theorem label_joint {H : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (q : Q) (f : ℕ → ExtOrd)
    (hm : Monotone f) (h0 : f 0 = ⊥) (hv : ∀ k, SelfVis 1 (f k)) :
    Joint H profile (fun d => f (index H profile q d)) := by
  refine ⟨fun d => hv _, ?_, ?_⟩
  · intro p
    apply transforms_of_table
    · intro d
      exact selfVis_min (hv _) (hv _)
    · intro d hd
      have hh := index_agreement H profile p q d
      rw [hd, Nat.zero_min] at hh
      rw [← hm.map_min]
      exact hh ▸ h0
    · intro d e hde
      rw [← hm.map_min, ← hm.map_min]
      apply hm
      change min (index H profile q d) (cut H (profile q) (profile p)) ≤
        min (index H profile q e) (cut H (profile q) (profile p))
      rw [index_agreement H profile p q d, index_agreement H profile p q e]
      exact min_le_min_right _ hde
  · intro d
    refine ⟨q, ?_⟩
    change f (index H profile q d) ≤ f (index H profile q (.inr q))
    rw [diagonal]
    exact hm (index_bound hb q d)

/-- The whole new-controller family is jointly consistent, even when its
old profiles have different ties, bottom patterns, or orders. -/
theorem rows_joint {H : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (q : Q) : Joint H profile (row H profile q) :=
  label_joint hb q value value_mono rfl value_visible

omit [Finite X] [Finite Q] in
theorem rows_coded (H : ℕ) (profile : Q → X → ℕ) (q : Q) (d : X ⊕ Q) :
    IsCodedLabel 1 (row H profile q d) := value_coded _

/-- An actual faithful target of a profile extends to a whole joint section.
The old occurrences are retained literally; there is no new witness search. -/
theorem section_of_transform {H : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (q : Q) {p : X → ExtOrd}
    (hp : TransformsTo (fun _ : X => 1) (fun d => value (profile q d)) p) :
    ∃ r : X ⊕ Q → ExtOrd, Joint H profile r ∧ ∀ d, r (.inl d) = p d := by
  obtain ⟨f, hm, h0, hv, he⟩ := table_of_transform hp
  exact ⟨fun d => f (index H profile q d), label_joint hb q f hm h0 hv, he⟩

omit [Finite X] in
/-- An arbitrary lawful ambient is a monotone target of one actual controller.
This is derived from finite availability, not imposed on the ambient. -/
theorem Joint.exists_shape [Nonempty Q] {H : ℕ} {profile : Q → X → ℕ}
    {p : X ⊕ Q → ExtOrd} (hp : Joint H profile p) :
    ∃ q f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
      ∀ d, p d = f (index H profile q d) := by
  obtain ⟨q, hq⟩ := Finite.exists_max (fun q : Q => p (.inr q))
  have hd : ∀ d, p d ≤ p (.inr q) := by
    intro d
    obtain ⟨r, hr⟩ := hp.2.2 d
    exact hr.trans (hq r)
  have ht := hp.2.1 q
  have he : (fun d => min (p d) (p (.inr q))) = p :=
    funext (fun d => min_eq_left (hd d))
  rw [he] at ht
  obtain ⟨f, hm, h0, hv, hf⟩ := table_of_transform ht
  exact ⟨q, f, hm, h0, hv, fun d => (hf d).symm⟩

/-- Exact normal form for the whole row layer. The converse retains every
controller, so it is stronger than merely covering the old occurrences. -/
theorem joint_iff_shape [Nonempty Q] {H : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (p : X ⊕ Q → ExtOrd) :
    Joint H profile p ↔
      ∃ q f, Monotone f ∧ f 0 = ⊥ ∧ (∀ i, SelfVis 1 (f i)) ∧
        ∀ d, p d = f (index H profile q d) := by
  refine ⟨Joint.exists_shape, ?_⟩
  rintro ⟨q, f, hm, h0, hv, he⟩
  have hh : p = fun d => f (index H profile q d) := funext he
  rw [hh]
  exact label_joint hb q f hm h0 hv

omit [Finite X] [Finite Q] in
/-- A sufficient source-cut replacement test, preserving the ambient cap at
every occurrence, including every auxiliary controller. Neither the cut nor
the replacement profile is assumed to exist in a lifting problem. -/
theorem cap_agreement_of_cut {H a : ℕ} {profile : Q → X → ℕ} (p q : Q)
    (ha : a ≤ cut H (profile p) (profile q)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγ : γ ≤ f a) (hfg : ∀ k, k ≤ a → f k = g k) (d : X ⊕ Q) :
    min (f (index H profile p d)) γ = min (g (index H profile q d)) γ := by
  have hs := index_agreement H profile q p d
  have he := congrArg (fun z => min z a) hs
  simp only [min_assoc, min_eq_right ha] at he
  by_cases hp : index H profile p d < a
  · have hq : index H profile q d = index H profile p d := by omega
    rw [hq, hfg _ hp.le]
  · have hpa : a ≤ index H profile p d := Nat.le_of_not_gt hp
    have hqa : a ≤ index H profile q d := by omega
    rw [min_eq_right (hγ.trans (hf hpa)),
      min_eq_right ((hγ.trans_eq (hfg a le_rfl)).trans (hg hqa))]

omit [Finite X] [Finite Q] in
/-- The maps may differ at the cut itself: both cut images need only reach
the external cap. This permits a prescribed value equal to the cap even when
the old map sends the cut strictly above it. -/
theorem cap_agreement_of_open_cut {H a : ℕ} {profile : Q → X → ℕ} (p q : Q)
    (ha : a ≤ cut H (profile p) (profile q)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) {γ : ExtOrd}
    (hγf : γ ≤ f a) (hγg : γ ≤ g a) (hfg : ∀ k, k < a → f k = g k)
    (d : X ⊕ Q) :
    min (f (index H profile p d)) γ = min (g (index H profile q d)) γ := by
  have hs := index_agreement H profile q p d
  have he := congrArg (fun z => min z a) hs
  simp only [min_assoc, min_eq_right ha] at he
  by_cases hp : index H profile p d < a
  · have hq : index H profile q d = index H profile p d := by omega
    rw [hq, hfg _ hp]
  · have hpa : a ≤ index H profile p d := Nat.le_of_not_gt hp
    have hqa : a ≤ index H profile q d := by omega
    rw [min_eq_right (hγf.trans (hf hpa)), min_eq_right (hγg.trans (hg hqa))]

/-- Once the source-cut replacement data are supplied, the entire new
labelling is constructed, including all faithful localities and controller
caps. No new-controller respect premise is required. -/
theorem replace_at_cut {H a : ℕ} {profile : Q → X → ℕ}
    (hb : ∀ q d, profile q d ≤ H) (p q : Q)
    (ha : a ≤ cut H (profile p) (profile q)) (f g : ℕ → ExtOrd)
    (hf : Monotone f) (hg : Monotone g) (h0 : g 0 = ⊥)
    (hv : ∀ k, SelfVis 1 (g k)) {γ : ExtOrd}
    (hγf : γ ≤ f a) (hγg : γ ≤ g a) (hfg : ∀ k, k < a → f k = g k) :
    Joint H profile (fun d => g (index H profile q d)) ∧
      ∀ d, min (g (index H profile q d)) γ = min (f (index H profile p d)) γ :=
  ⟨label_joint hb q g hg h0 hv,
    fun d => (cap_agreement_of_open_cut p q ha f g hf hg hγf hγg hfg d).symm⟩

end VaughtConjecture.Knight.FiniteProfileControllers
