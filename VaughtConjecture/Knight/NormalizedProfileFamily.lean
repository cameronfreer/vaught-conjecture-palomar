/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteProfileRefinement

/-! # Finite normalized profile families with a preserved algebraic contract

`OrderLaw` records the properties of a class of lawful grade-one labellings
used by source refinement. `family` constructs a whole joint controller
family and proves those properties again for its output. These are row-layer
properties, not a support plan, mixed-grade bountifulness, or request forcing.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.NormalizedProfileFamily

open Transform Value ExtOrd SlotControllerFamily
open SlotPatternRefinement (mix)

theorem value_ne_bot {n : ℕ} (hn : 0 < n) : value n ≠ ⊥ := by
  intro h
  have hh := (value_le_iff n 0).mp h.le
  omega

/-- The algebraic input contract for finite source-profile saturation. Its
fields are proved for the constructed output below, not supplied anew. -/
structure OrderLaw (X : Type*) where
  holds : (X → ExtOrd) → Prop
  bottom : holds (fun _ => ⊥)
  visible : ∀ {p}, holds p → ∀ d, SelfVis 1 (p d)
  order : ∀ {p r}, holds p → (∀ d, SelfVis 1 (r d)) →
    (∀ d, p d = ⊥ → r d = ⊥) → (∀ d e, p d ≤ p e → r d ≤ r e) → holds r
  refine : ∀ {q b : X → ℕ} {a : ℕ}, 0 < a →
    holds (fun d => value (q d)) → holds (fun d => value (b d)) →
    (∀ d e, q d < a → a ≤ q e → b d < b e) → holds (fun d => value (mix q b a d))

variable {X : Type*} [Fintype X]

open Classical in
noncomputable def code (p : X → ExtOrd) (d : X) : ℕ :=
  if p d = ⊥ then 0 else FreshSourceSlots.rank p d + 1

theorem code_le (p : X → ExtOrd) (d : X) : code p d ≤ Fintype.card X := by
  classical
  have h := FreshSourceSlots.rank_lt_card p d
  unfold code
  split_ifs <;> omega

theorem code_zero (p : X → ExtOrd) (d : X) : code p d = 0 ↔ p d = ⊥ := by
  classical
  simp [code]

theorem code_order (p : X → ExtOrd) (d e : X) : code p d ≤ code p e ↔ p d ≤ p e := by
  classical
  by_cases hd : p d = ⊥
  · simp [code, hd]
  by_cases he : p e = ⊥
  · simp [code, hd, he]
  simp only [code, hd, he, ↓reduceIte, Nat.add_le_add_iff_right]
  exact FreshSourceSlots.rank_le_iff p d e

theorem value_code_bot (p : X → ExtOrd) (d : X) : value (code p d) = ⊥ ↔ p d = ⊥ := by
  rw [← le_bot_iff, show (⊥ : ExtOrd) = value 0 from rfl, value_le_iff,
    Nat.le_zero, code_zero]
  rfl

theorem rank_encoded (p : X → ExtOrd) (d : X) :
    FreshSourceSlots.rank (fun e => value (code p e)) d = FreshSourceSlots.rank p d := by
  classical
  unfold FreshSourceSlots.rank
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_not_ge,
    value_le_iff, code_order]

theorem code_idempotent (p : X → ExtOrd) (d : X) :
    code (fun e => value (code p e)) d = code p d := by
  classical
  change (if value (code p d) = ⊥ then 0 else
    FreshSourceSlots.rank (fun e => value (code p e)) d + 1) = code p d
  simp only [value_code_bot, rank_encoded]
  rfl

variable (L : OrderLaw X)

theorem encoded_lawful {p : X → ExtOrd} (hp : L.holds p) :
    L.holds (fun d => value (code p d)) := by
  apply L.order hp (fun _ => value_visible _)
  · intro d hd
    rw [(code_zero p d).mpr hd]
    rfl
  · intro d e hde
    exact value_mono ((code_order p d e).mpr hde)

def Profile := {p : X → Fin (Fintype.card X + 1) //
  L.holds (fun d => value (p d).val) ∧ ∀ d, code (fun e => value (p e).val) d = (p d).val}

instance : Finite (Profile L) := by unfold Profile; infer_instance
noncomputable instance : Fintype (Profile L) := Fintype.ofFinite (Profile L)

theorem profile_card_le :
    Fintype.card (Profile L) ≤ (Fintype.card X + 1) ^ Fintype.card X := by
  classical
  have h := Fintype.card_le_of_injective (fun p : Profile L => p.val) Subtype.val_injective
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

def profile (q : Profile L) (d : X) : ℕ := (q.val d).val

theorem profile_bound (q : Profile L) (d : X) : profile L q d ≤ Fintype.card X :=
  Nat.le_of_lt_succ (q.val d).isLt

noncomputable def encode {p : X → ExtOrd} (hp : L.holds p) : Profile L :=
  ⟨fun d => ⟨code p d, Nat.lt_succ_of_le (code_le p d)⟩,
    encoded_lawful L hp, code_idempotent p⟩

instance : Nonempty (Profile L) := ⟨encode L L.bottom⟩

theorem encoding_transforms {p : X → ExtOrd} (hp : L.holds p) :
    TransformsTo (fun _ : X => 1) (fun d => value (profile L (encode L hp) d)) p := by
  apply transforms_of_table
  · exact L.visible hp
  · intro d hd
    exact (code_zero p d).mp hd
  · intro d e hde
    exact (code_order p d e).mp hde

/-- The output satisfies the same order/refinement contract, now on the
enlarged inventory containing every old and new controller occurrence. -/
noncomputable def family : OrderLaw (X ⊕ Profile L) where
  holds := FiniteProfileControllers.Joint (Fintype.card X) (profile L)
  bottom := FiniteProfileControllers.label_joint (profile_bound L) (encode L L.bottom)
    (fun _ => ⊥) (fun _ _ _ => le_rfl) rfl (fun _ => selfVis_bot 1)
  visible hp := hp.1
  order := FiniteProfileRefinement.order_image (profile_bound L)
  refine := FiniteProfileRefinement.joint_mix (profile_bound L)

theorem restriction {p : X ⊕ Profile L → ExtOrd} (hp : (family L).holds p) :
    L.holds (fun d => p (.inl d)) := by
  obtain ⟨q, f, hf, h0, _, he⟩ := hp.exists_shape
  apply L.order q.property.1 (fun d => hp.1 (.inl d))
  · intro d hd
    have hz : profile L q d = 0 :=
      Nat.eq_zero_of_le_zero ((value_le_iff _ 0).mp hd.le)
    rw [he]
    change f (profile L q d) = ⊥
    rw [hz, h0]
  · intro d e hde
    rw [he, he]
    exact hf ((value_le_iff _ _).mp hde)

theorem exists_section {p : X → ExtOrd} (hp : L.holds p) :
    ∃ r, (family L).holds r ∧ ∀ d, r (.inl d) = p d :=
  FiniteProfileControllers.section_of_transform (profile_bound L) (encode L hp)
    (encoding_transforms L hp)

theorem section_iff (p : X → ExtOrd) :
    (∃ r, (family L).holds r ∧ ∀ d, r (.inl d) = p d) ↔ L.holds p := by
  refine ⟨?_, exists_section L⟩
  rintro ⟨r, hr, he⟩
  have h := restriction L hr
  rwa [show (fun d => r (.inl d)) = p from funext he] at h

theorem lower_code (q : Profile L) (s : X → ℕ) (a : ℕ)
    (hl : ∀ d, profile L q d < a → s d = profile L q d)
    (hu : ∀ d, a ≤ profile L q d → a ≤ s d)
    (d : X) (hd : profile L q d < a) :
    code (fun e => value (s e)) d = profile L q d := by
  classical
  have hr : FreshSourceSlots.rank (fun e => value (s e)) d =
      FreshSourceSlots.rank (fun e => value (profile L q e)) d := by
    unfold FreshSourceSlots.rank
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_not_ge, value_le_iff]
    rw [hl d hd]
    by_cases he : profile L q e < a
    · rw [hl e he]
    · have hse := hu e (Nat.le_of_not_gt he)
      omega
  have hz : value (s d) = value (profile L q d) := congrArg value (hl d hd)
  calc
    code (fun e => value (s e)) d = code (fun e => value (profile L q e)) d := by
      simp only [code, hr, hz]
    _ = profile L q d := q.property.2 d

theorem upper_code (q : Profile L) (s : X → ℕ) {a : ℕ} (ha : 0 < a)
    (hl : ∀ d, profile L q d < a → s d = profile L q d)
    (hu : ∀ d, a ≤ profile L q d → a ≤ s d)
    (d : X) (hd : a ≤ profile L q d) : a ≤ code (fun e => value (s e)) d := by
  classical
  let U := Finset.univ.filter (fun e => a ≤ profile L q e)
  have hU : U.Nonempty := ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩
  obtain ⟨e, heU, hemin⟩ := Finset.exists_min_image U (profile L q) hU
  have he : a ≤ profile L q e := (Finset.mem_filter.mp heU).2
  have hset : (Finset.univ.filter (fun j => profile L q j < profile L q e)) =
      Finset.univ.filter (fun j => profile L q j < a) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hn
      have hjU : j ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hn⟩
      have hm := hemin j hjU
      omega
    · intro hj
      omega
  have hrq : FreshSourceSlots.rank (fun j => value (profile L q j)) e =
      (Finset.univ.filter (fun j => profile L q j < a)).card := by
    unfold FreshSourceSlots.rank
    rw [← hset]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [lt_iff_not_ge, value_le_iff, not_le]
  have hn := q.property.2 e
  change code (fun j => value (profile L q j)) e = profile L q e at hn
  simp only [code, value_ne_bot (ha.trans_le he),
    ↓reduceIte, hrq] at hn
  have hcount : (Finset.univ.filter (fun j => profile L q j < a)).card ≤
      FreshSourceSlots.rank (fun j => value (s j)) d := by
    apply Finset.card_le_card
    intro j hj
    have hjl := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [lt_iff_not_ge, value_le_iff, hl j hjl]
    have hsd := hu d hd
    omega
  have hsd := hu d hd
  simp only [code, value_ne_bot (ha.trans_le hsd), ↓reduceIte]
  omega

theorem prefix_agree (q : Profile L) (s : X → ℕ) {a : ℕ} (ha : 0 < a)
    (hl : ∀ d, profile L q d < a → s d = profile L q d)
    (hu : ∀ d, a ≤ profile L q d → a ≤ s d) :
    FiniteProfileControllers.Agree (profile L q) (code (fun d => value (s d))) a := by
  intro d
  by_cases hd : profile L q d < a
  · rw [lower_code L q s a hl hu d hd]
  · have hqd := Nat.le_of_not_gt hd
    rw [min_eq_right hqd, min_eq_right (upper_code L q s ha hl hu d hqd)]

end VaughtConjecture.Knight.NormalizedProfileFamily
