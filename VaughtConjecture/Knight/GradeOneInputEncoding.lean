/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.GradeOneBottomLift

/-! # Finite ordered encoding of grade-one inputs

A finite inventory of self-visible grade-one values, including arbitrary
ordinals and literal top, can be encoded by bottom and bounded positive natural
ordinals. Explicit monotone, bottom-reflecting maps encode and decode the
inventory exactly. They commute with visibility replacement up to grade one.

Both maps preserve actual respect on grade-one lower domains, with rows fixed.
This uses source-block witness repair, not transitivity of faithful transforms.
The inverse is required only on the input inventory, not on all possible
outputs. That is enough to preserve lift existence in both directions.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-- A finite ordinal alphabet. Ordinal zero is omitted: it is not self-visible
at grade one. Bottom is different from ordinal zero. -/
def InAlphabet (N : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ x = ofOrd n

theorem InAlphabet.visible {N : ℕ} {x : ExtOrd} (h : InAlphabet N x) : SelfVis 1 x := by
  rcases h with rfl | ⟨n, hn, _, rfl⟩
  · exact selfVis_bot 1
  · rwa [selfVis_ofOrd_iff, finitePart_natCast]

theorem InAlphabet.mono {N M : ℕ} {x : ExtOrd} (h : InAlphabet N x) (hNM : N ≤ M) :
    InAlphabet M x := by
  rcases h with h | ⟨n, hn, hN, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨n, hn, hN.trans hNM, he⟩

/-- An interpolation between tables with matching bottom flags reflects bottom
on its entire domain, not just at the represented source values. -/
theorem orderInterpolate_bottom_iff {Y : Type*} [Fintype Y] {E r : Y → ExtOrd}
    (hbot : ∀ i, r i = ⊥ → E i = ⊥) (x : ExtOrd) :
    orderInterpolate E r x = ⊥ ↔ x = ⊥ := by
  classical
  constructor
  · intro h
    by_contra hx
    have hn : Finset.univ.inf (fun i => if x ≤ E i then r i else ⊤) ≠ (⊥ : ExtOrd) := by
      apply Finset.inf_induction (p := fun v : ExtOrd => v ≠ ⊥) top_ne_bot
        (fun _ ha _ hb => bot_lt_iff_ne_bot.mp
          (lt_min (bot_lt_iff_ne_bot.mpr ha) (bot_lt_iff_ne_bot.mpr hb)))
      intro i _
      split_ifs with hi
      · intro hz
        exact hx (le_bot_iff.mp ((hbot i hz) ▸ hi))
      · exact top_ne_bot
    exact hn (by simpa only [orderInterpolate, ite_eq_right hx] using h)
  · rintro rfl
    exact orderInterpolate_bot E r

namespace InputEncoding

open Classical in
/-- Positive values get their inventory order index plus one; bottom remains bottom. -/
noncomputable def code (S : Finset ExtOrd) (x : S) : ExtOrd :=
  if x.1 = ⊥ then ⊥ else ofOrd ((((S.orderIsoOfFin rfl).symm x).val + 1 : ℕ) : Ordinal)

theorem code_bot_iff (S : Finset ExtOrd) (x : S) : code S x = ⊥ ↔ x.1 = ⊥ := by
  classical
  by_cases hx : x.1 = ⊥ <;> simp [code, hx]

theorem code_le_iff (S : Finset ExtOrd) (x y : S) : code S x ≤ code S y ↔ x.1 ≤ y.1 := by
  classical
  by_cases hx : x.1 = ⊥
  · simp [code, hx]
  by_cases hy : y.1 = ⊥
  · simp [code, hx, hy]
  simp only [code, ite_eq_right hx, ite_eq_right hy, ofOrd_le_ofOrd,
    Nat.cast_le, Nat.add_le_add_iff_right]
  change (S.orderIsoOfFin rfl).symm x ≤ (S.orderIsoOfFin rfl).symm y ↔ x ≤ y
  exact (S.orderIsoOfFin rfl).symm.le_iff_le

theorem code_alphabet (S : Finset ExtOrd) (x : S) : InAlphabet S.card (code S x) := by
  classical
  by_cases hx : x.1 = ⊥
  · exact Or.inl ((code_bot_iff S x).mpr hx)
  · refine Or.inr ⟨((S.orderIsoOfFin rfl).symm x).val + 1, by omega, ?_, ?_⟩
    · exact Nat.succ_le_of_lt ((S.orderIsoOfFin rfl).symm x).isLt
    · exact ite_eq_right hx

/-- The encoder is defined on all labels, although its bounded alphabet claim
is needed and stated only on the finite input inventory. -/
noncomputable def encode (S : Finset ExtOrd) : ExtOrd → ExtOrd :=
  orderInterpolate (fun x : S => x.1) (code S)

/-- Exact finite inverse, extended monotonically away from the encoded values. -/
noncomputable def decode (S : Finset ExtOrd) : ExtOrd → ExtOrd :=
  orderInterpolate (code S) (fun x : S => x.1)

theorem encode_read (S : Finset ExtOrd) (x : S) : encode S x.1 = code S x :=
  orderInterpolate_read (fun a b h => (code_le_iff S a b).mpr h)
    (fun a h => (code_bot_iff S a).mpr h) x

theorem decode_read (S : Finset ExtOrd) (x : S) : decode S (code S x) = x.1 :=
  orderInterpolate_read (fun a b h => (code_le_iff S a b).mp h)
    (fun a h => (code_bot_iff S a).mp h) x

theorem decode_encode {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) :
    decode S (encode S x) = x := by
  rw [encode_read S ⟨x, hx⟩, decode_read]

theorem encode_alphabet {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) :
    InAlphabet S.card (encode S x) := by
  rw [encode_read S ⟨x, hx⟩]
  exact code_alphabet S ⟨x, hx⟩

theorem encode_bounded {S : Finset ExtOrd} (hS : ∀ x ∈ S, SelfVis 1 x) :
    BoundedMap 1 (encode S) :=
  orderInterpolate_bounded (fun x => hS x.1 x.2) (fun x => (code_alphabet S x).visible)

theorem decode_bounded {S : Finset ExtOrd} (hS : ∀ x ∈ S, SelfVis 1 x) :
    BoundedMap 1 (decode S) :=
  orderInterpolate_bounded (fun x => (code_alphabet S x).visible) (fun x => hS x.1 x.2)

theorem encode_bot_iff (S : Finset ExtOrd) (x : ExtOrd) : encode S x = ⊥ ↔ x = ⊥ :=
  orderInterpolate_bottom_iff (fun a h => (code_bot_iff S a).mp h) x

theorem decode_bot_iff (S : Finset ExtOrd) (x : ExtOrd) : decode S x = ⊥ ↔ x = ⊥ :=
  orderInterpolate_bottom_iff (fun a h => (code_bot_iff S a).mpr h) x

end InputEncoding

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Bottom reflection supplies the exact source-block conditions needed for
transport by a bounded-commuting map. No global faithful outer map is assumed. -/
theorem map_respects_of_bounded_reflecting {K : ℕ} {f : ExtOrd → ExtOrd}
    (hf : BoundedMap K f) (hb : ∀ x, f x = ⊥ ↔ x = ⊥)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {q : D.below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow sem BJ q) :
    RespectsSemanticsBelow sem BJ (fun d => f (q d)) := by
  apply (map_respects_iff_rowBlockBottom hq hK hf).mpr
  exact rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hq) (fun d => hb (q d))

/-- All cap equations and literal protected equations transport under a
monotone scalar map. The external cap is encoded along with the input. -/
theorem map_boundary {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q r : D.below BJ → ExtOrd} {γ : ExtOrd}
    {f : ExtOrd → ExtOrd} (hf : Monotone f) (h : Boundary embed p q γ r) :
    Boundary embed (fun x => f (p x)) (fun d => f (q d)) (f γ) (fun d => f (r d)) := by
  constructor
  · intro d
    rw [← hf.map_min, ← hf.map_min, h.1 d]
  · intro x
    change f (r (embed x)) = f (p x)
    rw [h.2 x]

/-- Exact equivalence, not just counterexample preservation in one direction.
The decoded output need not have belonged to the input inventory. -/
theorem lift_iff_encoded {S : Finset ExtOrd} (hS : ∀ x ∈ S, SelfVis 1 x)
    (hgrade : BJ.2 = 1) {X : Type*} {embed : X → D.below BJ}
    {p : X → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : ∀ x, p x ∈ S) (hq : ∀ d, q d ∈ S) (hγ : γ ∈ S) :
    HasLift (sem := sem) embed p q γ ↔
      HasLift (sem := sem) embed (fun x => InputEncoding.encode S (p x))
        (fun d => InputEncoding.encode S (q d)) (InputEncoding.encode S γ) := by
  have hK : ∀ d : D.below BJ, D.grade d.1 ≤ 1 := fun d => by
    rw [grade_eq_one hgrade d]
  constructor
  · rintro ⟨r, hr, hb⟩
    exact ⟨_, map_respects_of_bounded_reflecting (InputEncoding.encode_bounded hS)
      (InputEncoding.encode_bot_iff S) hK hr,
      map_boundary (InputEncoding.encode_bounded hS).mono hb⟩
  · rintro ⟨r, hr, hb⟩
    refine ⟨fun d => InputEncoding.decode S (r d),
      map_respects_of_bounded_reflecting (InputEncoding.decode_bounded hS)
        (InputEncoding.decode_bot_iff S) hK hr, ?_⟩
    have h := map_boundary (InputEncoding.decode_bounded hS).mono hb
    simpa only [InputEncoding.decode_encode (hp _), InputEncoding.decode_encode (hq _),
      InputEncoding.decode_encode hγ] using h

end VaughtConjecture.Knight.FullRowLifting
