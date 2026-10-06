/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveSourceCarrier
public import VaughtConjecture.Knight.CanonicalPairBoundary

/-! # Canonical catalogues on a genuinely recursive occurrence inventory

The first two catalogues are exactly the checked seed pair. Higher catalogues
use the entire original field inventory, including future proper-boundary
fields. Lawfulness is checked on the grade actually present.
No completed output is passed back as a proper boundary. Row coupling and
successor bountifulness remain separate from this constructed geometry.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveInventory
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

abbrev UpperProfile (j : ℕ) := CanonicalFieldLayer.Profile (GradeCutBoundary.rows D j sem)
  j (Cell D) (GradeCutBoundary.toCell D j)

def Profile : ℕ → Type 1
  | 0 => PUnit
  | 1 => CanonicalPairBoundary.firstProfiles sem 1 2
  | 2 => CanonicalPairBoundary.secondProfiles sem 2
  | n + 3 => UpperProfile sem (n + 3)

instance (j : ℕ) : Fintype (Profile sem j) := by
  rcases j with _ | _ | _ | j <;> dsimp only [Profile] <;> infer_instance

abbrev scheme (n : ℕ) (hn : n ≤ A.card) := RecursiveSourceCarrier.scheme D (Profile sem) n hn
abbrev boundary (n : ℕ) (hn : n ≤ A.card) :=
  RecursiveSourceCarrier.boundary D (Profile sem) n hn
abbrev step (n : ℕ) (hn : n + 1 ≤ A.card) :=
  RecursiveSourceCarrier.step D (Profile sem) n hn

/-- The recursion starts with the actual checked pair, without enlarging or
renormalizing its two controller inventories. -/
theorem seed_pair (hA : 2 ≤ A.card) :
    scheme sem 2 hA = CanonicalPairBoundary.scheme sem 1 2 (by decide)
      ((by decide : 1 ≤ 2).trans hA) (by decide) hA := rfl

theorem boundary_cell (n : ℕ) (hn : n ≤ A.card) (d : Cell D) :
    (scheme sem n hn).cell (boundary sem n hn d) = D.cell d :=
  RecursiveSourceCarrier.boundary_cell D (Profile sem) n hn d

theorem step_cell (n : ℕ) (hn : n + 1 ≤ A.card)
    (d : Cell (scheme sem n (Nat.le_of_succ_le hn))) :
    (scheme sem (n + 1) hn).cell (step sem n hn d) =
      (scheme sem n (Nat.le_of_succ_le hn)).cell d :=
  RecursiveSourceCarrier.step_cell D (Profile sem) n hn d

/-- Normalize from the actual current old lower domain; future fields are
retained in the vector but are not required to be lawful at absent owners. -/
def encode (n : ℕ) {p : Cell D → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤) :
    Profile sem (n + 3) := by
  let j := n + 3
  have hr := GradeCutBoundary.pullback_respects D j sem le_rfl hp
  apply CanonicalFieldLayer.encode (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) (GradeCutBoundary.grade_bound D j) _ ht
  exact hr.toRespects (fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D j d⟩)

theorem encode_val (n : ℕ) {p : Cell D → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤) :
    (encode sem n hp ht).val = normalize (n + 3) p := rfl

theorem decoded_fields (n : ℕ) {p : Cell D → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {C : ExtOrd} (hG : ∀ z ∈ G, SelfVis (n + 3) z)
    (hC : SelfVis (n + 3) C)
    (d : Cell D) :
    PairedSlotDecoder.decode (n + 3) (values p) G C ((encode sem n hp ht).val d) = p d :=
  PairedSlotDecoder.decode_normalize hG hC ht d

theorem separated (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme sem n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme sem n hn).cell d) :=
  RecursiveSourceCarrier.separated D (Profile sem) hp n hn d

/-- The recursive grade-four inventory contains every grade-three controller
unchanged, rather than appending grade four directly to a grade-one/two pair. -/
theorem grade_three_retained_at_four (hA : 4 ≤ A.card) (q : Profile sem 3) :
    (scheme sem 4 hA).cell (RecursiveSourceCarrier.retained D (Profile sem) 2 1 hA q) =
      (A, 3) :=
  RecursiveSourceCarrier.retained_cell D (Profile sem) 2 1 hA q

theorem proper_four_retained (hA : 4 ≤ A.card) (d : Cell D) (hd : D.grade d = 4) :
    (scheme sem 4 hA).grade (boundary sem 4 hA d) = 4 :=
  (congrArg Prod.snd (boundary_cell sem 4 hA d)).trans hd

theorem all_four_layers (hA : 4 ≤ A.card) (i : Fin 4) (q : Profile sem (i.val + 1)) :
    ∃ c : Cell (scheme sem 4 hA), (scheme sem 4 hA).cell c = (A, i.val + 1) := by
  have hi : i.val + 1 + (3 - i.val) = 4 := by have := i.isLt; omega
  have h := RecursiveSourceCarrier.retained_cell D (Profile sem)
    i.val (3 - i.val) (by omega : i.val + 1 + (3 - i.val) ≤ A.card) q
  have hex : ∃ c : Cell (scheme sem (i.val + 1 + (3 - i.val)) (by omega)),
      (scheme sem (i.val + 1 + (3 - i.val)) (by omega)).cell c = (A, i.val + 1) :=
    ⟨RecursiveSourceCarrier.retained D (Profile sem) i.val (3 - i.val) (by omega) q, h⟩
  have transport (m : ℕ) (hm : m ≤ A.card) (he : m = 4)
      (hx : ∃ c : Cell (scheme sem m hm),
        (scheme sem m hm).cell c = (A, i.val + 1)) :
      ∃ c : Cell (scheme sem 4 hA), (scheme sem 4 hA).cell c = (A, i.val + 1) := by
    subst m
    exact hx
  exact transport _ _ hi hex

end
end VaughtConjecture.Knight.CanonicalRecursiveInventory
