module

public import VaughtConjecture.Knight.TraceBoundary

/-! # The fair paired chain: the single-chain classification consumer

**The consumer kernel of the fair-chain reduction** (review-directed graduation,
2026-08-29): the universal joint supply (`JointTraceSupply`: every traced node and every
scheduled point extends) is replaced, on the consumer side, by ONE monotone chain of
actual paired whole occurrences covering both carriers — and such a chain already yields
the isomorphism of the sources.

* `FairPairedChain` — one ω-sequence of paired covers from the seed, consecutive paired
  steps, eventually covering both carriers; `FairPairedChain.emb` is the composite step
  embedding with tuple-stability (`emb_tuple₁`/`emb_tuple₂`).
* `nonempty_iso_of_fairPairedChain` — the chain yields the source isomorphism from exact
  parent consistency of the two witnesses and the reduct links alone: no modelhood, no
  supply, no menu intersection.  Forth/back are pure bookkeeping — the prescribed point
  is covered by some chain node, and the composite embedding projects any family member
  into a common later node; back is forth of the mirrored chain.
* `fairPairedChain_of_jointTraceSupply` — the adapter preserving the old route: the
  two-sided joint supply constructs a fair paired chain (alternating absorption along one
  surjective enumeration of `M₁ ⊕ M₂`).  Hence the chain hypothesis is FORMALLY WEAKER
  (lower quantifier surface) than the universal boundary: every consumer of
  `nonempty_iso_of_jointTraceSupply` is served through the chain.  (Reverse
  non-implication is NOT proved; "strictly weaker" is deliberately not claimed.)
* `exists_seed_iso_of_fairPairedChain` — the revised equal-code boundary: equal complete
  receipt codes provide a paired seed for which ONE fair paired chain is the sole open
  hypothesis for isomorphism of the sources.  (The RANK-ZERO branch needs no receipt
  data: `exists_empty_pairedSeed` in `Knight/EmptySeedBoundary.lean` (#200) supplies the
  empty paired seed, and `nonempty_iso_of_fairPairedChain` is seed-generic, so the chain
  consumer covers that branch unchanged.)

The open producer theorem on this route: **same-code receipt sources admit one
producer-selected fair paired chain** — a single ω-sequence of jointly chosen paired
events, not universal extension from every abstract paired node (the latter is equivalent
to `MenuIntersectionSupply`, `menuIntersection_iff_jointSupply`).  The terminal ruling in
`Knight/TraceBoundary.lean` is amended accordingly: menu intersection stays the exact
residual of the universal trace-family route, and is no longer the weakest known
classification hypothesis.

No producer machinery graduates with this module (the #57/producer stacks are untouched);
like the trace vocabulary it consumes, this module is deliberately not root-exported. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁} {R₂ : KnightRealization (blockStage 0) M₂}

/-- **The fair paired chain**: one ω-sequence of paired covers, consecutive paired steps,
starting at the seed and eventually covering BOTH carriers.  Formally weaker than
`JointTraceSupply` (lower quantifier surface): nothing is demanded of unreached nodes or
unscheduled extensions. -/
structure FairPairedChain (s : PairedCover hβ₁ hβ₂ W₁ W₂) where
  /-- The chain of paired covers. -/
  node : ℕ → PairedCover hβ₁ hβ₂ W₁ W₂
  /-- The chain starts at the seed. -/
  node_zero : node 0 = s
  /-- Consecutive nodes are joined by paired steps (shared embeddings). -/
  step : ∀ k, PairedStep (node k) (node (k + 1))
  /-- Every left carrier point is eventually covered. -/
  covers_left : ∀ x : M₁, ∃ (k : ℕ) (i : Fin (node k).arity), (node k).tuple₁ i = x
  /-- Every right carrier point is eventually covered. -/
  covers_right : ∀ y : M₂, ∃ (k : ℕ) (i : Fin (node k).arity), (node k).tuple₂ i = y

namespace FairPairedChain

variable {s : PairedCover hβ₁ hβ₂ W₁ W₂}

/-- The composite step embedding of the chain. -/
noncomputable def emb (c : FairPairedChain s) {j k : ℕ} (h : j ≤ k) :
    Fin (c.node j).arity ↪ Fin (c.node k).arity :=
  Nat.leRecOn h (fun {i} e => e.trans (c.step i).emb) (Function.Embedding.refl _)

theorem emb_self (c : FairPairedChain s) {j : ℕ} (h : j ≤ j) :
    c.emb h = Function.Embedding.refl _ :=
  Nat.leRecOn_self _

theorem emb_succ (c : FairPairedChain s) {j k : ℕ} (h1 : j ≤ k) (h2 : j ≤ k + 1) :
    c.emb h2 = (c.emb h1).trans (c.step k).emb :=
  Nat.leRecOn_succ h1 _

/-- Left tuples are stable along the composite embedding. -/
theorem emb_tuple₁ (c : FairPairedChain s) {j : ℕ} :
    ∀ {k : ℕ} (h : j ≤ k) (i : Fin (c.node j).arity),
      (c.node k).tuple₁ (c.emb h i) = (c.node j).tuple₁ i := by
  intro k h
  induction k, h using Nat.le_induction with
  | base => intro i; rw [emb_self]; rfl
  | succ k hk ih =>
    intro i
    rw [c.emb_succ hk, Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun (c.step k).trans₁ (c.emb hk i)).trans (ih i)

/-- Right tuples are stable along the composite embedding. -/
theorem emb_tuple₂ (c : FairPairedChain s) {j : ℕ} :
    ∀ {k : ℕ} (h : j ≤ k) (i : Fin (c.node j).arity),
      (c.node k).tuple₂ (c.emb h i) = (c.node j).tuple₂ i := by
  intro k h
  induction k, h using Nat.le_induction with
  | base => intro i; rw [emb_self]; rfl
  | succ k hk ih =>
    intro i
    rw [c.emb_succ hk, Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun (c.step k).trans₂ (c.emb hk i)).trans (ih i)

/-- The mirrored chain: back is symmetry. -/
def swap (c : FairPairedChain s) : FairPairedChain s.swap where
  node k := (c.node k).swap
  node_zero := by rw [c.node_zero]
  step k := (c.step k).swap
  covers_left := c.covers_right
  covers_right := c.covers_left

/-- **The chain-generated chart family** — the σ-projections of chain nodes: the
membership shape the Karp bridge consumes. -/
def family (c : FairPairedChain s) : Set (Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) :=
  {x | ∃ (k : ℕ) (σ : Fin x.1 → Fin (c.node k).arity),
    (c.node k).tuple₁ ∘ σ = x.2.1 ∧ (c.node k).tuple₂ ∘ σ = x.2.2}

theorem family_empty_mem (c : FairPairedChain s) :
    (⟨0, Fin.elim0, Fin.elim0⟩ : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family :=
  ⟨0, fun i => i.elim0, funext fun i => i.elim0, funext fun i => i.elim0⟩

/-- Every family member carries a common projected chart of the sources. -/
theorem family_commonChart (c : FairPairedChain s)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂) :
    ∀ x ∈ c.family, HasCommonChart R₁ R₂ x.2.1 x.2.2 := by
  rintro x ⟨k, σ, hσ₁, hσ₂⟩
  exact ⟨(c.node k).arity, (c.node k).tuple₁, (c.node k).tuple₂, σ, (c.node k).sourceType,
    (c.node k).source_eval₁ hred₁, (c.node k).source_eval₂ hred₂, hσ₁, hσ₂⟩

theorem family_swap_mem {c : FairPairedChain s}
    {x : Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)} (hx : x ∈ c.family) :
    (⟨x.1, x.2.2, x.2.1⟩ : Σ n : ℕ, (Fin n → M₂) × (Fin n → M₁)) ∈ c.swap.family := by
  obtain ⟨k, σ, hσ₁, hσ₂⟩ := hx
  exact ⟨k, σ, hσ₂, hσ₁⟩

/-- **Forth is pure bookkeeping** — no supply, no modelhood: the prescribed left point is
covered by some chain node; the composite embedding carries the current projection and
the covering index into a common later node. -/
theorem family_forth (c : FairPairedChain s) :
    ∀ x ∈ c.family, ∀ m : M₁, ∃ n' : M₂,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family := by
  rintro ⟨a0, a, b⟩ ⟨k, σ, hσ₁, hσ₂⟩ m
  obtain ⟨k', i, hi⟩ := c.covers_left m
  refine ⟨(c.node (max k k')).tuple₂ (c.emb (le_max_right k k') i), max k k',
    Fin.snoc (fun j => c.emb (le_max_left k k') (σ j)) (c.emb (le_max_right k k') i),
    funext fun j => ?_, funext fun j => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
      exact (c.emb_tuple₁ (le_max_right k k') i).trans hi
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.emb_tuple₁ (le_max_left k k') (σ j)).trans (congrFun hσ₁ j)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Function.comp_apply, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      exact (c.emb_tuple₂ (le_max_left k k') (σ j)).trans (congrFun hσ₂ j)

/-- Back is forth of the mirrored chain. -/
theorem family_back (c : FairPairedChain s) :
    ∀ x ∈ c.family, ∀ n' : M₂, ∃ m : M₁,
      (⟨x.1 + 1, Fin.snoc x.2.1 m, Fin.snoc x.2.2 n'⟩ :
        Σ n : ℕ, (Fin n → M₁) × (Fin n → M₂)) ∈ c.family := by
  intro x hx n'
  obtain ⟨m, hm⟩ := c.swap.family_forth _ (family_swap_mem hx) n'
  exact ⟨m, family_swap_mem hm⟩

end FairPairedChain

/-- **The single-chain consumer**: one fair paired chain from the seed yields the
isomorphism of the sources — no supply, no modelhood, no menu intersection; exact parent
consistency of the witnesses and the reduct links suffice. -/
theorem nonempty_iso_of_fairPairedChain [Countable M₁] [Countable M₂]
    (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent)
    (hred₁ : W₁.reduct hβ₁ = R₁) (hred₂ : W₂.reduct hβ₂ = R₂)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂} (c : FairPairedChain s) :
    Nonempty (R₁.Iso R₂) := by
  have hR₁c : R₁.IsExactParentConsistent := hred₁ ▸ hW₁c.reduct hβ₁
  have hR₂c : R₂.IsExactParentConsistent := hred₂ ▸ hW₂c.reduct hβ₂
  exact nonempty_iso_of_commonCharts hR₁c hR₂c c.family (c.family_empty_mem)
    (c.family_commonChart hred₁ hred₂) c.family_forth c.family_back

/-! ### Certification: the chain hypothesis strictly weakens the current boundary -/

open Classical in
/-- **The adapter from the universal boundary**: the two-sided joint supply constructs a
fair paired chain — alternate absorption along one surjective enumeration of `M₁ ⊕ M₂`,
rebuilding the trace step by step.  Hence the chain hypothesis is formally weaker (lower
quantifier surface): every consumer of the universal boundary is served through the
chain, and the open producer theorem shrinks to: same-code sources admit ONE
producer-selected fair paired chain. -/
theorem fairPairedChain_of_jointTraceSupply [Countable M₁] [Countable M₂]
    [Nonempty M₁] [Nonempty M₂]
    (hW₁c : W₁.IsExactParentConsistent) (hW₂c : W₂.IsExactParentConsistent)
    {s : PairedCover hβ₁ hβ₂ W₁ W₂}
    (hf : JointTraceSupply s) (hb : JointTraceSupply s.swap) :
    Nonempty (FairPairedChain s) := by
  obtain ⟨e, he⟩ := exists_surjective_nat (M₁ ⊕ M₂)
  -- one absorption step, left or right, rebuilding the trace
  have absorb : ∀ (nd : PairedCover hβ₁ hβ₂ W₁ W₂), PairedTrace s nd → ∀ z : M₁ ⊕ M₂,
      ∃ (nd' : PairedCover hβ₁ hβ₂ W₁ W₂) (_ : PairedStep nd nd'),
        Nonempty (PairedTrace s nd') ∧
        (∀ x : M₁, z = Sum.inl x → ∃ i, nd'.tuple₁ i = x) ∧
        (∀ y : M₂, z = Sum.inr y → ∃ i, nd'.tuple₂ i = y) := by
    intro nd tr z
    match z with
    | Sum.inl x =>
      obtain ⟨nd', st, hi, -⟩ := pairedTrace_absorb_of_jointSupply hW₁c hW₂c hf tr x
      refine ⟨nd', st, ⟨tr.step st⟩, ?_, ?_⟩
      · intro x' hx'
        obtain rfl : x = x' := Sum.inl.inj hx'
        exact hi
      · intro y hy
        exact absurd hy Sum.inl_ne_inr
    | Sum.inr y =>
      obtain ⟨nd'', st'', hi, -⟩ :=
        pairedTrace_absorb_of_jointSupply hW₂c hW₁c hb tr.swap y
      refine ⟨nd''.swap, st''.swap, ⟨tr.step st''.swap⟩, ?_, ?_⟩
      · intro x hx
        exact absurd hx.symm Sum.inl_ne_inr
      · intro y' hy'
        obtain rfl : y = y' := Sum.inr.inj hy'
        exact hi
  -- the chain state: node with its trace
  let state : ℕ → Σ' (nd : PairedCover hβ₁ hβ₂ W₁ W₂), Nonempty (PairedTrace s nd) :=
    Nat.rec ⟨s, ⟨.refl⟩⟩ (fun k prev =>
      ⟨(absorb prev.1 prev.2.some (e k)).choose,
        (absorb prev.1 prev.2.some (e k)).choose_spec.choose_spec.1⟩)
  have hstep : ∀ k, ∃ (_ : PairedStep (state k).1 (state (k + 1)).1),
      (∀ x : M₁, e k = Sum.inl x → ∃ i, (state (k + 1)).1.tuple₁ i = x) ∧
      (∀ y : M₂, e k = Sum.inr y → ∃ i, (state (k + 1)).1.tuple₂ i = y) := by
    intro k
    have h := (absorb (state k).1 (state k).2.some (e k)).choose_spec
    exact ⟨h.choose, h.choose_spec.2.1, h.choose_spec.2.2⟩
  refine ⟨{
    node := fun k => (state k).1
    node_zero := rfl
    step := fun k => (hstep k).choose
    covers_left := fun x => ?_
    covers_right := fun y => ?_ }⟩
  · obtain ⟨k, hk⟩ := he (Sum.inl x)
    obtain ⟨i, hi⟩ := (hstep k).choose_spec.1 x hk
    exact ⟨k + 1, i, hi⟩
  · obtain ⟨k, hk⟩ := he (Sum.inr y)
    obtain ⟨i, hi⟩ := (hstep k).choose_spec.2 y hk
    exact ⟨k + 1, i, hi⟩

end KnightRealization
end VaughtConjecture.Knight
