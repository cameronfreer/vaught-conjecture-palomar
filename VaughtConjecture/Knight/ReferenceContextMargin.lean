/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext

/-! # The reference context with the endpoint margin (notes32 §1, audit5 §1)

The construction of `exists_referenceContext` rerun (as `exists_referenceContext_graded` reruns
it) with two additions:

* a **threshold floor** `Nmin < N` (the request arity is below the threshold);
* the **endpoint margin** (1): the final High-Grade Dominance bound also includes every block
  endpoint `μ + N`, so the cap's label lies strictly above `μ + N` for every requested block.

The order of choices is the existing one and is not circular: the representatives are acquired
first, their offsets Skolemized, the threshold `N` chosen above the context arity, every offset
and the floor; only then is the cap requested above the finite maximum of the requested values,
the representative labels and the endpoints `μ + N` — all below the limit stage.  The cap is
positive.  This is exactly the model clause used before, with a larger finite bound. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- The intermediate-context view of a reference context. -/
def ReferenceContext.toCtx {reqs : List BlockRequest} (C : ReferenceContext R t reqs) : Ctx R t :=
  ⟨C.m, C.ctx, C.proj, C.proj_ctx, C.p₀, C.eval_ctx⟩

/-- A property of intermediate contexts preserved by every coface step. -/
def Ctx.StepClosed (Q : Ctx R t → Prop) : Prop :=
  ∀ (C : Ctx R t) (y : M) (hy : y ∉ Set.range C.ctx) (q : S α.1 (C.m + 1))
    (_hq : IsCoface C.p₀ q) (heval : R.eval (snoc C.ctx y hy) = some q),
    Q C → Q (C.step y hy q heval)

/-- `exists_ctx_hasCells`, carrying a step-closed property. -/
theorem exists_ctx_hasCells_pres (hM : R.IsModel) {Q : Ctx R t → Prop} (hQ : Ctx.StepClosed Q)
    (C : Ctx R t) (hC : Q C) (rs : List BlockRequest)
    (hrs : ∀ r ∈ rs, Value.IsNonSuccessor r.block ∧ r.block < α.1) :
    ∃ C' : Ctx R t, C'.HasCells rs ∧ Q C' := by
  induction rs generalizing C with
  | nil => exact ⟨C, fun r hr => by simp at hr, hC⟩
  | cons r rs ih =>
    obtain ⟨C₁, h₁, hQ₁⟩ := ih C hC fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')
    obtain ⟨hns, hlt⟩ := hrs r List.mem_cons_self
    obtain ⟨y, hy, q, ⟨Sig, hlo, hhi⟩, hcof, heval⟩ :=
      hM.uniformity C₁.ctx C₁.p₀ C₁.eval_ctx r.block hns hlt
    obtain ⟨j, hj⟩ := exists_nat_of_band hlo hhi
    refine ⟨C₁.step y hy q heval, fun r' hr' => ?_, hQ C₁ y hy q hcof heval hQ₁⟩
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact ⟨Sig, j, hj⟩
    · exact (h₁.step hcof heval) r' hr'

/-- `exists_ctx_pad`, carrying a step-closed property. -/
theorem exists_ctx_pad_pres (hM : R.IsModel) {Q : Ctx R t → Prop} (hQ : Ctx.StepClosed Q)
    (C : Ctx R t) (hC : Q C) (rs : List BlockRequest) (off : ∀ r, r ∈ rs → ℕ)
    (h : C.HasCellsWith rs off) (k : ℕ) :
    ∃ C' : Ctx R t, C'.m = C.m + k ∧ C'.HasCellsWith rs off ∧ Q C' := by
  induction k with
  | zero => exact ⟨C, rfl, h, hC⟩
  | succ k ih =>
    obtain ⟨C₁, hm, h₁, hQ₁⟩ := ih
    obtain ⟨y, hy, q, -, hcof, heval⟩ :=
      hM.highGradeDominance C₁.ctx C₁.p₀ C₁.eval_ctx 0 stage_pos
    refine ⟨C₁.step y hy q heval, ?_, h₁.step hcof heval, hQ C₁ y hy q hcof heval hQ₁⟩
    change C₁.m + 1 = C.m + (k + 1)
    omega

/-- **The reference context with the endpoint margin, from any intermediate context and carrying
any step-closed property**: the construction of `exists_referenceContext_margin` started at `C₀`
instead of the root, with the property `Q` of `C₀` retained by the final context, and the arity
equation `C.m = C.N` (the context is padded to arity `N - 1` and takes one coface step). -/
theorem exists_referenceContext_margin_from' (hM : R.IsModel) (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) (Nmin : ℕ)
    {Q : Ctx R t → Prop} (hQ : Ctx.StepClosed Q) (C₀ : Ctx R t) (hQ₀ : Q C₀) :
    ∃ C : ReferenceContext R t reqs, Nmin < C.N ∧ ⊥ < C.p₀.label C.capBase ∧
      (∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) ∧ Q C.toCtx ∧ C.m = C.N := by
  classical
  -- representatives, then Skolemize their offsets
  obtain ⟨C₁, h₁, hQ₁⟩ := exists_ctx_hasCells_pres hM hQ C₀ hQ₀ reqs hreqs
  choose cell₁ off hcell₁ using h₁
  have h₁' : C₁.HasCellsWith reqs off := fun r hr => ⟨cell₁ r hr, hcell₁ r hr⟩
  -- the threshold: above the context arity, every offset, and the floor
  let offs : List ℕ := reqs.attach.map fun x => off x.1 x.2
  let N : ℕ := C₁.m + 1 + natMax offs + natMax (reqs.map fun r => r.offset) + Nmin
  have hN_off : ∀ r (hr : r ∈ reqs), off r hr < N := by
    intro r hr
    have : off r hr ≤ natMax offs :=
      le_natMax (List.mem_map.mpr ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩)
    omega
  have hN_req : ∀ r ∈ reqs, r.offset < N := by
    intro r hr
    have : r.offset ≤ natMax (reqs.map fun r => r.offset) :=
      le_natMax (List.mem_map_of_mem hr)
    omega
  have hNmin : Nmin < N := by omega
  -- pad to arity `N - 1`
  obtain ⟨C₂, hm₂, h₂, hQ₂⟩ := exists_ctx_pad_pres hM hQ C₁ hQ₁ reqs off h₁' (N - 1 - C₁.m)
  have hm₂' : C₂.m + 1 = N := by omega
  -- the cap: high-grade dominance above every requested value, every representative label,
  -- and every block endpoint `μ + N`
  let vals : List Ordinal.{0} :=
    (reqs.map fun r => r.value) ++
      (reqs.attach.map fun x => x.1.block + ((off x.1 x.2 : ℕ) : Ordinal.{0})) ++
      (reqs.map fun r => r.block + (N : Ordinal.{0}))
  have hvals : ∀ a ∈ vals, a < α.1 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
        exact add_nat_lt_stage (hreqs r hr).2 r.offset
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
        exact add_nat_lt_stage (hreqs x.1 x.2).2 _
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact add_nat_lt_stage (hreqs r hr).2 N
  have hγ : listMax vals < α.1 := listMax_lt stage_pos hvals
  obtain ⟨y, hy, q, ⟨cap, hcapg, hcapl⟩, hcof, heval⟩ :=
    hM.highGradeDominance C₂.ctx C₂.p₀ C₂.eval_ctx (listMax vals) hγ
  let C₃ := C₂.step y hy q heval
  have h₃ : ∀ r (hr : r ∈ reqs), ∃ c : Cell q.scheme.scheme,
      q.label c = ofOrd (r.block + off r hr) := h₂.step hcof heval
  choose cell₃ hcell₃ using h₃
  -- totalize over blocks
  let repBase : Ordinal.{0} → Cell q.scheme.scheme := totalize reqs cell₃ cap
  let repOff : Ordinal.{0} → ℕ := totalize reqs off 0
  have hrep_label : ∀ μ (h : ∃ r ∈ reqs, r.block = μ),
      q.label (repBase μ) = ofOrd (μ + repOff μ) := by
    intro μ h
    change q.label (totalize reqs cell₃ cap μ) =
      ofOrd (μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0}))
    rw [totalize_of_ex reqs cell₃ cap h, totalize_of_ex reqs off 0 h]
    have e := hcell₃ (pick reqs μ h) (pick_mem reqs μ h)
    rw [pick_block reqs μ h] at e
    exact e
  have hoff_lt : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), repOff μ < N := by
    intro μ h
    change totalize reqs off 0 μ < N
    rw [totalize_of_ex reqs off 0 h]
    exact hN_off _ _
  have hrep_le : ∀ μ (h : ∃ r ∈ reqs, r.block = μ), q.label (repBase μ) ≤ q.label cap := by
    intro μ h
    rw [hrep_label μ h]
    have hmem : μ + ((repOff μ : ℕ) : Ordinal.{0}) ∈ vals := by
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨⟨pick reqs μ h, pick_mem reqs μ h⟩, List.mem_attach _ _, ?_⟩))
      change (pick reqs μ h).block +
          ((off (pick reqs μ h) (pick_mem reqs μ h) : ℕ) : Ordinal.{0}) =
        μ + ((totalize reqs off 0 μ : ℕ) : Ordinal.{0})
      rw [totalize_of_ex reqs off 0 h, pick_block reqs μ h]
    exact le_of_lt (lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals) hmem)) hcapl)
  refine ⟨⟨C₃.m, C₃.ctx, C₃.proj, C₃.proj_ctx, C₃.p₀, C₃.eval_ctx, N, cap, ?_, ?_,
    repBase, repOff, ?_, ?_, ?_, hN_req⟩, hNmin, ?_, ?_, hQ C₂ y hy q hcof heval hQ₂, hm₂'⟩
  · change q.scheme.scheme.grade cap = N
    rw [hcapg]; exact hm₂'
  · intro r hr
    change ofOrd r.value < q.label cap
    exact lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr))))) hcapl
  · intro r hr; exact hrep_label r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hoff_lt r.block ⟨r, hr, rfl⟩
  · intro r hr; exact hrep_le r.block ⟨r, hr, rfl⟩
  · exact (bot_lt_ofOrd _).trans hcapl
  · intro r hr
    change ofOrd (r.block + (N : Ordinal.{0})) < q.label cap
    exact lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (le_listMax (l := vals)
      (List.mem_append_right _ (List.mem_map_of_mem hr)))) hcapl

/-- **The reference context with the endpoint margin, from any intermediate context and carrying
any step-closed property** (the arity equation of `exists_referenceContext_margin_from'`
dropped). -/
theorem exists_referenceContext_margin_from (hM : R.IsModel) (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) (Nmin : ℕ)
    {Q : Ctx R t → Prop} (hQ : Ctx.StepClosed Q) (C₀ : Ctx R t) (hQ₀ : Q C₀) :
    ∃ C : ReferenceContext R t reqs, Nmin < C.N ∧ ⊥ < C.p₀.label C.capBase ∧
      (∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) ∧ Q C.toCtx := by
  obtain ⟨C, h1, h2, h3, h4, -⟩ := exists_referenceContext_margin_from' hM reqs hreqs Nmin hQ C₀ hQ₀
  exact ⟨C, h1, h2, h3, h4⟩

/-- **The reference context with the endpoint margin and the arity equation `m = N`**: the
construction pads to arity `N - 1` and takes one coface step carrying the cap, so the acquired
context has exactly the threshold arity. -/
theorem exists_referenceContext_margin' (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) (Nmin : ℕ) :
    ∃ C : ReferenceContext R t reqs, Nmin < C.N ∧ ⊥ < C.p₀.label C.capBase ∧
      (∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) ∧ C.m = C.N := by
  obtain ⟨C, h1, h2, h3, -, h5⟩ := exists_referenceContext_margin_from' hM reqs hreqs Nmin
    (Q := fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (Ctx.root p hp) trivial
  exact ⟨C, h1, h2, h3, h5⟩

/-- **The reference context with the endpoint margin**: `exists_referenceContext` with the
threshold above `Nmin` and the cap strictly above every block endpoint `μ + N`. -/
theorem exists_referenceContext_margin (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1) (Nmin : ℕ) :
    ∃ C : ReferenceContext R t reqs, Nmin < C.N ∧ ⊥ < C.p₀.label C.capBase ∧
      ∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase := by
  obtain ⟨C, h1, h2, h3, -⟩ := exists_referenceContext_margin_from hM reqs hreqs Nmin
    (Q := fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (Ctx.root p hp) trivial
  exact ⟨C, h1, h2, h3⟩

end VaughtConjecture.Knight
