/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext

/-! # Actual block references before a cap is chosen

Uniformity supplies one actual representative per requested block. No padding,
threshold or intermediate cap is constructed. References are indexed by the
finite requested blocks: an empty root and empty request set need no default
cell. Clients choose a final cap only after observing the reference offsets.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight
open TypeTower StageType KnightRealization Value ExtOrd
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M}

/-- The reference-only prefix of acquisition, with no intermediate cap. -/
structure RawReferenceContext (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (blocks : Finset Ordinal.{0}) extends Ctx R t where
  repBase : blocks → Cell p₀.scheme.scheme
  repOff : blocks → ℕ
  rep_label : ∀ μ, p₀.label (repBase μ) = ofOrd (μ.1 + repOff μ)

namespace RawReferenceContext
variable {blocks : Finset Ordinal.{0}} (C : RawReferenceContext R t blocks)

/-- A finite bound chosen after the actual offsets have been obtained. -/
def offsetBound : ℕ := Finset.univ.sup C.repOff

theorem rep_off_le (μ : blocks) : C.repOff μ ≤ C.offsetBound :=
  Finset.le_sup (f := C.repOff) (Finset.mem_univ μ)

end RawReferenceContext

/-- Acquire the root and raw representatives only. In particular the empty
request set performs no padding or high-grade dominance step. -/
theorem exists_rawReferenceContext (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) (blocks : Finset Ordinal.{0})
    (hblocks : ∀ μ ∈ blocks, IsNonSuccessor μ ∧ μ < α.1) :
    Nonempty (RawReferenceContext R t blocks) := by
  classical
  let reqs : List BlockRequest := blocks.toList.map (fun μ => ⟨μ, 0⟩)
  have hreqs : ∀ r ∈ reqs, IsNonSuccessor r.block ∧ r.block < α.1 := by
    intro r hr
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hr
    exact hblocks μ (Finset.mem_toList.mp hμ)
  obtain ⟨C, hC⟩ := exists_ctx_hasCells hM (Ctx.root p hp) reqs hreqs
  have href (μ : blocks) : ∃ (c : Cell C.p₀.scheme.scheme) (j : ℕ),
      C.p₀.label c = ofOrd (μ.1 + j) :=
    hC ⟨μ.1, 0⟩ (List.mem_map.mpr ⟨μ.1, Finset.mem_toList.mpr μ.2, rfl⟩)
  choose rep off hrep using href
  exact ⟨{ toCtx := C, repBase := rep, repOff := off, rep_label := hrep }⟩

end
end VaughtConjecture.Knight
