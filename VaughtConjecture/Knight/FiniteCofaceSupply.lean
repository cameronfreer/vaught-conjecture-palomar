/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteTupleGeometry

/-! # Prescribed finite coface supply

These contracts prescribe an entire coface. Family-serving supply is kept separately in
`FiniteFamilySupply`; no strengthening is made during extraction. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w} {β : LimitStage}

/-- **The pinned master-coface supply** (the completion gate's missing input): a coface of
the current master whose face over `g⌢last` is a PRESCRIBED coface of the base's face.
This is the exact old-pin/visibility collision: the new domain must keep the initial face
`dom P` literally (the old pin), make the face `g⌢last` VISIBLE in its plan, and restrict
there to `dom q` with the labels of `q` — a span gluing of two prescribed faces over their
common face `dom p`, where the compiled engine (`exists_respects_extends_capped`) pins ONE
face only.  The clean theorem to return to Knight-VC. -/
def PinnedCofaceSupply (β : LimitStage) : Prop :=
  ∀ {N n : ℕ} (P : S β.1 N) (g : Fin n ↪ Fin N) (p : S β.1 n),
    typeMap g P = some p → ∀ q : S β.1 (n + 1), IsCoface p q →
      ∃ Q : S β.1 (N + 1), IsCoface P Q ∧ typeMap (extendFace g) Q = some q

/-- Exact-pair amalgamation for two cofaces of one explicitly supplied base — the coatom
instance of Cor. 4.3.22. -/
def ExactPairAmalgamation (β : LimitStage) : Prop :=
  ∀ {n : ℕ} (p : S β.1 n) (P q : S β.1 (n + 1)),
    IsCoface p P → IsCoface p q →
      ∃ Q : S β.1 (n + 2),
        IsCoface P Q ∧
          typeMap (extendFace (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))) Q = some q

/-- The pinned coface supply contains exact-pair amalgamation (the `N = n + 1`,
`g = castSuccEmb` instance). -/
theorem PinnedCofaceSupply.exactPairAmalgamation (h : PinnedCofaceSupply β) :
    ExactPairAmalgamation β := by
  intro n p P q hP hq
  exact h P Fin.castSuccEmb p hP q hq

end FixedHeight
end VaughtConjecture.Knight
