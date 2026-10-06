/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorAttachment
public import VaughtConjecture.Knight.OrdinaryPredecessorSupply

/-! # Feeding literal input attachment into the checked predecessor

This is only the input adapter. It leaves the predecessor constructor and
the final receiving catalogue/installation unchanged.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorAttachment
open AmalgamationPlan Transform Value ExtOrd
noncomputable section
variable {n k : ℕ} (e : Fin n ↪ Fin (k + 4))
variable (P : SemScheme (k + 4)) (D : SemScheme (n + 1)) (Q : SemScheme n)
variable (hp : Finset.univ.image e ∈ P.scheme.plan)
variable (hd : Finset.univ.image Fin.castSuccEmb ∈ D.scheme.plan)
variable (hpr : P.restrictFace e hp = Q) (hdr : D.restrictFace Fin.castSuccEmb hd = Q)
variable (hsmall : n + 1 < k + 4)
variable {G : Finset ExtOrd} {θ : ExtOrd}
variable (hG : ∀ z ∈ G, SelfVis (k + 4) z) (hθ : SelfVis (k + 4) θ)
variable (htθ : θ ≠ ⊤) (hθG : θ ∈ G)

/-- No attached plan, geometry, occurrence inventory, or local lifting is
supplied: the literal schemes and common root construct all of those inputs. -/
def predecessor : OrdinaryPredecessorSupply.Output (input e P D Q hp hd hpr hdr) (k + 4) G θ :=
  OrdinaryPredecessorSupply.build (input e P D Q hp hd hpr hdr) k private_proper
    (donor_proper e hsmall) (union e) (Finset.card_fin _) private_card
    ((donor_card e).trans_lt hsmall) hG hθ htθ hθG

end
end VaughtConjecture.Knight.WholeDonorAttachment
