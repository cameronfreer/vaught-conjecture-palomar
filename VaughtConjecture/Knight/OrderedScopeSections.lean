/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrderedScopeRelocation

/-! # Selected sections through ordered ambient relocation

The local renderer is applied to the actual restriction of the preceding
section. The grid and ceiling are unchanged. Support is flattened to the
original field vector rather than treating earlier auxiliaries as new fields.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.OrderedScopeRelocation
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}
variable {D : CellScheme A} (sem : Semantics D) (hB : B ∈ D.plan) {k : ℕ}
variable (S : OrdinaryScopeOperator.Core (ScopeBoundary.rows D B hB sem) k)
variable (hsep : Separated (D := D) (B := B))

local notation "K" => carrier sem hB S
local notation "l" => old sem hB S
local notation "r" => localCell sem hB S

def boundaryFace : ExactSemanticFace (ScopeBoundary.rows D B hB sem) sem where
  map := (ScopeBoundary.toCell D B hB).toEmbedding
  index _ := rfl
  exhaustive _ := ScopeBoundary.exhaustive D B hB
  row _ _ := rfl

/-- Compatible whole sections glue on the actual occurrences. -/
theorem lawful_of_restrictions {v : Cell K → ExtOrd}
    (hp : RespectsSemantics sem (v ∘ l))
    (hq : RespectsSemantics S.rows (v ∘ r)) :
    RespectsSemantics (rows sem hB S hsep) v where
  orderly z := by
    rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simpa only [Function.comp_apply, CellScheme.grade, old_index] using hp.orderly c
    · simpa only [Function.comp_apply, CellScheme.grade, local_index] using hq.orderly c
  locality z := by
    rcases covered sem hB S z with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact TransformsTo.of_equiv (oldBelow sem hB S hsep c)
        (fun d => congrArg Prod.snd (old_index sem hB S d.1))
        (row_old sem hB S hsep c) (fun _ => rfl) (hp.locality c)
    · exact (localFace sem hB S hsep).locality_of_restrict hq c
  availability z c hs hg := by
    rcases covered sem hB S c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hz : (K).scope z ⊆ D.scope c := by
        simpa only [CellScheme.scope, old_index] using hs
      obtain ⟨d, rfl⟩ := old_exhaustive sem hB S hsep c z hz
      have hdc : D.scope d ⊆ D.scope c := by
        simpa only [CellScheme.scope, old_index] using hs
      have hdg : D.grade d = D.grade c := by
        simpa only [CellScheme.grade, old_index] using hg
      obtain ⟨e, he, hv⟩ := hp.availability d c hdc hdg
      exact ⟨l e, (old_index sem hB S e).trans
        (he.trans (old_index sem hB S c).symm), hv⟩
    · exact (localFace sem hB S hsep).availability_at hq z c hs hg

def paste (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) : Cell K → ExtOrd :=
  fun z => ProfileFaceUnion.paste (rightMap sem hB S) p q ((enumeration sem hB S).symm z)

theorem paste_old (p : Cell D → ExtOrd) (q : Cell S.carrier → ExtOrd) (d : Cell D) :
    paste sem hB S p q (l d) = p d := by
  unfold paste old
  rw [Equiv.symm_apply_apply]
  rfl

theorem paste_local {p : Cell D → ExtOrd} {q : Cell S.carrier → ExtOrd}
    (he : ∀ c, p (ScopeBoundary.toCell D B hB c) = q (S.original c)) (d : Cell S.carrier) :
    paste sem hB S p q (r d) = q d := by
  unfold paste localCell
  rw [Equiv.symm_apply_apply]
  exact ProfileFaceUnion.paste_right _ _ he d

theorem paste_lawful {p : Cell D → ExtOrd} {q : Cell S.carrier → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics S.rows q)
    (he : ∀ c, p (ScopeBoundary.toCell D B hB c) = q (S.original c)) :
    RespectsSemantics (rows sem hB S hsep) (paste sem hB S p q) := by
  apply lawful_of_restrictions sem hB S hsep
  · simpa only [Function.comp_def, paste_old] using hp
  · simpa only [Function.comp_def, paste_local sem hB S he] using hq

def render {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    (G : Finset ExtOrd) (θ : ExtOrd) : Cell K → ExtOrd :=
  paste sem hB S p (S.render ((boundaryFace sem hB).restrict hp)
    (fun c => ht (ScopeBoundary.toCell D B hB c)) G θ)

variable {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
variable {G : Finset ExtOrd} {θ : ExtOrd}

theorem render_old (d : Cell D) : render sem hB S hp ht G θ (l d) = p d :=
  paste_old sem hB S _ _ d

theorem render_local (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ) (d : Cell S.carrier) :
    render sem hB S hp ht G θ (r d) =
      S.render ((boundaryFace sem hB).restrict hp)
        (fun c => ht (ScopeBoundary.toCell D B hB c)) G θ d :=
  paste_local sem hB S (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
    (fun c => ht (ScopeBoundary.toCell D B hB c)) hG hθ c).symm) d

theorem render_lawful (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ) :
    RespectsSemantics (rows sem hB S hsep) (render sem hB S hp ht G θ) :=
  paste_lawful sem hB S hsep hp (S.lawful _ _ hG hθ)
    (fun c => (S.readback ((boundaryFace sem hB).restrict hp)
      (fun c => ht (ScopeBoundary.toCell D B hB c)) hG hθ c).symm)

theorem render_bound (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    (hb : ∀ d, p d ≤ θ) (d : Cell K) : render sem hB S hp ht G θ d ≤ θ := by
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hb c
  · rw [render_local sem hB S hp ht hG hθ]
    exact S.bound _ _ hθ (fun c => hb _) c

theorem render_proper (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    (hb : ∀ d, p d ≤ θ) (htθ : θ ≠ ⊤) (d : Cell K) :
    render sem hB S hp ht G θ d ≠ ⊤ :=
  ne_top_of_le_ne_top htθ (render_bound sem hB S hp ht hG hθ hb d)

theorem render_supported {X : Type*} {v : X → ExtOrd} {L : ℕ} (hk : k ≤ L)
    (hG : ∀ z ∈ G, SelfVis L z) (hθ : SelfVis k θ) (hθG : θ ∈ G)
    (hv : ∀ d, Supported L (G : Set ExtOrd) v (p d)) (d : Cell K) :
    Supported L (G : Set ExtOrd) v (render sem hB S hp ht G θ d) := by
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old]; exact hv c
  · rw [render_local sem hB S hp ht (fun z hz => selfVis_mono (hG z hz) hk) hθ]
    exact (S.support _ _ hk hθG c).substitute hG (fun c => hv _)

theorem render_agreement {q : Cell D → ExtOrd} (hq : RespectsSemantics sem q)
    (htq : ∀ d, q d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hθ : SelfVis k θ)
    {γ : ExtOrd} (hγ : γ ∈ G) (hγθ : γ ≤ θ) (he : Agree p q γ) :
    Agree (render sem hB S hp ht G θ) (render sem hB S hq htq G θ) γ := by
  intro d
  rcases covered sem hB S d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [render_old, render_old]; exact he c
  · rw [render_local sem hB S hp ht hG hθ, render_local sem hB S hq htq hG hθ]
    exact S.agreement _ _ _ _ hG hθ hγ hγθ (fun c => he _) c

end
end VaughtConjecture.Knight.OrderedScopeRelocation
