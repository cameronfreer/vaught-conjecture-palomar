/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteFloorCompletion
public import VaughtConjecture.Knight.TwoContextCoupled

/-! # The owner-local saturation endpoint (audit13 / notes40 §2.1)

The reviewer's grid-free replacement for first-cut minimality in owner alignment
(`/home/freer/work/vc-notes/audit-notes1/notes40_foundations_and_relative_generics.md` §2.1,
audit13).  Fix a grade `j`, a finite family of owner arguments `ι` with source section `s` and
target section `p`, an owner `c`, a positive cap `γ`, and a bottom-preserving monotone map `τ`
bounded by `γ` with `τ (s d) = min (p d) γ` on every argument.  A *saturated* argument is one
whose image reaches the cap, `τ (s d) = γ`; the owner is saturated because `γ < p c`.  Define

    E = { R_j (s d) | τ (s d) = γ },      h = min E,

where `R_j x = extVisibilityReplace x j j` rounds `x` up to the `j`-visible endpoint of its strip.
Then `⊥ < h`, `h` is proper and `j`-visible, `τ h = γ` (reaching), `h ≤ s c` (the owner
bound), and every saturated argument with `s d < h` has `R_j (s d) = h` — it lies in the single
short strip ending at `h` (`IsEndpoint.strip`), is `j`-invisible (`IsEndpoint.not_selfVis_of_lt`)
and shares the block floor of `h` (`IsEndpoint.blockFloor_eq_of_lt`).

There is no source-grid cardinal in the statement: the endpoint is characterised by a least-element
property over the saturated observations (`IsEndpoint`), the observations range over an arbitrary
finite type, and `exists_isEndpoint` produces it.  The wrapper `exists_isEndpoint_below` states it
on the owner's lower domain `D.below (D.cell c)` with the shapes used by owner face alignment, and
`Saturation.of_witness` derives the map hypotheses from a normalized witness with suppressor
`gTop j`.

V-C's source module retains the regression `Example`: `j = 2`, owner observations `ω·6+1` and
`ω·6+2`, and `τ` bottom on block `0` and constantly `γ = ω·10+2` on every later block.  The
full source grid already reaches `γ` at `ω+2`, but the owner-local endpoint is `ω·6+2`; no
property of the unused earlier grid point is needed. That numerical regression
is not duplicated in this dependency port.

Ported from V-C commit `7aeeea5`, with the endpoint statements and proofs retained.
The three scalar endpoint helpers use the existing KVC dependencies directly;
the source-side numerical example stays on the V-C branch. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace OwnerLocalEndpoint

/-- Rounding to the `j`-visible endpoint of the strip of `x`. -/
noncomputable abbrev endpoint (j : ℕ) (x : ExtOrd) : ExtOrd := extVisibilityReplace x j j

theorem le_endpoint (j : ℕ) (x : ExtOrd) : x ≤ endpoint j x := le_extVisibilityReplace_self x j

theorem selfVis_endpoint (j : ℕ) (x : ExtOrd) : SelfVis j (endpoint j x) := by
  unfold endpoint
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot j
  · exact extVisibilityReplace_top j j
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs <;> omega

theorem endpoint_of_selfVis {j : ℕ} {x : ExtOrd} (h : SelfVis j x) : endpoint j x = x := h

theorem endpoint_mono {j : ℕ} {x y : ExtOrd} (h : x ≤ y) : endpoint j x ≤ endpoint j y :=
  evr_mono h le_rfl

theorem endpoint_ne_top {j : ℕ} {x : ExtOrd} (h : x ≠ ⊤) : endpoint j x ≠ ⊤ := by
  unfold endpoint
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_ne_top
  · exact absurd rfl h
  · rw [extVisibilityReplace_ofOrd]; exact ofOrd_ne_top _

variable {ι : Type*}

/-- The owner-local saturation hypotheses: `τ` is bottom-preserving, monotone and bounded by the
positive cap `γ`; the owner `c` exceeds the cap under `p`; the face equation holds on every
argument; every source observation is proper; and the owner's source value is `j`-visible. -/
structure Saturation (j : ℕ) (s p : ι → ExtOrd) (c : ι) (τ : ExtOrd → ExtOrd) (γ : ExtOrd) :
    Prop where
  bot : τ ⊥ = ⊥
  mono : Monotone τ
  bound : ∀ x, τ x ≤ γ
  pos : ⊥ < γ
  cap : γ < p c
  face : ∀ d, τ (s d) = min (p d) γ
  proper : ∀ d, s d ≠ ⊤
  owner_vis : SelfVis j (s c)

/-- The endpoint `h` is the least rounded saturated observation. -/
structure IsEndpoint (j : ℕ) (s : ι → ExtOrd) (τ : ExtOrd → ExtOrd) (γ h : ExtOrd) : Prop where
  least : IsLeast {x | ∃ d, τ (s d) = γ ∧ endpoint j (s d) = x} h

theorem IsEndpoint.unique {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h h' : ExtOrd}
    (H : IsEndpoint j s τ γ h) (H' : IsEndpoint j s τ γ h') : h = h' :=
  H.least.unique H'.least

theorem IsEndpoint.le_of_saturated {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) {d : ι} (hd : τ (s d) = γ) : h ≤ endpoint j (s d) :=
  H.least.2 ⟨d, hd, rfl⟩

theorem IsEndpoint.exists_witness {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) : ∃ d, τ (s d) = γ ∧ endpoint j (s d) = h :=
  H.least.1

section Conclusions

variable {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}

/-- The owner is saturated. -/
theorem Saturation.owner_saturated (S : Saturation j s p c τ γ) : τ (s c) = γ := by
  rw [S.face c, min_eq_right S.cap.le]

/-- Visibility: the endpoint is `j`-visible. -/
theorem IsEndpoint.selfVis (H : IsEndpoint j s τ γ h) : SelfVis j h := by
  obtain ⟨d, -, hd⟩ := H.exists_witness
  rw [← hd]
  exact selfVis_endpoint j (s d)

/-- Properness, from properness of the observations. -/
theorem IsEndpoint.ne_top (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : h ≠ ⊤ := by
  obtain ⟨d, -, hd⟩ := H.exists_witness
  rw [← hd]
  exact endpoint_ne_top (S.proper d)

/-- Reaching: the endpoint itself is mapped to the cap. -/
theorem IsEndpoint.reach (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : τ h = γ := by
  obtain ⟨d, hd, hdh⟩ := H.exists_witness
  refine le_antisymm (S.bound h) ?_
  calc γ = τ (s d) := hd.symm
    _ ≤ τ h := S.mono (hdh ▸ le_endpoint j (s d))

/-- Positivity: a saturated observation is not bottom, so neither is the endpoint. -/
theorem IsEndpoint.bot_lt (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : ⊥ < h := by
  refine bot_lt_iff_ne_bot.mpr fun hb ↦ ?_
  have := H.reach S
  rw [hb, S.bot] at this
  exact S.pos.ne this

/-- The owner bound: the endpoint is at most the owner's (visible) source value. -/
theorem IsEndpoint.le_owner (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : h ≤ s c :=
  (H.le_of_saturated S.owner_saturated).trans_eq (endpoint_of_selfVis S.owner_vis)

/-- The single-strip conclusion: a saturated observation below the endpoint rounds to it. -/
theorem IsEndpoint.strip (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h) (hd : τ (s d) = γ) :
    endpoint j (s d) = h :=
  le_antisymm ((endpoint_mono hlt.le).trans_eq (endpoint_of_selfVis H.selfVis))
    (H.le_of_saturated hd)

/-- A saturated observation strictly below the endpoint is `j`-invisible. -/
theorem IsEndpoint.not_selfVis_of_lt (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h)
    (hd : τ (s d) = γ) : ¬ SelfVis j (s d) := fun hv ↦
  hlt.ne (((endpoint_of_selfVis hv).symm.trans (H.strip hlt hd)))

/-- A saturated observation strictly below the endpoint lies in the block of the endpoint. -/
theorem IsEndpoint.blockFloor_eq_of_lt (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h)
    (hd : τ (s d) = γ) : blockFloor (s d) = blockFloor h := by
  rw [← H.strip hlt hd]
  exact (blockFloor_evr (s d) j j).symm

end Conclusions

/-- **The owner-local saturation endpoint lemma** (notes40 §2.1).  Over a finite family of owner
arguments the least rounded saturated observation exists; it is positive, proper, `j`-visible,
reaches the cap, is bounded by the owner's source value, and collects every saturated
observation below it into its own strip. -/
theorem exists_isEndpoint [Finite ι] {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (S : Saturation j s p c τ γ) :
    ∃ h, IsEndpoint j s τ γ h ∧ ⊥ < h ∧ h ≠ ⊤ ∧ SelfVis j h ∧ τ h = γ ∧ h ≤ s c ∧
      ∀ d, s d < h → τ (s d) = γ → endpoint j (s d) = h := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨d₀, hd₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun d ↦ τ (s d) = γ)
    (fun d ↦ endpoint j (s d)) ⟨c, by simp [S.owner_saturated]⟩
  have H : IsEndpoint j s τ γ (endpoint j (s d₀)) :=
    ⟨⟨⟨d₀, (Finset.mem_filter.mp hd₀).2, rfl⟩, by
      rintro x ⟨d, hd, rfl⟩
      exact hmin d (by simp [hd])⟩⟩
  exact ⟨_, H, H.bot_lt S, H.ne_top S, H.selfVis, H.reach S, H.le_owner S,
    fun d hlt hd ↦ H.strip hlt hd⟩

/-- The map hypotheses of `Saturation` from a normalized witness with suppressor `gTop j`
(the sufficient condition named in notes40 §2). -/
theorem Saturation.of_witness {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (hτ : Witness (gTop j) τ) (bound : ∀ x, τ x ≤ γ) (pos : ⊥ < γ) (cap : γ < p c)
    (face : ∀ d, τ (s d) = min (p d) γ) (proper : ∀ d, s d ≠ ⊤) (owner_vis : SelfVis j (s c)) :
    Saturation j s p c τ γ :=
  ⟨hτ.bot, hτ.mono, bound, pos, cap, face, proper, owner_vis⟩

/-- The endpoint lemma on the owner's complete lower domain `D.below (D.cell c)`: the source
section is a full labelling `s : Cell D → ExtOrd`, the target section `p` lives on the lower
domain, and the face equation is stated on the lower domain. -/
theorem exists_isEndpoint_below {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {D : CellScheme (ι := ι) S} {c : Cell D} {s : Cell D → ExtOrd}
    {p : D.below (D.cell c) → ExtOrd} {τ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hbot : τ ⊥ = ⊥) (hmono : Monotone τ) (hbound : ∀ x, τ x ≤ γ) (hpos : ⊥ < γ)
    (hcap : γ < p ⟨c, GradedLe.refl _⟩) (hface : ∀ e : D.below (D.cell c), τ (s e.1) = min (p e) γ)
    (hproper : ∀ e : D.below (D.cell c), s e.1 ≠ ⊤) (hvis : SelfVis (D.grade c) (s c)) :
    ∃ h, IsEndpoint (D.grade c) (fun e : D.below (D.cell c) ↦ s e.1) τ γ h ∧ ⊥ < h ∧ h ≠ ⊤ ∧
      SelfVis (D.grade c) h ∧ τ h = γ ∧ h ≤ s c ∧
      ∀ e : D.below (D.cell c), s e.1 < h → τ (s e.1) = γ → endpoint (D.grade c) (s e.1) = h :=
  exists_isEndpoint (c := ⟨c, GradedLe.refl _⟩)
    ⟨hbot, hmono, hbound, hpos, hcap, hface, hproper, hvis⟩

end OwnerLocalEndpoint

end VaughtConjecture.Knight
