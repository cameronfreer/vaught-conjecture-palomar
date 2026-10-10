/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopFreeExtensionWitness

/-! # Existence of top-free extension realizations

The amalgamation step is an exact top-free pinned extension: a top-free donor over a
visible face of a top-free finite master is realized exactly by a top-free literal
master extension (`exists_exact`). It is the existing pinned coface followed by a cap
chosen above the master's labels and the donor's labels, so the cap fixes both.

With exact requests instead of cutoff requests, the shared finite-master scheduler then
gives a top-free extension realization on every countable infinite carrier at every
countable limit stage (`exists_isTopFreeExtension`, proved). This file only tests the
alternative; the capped scheduler of `TopFreeCapHenkin` is unchanged and still used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.TopFreeExtensionExistence
open TypeTower StageType Value ExtOrd KnightRealization FixedHeight TopFreeCapHenkin
universe w
variable {β : LimitStage} {M : Type w}

/-- **Exact top-free pinned extension** (proved). Every top-free coface of a visible face
of a top-free master is the exact image of a top-free coface of the master. -/
theorem exists_exact {N n : ℕ} (P : S β.1 N) (hP : ∀ d, P.label d ≠ ⊤)
    (g : Fin n ↪ Fin N) (p : S β.1 n) (hg : typeMap g P = some p)
    (q : S β.1 (n + 1)) (hq : IsCoface p q) (hqtop : ∀ d, q.label d ≠ ⊤) :
    ∃ Q : S β.1 (N + 1), IsCoface P Q ∧ (∀ d, Q.label d ≠ ⊤) ∧
      typeMap (extendFace g) Q = some q := by
  classical
  obtain ⟨Q, hQP, hQq⟩ :=
    pinnedCofaceSupply_of_supply (CanonicalCoatomSupply.supply β.2) P g p hg q hq
  let v : Cell P.scheme.scheme ⊕ Cell q.scheme.scheme → ExtOrd := Sum.elim P.label q.label
  have hv : ∀ i, v i < ofOrd β.1 := by
    rintro (d | d)
    · exact (P.label_bound d).resolve_right (hP d)
    · exact (q.label_bound d).resolve_right (hqtop d)
  obtain ⟨γ, hγ, _, hvγ, hγβ⟩ := FiniteCutCapping.exists_cap_below_limit v β.2 hv (N + 1)
  exact ⟨TopFreePinnedExtension.cap Q γ hγ hγβ,
    TopFreePinnedExtension.cap_typeMap_fixed Q γ hγ hγβ Fin.castSuccEmb P hQP
      (fun d ↦ hvγ (.inl d)),
    fun d ↦ ne_top_of_lt ((min_le_right (Q.label d) γ).trans_lt hγβ),
    TopFreePinnedExtension.cap_typeMap_fixed Q γ hγ hγβ (extendFace g) q hQq
      (fun d ↦ hvγ (.inr d))⟩

/-- Exact requests: a literal root, its label, and a top-free coface. No cutoff. -/
abbrev Request (β : LimitStage) (M : Type w) :=
  Σ n, (Fin n ↪ M) × Σ p : S β.1 n,
    {q : S β.1 (n + 1) // IsCoface p q ∧ ∀ d, q.label d ≠ ⊤}

/-- The donor is realized exactly over the literal root. -/
def Serves (A : KnightRealization β M) : Request β M → Prop
  | ⟨_, t, _, q⟩ => ∃ (y : M) (hy : y ∉ Set.range t), A.eval (snoc t y hy) = some q.1

theorem Serves.mono {A B : KnightRealization β M} (h : Extends A B)
    {r : Request β M} (hr : Serves A r) : Serves B r := by
  obtain ⟨n, t, p, q⟩ := r
  obtain ⟨y, hy, hs⟩ := hr
  exact ⟨y, hy, h _ _ hs⟩

/-- The rooted task of an exact request. -/
def task : Request β M → RootedTask knightTower β M
  | r@⟨n, t, p, _⟩ => ⟨n, t, p, fun A ↦ Serves A r, fun h hs ↦ hs.mono h⟩

/-- One finite step serves an applicable exact request by a top-free literal extension. -/
theorem service [Infinite M] (st : State β M) (r : Request β M)
    (hr : st.A.eval r.2.1 = some r.2.2.1) :
    ∃ st' : State β M, Extends st.A st'.A ∧ Serves st'.A r := by
  obtain ⟨n, t, p, q, hq, hqtop⟩ := r
  change st.A.eval t = some p at hr
  obtain ⟨f, hf⟩ := st.hM t (by rw [hr]; rfl)
  have hface : typeMap f st.P = some p := by
    have hh := st.hA.consistent _ _ f st.htup
    rw [hf] at hh
    exact hh.symm.trans hr
  obtain ⟨Q, hQP, hQtop, hQq⟩ := exists_exact st.P st.proper f p hface q hq hqtop
  obtain ⟨y, hy, _⟩ := exists_fresh st.hA.finite st.tup
  obtain ⟨st', hext, _, hQ, _⟩ := install st hy Q hQP hQtop
  have hyt : y ∉ Set.range t := by
    rintro ⟨i, rfl⟩
    exact hy ⟨f i, congrArg (fun e : Fin n ↪ M ↦ e i) hf⟩
  refine ⟨st', hext, y, hyt, ?_⟩
  have htup : (extendFace f).trans (snoc st.tup y hy) = snoc t y hyt := by
    subst t
    exact extendFace_trans_snoc f hy hyt
  rw [← htup, st'.hA.consistent _ Q (extendFace f) hQ]
  exact hQq

/-- **Existence** (proved): a top-free extension realization on every countable infinite
carrier at every countable limit stage, from the shared finite-master scheduler. -/
theorem exists_isTopFreeExtension [Countable M] [Infinite M]
    (hβ : β.1.card ≤ Cardinal.aleph0) :
    ∃ R : KnightRealization β M, R.IsTopFreeExtension := by
  have : ∀ n : ℕ, Countable (S β.1 n) := StageType.countable_S hβ
  have : Countable (Request β M) := by unfold Request; infer_instance
  let master : State β M → FiniteMaster knightTower β M := fun s ↦ s.toRunState.master
  have habs : ∀ s x, ∃ t, master s ≤ master t ∧ x ∈ Set.range (master t).tuple := by
    intro s x
    by_cases hx : x ∈ Set.range s.tup
    · exact ⟨s, le_rfl, hx⟩
    · obtain ⟨t, hext, _, ht⟩ := absorb s hx
      exact ⟨t, RunState.master_extends hext, ht⟩
  have hserve : ∀ s r, (master s).chart.eval (task r).root = some (task r).base →
      ∃ t, master s ≤ master t ∧ (task r).Served (master t).chart := by
    intro s r hr
    obtain ⟨n, t, p, q⟩ := r
    change s.toRunState.master.chart.eval t = some p at hr
    rw [RunState.chart_eq] at hr
    obtain ⟨s', hext, hs'⟩ := service s ⟨n, t, p, q⟩ hr
    exact ⟨s', RunState.master_extends hext, s'.toRunState.chart_eq.symm ▸ hs'⟩
  obtain ⟨R, hc, hcover, _, hs, hfinite⟩ :=
    FiniteMasterScheduler.exists_realization master habs task hserve (initial β M)
  refine ⟨R, ⟨hc, hcover.toInitialSegment knightTower_permTotal hc.isVisibleFaceConsistent,
    ?_, ?_⟩⟩
  · intro n t p hp
    obtain ⟨s, hs⟩ := hfinite t p hp
    exact s.topFree t p (s.toRunState.chart_eq ▸ hs)
  · intro n t p hp q hq hqtop
    exact hs ⟨n, t, p, ⟨q, hq, hqtop⟩⟩ hp

/-- The terminal-witness conclusion of `TopFreeCapHenkin.exists_terminal_model` (proved),
verbatim, through top-free extension realizations and without cutoff requests. -/
theorem exists_terminal_model [Countable M] [Infinite M]
    (hβ : β.1.card ≤ Cardinal.aleph0) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ (γ : LimitStage) (hβγ : β < γ), R.NoProlongationToIn IsModelClass hβγ.le :=
  exists_terminal_model_of_isTopFreeExtension (exists_isTopFreeExtension hβ)

end VaughtConjecture.Knight.TopFreeExtensionExistence
