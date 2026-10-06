/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopFreePinnedExtension
public import VaughtConjecture.Knight.FiniteMasterState
public import VaughtConjecture.Knight.FiniteRequestData
public import VaughtConjecture.Knight.FixedHeightChain
public import VaughtConjecture.Knight.CapReceivingModel
public import VaughtConjecture.Knight.TopFreeTerminal
public import VaughtConjecture.TypeTower.FiniteMasterScheduler

/-! # Capped scheduling with top-free masters

Requests specify a whole coface and an observation cutoff. The existence endpoint
uses the shared finite-master dense-set scheduler: absorb the root, then resolve
the request permanently. Each finite step uses the constructed top-free pinned
extension, and every union label comes from a top-free finite master.

The historical repeated-run statements remain for compatibility, but neither
existence endpoint uses them. Only the donor is approximated at a cutoff; the old
master is always retained literally. No exact realization of a top donor is claimed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.TopFreeCapHenkin
open TypeTower StageType Value ExtOrd KnightRealization FixedHeight AmalgamationPlan
universe w
variable {β : LimitStage} {M : Type w}

structure State (β : LimitStage) (M : Type w) extends RunState β M where
  proper : ∀ d, P.label d ≠ ⊤

theorem State.topFree (st : State β M) {n : ℕ} (t : Fin n ↪ M)
    (p : S β.1 n) (hp : st.A.eval t = some p) : ∀ d, p.label d ≠ ⊤ := by
  obtain ⟨f, rfl⟩ := st.hM t (by rw [hp]; rfl)
  have hf : typeMap f st.P = some p := (st.hA.consistent _ _ f st.htup).symm.trans hp
  have hv := (typeMap_isSome_iff f st.P).mp (by rw [hf]; rfl)
  have he := Option.some.inj ((typeMap_eq_some f st.P hv).symm.trans hf)
  subst p
  exact fun d => st.proper _

noncomputable def initial (β : LimitStage) (M : Type w) : State β M :=
  { initState β M with
    proper := by
      intro d
      have hp := (initState β M).P.scheme.scheme.grade_pos d
      have h := FiniteCoverReceiving.grade_le_points (initState β M).P.scheme d
      change (initState β M).P.scheme.scheme.grade d ≤ 0 at h
      omega }

theorem install (st : State β M) {y : M} (hy : y ∉ Set.range st.tup)
    (Q : S β.1 (st.N + 1)) (hQ : IsCoface st.P Q) (hproper : ∀ d, Q.label d ≠ ⊤) :
    ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
      st'.A.eval (snoc st.tup y hy) = some Q ∧ y ∈ Set.range st'.tup := by
  let st' : State β M := ⟨RunState.ofMaster ⟨_, snoc st.tup y hy, Q⟩, hproper⟩
  have hm : st.toRunState.master ≤ st'.toRunState.master :=
    ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc st.tup y hy, hQ⟩
  exact ⟨st', RunState.extends_of_master hm, hm.range_mono, st'.htup,
    ⟨Fin.last _, snoc_apply_last st.tup y hy⟩⟩

abbrev Request (β : LimitStage) (M : Type w) :=
  Σ n, (Fin n ↪ M) × Σ p : S β.1 n,
    {q : S β.1 (n + 1) // IsCoface p q} × {ν : Ordinal.{0} // ν < β.1}

def Applicable (A : KnightRealization β M) : Request β M → Prop
  | ⟨_, t, p, _, _⟩ => A.eval t = some p

def Serves (A : KnightRealization β M) : Request β M → Prop
  | ⟨n, t, _, q, ν⟩ =>
    ∃ (y : M) (hy : y ∉ Set.range t) (r : S β.1 (n + 1)),
      A.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.1.scheme,
        ∀ d, min (r.label d) (ofOrd ν.1) =
          min (q.1.label (SemScheme.castCell he d)) (ofOrd ν.1)

theorem service [Infinite M] (st : State β M) (r : Request β M)
    (hr : Applicable st.A r) :
    ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
      Serves st'.A r := by
  obtain ⟨n, t, p, q, ν⟩ := r
  obtain ⟨f, hf⟩ := st.hM t (by rw [show st.A.eval t = some p from hr]; rfl)
  have hface : typeMap f st.P = some p := by
    have hh := st.hA.consistent _ _ f st.htup
    rw [hf] at hh
    exact hh.symm.trans hr
  obtain ⟨Q, hQP, hQtop, q', hQq, he, hcap⟩ := TopFreePinnedExtension.exists_pinned
    st.P st.proper f p hface q.1 q.2 (ofOrd ν.1) (ofOrd_lt_ofOrd.mpr ν.2)
  obtain ⟨y, hy, _⟩ := exists_fresh st.hA.finite st.tup
  obtain ⟨st', hext, hrange, hQ, _⟩ := install st hy Q hQP hQtop
  have hyt : y ∉ Set.range t := by
    rintro ⟨i, rfl⟩
    exact hy ⟨f i, congrArg (fun e : Fin n ↪ M => e i) hf⟩
  refine ⟨st', hext, hrange, y, hyt, q', ?_, he, hcap⟩
  have htup : (extendFace f).trans (snoc st.tup y hy) = snoc t y hyt := by
    subst t
    exact extendFace_trans_snoc f hy hyt
  rw [← htup]
  rw [st'.hA.consistent _ Q (extendFace f) hQ]
  exact hQq

theorem absorb (st : State β M) {x : M} (hx : x ∉ Set.range st.tup) :
    ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
      x ∈ Set.range st'.tup := by
  obtain ⟨q, _, hq⟩ := exists_highGrade_coface (CanonicalCoatomSupply.supply β.2)
    st.P 0 β.2.pos
  obtain ⟨Q, hQ, hproper, _⟩ := TopFreePinnedExtension.exists_pinned st.P st.proper
    (Function.Embedding.refl _) st.P (typeMap_refl _) q hq ⊥ (bot_lt_ofOrd _)
  obtain ⟨st', hext, hrange, _, hx'⟩ := install st hx Q hQ hproper
  exact ⟨st', hext, hrange, hx'⟩

def StepServes (A : KnightRealization β M) (st : State β M) : Request β M ⊕ M → Prop
  | .inl r => Applicable A r → Serves st.A r
  | .inr x => x ∈ Set.range st.tup

theorem step [Infinite M] (st : State β M) (i : Request β M ⊕ M) :
    ∃ st' : State β M, Extends st.A st'.A ∧ Set.range st.tup ⊆ Set.range st'.tup ∧
      StepServes st.A st' i := by
  classical
  cases i with
  | inl r =>
    by_cases hr : Applicable st.A r
    · obtain ⟨st', hext, hrange, hs⟩ := service st r hr
      exact ⟨st', hext, hrange, fun _ => hs⟩
    · exact ⟨st, Extends.refl _, subset_rfl, fun h => False.elim (hr h)⟩
  | inr x =>
    by_cases hx : x ∈ Set.range st.tup
    · exact ⟨st, Extends.refl _, subset_rfl, hx⟩
    · exact absorb st hx

noncomputable def run [Infinite M] (e : ℕ → Request β M ⊕ M) : ℕ → State β M
  | 0 => initial β M
  | k + 1 => (step (run e k) (e k)).choose

theorem run_spec [Infinite M] (e : ℕ → Request β M ⊕ M) (k : ℕ) :
    Extends (run e k).A (run e (k + 1)).A ∧
      Set.range (run e k).tup ⊆ Set.range (run e (k + 1)).tup ∧
      StepServes (run e k).A (run e (k + 1)) (e k) :=
  (step (run e k) (e k)).choose_spec

theorem run_chain [Infinite M] (e : ℕ → Request β M ⊕ M) (k : ℕ) :
    Extends (run e k).A (run e (k + 1)).A := (run_spec e k).1

theorem run_range_mono [Infinite M] (e : ℕ → Request β M ⊕ M) {j k : ℕ} (hjk : j ≤ k) :
    Set.range (run e j).tup ⊆ Set.range (run e k).tup := by
  induction hjk with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (run_spec e _).2.1

/-- A serviced observation is a literal finite evaluation, so it persists. -/
theorem Serves.mono {A B : KnightRealization β M} (h : Extends A B)
    {r : Request β M} (hr : Serves A r) : Serves B r := by
  obtain ⟨n, t, p, q, ν⟩ := r
  obtain ⟨y, hy, s, hs, he, hcap⟩ := hr
  exact ⟨y, hy, s, h _ _ hs, he, hcap⟩

/-- The cutoff belongs to the task's answer predicate, not to master extension. -/
def task : Request β M → RootedTask knightTower β M
  | r@⟨n, t, p, _, _⟩ => ⟨n, t, p, fun A => Serves A r, fun h hs => hs.mono h⟩

theorem run_receiving [Infinite M] (e : ℕ → Request β M ⊕ M)
    (he : ∀ x k, ∃ m, k ≤ m ∧ e m = x) :
    FiniteCutReceiving (chainLimit fun k => (run e k).A) := by
  intro n t p hp q hq δ hδ hδβ
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < β.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · exact False.elim ((not_lt_of_ge le_top) hδβ)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδβ⟩
  let r : Request β M := ⟨n, t, p, ⟨q, hq⟩, ⟨ν, hν⟩⟩
  obtain ⟨k, hk⟩ := chainLimit_eval_some_exists hp
  obtain ⟨m, hkm, hem⟩ := he (.inl r) k
  have hs := (run_spec e m).2.2
  rw [hem] at hs
  have hr : Applicable (run e m).A r := extends_of_le (run_chain e) hkm _ _ hk
  exact (hs hr).mono (extends_chainLimit (run_chain e) (m + 1))

theorem run_covering [Infinite M] (e : ℕ → Request β M ⊕ M)
    (he : ∀ x k, ∃ m, k ≤ m ∧ e m = x) :
    (chainLimit fun k => (run e k).A).IsInitialSegmentCovering := by
  intro n t
  have habs : ∀ i : Fin n, ∃ k, t i ∈ Set.range (run e k).tup := by
    intro i
    obtain ⟨m, _, hm⟩ := he (.inr (t i)) 0
    have hs := (run_spec e m).2.2
    rw [hm] at hs
    exact ⟨m + 1, hs⟩
  choose ks hks using habs
  let k := Finset.univ.sup ks
  have ht : ∀ i, t i ∈ Set.range (run e k).tup := fun i =>
    run_range_mono e (Finset.le_sup (Finset.mem_univ i)) (hks i)
  obtain ⟨m, s, hst, hs⟩ := initialSegmentCover_of_mastered (run e k).hA.consistent
    (by rw [(run e k).htup]; rfl) t ht
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨m, s, hst, by rw [extends_chainLimit (run_chain e) k s Q hQ]; rfl⟩

theorem run_topFree [Infinite M] (e : ℕ → Request β M ⊕ M)
    {n : ℕ} (t : Fin n ↪ M) (p : S β.1 n)
    (hp : (chainLimit fun k => (run e k).A).eval t = some p) : ∀ d, p.label d ≠ ⊤ := by
  obtain ⟨k, hk⟩ := chainLimit_eval_some_exists hp
  exact (run e k).topFree t p hk

/-- Invisible faces of an old master remain undefined in the union. Mere
preservation of defined evaluations would not state this receipt. -/
theorem run_invisible [Infinite M] (e : ℕ → Request β M ⊕ M) (k : ℕ)
    {n : ℕ} (f : Fin n ↪ Fin (run e k).N)
    (hf : Finset.univ.image f ∉ (run e k).P.scheme.scheme.plan) :
    (chainLimit fun k => (run e k).A).eval (f.trans (run e k).tup) = none :=
  eval_invisible_of_master (chainLimit_consistent (run_chain e) (fun k => (run e k).hA.consistent))
    (extends_chainLimit (run_chain e) k _ _ (run e k).htup) f hf

theorem run_isModel [Infinite M] (e : ℕ → Request β M ⊕ M)
    (he : ∀ x k, ∃ m, k ≤ m ∧ e m = x) :
    (chainLimit fun k => (run e k).A).IsModel :=
  FiniteCutReceiving.isModel (run_receiving e he) inferInstance
    (chainLimit_consistent (run_chain e) (fun k => (run e k).hA.consistent))
    (run_covering e he)

/-- At every countable limit stage there is a top-free model on any countable
infinite carrier. The request alphabet is countable, not asserted computable. -/
theorem exists_topFree_model [Countable M] [Infinite M]
    (hβ : β.1.card ≤ Cardinal.aleph0) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ {n} (t : Fin n ↪ M) (p : S β.1 n), R.eval t = some p → ∀ d, p.label d ≠ ⊤ := by
  have : ∀ n : ℕ, Countable (S β.1 n) := StageType.countable_S hβ
  have : Countable {ν : Ordinal.{0} // ν < β.1} := countable_lt hβ
  have : Countable (Request β M) := by unfold Request; infer_instance
  let master : State β M → FiniteMaster knightTower β M := fun s => s.toRunState.master
  have habs : ∀ s x, ∃ t, master s ≤ master t ∧ x ∈ Set.range (master t).tuple := by
    intro s x
    by_cases hx : x ∈ Set.range s.tup
    · exact ⟨s, le_rfl, hx⟩
    · obtain ⟨t, hext, _, ht⟩ := absorb s hx
      exact ⟨t, RunState.master_extends hext, ht⟩
  have hserve : ∀ s r, (master s).chart.eval (task r).root = some (task r).base →
      ∃ t, master s ≤ master t ∧ (task r).Served (master t).chart := by
    intro s r hr
    obtain ⟨n, t, p, q, ν⟩ := r
    change s.toRunState.master.chart.eval t = some p at hr
    rw [RunState.chart_eq] at hr
    obtain ⟨s', hext, _, hs'⟩ := service s ⟨n, t, p, q, ν⟩ hr
    exact ⟨s', RunState.master_extends hext, s'.toRunState.chart_eq.symm ▸ hs'⟩
  obtain ⟨R, hc, hcover, _, hs, hfinite⟩ :=
    FiniteMasterScheduler.exists_realization master habs task hserve (initial β M)
  have hreceiving : FiniteCutReceiving R := by
    intro n t p hp q hq δ hδ hδβ
    obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < β.1 := by
      rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
      · exact False.elim (lt_irrefl _ hδ)
      · exact False.elim ((not_lt_of_ge le_top) hδβ)
      · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδβ⟩
    exact hs ⟨n, t, p, ⟨q, hq⟩, ⟨ν, hν⟩⟩ hp
  refine ⟨R, hreceiving.isModel inferInstance hc
    (hcover.toInitialSegment knightTower_permTotal hc.isVisibleFaceConsistent), ?_⟩
  intro n t p hp
  obtain ⟨s, hs⟩ := hfinite t p hp
  exact s.topFree t p (s.toRunState.chart_eq ▸ hs)

theorem exists_terminal_model [Countable M] [Infinite M]
    (hβ : β.1.card ≤ Cardinal.aleph0) :
    ∃ R : KnightRealization β M, R.IsModel ∧
      ∀ (γ : LimitStage) (hβγ : β < γ), R.NoProlongationToIn IsModelClass hβγ.le := by
  obtain ⟨R, hR, htop⟩ := exists_topFree_model (M := M) hβ
  exact ⟨R, hR, fun _ hβγ => hR.noProlongation_of_topFree hβγ htop⟩

end VaughtConjecture.Knight.TopFreeCapHenkin
