/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedMixedAmbient

/-! # Retuning a saturated strip from its owner's actual witness

An invisible image determines the source offset and the entire affine source
strip by clause 5. The prescribed witness on that strip produces a retuned
witness, rather than an assumed alignment map. Repaired composition is used
only on grade-short constructed sources; no composition principle for arbitrary
faithful transformations is assumed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.OwnerStripRetuning

open Transform Value ExtOrd SharpWitnessComposition

theorem invisible_preimage {K i : ℕ} {α : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) {x : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i)) :
    ∃ v : Ordinal.{0}, x = ofOrd (limitPart v + i) ∧
      ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
  have hinvis : ¬ SelfVis K (α x) := by
    rw [hx, selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    exact not_le_of_gt hi
  have hxinvis : ¬ SelfVis K x := by
    intro hv
    have he := hα.clause5 x K (by rw [gTop_of_le le_rfl]; exact le_top) K le_rfl
    rw [hv] at he
    exact hinvis he.symm
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (hxinvis (selfVis_bot K)).elim
  · exact (hxinvis (extVisibilityReplace_top K K)).elim
  have hv : finitePart v < K := by
    exact not_le.mp (fun h => hxinvis (selfVis_ofOrd_iff.mpr h))
  have orbit (n : ℕ) (hn : n ≤ K) :
      α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
    have he := hα.clause5 (ofOrd v) K
      (by rw [gTop_of_le le_rfl]; exact le_top) n hn
    rw [hx, extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hv,
      ordinalReplace, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact hi),
      ordinalReplace, limitPart_limitPart_add_nat] at he
    exact he
  have hoff : finitePart v = i := by
    have he := orbit (finitePart v) hv.le
    rw [decomposition, hx, ofOrd_inj] at he
    exact (Nat.cast_inj.mp ((add_right_inj (limitPart u)).mp he)).symm
  exact ⟨v, by rw [← hoff, decomposition], orbit⟩

/-- A visible lower bound at an invisible source already holds at its floor.
This includes a plateau whose interior output equals the agreement cap. -/
theorem floor_bound {K i : ℕ} {β : ExtOrd → ExtOrd}
    (hβ : Witness (gTop K) β) {v : Ordinal.{0}} (hi : i < K)
    {γ : ExtOrd} (hγ : SelfVis K γ)
    (hb : γ ≤ β (ofOrd (limitPart v + i))) : γ ≤ β (ofOrd (limitPart v)) := by
  have he := hβ.clause5 (ofOrd (limitPart v + i)) K
    (by rw [gTop_of_le le_rfl]; exact le_top) 0 (Nat.zero_le _)
  rw [extVisibilityReplace_ofOrd, visibilityReplace,
    ite_eq_left (by rw [finitePart_limitPart_add_nat]; exact hi),
    ordinalReplace, limitPart_limitPart_add_nat, Nat.cast_zero, add_zero] at he
  rw [he, ← evr_eq_self_of_selfVis hγ 0]
  exact evr_mono hb (Nat.zero_le _)

/-- Distinct original strips cannot both map affinely onto the same strip.
This is proved from the actual monotone witness, not a source-order record. -/
theorem strip_unique {K : ℕ} {α : ExtOrd → ExtOrd} (hα : Witness (gTop K) α)
    (hK : 0 < K) {u v w : Ordinal.{0}}
    (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
    (hw : ∀ n ≤ K, α (ofOrd (limitPart w + n)) = ofOrd (limitPart u + n)) :
    limitPart v = limitPart w := by
  have no_lt (v w : Ordinal.{0})
      (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
      (hw : ∀ n ≤ K, α (ofOrd (limitPart w + n)) = ofOrd (limitPart u + n)) :
      ¬ limitPart v < limitPart w := by
    intro hlt
    have he := hα.mono (ofOrd_le_ofOrd.mpr (limitPart_add_nat_le_of_lt hlt K))
    have hz := hw 0 (Nat.zero_le K)
    simp only [Nat.cast_zero, add_zero] at hz
    rw [hv K le_rfl, hz, ofOrd_le_ofOrd] at he
    have hh : limitPart u < limitPart u + K := by
      have hk : (0 : Ordinal.{0}) < (K : Ordinal.{0}) := Nat.cast_lt.mpr hK
      simpa only [add_zero] using add_lt_add_right hk (limitPart u)
    exact not_lt_of_ge he hh
  exact le_antisymm (not_lt.mp (no_lt w v hw hv)) (not_lt.mp (no_lt v w hv hw))

/-- The affine endpoint reflects order even though the witness need not be
injective elsewhere. -/
theorem endpoint_reflects {K : ℕ} {α : ExtOrd → ExtOrd} (hα : Witness (gTop K) α)
    (hK : 0 < K) {u v : Ordinal.{0}}
    (hv : ∀ n ≤ K, α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n))
    {z : ExtOrd} (hz : ofOrd (limitPart u + K) ≤ α z) :
    ofOrd (limitPart v + K) ≤ z := by
  by_contra hn
  have hlt := not_le.mp hn
  rcases ExtOrd.cases z with rfl | rfl | ⟨w, rfl⟩
  · exact not_ofOrd_le_bot _ (hα.bot ▸ hz)
  · exact (not_lt_of_ge le_top hlt).elim
  · have hKn : (K : Ordinal.{0}) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
    obtain ⟨t, ht, hwt⟩ := Ordinal.lt_add_iff hKn |>.mp (ofOrd_lt_ofOrd.mp hlt)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (ht.trans (Ordinal.natCast_lt_omega0 K))
    have hnK : n < K := Nat.cast_lt.mp ht
    have he := hz.trans (hα.mono (ofOrd_le_ofOrd.mpr hwt))
    rw [hv n hnK.le, ofOrd_le_ofOrd] at he
    exact not_lt_of_ge he (add_lt_add_right ht (limitPart u))

theorem invisible_readback {K n : ℕ} {α : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) {u v : Ordinal.{0}}
    (hv : ∀ m ≤ K, α (ofOrd (limitPart v + m)) = ofOrd (limitPart u + m))
    {z : ExtOrd} (hn : n < K) (hz : α z = ofOrd (limitPart u + n)) :
    z = ofOrd (limitPart v + n) := by
  obtain ⟨w, hw, hwo⟩ := invisible_preimage hα hn hz
  have he := strip_unique hα (Nat.zero_le n |>.trans_lt hn) hv hwo
  simpa only [he] using hw

private theorem ray_cases (K : ℕ) (u v : Ordinal.{0}) (x : ExtOrd) :
    FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x = ⊥ ∨
      ofOrd (limitPart u) ≤ x ∧ ofOrd (limitPart v) ≤
        FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v) x := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨w, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨le_top, ofOrd_le_ofOrd.mpr le_self_add⟩
  · rw [FiniteOrbitEmbedding.ray_ofOrd]
    by_cases hw : limitPart w < limitPart u
    · exact Or.inl (ite_eq_left hw)
    · rw [ite_eq_right hw]
      refine Or.inr ⟨ofOrd_le_ofOrd.mpr ((not_lt.mp hw).trans (limitPart_le w)), ?_⟩
      split_ifs <;> exact ofOrd_le_ofOrd.mpr le_self_add

/-- Construct the replacement strip directly from two owner witnesses and a
saturated invisible incidence. Every short source retains its ORIGINAL cap,
including unused strip points and all supported controller coordinates. -/
theorem exists_retuning {K i : ℕ} {α β τ : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) (hβ : Witness (gTop K) β) (hτ : Witness (gTop K) τ)
    {x γ M : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i))
    (hγ : SelfVis K γ) (hτbound : ∀ z, τ z ≤ γ) (hsat : τ (α x) = γ)
    (hp : γ ≤ β x) (hβbound : ∀ z, β z ≤ M) :
    ∃ (v : Ordinal.{0}) (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      x = ofOrd (limitPart v + i) ∧ Witness (gTop K) ρ ∧
      γ ≤ δ ∧ δ ≤ M ∧ SelfVis K δ ∧
      ρ (ofOrd (limitPart u + K)) = δ ∧
      ρ (α x) = β x ∧
      (∀ n ≤ K, ρ (ofOrd (limitPart u + n)) = β (ofOrd (limitPart v + n))) ∧
      (∀ z, Short K z → min (ρ z) γ = min (τ z) γ) ∧
      ∀ z, ρ z ≤ M := by
  obtain ⟨v, hv, _⟩ := invisible_preimage hα hi hx
  have hbf : γ ≤ β (ofOrd (limitPart v)) := floor_bound hβ hi hγ (hv ▸ hp)
  have htf : τ (ofOrd (limitPart u)) = γ := le_antisymm (hτbound _)
    (floor_bound hτ hi hγ (by rw [← hx, hsat]))
  let η := FiniteOrbitEmbedding.ray K (limitPart u) (limitPart v)
  have hη : Witness (gTop K) η :=
    (FiniteOrbitEmbedding.ray_step K (limitPart_idem v)).normalizedWitness
  let κ := (β ∘ η) ∘ trim K
  have hκ : Witness (gTop K) κ := (bounded_comp hη hβ le_rfl).witness
  have hκread (z : ExtOrd) (hz : Short K z) : κ z = β (η z) := by
    simp only [κ, Function.comp_apply, trim_of_short hz]
  let ρ := fun z => max (τ z) (κ z)
  let δ := β (ofOrd (limitPart v + K))
  have hδ : γ ≤ δ := hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add))
  have hδvis : SelfVis K δ := by
    have he := hβ.clause5 (ofOrd (limitPart v + K)) K
      (by rw [gTop_of_le le_rfl]; exact le_top) K le_rfl
    have hvv : SelfVis K (ofOrd (limitPart v + K)) := by
      rw [selfVis_ofOrd_iff, finitePart_limitPart_add_nat]
    rw [hvv] at he
    exact he.symm
  have hstrip (n : ℕ) (hn : n ≤ K) :
      ρ (ofOrd (limitPart u + n)) = β (ofOrd (limitPart v + n)) := by
    have hshort : Short K (ofOrd (limitPart u + n)) :=
      Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; exact hn⟩)
    have he : η (ofOrd (limitPart u + n)) = ofOrd (limitPart v + n) := by
      simp only [η, FiniteOrbitEmbedding.ray_ofOrd, limitPart_limitPart_add_nat,
        lt_self_iff_false, ite_false, ite_true, finitePart_limitPart_add_nat, min_eq_left hn]
    change max _ _ = _
    rw [hκread _ hshort, he, max_eq_right]
    exact (hτbound _).trans (hbf.trans (hβ.mono (ofOrd_le_ofOrd.mpr le_self_add)))
  have hcap (z : ExtOrd) (hz : Short K z) : min (ρ z) γ = min (τ z) γ := by
    change min (max _ _) γ = _
    rw [hκread _ hz]
    rcases ray_cases K u v z with he | ⟨hzu, hzv⟩
    · change η z = ⊥ at he
      rw [he, hβ.bot, max_bot_right]
    · have htz : τ z = γ := le_antisymm (hτbound _) (htf ▸ hτ.mono hzu)
      have hbz : γ ≤ β (η z) := hbf.trans (hβ.mono hzv)
      rw [htz, max_eq_right hbz, min_eq_right hbz, min_self]
  refine ⟨v, ρ, δ, hv, hτ.max hκ, hδ, hβbound _, hδvis, hstrip K le_rfl,
    ?_, hstrip, hcap, ?_⟩
  · rw [hx, hstrip i hi.le, ← hv]
  · intro z
    apply max_le ((hτbound z).trans (hδ.trans (hβbound _)))
    -- The repaired composite has its bounded range even off the short grid.
    exact hβbound _

/-- The same constructed retuning reads EVERY occurrence from the saturated
strip, not just the occurrence used to choose it. Values beyond the endpoint
have the required prescribed-witness lower bound, derived from source order. -/
theorem exists_retuning_with_transfer {K i : ℕ} {α β τ : ExtOrd → ExtOrd}
    (hα : Witness (gTop K) α) (hβ : Witness (gTop K) β) (hτ : Witness (gTop K) τ)
    {x γ M : ExtOrd} {u : Ordinal.{0}} (hi : i < K)
    (hx : α x = ofOrd (limitPart u + i))
    (hγ : SelfVis K γ) (hτbound : ∀ z, τ z ≤ γ) (hsat : τ (α x) = γ)
    (hp : γ ≤ β x) (hβbound : ∀ z, β z ≤ M) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd), Witness (gTop K) ρ ∧
      γ ≤ δ ∧ δ ≤ M ∧ SelfVis K δ ∧ ρ (ofOrd (limitPart u + K)) = δ ∧
      (∀ z n, n < K → α z = ofOrd (limitPart u + n) → ρ (α z) = β z) ∧
      (∀ z, ofOrd (limitPart u + K) ≤ α z → δ ≤ β z) ∧
      (∀ z, Short K z → min (ρ z) γ = min (τ z) γ) ∧ ∀ z, ρ z ≤ M := by
  obtain ⟨v, ρ, δ, hv, hρ, hγδ, hδM, hδvis, hend, _, hstrip, hcap, hbound⟩ :=
    exists_retuning hα hβ hτ hi hx hγ hτbound hsat hp hβbound
  obtain ⟨w, hw, hwo⟩ := invisible_preimage hα hi hx
  have he : limitPart w = limitPart v := by
    have heq := congrArg limitPart (ofOrd_inj.mp (hw.symm.trans hv))
    simpa only [limitPart_limitPart_add_nat] using heq
  have horbit (n : ℕ) (hn : n ≤ K) :
      α (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
    simpa only [he] using hwo n hn
  refine ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, ?_, ?_, hcap, hbound⟩
  · intro z n hn hz
    have hread := invisible_readback hα horbit hn hz
    exact (congrArg ρ hz).trans ((hstrip n hn.le).trans (congrArg β hread).symm)
  · intro z hz
    have hlow := endpoint_reflects hα (Nat.zero_le i |>.trans_lt hi) horbit hz
    exact (hend.symm.trans (hstrip K le_rfl)).le.trans (hβ.mono hlow)

/-- The two witnesses consumed above are obtained from the actual locality
clauses at the prescribed owner. The source subcut bound is stated explicitly;
the arbitrary-face theorem must derive it from the grid geometry. -/
theorem exists_retuning_of_locality
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} (c : Cell D)
    {s p : D.below (D.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (d : D.below (D.cell c)) {i : ℕ} {u : Ordinal.{0}}
    (hi : i < D.grade c) (hsd : s d = ofOrd (limitPart u + i))
    (hunder : s d ≤ s ⟨c, GradedLe.refl _⟩)
    {γ : ExtOrd} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop (D.grade c)) τ)
    (hγ : SelfVis (D.grade c) γ) (hτbound : ∀ z, τ z ≤ γ)
    (hsat : τ (s d) = γ) (hpd : γ ≤ p d) (hpc : γ < p ⟨c, GradedLe.refl _⟩) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ (ofOrd (limitPart u + D.grade c)) = δ ∧
      ρ (s d) = min (p d) (p ⟨c, GradedLe.refl _⟩) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  obtain ⟨α, hα, _, hαread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := s) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hs.orderly self).symm (hs.locality self)
  obtain ⟨β, hβ, hβbound, hβread⟩ := exists_bounded_exact_capped_witness
    (grade := fun x : D.below (D.cell c) => D.grade x.1) (p := p) (c := self)
    (fun x : D.below (D.cell c) => x.2.2) (hp.orderly self).symm (hp.locality self)
  have ha : α (sem.E c d) = s d := (hαread d).trans (min_eq_left hunder)
  have hb : β (sem.E c d) = min (p d) (p self) := hβread d
  obtain ⟨_, ρ, δ, _, hρ, hγδ, hδM, hδvis, hend, hread, _, hcap, _⟩ :=
    exists_retuning hα hβ hτ hi (ha.trans hsd) hγ hτbound (ha ▸ hsat)
      (hb ▸ le_min hpd hpc.le) hβbound
  exact ⟨ρ, δ, hρ, hγδ, hδM, hδvis, hend, by rwa [ha, hb] at hread, hcap⟩

/-- A proper owner at the upper grade has a source in the actual paired grid.
Coding alone would not suffice; its lawful grade and shortness fix the offset. -/
theorem profile_owner_grid {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {K : ℕ}
    (a : PairedBoundarySections.Profile sem K) (c : Cell D) (hc : D.grade c = K) :
    a.val c ∈ PairedSlotComparison.sourceGrid K (Fintype.card (Cell D)) := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp (a.property.2.1 c) with hb | ⟨b, n, hb, _, he⟩
  · rw [hb]
    exact PairedSlotComparison.sourceGrid_bot _ _
  · have hv : SelfVis K (a.val c) := hc ▸ (a.property.1.orderly c).symm
    have hlo : K ≤ n := by
      rwa [he, selfVis_ofOrd_iff, finitePart_mul_add] at hv
    have hhi : n ≤ K := by
      rcases a.property.2.2 c with hz | hz | ⟨w, hw, hshort⟩
      · exact (ofOrd_ne_bot _ (he.symm.trans hz)).elim
      · exact (ofOrd_ne_top _ (he.symm.trans hz)).elim
      · have heq := ofOrd_inj.mp (he.symm.trans hw)
        simpa only [← heq, finitePart_mul_add] using hshort
    have hn : n = K := Nat.le_antisymm hhi hlo
    rw [he, hn]
    exact PairedSlotComparison.sourceGrid_endpoint (hb.trans (Nat.le_succ _))

/-- First-cut minimality gives the source-under-owner bound on every actual
subcut occurrence. It makes no assertion about unused off-grid decodings. -/
theorem source_under_owner {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} {K : ℕ}
    (a : PairedBoundarySections.Profile sem K) (c : Cell D) (hc : D.grade c = K)
    {τ : ExtOrd → ExtOrd} {h γ : ExtOrd}
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid K (Fintype.card (Cell D)),
      z < h → τ z < γ) (hactive : γ ≤ τ (a.val c))
    (d : Cell D) (hd : a.val d < h) : a.val d ≤ a.val c := by
  have hh : h ≤ a.val c := by
    by_contra hn
    exact not_lt_of_ge hactive (hfirst _ (profile_owner_grid a c hc) (not_le.mp hn))
  exact hd.le.trans hh

/-- In the saturated-invisible branch, all retuning inputs come from the
lawful prescription, the actual source profile and its extracted cap receipt.
Neither a retuning map nor the source-under-owner bound is supplied. This
constructs the strip operator, not the subsequent coded whole completion. -/
theorem exists_retuning_from_prescription
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} (c : Cell D)
    (a : PairedBoundarySections.Profile sem (D.grade c))
    {p : D.below (D.cell c) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    {τ : ExtOrd → ExtOrd} {h γ : ExtOrd}
    (hτ : Witness (gTop (D.grade c)) τ) (hγ : SelfVis (D.grade c) γ)
    (hτbound : ∀ z, τ z ≤ γ)
    (hfirst : ∀ z ∈ PairedSlotComparison.sourceGrid (D.grade c) (Fintype.card (Cell D)),
      z < h → τ z < γ)
    (hface : ∀ e : D.below (D.cell c), τ (a.val e.1) = min (p e) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (d : D.below (D.cell c)) {i : ℕ} {u : Ordinal.{0}}
    (hi : i < D.grade c) (hsd : a.val d.1 = ofOrd (limitPart u + i))
    (hsub : a.val d.1 < h) (hpd : γ ≤ p d) :
    ∃ (ρ : ExtOrd → ExtOrd) (δ : ExtOrd),
      Witness (gTop (D.grade c)) ρ ∧ γ ≤ δ ∧ δ ≤ p ⟨c, GradedLe.refl _⟩ ∧
      SelfVis (D.grade c) δ ∧ ρ (ofOrd (limitPart u + D.grade c)) = δ ∧
      ρ (a.val d.1) = min (p d) (p ⟨c, GradedLe.refl _⟩) ∧
      ∀ z, Short (D.grade c) z → min (ρ z) γ = min (τ z) γ := by
  have hactive : γ ≤ τ (a.val c) := by
    rw [hface ⟨c, GradedLe.refl _⟩, min_eq_right hpc.le]
  have hunder := source_under_owner a c rfl hfirst hactive d.1 hsub
  exact exists_retuning_of_locality c (a.property.1.toBelow (D.cell c)) hp d hi hsd
    hunder hτ hγ hτbound (by rw [hface d, min_eq_right hpd]) hpd hpc

end VaughtConjecture.Knight.OwnerStripRetuning
