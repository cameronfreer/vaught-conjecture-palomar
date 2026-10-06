/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OneBlockReceiving
public import VaughtConjecture.Knight.FiniteCoverCoordinates
public import VaughtConjecture.Knight.ModelEmpty
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Sentence
public import VaughtConjecture.Knight.VisibleFaceOneStep
public import VaughtConjecture.CountableQuantifierRank
public import VaughtConjecture.InfinitaryRelabel
public import InfinitaryLogic.Karp.CarrierTheorem

/-! # Logical comparison from one-block receiving

A common labelled chart at `blockStage (ω * η)` gives back-and-forth equivalence
through `η`, and hence agreement on sentences of quantifier rank at most `η`.
A finite cover costs one block per added point. No terminal classification,
stopping-rank boundedness, or descriptive thinness result is used here.

The old `OneBlockReadback` module reexports this API together with its historical
rank applications. All moved theorem statements and proofs are unchanged. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower FirstOrder Language Structure KnightRealization Cardinal

universe w u v u'

/-! ## Common charts: reduction and symmetry -/

theorem HasCommonChart.reduct {α β : LimitStage} (h : β ≤ α) {M N : Type w}
    {R : KnightRealization α M} {R' : KnightRealization α N} {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (hc : HasCommonChart R R' a b) :
    HasCommonChart (R.reduct h) (R'.reduct h) a b := by
  obtain ⟨m, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  refine ⟨m, ta, tb, σ, reduceType β.2 h p, ?_, ?_, ha, hb⟩
  · rw [Realization.reduct_eval, hta]; rfl
  · rw [Realization.reduct_eval, htb]; rfl

theorem HasCommonChart.symm {α : LimitStage} {M N : Type w} {R : KnightRealization α M}
    {R' : KnightRealization α N} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hc : HasCommonChart R R' a b) : HasCommonChart R' R b a := by
  obtain ⟨m, ta, tb, σ, p, hta, htb, ha, hb⟩ := hc
  exact ⟨m, tb, ta, σ, p, htb, hta, hb, ha⟩

/-! ## Extending an embedding of coordinates by one coordinate -/

/-- A one-coordinate extension of a coordinate embedding, transported to a tuple, is the
one-point extension of the transported tuple. -/
theorem snoc_trans {M : Type w} {n m : ℕ} (f : Fin n ↪ Fin m) (c : Fin m) (hc : c ∉ Set.range f)
    (u : Fin m ↪ M) :
    (snoc f c hc).trans u =
      snoc (f.trans u) (u c) (by rintro ⟨i, hi⟩; exact hc ⟨i, u.injective hi⟩) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [Function.Embedding.trans_apply]
  | cast j => simp [Function.Embedding.trans_apply]

/-! ## The multi-point transfer: one block per point -/

/-- **Transfer of a labelled cover, one block per point.**  At `blockStage (β + r)`, with a
labelled tuple `u` of type `Q` whose coordinate face `f` is labelled `p` and matched by `tb` on
the other side, `r` applications of OBR along a saturated visible chain of `Q`'s plan produce a
tuple `ub` over `tb` whose reduction to `blockStage β` is that of `Q`. -/
theorem transfer_of_obr (h : OneBlockReadback.{w}) (β : Ordinal.{0}) (r : ℕ) :
    ∀ {M N : Type w} (W : KnightRealization (blockStage (β + r)) M)
      (W' : KnightRealization (blockStage (β + r)) N), W.IsModel → W'.IsModel →
      ∀ {n m : ℕ} (u : Fin m ↪ M) (Q : S (blockStage (β + r)).1 m), W.eval u = some Q →
        ∀ (f : Fin n ↪ Fin m), n + r = m →
          ∀ (tb : Fin n ↪ N) (p : S (blockStage (β + r)).1 n),
            W.eval (f.trans u) = some p → W'.eval tb = some p →
            ∃ (ub : Fin m ↪ N) (Q' : S (blockStage (β + r)).1 m), f.trans ub = tb ∧
              W'.eval ub = some Q' ∧
              reduceType (blockStage β).2 (blockStage_mono le_self_add) Q' =
                reduceType (blockStage β).2 (blockStage_mono le_self_add) Q := by
  induction r with
  | zero =>
    intro M N W W' hW hW' n m u Q hu f hcard tb p hta htb
    subst hcard
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp f.injective
    let e : Fin n ≃ Fin (n + 0) := Equiv.ofBijective f hbij
    let g : Fin (n + 0) ↪ Fin n := e.symm.toEmbedding
    have hfg : f.trans g = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i => e.symm_apply_apply i
    have hgf : g.trans f = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i => e.apply_symm_apply i
    refine ⟨g.trans tb, Q, ?_, ?_, rfl⟩
    · rw [← Function.Embedding.trans_assoc, hfg, Function.Embedding.refl_trans]
    · have h1 := hW'.consistent tb p g htb
      have h2 : typeMap f Q = some p := by
        have := hW.consistent u Q f hu
        rw [hta] at this
        exact this.symm
      rw [h1]
      change typeMap g p = some Q
      rw [typeMap_trans g f Q p h2, hgf, typeMap_refl]
  | succ r ih =>
    intro M N W W' hW hW' n m u Q hu f hcard tb p hta htb
    -- the visible face of `f` and a one-coordinate visible superface
    have hp : typeMap f Q = some p := by
      have := hW.consistent u Q f hu
      rw [hta] at this
      exact this.symm
    have hvis : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hp]; rfl)
    have hcardF : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    have hne : Finset.univ.image f ≠ (Finset.univ : Finset (Fin m)) := by
      intro heq
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcardF
      omega
    obtain ⟨C, hC, hsub, hcardC⟩ :=
      Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hvis hne
    obtain ⟨c, hcC, hcF⟩ := Finset.exists_of_ssubset hsub
    have hcf : c ∉ Set.range f := by
      rintro ⟨i, rfl⟩
      exact hcF (Finset.mem_image_of_mem f (Finset.mem_univ i))
    have himage : Finset.univ.image (snoc f c hcf) = C := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        induction i using Fin.lastCases with
        | last => rw [snoc_apply_last]; exact hcC
        | cast j =>
          rw [snoc_apply_castSucc]
          exact hsub.subset (Finset.mem_image_of_mem f (Finset.mem_univ j))
      · rw [hcardC, hcardF, Finset.card_image_of_injective _ (snoc f c hcf).injective,
          Finset.card_univ, Fintype.card_fin]
    have hvis' : (typeMap (snoc f c hcf) Q).isSome :=
      (typeMap_isSome_iff _ Q).mpr (himage ▸ hC)
    obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp hvis'
    have hc' : u c ∉ Set.range (f.trans u) := by
      rintro ⟨i, hi⟩
      exact hcf ⟨i, u.injective hi⟩
    have hta' : W.eval (snoc (f.trans u) (u c) hc') = some p' := by
      rw [← snoc_trans f c hcf u]
      have := hW.consistent u Q (snoc f c hcf) hu
      rw [this]
      exact hp'
    -- OBR at block `β + r`
    have hδ : blockStage (β + ↑(r + 1)) = blockStage (β + ↑r + 1) := by
      rw [Nat.cast_succ, add_assoc]
    have hγ : blockStage (β + ↑r) ≤ blockStage (β + ↑(r + 1)) :=
      blockStage_mono (by rw [Nat.cast_succ, ← add_assoc]; exact le_self_add)
    obtain ⟨y', hy', q', hq', hred⟩ :=
      h.at (β + ↑r) hδ hγ W W' hW hW' (f.trans u) tb p hta htb (u c) hc' p' hta'
    -- reduce one block and apply the induction hypothesis
    have hu₁ : (W.reduct hγ).eval u = some (reduceType (blockStage (β + ↑r)).2 hγ Q) := by
      rw [Realization.reduct_eval, hu]; rfl
    have hta₁ : (W.reduct hγ).eval ((snoc f c hcf).trans u) =
        some (reduceType (blockStage (β + ↑r)).2 hγ p') := by
      rw [snoc_trans, Realization.reduct_eval, hta']; rfl
    have htb₁ : (W'.reduct hγ).eval (snoc tb y' hy') =
        some (reduceType (blockStage (β + ↑r)).2 hγ p') := by
      rw [Realization.reduct_eval, hq', ← hred]; rfl
    obtain ⟨ub, Q₁', hfub, hub, hred₁⟩ := ih (W.reduct hγ) (W'.reduct hγ) (hW.reduct hγ)
      (hW'.reduct hγ) u _ hu₁ (snoc f c hcf) (by omega) (snoc tb y' hy') _ hta₁ htb₁
    rw [Realization.reduct_eval] at hub
    obtain ⟨Q', hQ', hQ'red⟩ := Option.map_eq_some_iff.mp hub
    have hQ'red' : reduceType (blockStage (β + ↑r)).2 hγ Q' = Q₁' := hQ'red
    refine ⟨ub, Q', ?_, hQ', ?_⟩
    · have hf : f = Fin.castSuccEmb.trans (snoc f c hcf) := (castSuccEmb_trans_snoc f c hcf).symm
      rw [hf, Function.Embedding.trans_assoc, hfub, castSuccEmb_trans_snoc]
    · have e1 : reduceType (blockStage β).2 (blockStage_mono le_self_add) Q' =
          reduceType (blockStage β).2 (blockStage_mono le_self_add)
            (reduceType (blockStage (β + ↑r)).2 hγ Q') :=
        (reduceType_trans _ _ _ _ Q').symm
      have e2 : reduceType (blockStage β).2 (blockStage_mono le_self_add) Q =
          reduceType (blockStage β).2 (blockStage_mono le_self_add)
            (reduceType (blockStage (β + ↑r)).2 hγ Q) :=
        (reduceType_trans _ _ _ _ Q).symm
      rw [e1, e2, hQ'red']
      exact hred₁

/-! ## Back-and-forth equivalence with the `ω · η` budget -/

/-- **The forth step at depth `η + 1`**: from a common chart at `blockStage (ω · (η + 1))`, an
arbitrary carrier element is included through a labelled cover, transferred one block per point
down to `blockStage (ω · η)`, where the induction hypothesis applies. -/
theorem forth_of_obr (h : OneBlockReadback.{w}) (η : Ordinal.{0})
    (ih : ∀ {M N : Type w} (W : KnightRealization (blockStage (Ordinal.omega0 * η)) M)
      (W' : KnightRealization (blockStage (Ordinal.omega0 * η)) N), W.IsModel → W'.IsModel →
      ∀ {n : ℕ} {a : Fin n → M} {b : Fin n → N}, HasCommonChart W W' a b →
        @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _))) N
          (structureOf (W'.reduct (omegaStage_le _))) η n a b)
    {M N : Type w} (W : KnightRealization (blockStage (Ordinal.omega0 * (η + 1))) M)
    (W' : KnightRealization (blockStage (Ordinal.omega0 * (η + 1))) N) (hW : W.IsModel)
    (hW' : W'.IsModel) {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hcc : HasCommonChart W W' a b)
    (m : M) :
    ∃ m' : N, @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _))) N
      (structureOf (W'.reduct (omegaStage_le _))) η (n + 1)
      (Fin.snoc (α := fun _ => M) a m) (Fin.snoc (α := fun _ => N) b m') := by
  have h₁ : blockStage (Ordinal.omega0 * η) ≤ blockStage (Ordinal.omega0 * (η + 1)) :=
    blockStage_mono (mul_le_mul_right le_self_add _)
  -- a common chart at `blockStage (ω · η)` for the extended pair gives the conclusion
  have key : ∀ (m' : N), HasCommonChart (W.reduct h₁) (W'.reduct h₁)
      (Fin.snoc (α := fun _ => M) a m) (Fin.snoc (α := fun _ => N) b m') →
      @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _))) N
        (structureOf (W'.reduct (omegaStage_le _))) η (n + 1)
        (Fin.snoc (α := fun _ => M) a m) (Fin.snoc (α := fun _ => N) b m') := by
    intro m' hc
    have := ih (W.reduct h₁) (W'.reduct h₁) (hW.reduct h₁) (hW'.reduct h₁) hc
    rwa [Realization.reduct_reduct, Realization.reduct_reduct] at this
  obtain ⟨k, ta, tb, σ, p, hta, htb, ha, hb⟩ := hcc
  by_cases hmem : m ∈ Set.range ta
  · -- a repeated point of the container
    obtain ⟨j₀, hj₀⟩ := hmem
    refine ⟨tb j₀, key (tb j₀) ?_⟩
    refine (HasCommonChart.reduct h₁ ⟨k, ta, tb, Fin.snoc (α := fun _ => Fin k) σ j₀, p, hta, htb,
      ?_, ?_⟩)
    · funext i
      induction i using Fin.lastCases with
      | last => simp [hj₀]
      | cast j => simp [← ha]
    · funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simp [← hb]
  · -- a fresh point: cover it, transfer the cover one block per point
    obtain ⟨k', s, hs, hsome⟩ := hW.covering (snoc ta m hmem)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    have hseg : (initSeg k k').trans s = ta := initSeg_trans_of_castAdd hmem hs
    set δ₂ : LimitStage := blockStage (Ordinal.omega0 * η + ↑(k' + 1)) with hδ₂
    have h₂ : δ₂ ≤ blockStage (Ordinal.omega0 * (η + 1)) :=
      blockStage_mono (by rw [mul_add_one]; gcongr; exact (Ordinal.natCast_lt_omega0 _).le)
    have hu₂ : (W.reduct h₂).eval s = some (reduceType δ₂.2 h₂ P) := by
      rw [Realization.reduct_eval, hP]; rfl
    have hta₂ : (W.reduct h₂).eval ((initSeg k k').trans s) = some (reduceType δ₂.2 h₂ p) := by
      rw [hseg, Realization.reduct_eval, hta]; rfl
    have htb₂ : (W'.reduct h₂).eval tb = some (reduceType δ₂.2 h₂ p) := by
      rw [Realization.reduct_eval, htb]; rfl
    obtain ⟨ub, Q', hfub, hub, hred⟩ := transfer_of_obr h (Ordinal.omega0 * η) (k' + 1)
      (W.reduct h₂) (W'.reduct h₂) (hW.reduct h₂) (hW'.reduct h₂) s _ hu₂ (initSeg k k')
      (by omega) tb _ hta₂ htb₂
    have h₃ : blockStage (Ordinal.omega0 * η) ≤ δ₂ := blockStage_mono le_self_add
    refine ⟨ub (newPos k k'), key _ ?_⟩
    have hcomp : (W.reduct h₂).reduct h₃ = W.reduct h₁ := Realization.reduct_reduct _ _ W
    have hcomp' : (W'.reduct h₂).reduct h₃ = W'.reduct h₁ := Realization.reduct_reduct _ _ W'
    rw [← hcomp, ← hcomp']
    refine ⟨k + 1 + k', s, ub, Fin.snoc (α := fun _ => Fin (k + 1 + k'))
      (fun i => initSeg k k' (σ i)) (newPos k k'),
      reduceType (blockStage (Ordinal.omega0 * η)).2 h₃ (reduceType δ₂.2 h₂ P), ?_, ?_, ?_, ?_⟩
    · rw [Realization.reduct_eval, hu₂]; rfl
    · rw [Realization.reduct_eval, hub, ← hred]; rfl
    · funext i
      induction i using Fin.lastCases with
      | last =>
        have := congrArg (fun t : Fin (k + 1) ↪ M => t (Fin.last k)) hs
        simp only [Function.Embedding.trans_apply, snoc_apply_last] at this
        simpa [newPos] using this
      | cast j =>
        have := congrArg (fun t : Fin k ↪ M => t (σ j)) hseg
        simp only [Function.Embedding.trans_apply] at this
        simp [this, ← ha]
    · funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast j =>
        have := congrArg (fun t : Fin k ↪ N => t (σ j)) hfub
        simp only [Function.Embedding.trans_apply] at this
        simp [this, ← hb]

/-- **Back-and-forth equivalence from OBR with the `ω · η` budget**: a common chart at
`blockStage (ω · η)` gives back-and-forth equivalence through `η` in Knight's language on the
`ω`-reducts. -/
theorem bfEquiv_of_obr (h : OneBlockReadback.{w}) (η : Ordinal.{0}) :
    ∀ {M N : Type w} (W : KnightRealization (blockStage (Ordinal.omega0 * η)) M)
      (W' : KnightRealization (blockStage (Ordinal.omega0 * η)) N), W.IsModel → W'.IsModel →
      ∀ {n : ℕ} {a : Fin n → M} {b : Fin n → N}, HasCommonChart W W' a b →
        @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _))) N
          (structureOf (W'.reduct (omegaStage_le _))) η n a b := by
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro M N W W' hW hW' n a b hcc
    let _ : knightLang.Structure M := structureOf (W.reduct (omegaStage_le _))
    let _ : knightLang.Structure N := structureOf (W'.reduct (omegaStage_le _))
    rw [BFEquiv.zero]
    exact sameAtomicType_of_commonChart (hW.consistent_reduct _) (hW'.consistent_reduct _)
      (hcc.reduct _)
  | add_one η ih =>
    intro M N W W' hW hW' n a b hcc
    have h₁ : blockStage (Ordinal.omega0 * η) ≤ blockStage (Ordinal.omega0 * (η + 1)) :=
      blockStage_mono (mul_le_mul_right le_self_add _)
    have hlow : @BFEquiv knightLang M (structureOf (W.reduct (omegaStage_le _))) N
        (structureOf (W'.reduct (omegaStage_le _))) η n a b := by
      have := ih (W.reduct h₁) (W'.reduct h₁) (hW.reduct h₁) (hW'.reduct h₁) (hcc.reduct h₁)
      rwa [Realization.reduct_reduct, Realization.reduct_reduct] at this
    let _ : knightLang.Structure M := structureOf (W.reduct (omegaStage_le _))
    let _ : knightLang.Structure N := structureOf (W'.reduct (omegaStage_le _))
    have hs := BFEquiv.succ (L := knightLang) (M := M) (N := N) η a b
    rw [Order.succ_eq_add_one] at hs
    refine hs.mpr ⟨hlow, fun m => forth_of_obr h η ih W W' hW hW' hcc m, fun m' => ?_⟩
    obtain ⟨m, hm⟩ := forth_of_obr h η ih W' W hW' hW hcc.symm m'
    exact ⟨m, hm.symm⟩
  | limit η hlim ih =>
    intro M N W W' hW hW' n a b hcc
    let _ : knightLang.Structure M := structureOf (W.reduct (omegaStage_le _))
    let _ : knightLang.Structure N := structureOf (W'.reduct (omegaStage_le _))
    rw [BFEquiv.limit η hlim]
    intro β hβ
    have h₁ : blockStage (Ordinal.omega0 * β) ≤ blockStage (Ordinal.omega0 * η) :=
      blockStage_mono (mul_le_mul_right hβ.le _)
    have := ih β hβ (W.reduct h₁) (W'.reduct h₁) (hW.reduct h₁) (hW'.reduct h₁) (hcc.reduct h₁)
    rwa [Realization.reduct_reduct, Realization.reduct_reduct] at this

/-! ## Compatibility with the general formula-rank theorem -/

/-- The quantifier rank of an `L_{ω₁ω}` formula (countable branching) is a countable ordinal. -/
theorem qrank_lt_ord_aleph_one {L : Language.{u, v}} {γ : Type u'} :
    ∀ {n : ℕ} (φ : L.BoundedFormulaInf ℕ γ n), φ.qrank < (aleph 1).ord :=
  VaughtConjecture.qrank_lt_ord_aleph_one

/-! ## Sentence agreement -/

/-- **Models at `blockStage (ω · η)` agree on Knight's sentences of rank at most `η`**, on the
theory's structures of their `ω`-reducts: the empty tuples carry the same (unique) label. -/
theorem agree_sentence_of_obr (h : OneBlockReadback.{0}) {η : Ordinal.{0}} {M N : Type}
    (W : KnightRealization (blockStage (Ordinal.omega0 * η)) M)
    (W' : KnightRealization (blockStage (Ordinal.omega0 * η)) N) (hW : W.IsModel)
    (hW' : W'.IsModel) (φ : knightLang.Sentenceω) (hφ : φ.qrank ≤ η) :
    (@Sentenceω.Realize knightLang φ M (structureOf (W.reduct (omegaStage_le _))) ↔
      @Sentenceω.Realize knightLang φ N (structureOf (W'.reduct (omegaStage_le _)))) := by
  let instM : knightLang.Structure M := structureOf (W.reduct (omegaStage_le _))
  let instN : knightLang.Structure N := structureOf (W'.reduct (omegaStage_le _))
  -- the empty common chart
  obtain ⟨p, hp⟩ := exists_eval_empty_at hW
  obtain ⟨p', hp'⟩ := exists_eval_empty_at hW'
  have hcc : HasCommonChart W W' (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
    refine ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, Fin.elim0, p, hp, ?_,
      funext fun i => i.elim0, funext fun i => i.elim0⟩
    rw [hp', Subsingleton.elim p' p]
  have hbf := bfEquiv_of_obr h η W W' hW hW' hcc
  have key := BFEquiv_implies_agreeQR η Fin.elim0 Fin.elim0 hbf (ι := ℕ)
    (φ.relabelFree (Empty.elim : Empty → Fin 0))
    (by rw [BoundedFormulaInf.qrank_relabelFree]; exact hφ)
  have eM : (Fin.elim0 : Fin 0 → M) ∘ (Empty.elim : Empty → Fin 0) = Empty.elim :=
    funext fun e => e.elim
  have eN : (Fin.elim0 : Fin 0 → N) ∘ (Empty.elim : Empty → Fin 0) = Empty.elim :=
    funext fun e => e.elim
  change BoundedFormulaInf.Realize (φ.relabelFree Empty.elim) Fin.elim0 Fin.elim0 ↔
    BoundedFormulaInf.Realize (φ.relabelFree Empty.elim) Fin.elim0 Fin.elim0 at key
  rw [BoundedFormulaInf.realize_relabelFree, BoundedFormulaInf.realize_relabelFree, eM, eN] at key
  exact key

end VaughtConjecture.Knight
