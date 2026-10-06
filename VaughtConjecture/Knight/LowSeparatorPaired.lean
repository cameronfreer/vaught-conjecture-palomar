/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyNormalization
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # The LOW separator on the paired-slot catalogue (grades `K ≥ 2`)

The scalar separator argument of newapproach18 new41 §2 on the existing canonical paired-slot
catalogue (`CanonicalPairedProfiles.inventory`), for a complete field type `X` with a designated
cutoff field `b` and a designated set `N` of non-top donor fields:

* **The partner profile** (`partner`): from a canonical complete profile `s` with
  `h := R_K(M(s)) < s b`, lower only the cutoff field to `h` and normalize.  The partner is
  canonical (`partner_mem`), **its cutoff is exactly `h`** (`partner_cutoff`): `h` is the
  `K`-endpoint `ω·bl + K` of the block `bl` hosting the non-top maximum in `s`'s own canonical
  code (`cutoffCut_eq_endpoint`), and inserting that endpoint into the inventory changes neither
  the orbit flags (its offset is `K`, so it witnesses no orbit) nor the keys below its own key,
  while removing the old cutoff value — which lies at or above the next block — changes nothing
  below `ω·bl + K + 1` (`rank_congr_below`); so its paired code has block `bl` and offset `K`.
  This is represented-endpoint fixation on the actual inventory, not an assumption that
  normalization fixes arbitrary unused endpoints.  All future fields are retained in every
  comparison, since `X` is the complete field type.
* **Prefix agreement** `t ∧ h = s ∧ h` (`partner_cap`, by `normalize_cap` at the grid cut `h`),
  and **the common cut** `κ_K(s, t) = h` (`cut_partner`), `κ` being `SourcePrefixRows.cut` on the
  paired source grid, which coincides with `PairedSlotComparison.largestCommonCut` on canonical
  profiles (`largestCommonCut_eq_cut`).
* **Strict comparison activates LOW** (`activation_of_cut_lt`, `activation_of_chart_lt`): for
  any profile `a`, `κ(a, t) < κ(a, s)` forces `κ(a, t) = h < κ(a, s)` (the ultrametric
  identity), hence every non-top donor field of `a` equals that of `s` (all lie below `h`),
  `M(a) = M(s)`, and `a b > h`: `M(a) < a b`.  A monotone chart reading `κ(a, t)` strictly below
  `κ(a, s)` gives the same.

The family section instantiates this on KVC's `LowOnly.Family`: the partner state is admissible
and canonical, and the strict comparison at an admitted serving state activates its LOW
relation; a chart through `K` reading the private owner and low source as `⊤` then reads every
designated donor top as `⊤` (`donor_top_readback`).  No physical receiver is used: the actual
chart equations `σ (κ(a, t)) < σ (κ(a, s))`, `σ (a c) = ⊤`, `σ (a r) = ⊤` are hypotheses. -/

@[expose] public section

namespace VaughtConjecture.Knight.LowSeparator

open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SharpWitnessComposition
  SourcePrefixRows

noncomputable section

/-! ## The non-top donor maximum and the rounded frontier -/

section Scalar

variable {X : Type*} [Fintype X] (K : ℕ) (N : X → Prop) [DecidablePred N] (b : X)

/-- The non-top donor maximum of a complete profile. -/
def donorMax (s : X → ExtOrd) : ExtOrd := (Finset.univ.filter N).sup s

theorem le_donorMax (s : X → ExtOrd) {d : X} (hd : N d) : s d ≤ donorMax N s :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

theorem donorMax_le {s : X → ExtOrd} {c : ExtOrd} (h : ∀ d, N d → s d ≤ c) : donorMax N s ≤ c :=
  Finset.sup_le fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_congr {s a : X → ExtOrd} (h : ∀ d, N d → a d = s d) :
    donorMax N a = donorMax N s :=
  Finset.sup_congr rfl fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_ne_top {s : X → ExtOrd} (hs : ∀ d, s d ≠ ⊤) : donorMax N s ≠ ⊤ :=
  ne_of_lt ((Finset.sup_lt_iff bot_lt_top).mpr fun d _ => lt_top_iff_ne_top.mpr (hs d))

/-- The non-top maximum is bottom or attained. -/
theorem donorMax_cases (s : X → ExtOrd) :
    donorMax N s = ⊥ ∨ ∃ d, N d ∧ s d = donorMax N s := by
  by_cases hne : (Finset.univ.filter N).Nonempty
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup _ hne s
    exact Or.inr ⟨d, (Finset.mem_filter.mp hd).2, he.symm⟩
  · left
    unfold donorMax
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]

/-- The rounded frontier `R_K(M(s))`. -/
def cutoffCut (s : X → ExtOrd) : ExtOrd := extVisibilityReplace (donorMax N s) K K

theorem donorMax_le_cutoffCut (s : X → ExtOrd) : donorMax N s ≤ cutoffCut K N s :=
  TopSupport.le_evr_self _ _

theorem cutoffCut_selfVis (s : X → ExtOrd) : SelfVis K (cutoffCut K N s) :=
  TopSupport.selfVis_evr_self K _

theorem cutoffCut_ne_top {s : X → ExtOrd} (hs : ∀ d, s d ≠ ⊤) : cutoffCut K N s ≠ ⊤ :=
  TopSupport.evr_ne_top (donorMax_ne_top N hs) K K

/-- The partner: lower only the cutoff field to the rounded frontier, then normalize. -/
def partner [DecidableEq X] (s : X → ExtOrd) : X → ExtOrd :=
  PairedSlotEncoding.normalize K (Function.update s b (cutoffCut K N s))

/-! ## The frontier is a grid endpoint of the canonical code -/

/-- In a canonical profile the non-top maximum is bottom or a canonical code `ω·bl + off` with
`off ≤ K`, and its rounding is the block endpoint `ω·bl + K`. -/
theorem cutoffCut_eq_endpoint {s : X → ExtOrd}
    (hs : s ∈ CanonicalPairedProfiles.inventory X K) :
    cutoffCut K N s = ⊥ ∨
      ∃ (m₀ : Ordinal.{0}) (d₀ : X), N d₀ ∧ s d₀ = ofOrd m₀ ∧ donorMax N s = ofOrd m₀ ∧
        m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀ ∧
        cutoffCut K N s = ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  rcases ExtOrd.cases (donorMax N s) with hM | hM | ⟨m₀, hM⟩
  · left
    unfold cutoffCut
    rw [hM]
    rfl
  · exact absurd hM (donorMax_ne_top N hs.2)
  · right
    obtain ⟨d₀, hd₀, hd₀M⟩ : ∃ d, N d ∧ s d = donorMax N s := by
      rcases donorMax_cases N s with h | h
      · exact absurd (h.symm.trans hM) (ofOrd_ne_bot m₀).symm
      · exact h
    have hm₀ : s d₀ = ofOrd m₀ := hd₀M.trans hM
    have hcode : encode K (values s) m₀ = ofOrd m₀ := by
      have h := congrFun hs.1 d₀
      rw [PairedSlotEncoding.normalize_ofOrd hm₀, hm₀] at h
      exact h
    set bl := block K (values s) m₀ with hbl
    set off := offset K (values s) m₀ with hoffdef
    have hdec : m₀ = Ordinal.omega0 * bl + off := (ofOrd_inj.mp hcode).symm
    have hlim : limitPart m₀ = Ordinal.omega0 * bl := by rw [hdec]; exact limitPart_mul_add _ _
    have hfin : finitePart m₀ = off := by rw [hdec]; exact finitePart_mul_add _ _
    have hoff : off ≤ K := offset_le K (values s) m₀
    refine ⟨m₀, d₀, hd₀, hm₀, hM, hdec, ?_⟩
    unfold cutoffCut
    rw [hM]
    change extVisibilityReplace (ofOrd m₀) K K = ofOrd (Ordinal.omega0 * bl + K)
    rcases lt_or_eq_of_le hoff with hlt | heq
    · rw [extVisibilityReplace_of_finitePart_lt (by rw [hfin]; exact hlt) K, hlim]
    · rw [extVisibilityReplace_of_le_finitePart (by rw [hfin, heq]) K, hdec, heq]

/-! ## The partner's cutoff is the frontier: represented-endpoint fixation -/

section Partner

variable [DecidableEq X]

theorem mem_values_update {s : X → ExtOrd} {x : ExtOrd} {c : Ordinal.{0}} :
    c ∈ values (Function.update s b x) ↔ x = ofOrd c ∨ ∃ d, d ≠ b ∧ s d = ofOrd c := by
  rw [mem_values]
  constructor
  · rintro ⟨d, hd⟩
    by_cases hdb : d = b
    · subst hdb
      rw [Function.update_self] at hd
      exact Or.inl hd
    · rw [Function.update_of_ne hdb] at hd
      exact Or.inr ⟨d, hdb, hd⟩
  · rintro (h | ⟨d, hdb, hd⟩)
    · exact ⟨b, by rw [Function.update_self]; exact h⟩
    · exact ⟨d, by rw [Function.update_of_ne hdb]; exact hd⟩

/-- **Represented-endpoint fixation.**  Inserting the `K`-endpoint `ω·bl + K` of the block of a
canonical code `m₀ = ω·bl + off` (`off ≤ K`) into the inventory and removing a value above that
endpoint leaves its paired code at block `bl`, offset `K`: the endpoint witnesses no orbit, the
keys below its key are those below `m₀`'s key, and the removed value lies at or above
`ω·bl + K + 1`. -/
theorem encode_endpoint {s : X → ExtOrd} {m₀ : Ordinal.{0}} {d₀ : X} (hm₀ : s d₀ = ofOrd m₀)
    (hdec : m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀)
    (hsb : ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) < s b) :
    encode K (values (Function.update s b (ofOrd (Ordinal.omega0 * block K (values s) m₀ + K))))
      (Ordinal.omega0 * block K (values s) m₀ + K) =
      ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  classical
  set S := values s with hSdef
  set bl := block K S m₀ with hbl
  set off := offset K S m₀ with hoffdef
  set h₀ : Ordinal.{0} := Ordinal.omega0 * bl + K with hh₀
  set T := values (Function.update s b (ofOrd h₀)) with hTdef
  set S' : Finset Ordinal.{0} := insert h₀ S with hS'def
  have hoff : off ≤ K := offset_le K S m₀
  have hm₀S : m₀ ∈ S := mem_values.mpr ⟨d₀, hm₀⟩
  have hh₀lim : limitPart h₀ = Ordinal.omega0 * bl := limitPart_mul_add _ _
  have hh₀fin : finitePart h₀ = K := finitePart_mul_add _ _
  have hm₀lim : limitPart m₀ = Ordinal.omega0 * bl := by rw [hdec]; exact limitPart_mul_add _ _
  have hm₀fin : finitePart m₀ = off := by rw [hdec]; exact finitePart_mul_add _ _
  -- (a) the endpoint witnesses no orbit
  have horb : ∀ c, Orbit K S' c ↔ Orbit K S c := by
    intro c
    constructor
    · rintro ⟨hf, e, he, hej, hec⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · rw [hh₀fin] at hej
        exact absurd hej (lt_irrefl K)
      · exact ⟨hf, e, he, hej, hec⟩
    · rintro ⟨hf, e, he, hej, hec⟩
      exact ⟨hf, e, Finset.mem_insert_of_mem he, hej, hec⟩
  have hkey : ∀ c, key K S' c = key K S c := by
    intro c
    by_cases ho : Orbit K S c
    · simp only [key, ite_eq_left ho, ite_eq_left ((horb c).mpr ho)]
    · simp only [key, ite_eq_right ho, ite_eq_right (fun h => ho ((horb c).mp h))]
  -- (b) the endpoint and the maximum share their orbit status and key in `S`
  have horb₀ : Orbit K S h₀ ↔ Orbit K S m₀ := by
    constructor
    · rintro ⟨-, e, he, hej, hec⟩
      exact ⟨hm₀fin ▸ hoff, e, he, hej, hec.trans (hh₀lim.trans hm₀lim.symm)⟩
    · rintro ⟨-, e, he, hej, hec⟩
      exact ⟨hh₀fin ▸ le_rfl, e, he, hej, hec.trans (hm₀lim.trans hh₀lim.symm)⟩
  have hkey₀ : key K S h₀ = key K S m₀ := by
    by_cases ho : Orbit K S m₀
    · simp only [key, ite_eq_left ho, ite_eq_left (horb₀.mpr ho), hh₀lim, hm₀lim]
    · have hoffK : off = K := by
        by_contra hne
        exact ho (orbit_of_invisible hm₀S (by rw [hm₀fin]; exact lt_of_le_of_ne hoff hne))
      have hm₀h₀ : m₀ = h₀ := by rw [hdec, hoffK]
      rw [hm₀h₀]
  -- (c) the keys below the common key are unchanged by the insertion
  have hkeys : (PairedSlotEncoding.keys K S').filter (· < key K S m₀) =
      (PairedSlotEncoding.keys K S).filter (· < key K S m₀) := by
    have himg : PairedSlotEncoding.keys K S' =
        insert (key K S h₀) (PairedSlotEncoding.keys K S) := by
      change S'.image (key K S') = insert (key K S h₀) (S.image (key K S))
      rw [hS'def, Finset.image_insert, hkey h₀]
      exact congrArg _ (Finset.image_congr (fun c _ => hkey c))
    rw [himg, Finset.filter_insert, ite_eq_right (by rw [hkey₀]; exact lt_irrefl _)]
  have hrank' : PairedSlotEncoding.rank K S' h₀ = PairedSlotEncoding.rank K S m₀ := by
    unfold PairedSlotEncoding.rank
    rw [hkey h₀, hkey₀, hkeys]
  -- (d) below `ω·bl + K + 1` the actual inventory of the partner is the enlarged inventory
  set h' : Ordinal.{0} := Ordinal.omega0 * bl + ((K + 1 : ℕ) : Ordinal.{0}) with hh'
  have hh'fin : K ≤ finitePart h' := by rw [finitePart_mul_add]; exact Nat.le_succ K
  have hh₀h' : h₀ < h' := by
    rw [hh₀, hh']
    exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (Nat.lt_succ_self K))
  have heq : ∀ c, c < h' → (c ∈ T ↔ c ∈ S') := by
    intro c hc
    rw [hTdef, mem_values_update, hS'def, Finset.mem_insert, hSdef, mem_values]
    constructor
    · rintro (h | ⟨d, -, hd⟩)
      · exact Or.inl (ofOrd_inj.mp h).symm
      · exact Or.inr ⟨d, hd⟩
    · rintro (h | ⟨d, hd⟩)
      · exact Or.inl (by rw [h])
      · by_cases hdb : d = b
        · subst hdb
          exfalso
          have h1 : h₀ < c := ofOrd_lt_ofOrd.mp (hd ▸ hsb)
          have h2 : c ≤ h₀ := by
            have hc' : c < h₀ + 1 := by
              rw [hh'] at hc
              rw [hh₀]
              rw [Nat.cast_succ, ← add_assoc] at hc
              exact hc
            exact Order.lt_add_one_iff.mp hc'
          exact absurd h1 (not_lt.mpr h2)
        · exact Or.inr ⟨d, hdb, hd⟩
  have hrankT : PairedSlotEncoding.rank K T h₀ = PairedSlotEncoding.rank K S' h₀ :=
    rank_congr_below hh'fin heq hh₀h'
  have horbT : Orbit K T h₀ ↔ Orbit K S' h₀ :=
    orbit_congr_below hh'fin heq (by rw [hh₀lim]; exact hh₀h'.trans_le' (by
      rw [hh₀]; exact le_self_add))
  -- (e) the code of the endpoint in the partner inventory
  have hblock : block K T h₀ = bl := by
    change block K T h₀ = block K S m₀
    unfold block
    rw [hrankT, hrank']
    by_cases ho : Orbit K S m₀
    · rw [ite_eq_left (((horbT.trans (horb h₀)).trans horb₀).mpr ho), ite_eq_left ho]
    · rw [ite_eq_right (fun h => ho (((horbT.trans (horb h₀)).trans horb₀).mp h)),
        ite_eq_right ho]
  have hoffT : offset K T h₀ = K := by
    unfold offset
    split_ifs
    · exact hh₀fin
    · rfl
  unfold encode
  rw [hblock, hoffT]

end Partner


/-- The paired source grid of the complete field type. -/
abbrev grid : Finset ExtOrd := sourceGrid K (Fintype.card X)

theorem grid_bot : (⊥ : ExtOrd) ∈ grid (X := X) K := sourceGrid_bot _ _

/-- The reserved ceiling of the source grid. -/
def ceiling : ExtOrd := ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + K)

theorem ceiling_mem : ceiling (X := X) K ∈ grid (X := X) K := sourceGrid_endpoint le_rfl

theorem grid_le_ceiling {e : ExtOrd} (he : e ∈ grid (X := X) K) : e ≤ ceiling (X := X) K := by
  classical
  rcases Finset.mem_insert.mp he with rfl | he
  · exact bot_le
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp he
    have hc' : (c : Ordinal.{0}) ≤ ((2 * Fintype.card X + 1 : ℕ) : Ordinal.{0}) := by
      apply Nat.cast_le.mpr
      have := Finset.mem_range.mp hc
      omega
    unfold ceiling
    apply ofOrd_le_ofOrd.mpr
    have hm : Ordinal.omega0 * (c : Ordinal.{0}) ≤
        Ordinal.omega0 * ((2 * Fintype.card X + 1 : ℕ) : Ordinal.{0}) := by gcongr
    exact add_le_add_left hm _

/-! ## The partner: canonical, cutoff `h`, prefix agreement, common cut `h` -/

section PartnerProfile

variable [DecidableEq X] {s : X → ExtOrd} (hs : s ∈ CanonicalPairedProfiles.inventory X K)
  (hb : ¬ N b) (hlt : cutoffCut K N s < s b)

include hs in
theorem partner_mem : partner K N b s ∈ CanonicalPairedProfiles.inventory X K := by
  apply CanonicalPairedProfiles.normalize_mem_inventory
  intro d
  by_cases hdb : d = b
  · subst hdb
    rw [Function.update_self]
    exact cutoffCut_ne_top K N hs.2
  · rw [Function.update_of_ne hdb]
    exact hs.2 d

include hs hlt in
/-- **The partner's cutoff is exactly the frontier.** -/
theorem partner_cutoff : partner K N b s b = cutoffCut K N s := by
  unfold partner
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, -, hm₀, -, hdec, hend⟩
  · rw [h0]
    exact (PairedSlotEncoding.normalize_bot_iff K _ b).mpr (by rw [Function.update_self])
  · rw [PairedSlotEncoding.normalize_ofOrd (by rw [Function.update_self, hend]), hend]
    rw [hend] at hlt
    exact encode_endpoint K b hm₀ hdec hlt

include hs hlt in
/-- **Prefix agreement** `t ∧ h = s ∧ h`, on every complete field. -/
theorem partner_cap (d : X) :
    min (partner K N b s d) (cutoffCut K N s) = min (s d) (cutoffCut K N s) := by
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, -, hm₀, -, hdec, hend⟩
  · rw [h0, min_eq_right bot_le, min_eq_right bot_le]
  · rw [hend]
    unfold partner
    rw [hend]
    refine CanonicalPairedProfiles.normalize_cap X K hs (fun e => ?_) d
    by_cases heb : e = b
    · subst heb
      rw [Function.update_self, min_self, min_eq_right]
      rw [hend] at hlt
      exact hlt.le
    · rw [Function.update_of_ne heb]

omit [DecidableEq X] in
include hs in
theorem cutoffCut_mem_grid : cutoffCut K N s ∈ grid (X := X) K := by
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, -, hm₀, -, -, hend⟩
  · rw [h0]; exact grid_bot K
  · rw [hend]
    apply sourceGrid_endpoint
    have h1 := block_le_twice_card (j := K) (mem_values.mpr ⟨d₀, hm₀⟩)
    have h2 := values_card_le s
    omega

omit [DecidableEq X] in
include hs in
theorem cutoffCut_lt_ceiling : cutoffCut K N s < ceiling (X := X) K := by
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, -, hm₀, -, -, hend⟩
  · rw [h0]; exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  · rw [hend]
    unfold ceiling
    apply ofOrd_lt_ofOrd.mpr
    have h1 := block_le_twice_card (j := K) (mem_values.mpr ⟨d₀, hm₀⟩)
    have h2 := values_card_le s
    have h3 : block K (values s) m₀ < 2 * Fintype.card X + 1 := by omega
    exact (code_add_lt_mul (Nat.cast_lt.mpr h3) K).trans_le le_self_add

include hs hlt in
/-- **The common cut of `s` and its partner is the frontier**: `κ_K(s, t) = h`. -/
theorem cut_partner : cut (grid (X := X) K) s (partner K N b s) = cutoffCut K N s := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hag := agree_cut (grid_bot (X := X) K) s (partner K N b s) b
    rw [partner_cutoff K N b hs hlt, min_eq_left hgt.le] at hag
    have : cutoffCut K N s < min (s b) (cut (grid (X := X) K) s (partner K N b s)) := lt_min hlt hgt
    rw [hag] at this
    exact lt_irrefl _ this
  · exact le_cut (cutoffCut_mem_grid K N hs) (fun x => (partner_cap K N b hs hlt x).symm)

omit [DecidableEq X] in
/-- The raw selected pair: the diagonal cut is the reserved ceiling, strictly above the
frontier. -/
theorem cut_self : cut (grid (X := X) K) s s = ceiling (X := X) K :=
  cut_refl (ceiling_mem K) (fun _ he => grid_le_ceiling K he) s

include hs in
theorem largestCommonCut_eq_cut :
    largestCommonCut K s (partner K N b s) = cut (grid (X := X) K) s (partner K N b s) := by
  have ht := partner_mem K N b hs
  unfold largestCommonCut cut
  apply Finset.sup_congr
  · ext e
    simp only [Finset.mem_filter, Agree, hs.1, ht.1]
  · intros
    rfl

end PartnerProfile

/-! ## Strict comparison activates LOW -/

section Activation

variable [DecidableEq X] {s : X → ExtOrd} (hs : s ∈ CanonicalPairedProfiles.inventory X K)
  (hlt : cutoffCut K N s < s b)

include hs hlt in
/-- The ultrametric identity: a strict comparison of the two common cuts pins the partner cut at
the frontier and puts the other cut strictly above it. -/
theorem cut_partner_eq_of_lt {a : X → ExtOrd}
    (h : cut (grid (X := X) K) a (partner K N b s) < cut (grid (X := X) K) a s) :
    cut (grid (X := X) K) a (partner K N b s) = cutoffCut K N s ∧
      cutoffCut K N s < cut (grid (X := X) K) a s := by
  have hst := cut_partner K N b hs hlt
  have h1 := cut_triangle (grid_bot (X := X) K) a s (partner K N b s)
  have h2 := cut_triangle (grid_bot (X := X) K) s a (partner K N b s)
  rw [hst] at h1 h2
  rw [cut_symm (grid_bot (X := X) K) s a] at h2
  have hcu : cutoffCut K N s < cut (grid (X := X) K) a s := by
    by_contra hn
    rw [min_eq_left (not_lt.mp hn)] at h1
    exact absurd (h1.trans_lt h) (lt_irrefl _)
  refine ⟨le_antisymm ?_ ?_, hcu⟩
  · rw [min_eq_right h.le] at h2
    exact h2
  · rw [min_eq_right hcu.le] at h1
    exact h1

include hs hlt in
/-- **Strict comparison activates LOW**: the non-top donor maximum is unchanged and the cutoff
of the serving profile exceeds the frontier. -/
theorem activation_of_cut_lt {a : X → ExtOrd}
    (h : cut (grid (X := X) K) a (partner K N b s) < cut (grid (X := X) K) a s) :
    donorMax N a = donorMax N s ∧ cutoffCut K N s < a b := by
  obtain ⟨-, hu⟩ := cut_partner_eq_of_lt K N b hs hlt h
  have hag := agree_cut (grid_bot (X := X) K) a s
  refine ⟨donorMax_congr N (fun d hd => ?_), ?_⟩
  · have hsd : s d < cut (grid (X := X) K) a s :=
      ((le_donorMax N s hd).trans (donorMax_le_cutoffCut K N s)).trans_lt hu
    exact (eq_of_cap_eq_lt (hag d).symm hsd).symm
  · have hb' := hag b
    have hgt : cutoffCut K N s < min (s b) (cut (grid (X := X) K) a s) := lt_min hlt hu
    rw [← hb'] at hgt
    exact hgt.trans_le (min_le_left _ _)

include hs hlt in
/-- A monotone chart reading the partner cut strictly below the diagonal cut activates LOW. -/
theorem activation_of_chart_lt {a : X → ExtOrd} {σ : ExtOrd → ExtOrd} (hσ : Monotone σ)
    (h : σ (cut (grid (X := X) K) a (partner K N b s)) < σ (cut (grid (X := X) K) a s)) :
    donorMax N a = donorMax N s ∧ cutoffCut K N s < a b :=
  activation_of_cut_lt K N b hs hlt (lt_of_not_ge fun hle => not_lt.mpr (hσ hle) h)

end Activation

end Scalar

/-! ## The family instance: KVC's gate-free LOW family -/

section Family

open LowOnly

variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

/-- The non-top donor fields among the complete fields. -/
def donorField : LowOnly.Field P C → Prop
  | .inl d => F.p d ≠ ⊤
  | .inr _ => False

noncomputable instance : DecidablePred (donorField F) := Classical.decPred _

/-- The cutoff field. -/
abbrev cutoffField : LowOnly.Field P C := Sum.inr (Sum.inr ())

theorem cutoffField_not_donor : ¬ donorField F (cutoffField (P := P) (C := C)) := fun h => h

/-- The family's non-top maximum is the donor maximum of the complete profile. -/
theorem maximum_eq_donorMax (S : State P C) :
    F.maximum S = donorMax (donorField F) S.profile := by
  apply le_antisymm
  · unfold LowOnly.Family.maximum LowOnly.nonTopMax
    apply Finset.sup_le
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact le_donorMax (donorField F) S.profile (d := Sum.inl d) hd
  · unfold donorMax
    apply Finset.sup_le
    intro x hx
    have hx' : donorField F x := (Finset.mem_filter.mp hx).2
    rcases x with d | d | d
    · exact LowOnly.le_nonTopMax S.u hx'
    · exact hx'.elim
    · exact hx'.elim

/-- The partner state: only the cutoff is lowered to the frontier, then normalized. -/
def partnerState (S : State P C) : State P C :=
  (⟨S.u, S.v, cutoffCut K (donorField F) S.profile⟩ : State P C).normalize K

theorem partnerState_profile (S : State P C) :
    (partnerState F S).profile =
      partner K (donorField F) (cutoffField (P := P) (C := C)) S.profile := by
  funext d
  unfold partnerState partner
  rw [State.profile_normalize]
  congr 1
  funext e
  rcases e with e | e | e
  · rfl
  · rfl
  · rfl

theorem partnerState_cutoff {S : State P C} (hcan : S.profile ∈
      CanonicalPairedProfiles.inventory (LowOnly.Field P C) K)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) :
    (partnerState F S).b = cutoffCut K (donorField F) S.profile := by
  have h := congrFun (partnerState_profile F S) cutoffField
  change (partnerState F S).b = _ at h
  rw [h]
  exact partner_cutoff K (donorField F) cutoffField hcan hlt

theorem partnerState_mem {S : State P C} (hcan : S.profile ∈
      CanonicalPairedProfiles.inventory (LowOnly.Field P C) K) :
    (partnerState F S).profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K := by
  rw [partnerState_profile]
  exact partner_mem K (donorField F) cutoffField hcan

/-- **The partner state is admitted**: lowering the cutoff keeps both original sections and the
root; if the new LOW premise is active the old one was (the frontier bounds the maximum and lies
below the old cutoff), and the old bound dominates the new one; normalization preserves
admission. -/
theorem partnerState_admissible {S : State P C} (hS : F.Admissible K S)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) (hK : 1 ≤ K) :
    F.Admissible K (partnerState F S) := by
  have hm : F.maximum S < S.b := by
    rw [maximum_eq_donorMax]
    exact (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hlt
  have hS' : F.Admissible K (⟨S.u, S.v, cutoffCut K (donorField F) S.profile⟩ : State P C) :=
    { lawfulP := hS.lawfulP
      lawfulC := hS.lawfulC
      shared := hS.shared
      futureP := hS.futureP
      futureC := hS.futureC
      cutoff := by
        rw [min_self]
        exact cutoffCut_selfVis K (donorField F) S.profile
      low := fun hj _ d hd => (max_le_max hlt.le le_rfl).trans (hS.low hj hm d hd) }
  exact F.normalize_admissible hK hS'

/-- **Donor-top readback at an active state**: a chart through `K` reading the private owner
and the low source as `⊤` reads every designated donor top as `⊤`, by LOW. -/
theorem donor_top_readback {S : State P C} (hS : F.Admissible K S) (hm : F.maximum S < S.b)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ) (hc : σ (S.v F.gap.c) = ⊤)
    (hr : σ (S.v F.gap.r.1) = ⊤) (d : Cell P.scheme) (hd : F.p d = ⊤) : σ (S.u d) = ⊤ := by
  have hlow := hS.low le_rfl hm d hd
  change max S.b (min (S.v F.gap.c) (extVisibilityReplace (S.v F.gap.r.1) K K)) ≤ S.u d at hlow
  have h1 := hσ.mono ((le_max_right _ _).trans hlow)
  rw [hσ.mono.map_min, hσ.comm_gTop _ le_rfl, hc, hr, extVisibilityReplace_top, min_self] at h1
  exact top_le_iff.mp h1

/-- **Strict comparison at a serving state activates LOW there**: a monotone chart reading the
partner cut strictly below the diagonal cut at an admitted serving profile forces the serving
state's non-top maximum below its cutoff. -/
theorem activation_of_serving {S A : State P C}
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) {σ : ExtOrd → ExtOrd} (hσ : Monotone σ)
    (h : σ (cut (grid (X := LowOnly.Field P C) K) A.profile (partnerState F S).profile) <
      σ (cut (grid (X := LowOnly.Field P C) K) A.profile S.profile)) :
    F.maximum A < A.b := by
  rw [partnerState_profile] at h
  obtain ⟨heq, hab⟩ := activation_of_chart_lt K (donorField F) cutoffField hcan hlt hσ h
  rw [maximum_eq_donorMax, heq]
  exact (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hab

/-- **The separator readback**: at an admitted serving state whose chart reads the partner cut
strictly below the diagonal cut and reads the private owner and low source as `⊤`, every
designated donor top reads `⊤`. -/
theorem serving_readback {S A : State P C} (hA : F.Admissible K A)
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop K) σ)
    (h : σ (cut (grid (X := LowOnly.Field P C) K) A.profile (partnerState F S).profile) <
      σ (cut (grid (X := LowOnly.Field P C) K) A.profile S.profile))
    (hc : σ (A.v F.gap.c) = ⊤) (hr : σ (A.v F.gap.r.1) = ⊤) (d : Cell P.scheme)
    (hd : F.p d = ⊤) : σ (A.u d) = ⊤ :=
  donor_top_readback F hA (activation_of_serving F hcan hlt hσ.mono h) hσ hc hr d hd

end Family


end

end VaughtConjecture.Knight.LowSeparator
