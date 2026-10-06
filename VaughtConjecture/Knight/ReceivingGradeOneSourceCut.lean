/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLowerCatalogueInsertion

/-! # Visible cuts before invisible canonical fields

An invisible grade-two field starts an orbit slot. The preceding odd slot is
unused, and its endpoint separates exactly the same represented fields. Thus
the source cut need not be obtained by rounding the invisible field upward.
No claim of minimality at unused ordinal points is needed.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingGradeOneSourceCut
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section

/-- The unused point slot before an invisible orbit gives a visible separator.
The positivity hypothesis excludes an offset-zero field earlier in that orbit. -/
theorem encode_separator {S : Finset Ordinal.{0}} {x : Ordinal.{0}}
    (hx : x ∈ S) (hvis : ∀ y ∈ S, 1 ≤ finitePart y) :
    ∃ B : ℕ, CanonicalPairedInverse.grid 2 B ≤ encode 2 S x ∧
      ∀ y ∈ S, encode 2 S y < CanonicalPairedInverse.grid 2 B ↔
        encode 2 S y < encode 2 S x := by
  by_cases hoff : offset 2 S x = 2
  · refine ⟨block 2 S x, ?_, ?_⟩
    · simp only [encode, hoff, CanonicalPairedInverse.grid, le_refl]
    · intro y _
      simp only [encode, hoff, CanonicalPairedInverse.grid]
  have ho : Orbit 2 S x := by
    by_contra hn
    exact hoff (by simp only [offset, ite_eq_right hn])
  have hfx : finitePart x = 1 := by
    have h1 := hvis x hx
    have h2 := ho.1
    have hn : finitePart x ≠ 2 := by
      simpa only [offset, ite_eq_left ho] using hoff
    omega
  let B := 2 * rank 2 S x + 1
  have hcut : CanonicalPairedInverse.grid 2 B ≤ encode 2 S x := by
    apply le_of_lt
    apply ofOrd_lt_ofOrd.mpr
    exact (code_add_lt_mul (Nat.cast_lt.mpr
      (show B < block 2 S x by simp only [B, block, ite_eq_left ho]; omega)) 2).trans_le
      le_self_add
  refine ⟨B, hcut, fun y hy => ⟨fun h => h.trans_le hcut, ?_⟩⟩
  intro hlt
  have hyx : y < x := by
    by_contra hn
    exact hlt.not_ge ((encode_strictMonoOn 2 S).monotoneOn hx hy (not_lt.mp hn))
  have hk : key 2 S y < key 2 S x := by
    apply lt_of_le_of_ne (key_mono 2 S hyx.le)
    intro he
    have hoy := (orbit_iff_of_key_eq hy hx he).mpr ho
    have hl : limitPart y = limitPart x := by
      simpa only [key, ite_eq_left hoy, ite_eq_left ho] using he
    have hf := hvis y hy
    exact hyx.not_ge (le_of_finitePart_le hl.symm (by omega))
  have hr := rank_lt_of_key_lt hy hk
  have hb : block 2 S y < B := by
    unfold block
    split_ifs <;> dsimp only [B] <;> omega
  exact ofOrd_lt_ofOrd.mpr
    ((code_add_lt_mul (Nat.cast_lt.mpr hb) _).trans_le le_self_add)

/-- Every positive canonical field admits a grade-two grid separator with
exactly the same strict lower field set, including when that field is invisible. -/
theorem canonical_separator {X : Type*} [Fintype X] {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X 2)
    (hvis : ∀ f, SelfVis 1 (a f)) (c : X) (hc : a c ≠ ⊥) :
    ∃ B : ℕ, CanonicalPairedInverse.grid 2 B ≤ a c ∧
      ∀ f, a f < CanonicalPairedInverse.grid 2 B ↔ a f < a c := by
  rcases ExtOrd.cases (a c) with hb | ht | ⟨x, hx⟩
  · exact (hc hb).elim
  · exact (ha.2 c ht).elim
  have hmem : x ∈ values a := mem_values.mpr ⟨c, hx⟩
  have hv : ∀ y ∈ values a, 1 ≤ finitePart y := by
    intro y hy
    obtain ⟨d, hd⟩ := mem_values.mp hy
    exact selfVis_ofOrd_iff.mp (hd ▸ hvis d)
  have he (d : X) : normalize 2 a d = a d := congrFun ha.1 d
  have hec : encode 2 (values a) x = a c := (normalize_ofOrd hx).symm.trans (he c)
  obtain ⟨B, hB, hsep⟩ := encode_separator hmem hv
  refine ⟨B, hB.trans_eq hec, ?_⟩
  intro d
  rcases ExtOrd.cases (a d) with hb | ht | ⟨y, hy⟩
  · rw [hb]
    exact iff_of_true (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) (bot_lt_iff_ne_bot.mpr hc)
  · exact (ha.2 d ht).elim
  · have hed : encode 2 (values a) y = a d := (normalize_ofOrd hy).symm.trans (he d)
    simpa only [hed, hec] using hsep y (mem_values.mpr ⟨d, hy⟩)

open CappedDonor CappedDonor.Ref ReceivingLadderCarrier ReceivingCatalogueSources

variable {I : Type*} [Fintype I] {nP K : ℕ} {P : SemScheme (nP + 1)}
  {C : SemScheme 2} {R : Ref I nP 2 2 P C} (L : R.LowRef K)
  (hC : C.scheme.plan = privatePlan) (request : Cell P.scheme)

local notation "D" => carrier L hC
local notation "E" => semantics L hC request
local notation "ℓ" => rungs (P := P) (C := C)

local instance : Fintype (C.scheme.below (effC 2 1)) := Fintype.ofFinite _

/-- The actual ambient constructs a visible source cut. The cut's low field
set is exactly the low physical-reading set; no alignment is an input. -/
theorem exists_source_cut
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    (c : C.scheme.below (effC 2 1)) {γ : ExtOrd}
    (hpos : ⊥ < γ) (hactive : γ ≤ q (ReceivingGradeOnePhysicalChart.privateAt L hC c)) :
    ∃ a : Controller L, ∃ σ B, Witness (gTop 1) σ ∧
      (∀ d, σ (ReceivingGradeOnePhysicalChart.lowerSource L hC request a d.1) = q d) ∧
      ∀ f, fields L a f < CanonicalPairedInverse.grid 2 B ↔
        σ (SupportLadderRows.source ℓ (ranks L a f)) < γ := by
  classical
  obtain ⟨a, σ, k, hσ, hread, _, hkc, _, hreach, _, _, _⟩ :=
    ReceivingGradeOnePhysicalChart.exists_active_private_cut L hC request hq c hpos hactive
  let v : TField P C → ExtOrd := fun f => σ (SupportLadderRows.source ℓ (ranks L a f))
  let S : Finset (TField P C) := Finset.univ.filter (fun f => γ ≤ v f)
  have hmem : privateField c.1 ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hreach.trans (hσ.mono (SupportLadderRows.source_mono ℓ hkc))⟩
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image S (fields L a) ⟨_, hmem⟩
  have hfg : γ ≤ v f := (Finset.mem_filter.mp hf).2
  have hfb : fields L a f ≠ ⊥ := by
    intro hz
    have hr : ranks L a f = 0 := by
      change LadderScalarRendering.rank (LadderScalarRendering.values (fields L a)) _ = 0
      rw [hz]
      exact LadderScalarRendering.rank_bot (Finset.notMem_erase _ _)
    have hzv : v f = ⊥ := by simp only [v, hr, SupportLadderRows.source_zero, hσ.bot]
    exact hpos.not_ge (hfg.trans_eq hzv)
  obtain ⟨B, _, hsep⟩ := canonical_separator a.property.1 (fields_visible L a) f hfb
  refine ⟨a, σ, B, hσ, hread, fun d => (hsep d).trans ?_⟩
  constructor
  · intro hd
    by_contra hn
    exact hd.not_ge (hmin d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hn⟩))
  · intro hd
    by_contra hn
    have hr : ranks L a f ≤ ranks L a d := by
      exact LadderScalarRendering.rank_mono
        (LadderScalarRendering.values (fields L a)) (not_lt.mp hn)
    exact hd.not_ge (hfg.trans (hσ.mono (SupportLadderRows.source_mono ℓ hr)))

/-- Encode an arbitrary lawful physical private prescription into a lawful
lower source prescription compatible with an actual installed profile at a
constructed grade-two grid cut. Literal-top prescriptions are permitted. -/
theorem exists_encoded_prescription
    {p : C.scheme.below (effC 2 1) → ExtOrd}
    {q : (D).below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC 2 1) p)
    (hq : RespectsSemanticsBelow E (Finset.univ, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (ReceivingGradeOnePhysicalChart.privateAt L hC d)) γ = min (p d) γ)
    (c : C.scheme.below (effC 2 1)) (hactive : γ < p c) :
    ∃ a : Controller L, ∃ σ, ∃ B b : ℕ, Witness (gTop 1) σ ∧
      (∀ d, σ (ReceivingGradeOnePhysicalChart.lowerSource L hC request a d.1) = q d) ∧
      (∀ f, fields L a f < CanonicalPairedInverse.grid 2 B ↔
        σ (SupportLadderRows.source ℓ (ranks L a f)) < γ) ∧
      CanonicalPairedInverse.grid 2 B < ofOrd (Ordinal.omega0 * b) ∧
      RespectsSemanticsBelow C.rows (effC 2 1)
        (AlignedCutEncoding.encode (fun d => fields L a (privateField d.1)) p 1 b
          (CanonicalPairedInverse.grid 2 B) γ) ∧
      ∀ d, min (AlignedCutEncoding.encode (fun d => fields L a (privateField d.1))
          p 1 b (CanonicalPairedInverse.grid 2 B) γ d) (CanonicalPairedInverse.grid 2 B) =
        min (fields L a (privateField d.1)) (CanonicalPairedInverse.grid 2 B) := by
  have hact : γ ≤ q (ReceivingGradeOnePhysicalChart.privateAt L hC c) := by
    apply min_eq_right_iff.mp
    exact (hag c).trans (min_eq_right hactive.le)
  obtain ⟨a, σ, B, hσ, hread, hsep⟩ := exists_source_cut L hC request hq c hpos hact
  have halign (d) (hd : γ < p d) :
      CanonicalPairedInverse.grid 2 B ≤ fields L a (privateField d.1) := by
    apply not_lt.mp
    intro hl
    have hlow := (hsep (privateField d.1)).mp hl
    have he := hread (ReceivingGradeOnePhysicalChart.privateAt L hC d)
    rw [ReceivingGradeOnePhysicalChart.lowerSource_private] at he
    rw [he] at hlow
    have hh := hag d
    rw [min_eq_left hlow.le, min_eq_right hd.le] at hh
    exact hlow.ne hh
  have hroom : CanonicalPairedInverse.grid 2 B < ofOrd (Ordinal.omega0 * (↑(B + 1) : Ordinal)) :=
    ofOrd_lt_ofOrd.mpr (code_add_lt_mul (Nat.cast_lt.mpr (Nat.lt_succ_self B)) 2)
  have hs : RespectsSemanticsBelow C.rows (effC 2 1)
      (fun d => fields L a (privateField d.1)) := (private_lawful L a).toBelow _
  refine ⟨a, σ, B, B + 1, hσ, hread, hsep, hroom, ?_, ?_⟩
  · exact AlignedCutEncoding.encode_respects hs hp (fun d => d.2.2)
      (selfVis_mono (CanonicalPairedInverse.grid_visible 2 B) (by decide))
      (ofOrd_ne_bot _) hγ hroom halign
  · exact AlignedCutEncoding.encode_cap _ _ hroom halign

end
end VaughtConjecture.Knight.ReceivingGradeOneSourceCut
