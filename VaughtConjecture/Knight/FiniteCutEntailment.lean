module

public import VaughtConjecture.Knight.CoupledRepairPaste
public import VaughtConjecture.Knight.FiniteCutoffBound
public import VaughtConjecture.Knight.RowReadback

/-!
# A finite-cut entailment test on the unchanged repaired domain

This bounded test uses the existing repaired domain and leaves all source rows unchanged.
The fresh request is the B-face grade-three cell, not a copied singleton.
Its label dominates the old A-face cap in every respecting labelling. Consequently
the cutoff inequality holds universally, with no further retention or pasting.
The inequality direction is old cap <= fresh label (not the reverse).
This is a one-request fixed-geometry theorem, not arbitrary comparison.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.FiniteCutEntailment

open Transform Value ExtOrd

abbrev Lower := D₂.below (Finset.univ, 3)

noncomputable def oldCap : Lower := ⟨a₂old, mema₂old₃⟩
noncomputable def fresh : Lower := ⟨b₁new, memb₁new₃⟩

/-- The decisive universal inequality uses only already compiled probe laws. -/
theorem oldCap_le_fresh {q : Lower → ExtOrd}
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q) :
    q oldCap ≤ q fresh := by
  change q ⟨a₂old, mema₂old₃⟩ ≤ q ⟨b₁new, memb₁new₃⟩
  rw [a₂old_eq_A₂c_of_respectsR hq, b₁new_eq_ub₁_of_respectsR hq]
  exact A₂c_le_ub₁_of_respectsR hq

/-- Cap dominance alone implies every requested cutoff inequality. -/
theorem cutoffBound_of_cap_le {D : Type*} {grade : D → ℕ}
    (R : FiniteReferenceData D grade) {q : D → ExtOrd}
    (h : ∀ r ∈ R.requests, q R.cap ≤ q r.cell) : R.CutoffBound q := by
  intro _ r hr
  rw [min_eq_right (h r hr)]
  exact min_le_right _ _

/-- A grade-one reference, the old A cap/trigger, and one fresh offset-zero request. -/
noncomputable def references (α : Ordinal.{0}) (sc : Lower) (hg : D₂.grade sc.1 = 1) :
    FiniteReferenceData Lower (fun d => D₂.grade d.1) where
  N := 3
  cap := oldCap
  cap_grade := grade_a₂old
  trigger := oldCap
  rep _ := sc
  requests := [⟨fresh, α, 0⟩]
  req_grade_le r hr := by
    have e : r = ⟨fresh, α, 0⟩ := List.mem_singleton.mp hr
    subst r
    exact grade_b₁new.le
  rep_grade_le _ _ := by rw [hg]; decide
  offset_lt r hr := by
    have e : r = ⟨fresh, α, 0⟩ := List.mem_singleton.mp hr
    subst r
    change 0 < 3
    decide

/-- Universal correctness in the inequality sense; it needs no reference-label equation. -/
theorem cutoffBound_of_respects (α : Ordinal.{0}) (sc : Lower) (hg : D₂.grade sc.1 = 1)
    {q : Lower → ExtOrd} (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q) :
    (references α sc hg).CutoffBound q := by
  apply cutoffBound_of_cap_le
  intro r hr
  have e : r = ⟨fresh, α, 0⟩ := List.mem_singleton.mp hr
  subst r
  exact oldCap_le_fresh hq

/-- The existing consumer applies uniformly in the displayed cut and offset. -/
theorem readback_via_reference (α : Ordinal.{0}) (hα : limitPart α = α)
    (sc : Lower) (hg : D₂.grade sc.1 = 1) {j : ℕ} (hj : j < 3)
    {q : Lower → ExtOrd} (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (href : q sc = ofOrd (α + j)) (hcap : ofOrd α ≤ q oldCap)
    (htrigger : q oldCap ≠ ⊥) : truncExt α (q fresh) = ⊤ := by
  exact (cutoffBound_of_respects α sc hg hq).readback_top htrigger
    (List.mem_singleton_self _) rfl hα hj href hcap

/-- Stronger direct readback: no representative, trigger, or limit assumption is needed. -/
theorem readback_of_old_cap (α : Ordinal.{0}) {q : Lower → ExtOrd}
    (hq : RespectsSemanticsBelow rowsR (Finset.univ, 3) q)
    (hcap : ofOrd α ≤ q oldCap) : truncExt α (q fresh) = ⊤ :=
  truncExt_eq_top_of_ge (hcap.trans (oldCap_le_fresh hq))

/-- The request uses the new point and does not lie in the protected A face. -/
theorem fresh_not_old_face : ¬ GradedLe (D₂.cell fresh.1) faceA :=
  not_faceA_of_three three_mem_scope_b₁new

/-- A consistent row, extended by bottom outside its lower set, respects its own index. -/
theorem rowOf_respects_at_index {n : ℕ} (D : SemScheme (n + 1)) (c : Cell D.scheme)
    (BJ : Finset (Fin (n + 1)) × ℕ) (hc : D.scheme.cell c = BJ) :
    RespectsSemanticsBelow D.rows BJ (fun d => D.rowOf c d.1) := by
  subst BJ
  have he : (fun d : D.scheme.below (D.scheme.cell c) => D.rowOf c d.1) = D.rows.E c :=
    funext fun d => D.rowOf_of_le c d.2
  rw [he]
  exact D.consistent c

/-- Every full-scope grade-three controller passes the actual row cutoff test. -/
theorem controllerRows_cutoffBound (α : Ordinal.{0}) (sc : Lower)
    (hg : D₂.grade sc.1 = 1) (c : Cell D₂) (hc : D₂.cell c = (Finset.univ, 3)) :
    (references α sc hg).CutoffBound (fun d => semSchemeR.rowOf c d.1) :=
  cutoffBound_of_respects α sc hg (rowOf_respects_at_index semSchemeR c _ hc)

/-- For any respecting labelling of the fixed A face with a high enough old cap, an extension
exists, and every respecting extension has the desired reduced value at the fresh cell. -/
theorem faceA_universal_readback (α : Ordinal.{0}) (p : D₂.below faceA → ExtOrd)
    (hp : RespectsSemanticsBelow rowsR faceA p)
    (hcap : ofOrd α ≤ p ⟨a₂old, a₂old_memA⟩) :
    (∃ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q ∧
      ∀ d, q (CellScheme.below.mono faceA_le d) = p d) ∧
    (∀ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q →
      (∀ d, q (CellScheme.below.mono faceA_le d) = p d) →
      truncExt α (q fresh) = ⊤) := by
  refine ⟨faceA_extendsR p hp, ?_⟩
  intro q hq hext
  apply readback_of_old_cap α hq
  have he := hext ⟨a₂old, a₂old_memA⟩
  change q oldCap = p ⟨a₂old, a₂old_memA⟩ at he
  rwa [he]

/-- The prescribed display really separates the two cap labels. -/
theorem prescribed_display_strict : qL oldCap.1 < qL fresh.1 := by
  have hA := a₂old_eq_A₂c_of_respectsR qL_respectsR
  have hB := b₁new_eq_ub₁_of_respectsR qL_respectsR
  change qL a₂old = qL A₂c at hA
  change qL b₁new = qL ub₁ at hB
  change qL a₂old < qL b₁new
  rw [hA, hB, qL_A₂c, qL_ub₁]
  exact γ₀_lt_γ₁

/-- A nonvacuous instance: the prescribed display has old cap `ω + 4`, a strictly larger
fresh cap, and top readback at cut `ω`. -/
theorem prescribed_cut_readback :
    truncExt Ordinal.omega0 (qL fresh.1) = ⊤ := by
  apply readback_of_old_cap Ordinal.omega0 qL_respectsR
  have hA := a₂old_eq_A₂c_of_respectsR qL_respectsR
  change qL a₂old = qL A₂c at hA
  change ofOrd Ordinal.omega0 ≤ qL a₂old
  rw [hA, qL_A₂c]
  unfold γ₀
  rw [ofOrd_le_ofOrd, Nat.cast_one, mul_one]
  simp

/-- The successful request is not a universal equality/duplication assertion. -/
theorem not_forced_duplicate :
    ¬ ∀ q : Lower → ExtOrd, RespectsSemanticsBelow rowsR (Finset.univ, 3) q →
      q fresh = q oldCap := by
  intro h
  exact (ne_of_lt prescribed_display_strict) (h (fun d => qL d.1) qL_respectsR).symm

/-- The apparently harder lower controllers already obey the cutoff inequality: the old cap
lies below `w`, and the exact orbit controls `z₁`. -/
theorem legal_cutoff_bounds {v x₀ x₁ H z₁ z₂ w : ExtOrd}
    (L : Legal₃ v x₀ x₁ H z₁ z₂ w) :
    min (extVisibilityReplace v 3 0) z₂ ≤ z₁ ∧ z₂ ≤ w ∧ z₂ ≤ H := by
  have hv0 : extVisibilityReplace v 3 0 ≤ v := by
    rcases ExtOrd.cases v with rfl | rfl | ⟨α, rfl⟩
    · simp
    · simp
    · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
      unfold visibilityReplace ordinalReplace
      split
      · simpa using limitPart_le α
      · exact le_rfl
  refine ⟨?_, L.z2w, L.z2w.trans L.wH⟩
  calc
    min (extVisibilityReplace v 3 0) z₂ ≤ min v w :=
      min_le_min hv0 L.z2w
    _ ≤ extVisibilityReplace (min v w) 3 3 := le_extVisibilityReplace_self _ _
    _ = z₁ := L.orbit.symm

/-- With both the proper value and old cap above a cut, all seven non-mute parameters and the
dependent old grade-two value are above it. This warns that the one-cut test is an all-high
test, not arbitrary finite-pattern transfer. -/
theorem all_parameters_above_cut {v x₀ x₁ H z₁ z₂ w c : ExtOrd}
    (L : Legal₃ v x₀ x₁ H z₁ z₂ w) (hv : c ≤ v) (hc : c ≤ z₂) :
    c ≤ x₀ ∧ c ≤ x₁ ∧ c ≤ H ∧ c ≤ z₁ ∧ c ≤ w ∧ c ≤ min x₀ H := by
  have hw := hc.trans L.z2w
  have hH := hw.trans L.wH
  have hx := hv.trans L.two.vle
  refine ⟨hx, hx.trans L.two.le01, hH, ?_, hw, le_min hx hH⟩
  rw [L.orbit]
  exact (le_min hv hw).trans (le_extVisibilityReplace_self _ _)

/-! ## Scheme-independent pasting of correctness -/

/-- Trigger agreement makes an active paste activate both inputs at a nonbottom paste cap. -/
theorem active_inputs {g a b : ExtOrd} (hg : g ≠ ⊥)
    (hab : min a g = min b g) (ht : paste g a b ≠ ⊥) : a ≠ ⊥ ∧ b ≠ ⊥ := by
  constructor
  · intro ha
    apply ht
    rw [ha, paste_of_lt (bot_lt_iff_ne_bot.mpr hg)]
  · rwa [paste_eq_of_agree hab] at ht

/-- Cutoff correctness is closed under paste at any comparison grade, provided the two inputs
agree below the paste cap at the representatives and the trigger. No cap-cell agreement. -/
theorem cutoffBound_paste {D : Type*} {grade : D → ℕ}
    (R : FiniteReferenceData D grade) {q s : D → ExtOrd} {g : ExtOrd}
    (hg : SelfVis R.N g) (hq : R.CutoffBound q) (hs : R.CutoffBound s)
    (hrep : ∀ r ∈ R.requests, min (q (R.rep r.block)) g = min (s (R.rep r.block)) g)
    (htrig : min (q R.trigger) g = min (s R.trigger) g) :
    R.CutoffBound (fun d => paste g (q d) (s d)) := by
  by_cases hgb : g = ⊥
  · subst g
    simpa only [paste_bot_cap] using hs
  intro ht r hr
  obtain ⟨hqt, hst⟩ := active_inputs hgb htrig ht
  have hν := map_paste_of_agree (fun x => extVisibilityReplace x R.N r.offset)
    (fun _ _ h => evr_mono h (R.offset_lt r hr).le)
    (evr_eq_self_of_selfVis hg r.offset) (hrep r hr)
  change min (extVisibilityReplace (paste g (q (R.rep r.block)) (s (R.rep r.block)))
    R.N r.offset) (paste g (q R.cap) (s R.cap)) ≤ _
  rw [hν, ← paste_min, ← paste_min]
  exact paste_mono (hq hqt r hr) (hs hst r hr)

/-- The finite equality form is closed under the very same paste hypotheses. -/
theorem correct_paste {D : Type*} {grade : D → ℕ}
    (R : FiniteReferenceData D grade) {q s : D → ExtOrd} {g : ExtOrd}
    (hg : SelfVis R.N g) (hq : R.Correct q) (hs : R.Correct s)
    (hrep : ∀ r ∈ R.requests, min (q (R.rep r.block)) g = min (s (R.rep r.block)) g)
    (htrig : min (q R.trigger) g = min (s R.trigger) g) :
    R.Correct (fun d => paste g (q d) (s d)) := by
  by_cases hgb : g = ⊥
  · subst g
    simpa only [paste_bot_cap] using hs
  intro ht r hr
  obtain ⟨hqt, hst⟩ := active_inputs hgb htrig ht
  have hν := map_paste_of_agree (fun x => extVisibilityReplace x R.N r.offset)
    (fun _ _ h => evr_mono h (R.offset_lt r hr).le)
    (evr_eq_self_of_selfVis hg r.offset) (hrep r hr)
  change min (paste g (q r.cell) (s r.cell)) (paste g (q R.cap) (s R.cap)) = _
  rw [← paste_min, hq hqt r hr, hs hst r hr, paste_min, ← hν]

end VaughtConjecture.Knight.FiniteCutEntailment
