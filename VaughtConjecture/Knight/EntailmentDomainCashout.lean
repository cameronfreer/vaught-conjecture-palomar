/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OnePointRootedExtension
public import VaughtConjecture.Knight.ActualOccurrence

/-! # The entailment-domain cash-out: Theorem 10.1.2's consumer

Proposition 7.3.3 realizes a requested one-point type `P` over a tuple `t` by building an
**entailment domain** `D*` over a context `ctx ⊇ t` (§§8–9) and showing (Lemma 10.1.1) that
every realized type with domain `D*` and the prescribed `−∞`-pattern projects literally to `P`
(Theorem 10.1.2).  Only the last step is consumed here.

The **one-request certificate** `EntailmentCertificate W t P` records: a realized context
tuple and its type; the extension domain `D*` bundled as a `SemScheme` extending the
context's domain; a respecting labelling `q'` of `D*` extending the context's labels; the
coordinate projection from the requested one-point type into the context's one-point
extension; and the Lemma 10.1.1 correctness statement — every coface of the context with
domain `D*` and the `−∞`-pattern of `q'` projects to `P`.
Clause (4)(a)(ii) of the model (`IsModel.bottomPattern`)
then realizes a coface of the context with domain `D*` and that pattern
(`BottomPatternFamily D* q'` fixes the domain as well as the pattern), correctness projects
its label to `P`, and exact consistency performs the projection on the realization
(`onePointOccurrence_of_entailmentCertificate`).

A certificate for every selected request is exactly literal one-point rooted transfer
(`onePointRootedExtensionOver_of_certificates`); the existing iteration upgrades it to
finite rooted transfer (`rootedExtensionOver_of_certificates`), and from there to the
selected common-chart step of the quotient-local terminal consumer
(`restrictedStepSupply_of_certificates`).  The construction of `D*` and the proof of its
correctness (§§8–9, Lemma 10.1.1) remain producer obligations: they are the certificate's
fields, never proved here.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

variable {α : LimitStage} {M : Type w}

/-- **The one-request entailment certificate** (Theorem 10.1.2's input for one request): a
realized context containing the request tuple, an extension domain `D*` of the context with
a respecting labelling extending the context's labels, and the correctness statement that
every coface of the context with domain `D*` and that `−∞`-pattern projects to the requested
one-point type `P` along the coordinate projection. -/
structure EntailmentCertificate (W : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (P : S α.1 (n + 1)) where
  /-- The arity of the context. -/
  m : ℕ
  /-- The context tuple. -/
  ctx : Fin m ↪ M
  /-- The realized type of the context. -/
  p₀ : S α.1 m
  /-- The context is realized. -/
  eval_ctx : W.eval ctx = some p₀
  /-- The request tuple sits inside the context. -/
  proj : Fin n ↪ Fin m
  /-- … at these coordinates. -/
  proj_ctx : proj.trans ctx = t
  /-- The entailment domain `D*`, as a domain with semantics on `m + 1` points. -/
  D : SemScheme (m + 1)
  /-- `D*` extends the context's domain: `D*⟨m,m⟩ = dom p₀`. -/
  extendsDomain : ExtendsDomain p₀ D
  /-- The prescribed labelling of `D*`. -/
  q' : Cell D.scheme → ExtOrd
  /-- It respects the semantics of `D*` (no stage bound). -/
  respects : RespectsSemantics D.rows q'
  /-- It extends the context's labels along the initial face. -/
  extends_label : ∀ d, q' (extendsDomain.cellOf d) = p₀.label d
  /-- **Lemma 10.1.1 (correctness)**: every coface of the context with domain `D*` and the
  `−∞`-pattern of `q'` projects literally to `P` (the paper's `s_y = p*`). -/
  correct : ∀ q : S α.1 (m + 1), q ∈ BottomPatternFamily D q' → IsCoface p₀ q →
    typeMap (onePointProj proj) q = some P

/-- **Theorem 10.1.2, consumed**: a certificate yields the requested occurrence — the
model's clause (4)(a)(ii) realizes a coface of the context with domain `D*` and the
prescribed pattern, correctness projects its label to `P`, and exact consistency projects
the realization. -/
theorem onePointOccurrence_of_entailmentCertificate {W : KnightRealization α M}
    (hW : W.IsModel) {n : ℕ} {t : Fin n ↪ M} {P : S α.1 (n + 1)}
    (C : EntailmentCertificate W t P) :
    ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ W.eval u = some P := by
  obtain ⟨y, hy, q, hqU, hcof, hq⟩ :=
    hW.bottomPattern C.ctx C.p₀ C.eval_ctx C.D C.extendsDomain C.q' C.respects C.extends_label
  refine ⟨(onePointProj C.proj).trans (snoc C.ctx y hy), ?_, ?_⟩
  · ext i
    change snoc C.ctx y hy (onePointProj C.proj (Fin.castSucc i)) = t i
    rw [onePointProj_castSucc, snoc_apply_castSucc]
    exact congrArg (fun e : Fin n ↪ M => e i) C.proj_ctx
  · rw [exactParent_typeMap hW.consistent _ q _ hq]
    exact C.correct q hqU hcof

/-- **Certificates for every selected request = literal one-point rooted transfer**: the
producer obligation of the upper-bound route, request by request. -/
def EntailmentCertificateSupply (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ (P : S α.1 (n + 1)), typeMap Fin.castSuccEmb P = some p → Adm Fin.castSuccEmb p P →
      Nonempty (EntailmentCertificate W t P)

/-- Certificates give literal one-point rooted transfer. -/
theorem onePointRootedExtensionOver_of_certificates {W : KnightRealization α M}
    (hW : W.IsModel) {c : ℕ} {core : Fin c ↪ M} {Adm : RootedAdmissibility α}
    (h : EntailmentCertificateSupply W core Adm) : OnePointRootedExtensionOver W core Adm :=
  fun t p hroot ht P hP hadm =>
    (h t p hroot ht P hP hadm).elim fun C => onePointOccurrence_of_entailmentCertificate hW C

/-- Certificates give finite rooted transfer (trivial admissibility, by the one-point
iteration). -/
theorem rootedExtensionOver_of_certificates {W : KnightRealization α M} (hW : W.IsModel)
    {c : ℕ} {core : Fin c ↪ M} (h : EntailmentCertificateSupply W core (AdmTop α)) :
    RootedExtensionOver W core (AdmTop α) :=
  rootedExtensionOver_of_onePoint hW.consistent (onePointRootedExtensionOver_of_certificates hW h)

/-- Under trivial admissibility every realized rooted extension is admissible. -/
theorem realizedAdmissibleOver_admTop (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M) :
    RealizedAdmissibleOver W core (AdmTop α) :=
  fun _ _ _ _ _ _ _ _ _ => trivial

/-- **The quotient-local terminal consumer from certificates**: certificate supplies over the
two selected cores give the selected common-chart step between two models. -/
theorem restrictedStepSupply_of_certificates {M₁ M₂ : Type w}
    {W₁ : KnightRealization α M₁} {W₂ : KnightRealization α M₂}
    (h₁ : W₁.IsModel) (h₂ : W₂.IsModel) {c : ℕ} (core₁ : Fin c ↪ M₁) (core₂ : Fin c ↪ M₂)
    (hc₁ : EntailmentCertificateSupply W₁ core₁ (AdmTop α))
    (hc₂ : EntailmentCertificateSupply W₂ core₂ (AdmTop α)) :
    RestrictedCommonChartStepSupply (A₁ := W₁) (A₂ := W₂) (ContainsCores core₁ core₂) :=
  restrictedStepSupply_of_rootedExtension h₁.consistent h₂.consistent h₁.covering h₂.covering
    (AdmTop α) core₁ core₂ (rootedExtensionOver_of_certificates h₁ hc₁)
    (rootedExtensionOver_of_certificates h₂ hc₂) (realizedAdmissibleOver_admTop W₁ core₁)
    (realizedAdmissibleOver_admTop W₂ core₂)

end VaughtConjecture.Knight
