/-
PhotoLean.RelationAudit.BoundedAudit.RAD2 — R5 Package RAD2 bounded screening evidence.

This module is additive. It imports the delivered theory modules and the audit semantic
core, and it changes no delivered statement. It carries only the four certificates needed
by the sixteen-pair RAD2 screening package when the legacy registry has no certificate of
the required kind. Every declaration is fully proved; there is no unproved placeholder and
no custom axiomatic declaration in this file.

The four certificates are observational-equivalence rows on explicit shared contexts:

* QY-EG: the quantum-yield radiative/nonradiative branch ratio equals the energy-gap-law
  rate ratio written through `nrBarrier`;
* QY-IC: the quantum-yield ISC/IC branch ratio equals the IC-vs-ISC spin/FC rate ratio;
* QY-FO: the Förster transfer efficiency equals one minus the donor quantum yield of the
  added-channel model;
* QY-EB: the Einstein radiative fraction `A * tauR (A + kNR)` equals the two-channel
  quantum yield of the radiative channel.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations
import PhotoLean.QuantumYield.Basic
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.ICvsISC.Basic
import PhotoLean.Forster.Basic
import PhotoLean.Einstein.Basic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open PhotoLean.RelationAudit

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace RAD2

/-! ## Local metadata helpers -/

/-- Build a statement reference. Content hashes live in the JSON screening layer. -/
def mkRef (theory statementId context provenance : String) : StatementRef where
  theory := theory
  statementId := statementId
  artifactVersion := "PhotoLean@0.1.0+lean-toolchain:v4.17.0"
  context := context
  provenance := provenance

/-- Build a named premise on a shared context. -/
def mkPremise {Δ : Type} (id : String) (predicate : Δ → Prop) : Premise Δ :=
  ⟨id, predicate⟩

/-! ## §1 — QuantumYield / EnergyGapLaw (observational equivalence)

The quantum-yield branch ratio of a radiative channel against an energy-gap-law
nonradiative channel is the ratio of their rates. Writing the EGL rate through its barrier
turns the spectroscopic branch ratio into an explicit exponential of the nonradiative
barrier. The premise bundle is exactly the positivity the division and the exponential
reading need. -/

/-- Shared context of the QY/EGL branch-ratio comparison. -/
structure QyEgCtx where
  kr : ℝ
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- The radiative rate is positive. -/
def pQyEgKr : Premise QyEgCtx := mkPremise "qyEg.krPositive" fun δ => 0 < δ.kr

/-- The EGL pre-exponential factor is positive. -/
def pQyEgA : Premise QyEgCtx := mkPremise "qyEg.preFactorPositive" fun δ => 0 < δ.A

/-- Premise set of the branch-ratio comparison. The totalized division makes the
`kB * T > 0` reading non-load-bearing for this identity, so it is not declared. -/
def qyEgPremises : List (Premise QyEgCtx) := [pQyEgKr, pQyEgA]

/-- The branch-ratio law for a two-channel quantum yield. -/
theorem qyTwoChannelRatio (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PhotoLean.QuantumYield.yieldOf ![a, b] 0
        / PhotoLean.QuantumYield.yieldOf ![a, b] 1 = a / b := by
  unfold PhotoLean.QuantumYield.yieldOf PhotoLean.QuantumYield.totalRate
  rw [Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  field_simp

/-- The branch-ratio law with the second channel in the numerator. -/
theorem qyTwoChannelRatioSwap (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PhotoLean.QuantumYield.yieldOf ![a, b] 1
        / PhotoLean.QuantumYield.yieldOf ![a, b] 0 = b / a := by
  unfold PhotoLean.QuantumYield.yieldOf PhotoLean.QuantumYield.totalRate
  rw [Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  field_simp

/-- The quantum-yield branch ratio against the energy-gap-law channel is the EGL rate
ratio, written through the nonradiative barrier. -/
theorem qyEgBranchRatio (kr A lam kB T x : ℝ) (hkr : 0 < kr) (hA : 0 < A) :
    PhotoLean.QuantumYield.yieldOf
        ![kr, PhotoLean.EnergyGapLaw.nrRate A lam kB T x] 0
        / PhotoLean.QuantumYield.yieldOf
          ![kr, PhotoLean.EnergyGapLaw.nrRate A lam kB T x] 1
      = (kr / A) * Real.exp (PhotoLean.EnergyGapLaw.nrBarrier lam x / (kB * T)) := by
  have hnr : 0 < PhotoLean.EnergyGapLaw.nrRate A lam kB T x := by
    unfold PhotoLean.EnergyGapLaw.nrRate
    exact mul_pos hA (Real.exp_pos _)
  rw [qyTwoChannelRatio kr (PhotoLean.EnergyGapLaw.nrRate A lam kB T x) hkr hnr]
  have hexp : Real.exp (PhotoLean.EnergyGapLaw.nrBarrier lam x / (kB * T))
      = (Real.exp (-(PhotoLean.EnergyGapLaw.nrBarrier lam x) / (kB * T)))⁻¹ := by
    rw [show PhotoLean.EnergyGapLaw.nrBarrier lam x / (kB * T)
          = -(-(PhotoLean.EnergyGapLaw.nrBarrier lam x) / (kB * T)) by ring]
    exact Real.exp_neg _
  unfold PhotoLean.EnergyGapLaw.nrRate
  rw [hexp]
  field_simp [ne_of_gt hA, Real.exp_ne_zero]

/-- The two readings compared by the branch-ratio row. -/
def qyEgSetup : ObservationalSetup QyEgCtx where
  left := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "QyEgCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  right := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrRate" "QyEgCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  leftState := QyEgCtx
  rightState := QyEgCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The radiative/nonradiative branch-ratio channel. -/
def qyEgChannel : Channel QyEgCtx qyEgSetup ℝ Unit where
  name := "radiativeToNonradiativeBranchRatio"
  domain := Set.univ
  leftObs := fun δ _ =>
    PhotoLean.QuantumYield.yieldOf
        ![δ.kr, PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x] 0
        / PhotoLean.QuantumYield.yieldOf
          ![δ.kr, PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x] 1
  rightObs := fun δ _ =>
    (δ.kr / δ.A) * Real.exp (PhotoLean.EnergyGapLaw.nrBarrier δ.lam δ.x / (δ.kB * δ.T))

/-- Observational equivalence of the radiative/nonradiative branch ratio. -/
def qyEgBridge : Certificate QyEgCtx :=
  .observationalEquivalence qyEgSetup qyEgPremises ℝ Unit [qyEgChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact qyEgBranchRatio δ.kr δ.A δ.lam δ.kB δ.T δ.x
        (hprem pQyEgKr (by simp [qyEgPremises]))
        (hprem pQyEgA (by simp [qyEgPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem qyEgBridge_kind :
    certificateKind qyEgBridge = RelationKind.observationalEquivalence := rfl

/-! ## §2 — QuantumYield / ICvsISC (observational equivalence)

The quantum-yield ISC/IC branch ratio is the IC-vs-ISC rate ratio; the delivered
`rate_ratio_eq` writes that ratio as the spin/prefactor factor times the Franck-Condon
exponential. The certificate composes the QY branching observable with the ICvsISC
competition law. -/

/-- Shared context of the QY/ICvsISC branch-ratio comparison. -/
structure QyIcCtx where
  AI : ℝ
  AS : ℝ
  lamI : ℝ
  lamS : ℝ
  kB : ℝ
  T : ℝ
  xI : ℝ
  xS : ℝ
  HSO : ℝ

/-- The ICvsISC premise bundle. -/
def pQyIcData : Premise QyIcCtx :=
  mkPremise "qyIc.fcData" fun δ => PhotoLean.ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T

/-- The spin-orbit coupling is positive (the ISC rate is then positive). -/
def pQyIcHSO : Premise QyIcCtx := mkPremise "qyIc.hsoPositive" fun δ => 0 < δ.HSO

/-- Premise set of the branch-ratio comparison. -/
def qyIcPremises : List (Premise QyIcCtx) := [pQyIcData, pQyIcHSO]

/-- The quantum-yield ISC/IC branch ratio is the IC-vs-ISC spin/FC rate ratio. -/
theorem qyIcBranchRatio (AI AS lamI lamS kB T xI xS HSO : ℝ)
    (h : PhotoLean.ICvsISC.FCData AI AS lamI lamS kB T) (hH : 0 < HSO) :
    PhotoLean.QuantumYield.yieldOf
        ![PhotoLean.ICvsISC.icRate AI lamI kB T xI,
          PhotoLean.ICvsISC.iscRate HSO AS lamS kB T xS] 1
        / PhotoLean.QuantumYield.yieldOf
          ![PhotoLean.ICvsISC.icRate AI lamI kB T xI,
            PhotoLean.ICvsISC.iscRate HSO AS lamS kB T xS] 0
      = (HSO ^ 2 * AS / AI)
        * Real.exp ((PhotoLean.ICvsISC.fcBarrier lamI xI
            - PhotoLean.ICvsISC.fcBarrier lamS xS) / (kB * T)) := by
  have hic : 0 < PhotoLean.ICvsISC.icRate AI lamI kB T xI := by
    unfold PhotoLean.ICvsISC.icRate
    exact mul_pos h.posAI (Real.exp_pos _)
  have hisc : 0 < PhotoLean.ICvsISC.iscRate HSO AS lamS kB T xS := by
    unfold PhotoLean.ICvsISC.iscRate
    exact mul_pos (mul_pos (pow_pos hH 2) h.posAS) (Real.exp_pos _)
  rw [qyTwoChannelRatioSwap (PhotoLean.ICvsISC.icRate AI lamI kB T xI)
    (PhotoLean.ICvsISC.iscRate HSO AS lamS kB T xS) hic hisc]
  exact PhotoLean.ICvsISC.rate_ratio_eq h xI xS HSO

/-- The two readings compared by the branch-ratio row. -/
def qyIcSetup : ObservationalSetup QyIcCtx where
  left := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "QyIcCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  right := mkRef "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.icRate" "QyIcCtx"
    "PhotoLean/ICvsISC/Basic.lean#icRate"
  leftState := QyIcCtx
  rightState := QyIcCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The ISC/IC branch-ratio channel. -/
def qyIcChannel : Channel QyIcCtx qyIcSetup ℝ Unit where
  name := "iscToIcBranchRatio"
  domain := Set.univ
  leftObs := fun δ _ =>
    PhotoLean.QuantumYield.yieldOf
        ![PhotoLean.ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI,
          PhotoLean.ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS] 1
        / PhotoLean.QuantumYield.yieldOf
          ![PhotoLean.ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI,
            PhotoLean.ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS] 0
  rightObs := fun δ _ =>
    (δ.HSO ^ 2 * δ.AS / δ.AI)
      * Real.exp ((PhotoLean.ICvsISC.fcBarrier δ.lamI δ.xI
          - PhotoLean.ICvsISC.fcBarrier δ.lamS δ.xS) / (δ.kB * δ.T))

/-- Observational equivalence of the ISC/IC branch ratio. -/
def qyIcBridge : Certificate QyIcCtx :=
  .observationalEquivalence qyIcSetup qyIcPremises ℝ Unit [qyIcChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact qyIcBranchRatio δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T δ.xI δ.xS δ.HSO
        (hprem pQyIcData (by simp [qyIcPremises]))
        (hprem pQyIcHSO (by simp [qyIcPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem qyIcBridge_kind :
    certificateKind qyIcBridge = RelationKind.observationalEquivalence := rfl

/-! ## §3 — QuantumYield / Forster (observational equivalence)

The Förster transfer efficiency in the added-donor-channel reading is one minus the
donor's retained radiative quantum yield. This consumes the delivered §15 composition row
`fretEff6_eq_one_sub_yieldOf` verbatim. -/

/-- Shared context of the QY/Förster efficiency comparison. -/
structure QyFoCtx where
  kD : ℝ
  r6 : ℝ
  R : ℝ

/-- The donor radiative rate is positive. -/
def pQyFoKD : Premise QyFoCtx := mkPremise "qyFo.donorRatePositive" fun δ => 0 < δ.kD

/-- The Förster sixth power is nonnegative. -/
def pQyFoR6 : Premise QyFoCtx := mkPremise "qyFo.r6Nonnegative" fun δ => 0 ≤ δ.r6

/-- The donor-acceptor separation is nonzero. -/
def pQyFoR : Premise QyFoCtx := mkPremise "qyFo.separationNonzero" fun δ => δ.R ≠ 0

/-- Premise set of the efficiency comparison. -/
def qyFoPremises : List (Premise QyFoCtx) := [pQyFoKD, pQyFoR6, pQyFoR]

/-- The Förster efficiency is one minus the donor's retained yield. -/
theorem qyFoEfficiency (kD r6 R : ℝ) (hkD : 0 < kD) (hr6 : 0 ≤ r6) (hR : R ≠ 0) :
    PhotoLean.Forster.fretEff6 r6 R
      = 1 - PhotoLean.QuantumYield.yieldOf ![kD, kD * (r6 / R ^ 6)] 0 :=
  PhotoLean.Relations.fretEff6_eq_one_sub_yieldOf kD r6 R hkD hr6 hR

/-- The two readings compared by the efficiency row. -/
def qyFoSetup : ObservationalSetup QyFoCtx where
  left := mkRef "PhotoLean.Forster" "PhotoLean.Forster.fretEff6" "QyFoCtx"
    "PhotoLean/Forster/Basic.lean#fretEff6"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "QyFoCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := QyFoCtx
  rightState := QyFoCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The transfer-efficiency channel. -/
def qyFoChannel : Channel QyFoCtx qyFoSetup ℝ Unit where
  name := "transferEfficiencyVersusRetainedDonorYield"
  domain := Set.univ
  leftObs := fun δ _ => PhotoLean.Forster.fretEff6 δ.r6 δ.R
  rightObs := fun δ _ =>
    1 - PhotoLean.QuantumYield.yieldOf ![δ.kD, δ.kD * (δ.r6 / δ.R ^ 6)] 0

/-- Observational equivalence of the transfer efficiency and the retained yield. -/
def qyFoBridge : Certificate QyFoCtx :=
  .observationalEquivalence qyFoSetup qyFoPremises ℝ Unit [qyFoChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact qyFoEfficiency δ.kD δ.r6 δ.R
        (hprem pQyFoKD (by simp [qyFoPremises]))
        (hprem pQyFoR6 (by simp [qyFoPremises]))
        (hprem pQyFoR (by simp [qyFoPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem qyFoBridge_kind :
    certificateKind qyFoBridge = RelationKind.observationalEquivalence := rfl

/-! ## §4 — QuantumYield / Einstein (observational equivalence)

The Einstein radiative fraction `A * tauR (A + kNR)` is the two-channel quantum yield of
the radiative channel. This consumes the delivered §15 composition row
`einstein_yield_via_qy` verbatim; the identity is totalized and carries no premise. -/

/-- Shared context of the QY/Einstein radiative-yield comparison. -/
structure QyEbCtx where
  A : ℝ
  kNR : ℝ

/-- Premise set of the radiative-yield comparison (the identity is totalized). -/
def qyEbPremises : List (Premise QyEbCtx) := []

/-- The Einstein radiative fraction is the two-channel radiative quantum yield. -/
theorem qyEbRadiativeYield (A kNR : ℝ) :
    A * PhotoLean.Einstein.tauR (A + kNR)
      = PhotoLean.QuantumYield.yieldOf ![A, kNR] 0 :=
  PhotoLean.Relations.einstein_yield_via_qy A kNR

/-- The two readings compared by the radiative-yield row. -/
def qyEbSetup : ObservationalSetup QyEbCtx where
  left := mkRef "PhotoLean.Einstein" "PhotoLean.Einstein.tauR" "QyEbCtx"
    "PhotoLean/Einstein/Basic.lean#tauR"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "QyEbCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := QyEbCtx
  rightState := QyEbCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The radiative-fraction channel. -/
def qyEbChannel : Channel QyEbCtx qyEbSetup ℝ Unit where
  name := "radiativeFractionVersusRadiativeYield"
  domain := Set.univ
  leftObs := fun δ _ => δ.A * PhotoLean.Einstein.tauR (δ.A + δ.kNR)
  rightObs := fun δ _ => PhotoLean.QuantumYield.yieldOf ![δ.A, δ.kNR] 0

/-- Observational equivalence of the radiative fraction and the radiative yield. -/
def qyEbBridge : Certificate QyEbCtx :=
  .observationalEquivalence qyEbSetup qyEbPremises ℝ Unit [qyEbChannel] (by decide)
    (fun δ _hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact qyEbRadiativeYield δ.A δ.kNR)

/-- Kind pin: the row is an observational equivalence. -/
theorem qyEbBridge_kind :
    certificateKind qyEbBridge = RelationKind.observationalEquivalence := rfl

end RAD2
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the RAD2 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD2.qyEgBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD2.qyIcBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD2.qyFoBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD2.qyEbBridge
