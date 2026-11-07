/-
PhotoLean.RelationAudit.BoundedAudit.R3 — R3 bounded screening evidence.

This module is additive. It imports the delivered theory modules and the audit semantic
core, and it changes no delivered statement. It carries only the certificates needed by the
eleven-pair R3 screening package (the missing surface pair plus the ten quenching /
quantum-yield pairs) when the legacy registry has no certificate of the required kind.

Each certificate wraps a delivered theorem from `PhotoLean/Relations.lean` §7, §11 or §15.
No statement is weakened, no new physical claim is introduced, and no delivered file is
modified. Every declaration is fully proved; there is no unproved placeholder and no custom
axiomatic declaration in this file.

Sections:

* §1 Marcus / SymmetryFactor: the Marcus barrier is the equal-curvature SymmetryFactor
  reactant surface at the β = 1/2 crossing coordinate (transitive-via-kernel tie-back).
* §2 Marcus / Kasha: Kasha conformance is a bound on the Marcus barrier (§7 bridge).
* §3 Kasha / QuantumYield: the ladder radiative branch is the two-channel quantum yield.
* §4 SternVolmer / QuantumYield: dynamic quenching dilutes the quantum yield.
* §5 SternVolmer / FluorPhos: the S₁ fluorescence/phosphorescence ratio is quench-invariant.
* §6 QuantumYield / FluorPhos: the fluorescence yield is the three-channel quantum yield,
  and the phosphorescence yield is a cascade of two quantum yields.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations

set_option autoImplicit false

noncomputable section

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace R3

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

/-! ## §1 — Marcus / SymmetryFactor (observational equivalence)

The delivered §11 tie-back `symmetryFactor_tsCoordZero_eq_kernel` identifies the
equal-curvature SymmetryFactor crossing coordinate with the kernel coordinate
`Kernel.tsCoord lam 0`. The delivered §1 pin `kernel_barrier_eq_marcus` is a definitional
identity between the kernel barrier and the Marcus barrier. The kernel coordinate is the
crossing point of the equal-curvature two-parabola surfaces, so the Marcus barrier at
thermoneutrality is exactly the SymmetryFactor equal-curvature reactant surface evaluated at
its β = 1/2 crossing coordinate. The channel observes that barrier height. -/

/-- Shared context of the Marcus/SymmetryFactor thermoneutral comparison. -/
structure MarcusSymFactorCtx where
  lam : ℝ

/-- The curvature is physical. -/
def pMarcusSymFactorLamPositive : Premise MarcusSymFactorCtx :=
  mkPremise "marcusSymmetryFactor.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the thermoneutral barrier comparison. -/
def marcusSymFactorPremises : List (Premise MarcusSymFactorCtx) :=
  [pMarcusSymFactorLamPositive]

/-- The two readings compared by the tie-back. -/
def marcusSymFactorSetup : ObservationalSetup MarcusSymFactorCtx where
  left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "MarcusSymFactorCtx"
    "PhotoLean/Marcus/Basic.lean#barrier"
  right := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.asymReactantSurface"
    "MarcusSymFactorCtx" "PhotoLean/SymmetryFactor/Basic.lean#asymReactantSurface"
  leftState := MarcusSymFactorCtx
  rightState := MarcusSymFactorCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The thermoneutral barrier-height channel. -/
noncomputable def marcusSymFactorChannel :
    Channel MarcusSymFactorCtx marcusSymFactorSetup ℝ Unit where
  name := "thermoneutralBarrierHeight"
  domain := Set.univ
  leftObs := fun δ _ => Marcus.barrier δ.lam 0
  rightObs := fun δ _ =>
    SymmetryFactor.asymReactantSurface δ.lam
      (SymmetryFactor.tsCoordZero δ.lam δ.lam)

/-- Observational equivalence: the Marcus thermoneutral barrier is the equal-curvature
SymmetryFactor reactant surface at the β = 1/2 crossing coordinate. -/
noncomputable def marcusSymFactorBarrierBridge : Certificate MarcusSymFactorCtx :=
  .observationalEquivalence marcusSymFactorSetup marcusSymFactorPremises ℝ Unit
    [marcusSymFactorChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      have hlam : 0 < δ.lam :=
        hprem pMarcusSymFactorLamPositive (by simp [marcusSymFactorPremises])
      rcases List.mem_singleton.mp hc with rfl
      show Marcus.barrier δ.lam 0 =
        SymmetryFactor.asymReactantSurface δ.lam
          (SymmetryFactor.tsCoordZero δ.lam δ.lam)
      rw [Relations.symmetryFactor_tsCoordZero_eq_kernel hlam]
      rw [← Relations.kernel_barrier_eq_marcus]
      unfold Kernel.barrier SymmetryFactor.asymReactantSurface Kernel.tsCoord
      field_simp
      ring)

/-- Source coherence: the delivered §11 tie-back plus the kernel/Marcus barrier pin. -/
theorem marcusSymFactorBarrierBridge_source (δ : MarcusSymFactorCtx) (hlam : 0 < δ.lam) :
    Marcus.barrier δ.lam 0 =
      SymmetryFactor.asymReactantSurface δ.lam
        (SymmetryFactor.tsCoordZero δ.lam δ.lam) := by
  rw [Relations.symmetryFactor_tsCoordZero_eq_kernel hlam]
  rw [← Relations.kernel_barrier_eq_marcus]
  unfold Kernel.barrier SymmetryFactor.asymReactantSurface Kernel.tsCoord
  field_simp
  ring

/-- Kind pin: the row is an observational equivalence. -/
theorem marcusSymFactorBarrierBridge_kind :
    certificateKind marcusSymFactorBarrierBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §2 — Marcus / Kasha (equivalence)

The delivered §7 bridge `kashaWithin_one_marcus` states that, under the declared `hic`
identification of the ladder's S₂→S₁ internal-conversion rate with the Marcus-form rate,
Kasha conformance at level 1 is exactly the squared-gap bound
`(lam - x)² ≤ 4 lam (kB T) log K`. Dividing by the positive `4 lam` turns that bound into a
bound on the Marcus barrier `(lam - x)² / (4 lam)`. The certificate compares the Kasha
predicate with the Marcus barrier bound. -/

/-- Shared context of the Marcus/Kasha window bridge. -/
structure MarcusKashaCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ
  tol : ℝ

/-- Ladder admissibility at level 1. -/
def pMarcusKashaRateData : Premise MarcusKashaCtx :=
  mkPremise "kasha.rateData" fun δ => Kasha.RateData δ.rad δ.ic 1

/-- The tolerance is positive. -/
def pMarcusKashaTolPositive : Premise MarcusKashaCtx :=
  mkPremise "kasha.tolerancePositive" fun δ => 0 < δ.tol

/-- The tolerance is below one. -/
def pMarcusKashaTolBelowOne : Premise MarcusKashaCtx :=
  mkPremise "kasha.toleranceBelowOne" fun δ => δ.tol < 1

/-- The Marcus pre-exponential factor is positive. -/
def pMarcusKashaAPositive : Premise MarcusKashaCtx :=
  mkPremise "marcus.preExponentialPositive" fun δ => 0 < δ.A

/-- The Marcus curvature is positive. -/
def pMarcusKashaLamPositive : Premise MarcusKashaCtx :=
  mkPremise "marcus.curvaturePositive" fun δ => 0 < δ.lam

/-- The thermal energy is positive. -/
def pMarcusKashaThermalPositive : Premise MarcusKashaCtx :=
  mkPremise "thermal.energyPositive" fun δ => 0 < δ.kB * δ.T

/-- The lowest-state radiative rate is positive. -/
def pMarcusKashaRadZeroPositive : Premise MarcusKashaCtx :=
  mkPremise "kasha.radZeroPositive" fun δ => 0 < δ.rad 0

/-- The next-state radiative rate is positive. -/
def pMarcusKashaRadOnePositive : Premise MarcusKashaCtx :=
  mkPremise "kasha.radOnePositive" fun δ => 0 < δ.rad 1

/-- The declared `hic` identification of the S₂→S₁ internal-conversion rate with the
Marcus-form rate at the gap. -/
def pMarcusKashaIcIdentification : Premise MarcusKashaCtx :=
  mkPremise "kashaMarcus.icIdentification" fun δ =>
    δ.ic 1 = Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x

/-- Premise set of the Marcus/Kasha window bridge. -/
def marcusKashaPremises : List (Premise MarcusKashaCtx) :=
  [pMarcusKashaRateData, pMarcusKashaTolPositive, pMarcusKashaTolBelowOne,
   pMarcusKashaAPositive, pMarcusKashaLamPositive, pMarcusKashaThermalPositive,
   pMarcusKashaRadZeroPositive, pMarcusKashaRadOnePositive, pMarcusKashaIcIdentification]

/-- The two predicates compared by the bridge. -/
def marcusKashaComparison : Comparison MarcusKashaCtx where
  left := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.KashaWithin" "MarcusKashaCtx"
    "PhotoLean/Kasha/Basic.lean#KashaWithin"
  right := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "MarcusKashaCtx"
    "PhotoLean/Marcus/Basic.lean#barrier"
  leftContext := MarcusKashaCtx
  rightContext := MarcusKashaCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => Kasha.KashaWithin δ.rad δ.ic δ.tol 1
  rightPredicate := fun δ =>
    Marcus.barrier δ.lam δ.x ≤
      δ.kB * δ.T *
        Real.log (Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
          (δ.rad 1) δ.tol)

/-- The typed equivalence link: Kasha conformance at level 1 is a Marcus barrier bound. -/
noncomputable def marcusKashaLink : ParentCertificate MarcusKashaCtx :=
  .equivalence "Q-R3-MK-01" marcusKashaComparison marcusKashaPremises
    (fun δ hprem => by
      have h : Kasha.RateData δ.rad δ.ic 1 :=
        hprem pMarcusKashaRateData (by simp [marcusKashaPremises])
      have htol0 : 0 < δ.tol :=
        hprem pMarcusKashaTolPositive (by simp [marcusKashaPremises])
      have htol1 : δ.tol < 1 :=
        hprem pMarcusKashaTolBelowOne (by simp [marcusKashaPremises])
      have hA : 0 < δ.A :=
        hprem pMarcusKashaAPositive (by simp [marcusKashaPremises])
      have hlam : 0 < δ.lam :=
        hprem pMarcusKashaLamPositive (by simp [marcusKashaPremises])
      have hkT : 0 < δ.kB * δ.T :=
        hprem pMarcusKashaThermalPositive (by simp [marcusKashaPremises])
      have hr0 : 0 < δ.rad 0 :=
        hprem pMarcusKashaRadZeroPositive (by simp [marcusKashaPremises])
      have hr1 : 0 < δ.rad 1 :=
        hprem pMarcusKashaRadOnePositive (by simp [marcusKashaPremises])
      have hic : δ.ic 1 = Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x :=
        hprem pMarcusKashaIcIdentification (by simp [marcusKashaPremises])
      have hbridge :=
        Kasha.kashaWithin_one_marcus h htol0 htol1 hA hlam hkT hr0 hr1 hic
      set K := Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
        (δ.rad 1) δ.tol with hK
      have h4 : (0 : ℝ) < 4 * δ.lam := by linarith
      constructor
      · intro hc
        have hsq : (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) * Real.log K :=
          hbridge.mp hc
        show Marcus.barrier δ.lam δ.x ≤ δ.kB * δ.T * Real.log K
        rw [show Marcus.barrier δ.lam δ.x = (δ.lam - δ.x) ^ 2 / (4 * δ.lam) from rfl]
        rw [div_le_iff₀ h4]
        calc (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) * Real.log K := hsq
          _ = δ.kB * δ.T * Real.log K * (4 * δ.lam) := by ring
      · intro hb
        have hb' : (δ.lam - δ.x) ^ 2 / (4 * δ.lam) ≤ δ.kB * δ.T * Real.log K := hb
        rw [div_le_iff₀ h4] at hb'
        apply hbridge.mpr
        calc (δ.lam - δ.x) ^ 2 ≤ δ.kB * δ.T * Real.log K * (4 * δ.lam) := hb'
          _ = 4 * δ.lam * (δ.kB * δ.T) * Real.log K := by ring)

/-- Equivalence certificate: Kasha conformance at level 1 is a Marcus barrier bound. -/
noncomputable def marcusKashaWindowBridge : Certificate MarcusKashaCtx :=
  .equivalence marcusKashaLink rfl

/-- Source coherence: the delivered §7 bridge. -/
theorem marcusKashaWindowBridge_source (δ : MarcusKashaCtx)
    (h : Kasha.RateData δ.rad δ.ic 1) (htol0 : 0 < δ.tol) (htol1 : δ.tol < 1)
    (hA : 0 < δ.A) (hlam : 0 < δ.lam) (hkT : 0 < δ.kB * δ.T)
    (hr0 : 0 < δ.rad 0) (hr1 : 0 < δ.rad 1)
    (hic : δ.ic 1 = Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x) :
    Kasha.KashaWithin δ.rad δ.ic δ.tol 1 ↔
      Marcus.barrier δ.lam δ.x ≤
        δ.kB * δ.T *
          Real.log (Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
            (δ.rad 1) δ.tol) := by
  have hbridge := Kasha.kashaWithin_one_marcus h htol0 htol1 hA hlam hkT hr0 hr1 hic
  set K := Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
    (δ.rad 1) δ.tol with hK
  have h4 : (0 : ℝ) < 4 * δ.lam := by linarith
  constructor
  · intro hc
    have hsq : (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) * Real.log K :=
      hbridge.mp hc
    rw [show Marcus.barrier δ.lam δ.x = (δ.lam - δ.x) ^ 2 / (4 * δ.lam) from rfl]
    rw [div_le_iff₀ h4]
    calc (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) * Real.log K := hsq
      _ = δ.kB * δ.T * Real.log K * (4 * δ.lam) := by ring
  · intro hb
    have hb' : (δ.lam - δ.x) ^ 2 / (4 * δ.lam) ≤ δ.kB * δ.T * Real.log K := hb
    rw [div_le_iff₀ h4] at hb'
    apply hbridge.mpr
    calc (δ.lam - δ.x) ^ 2 ≤ δ.kB * δ.T * Real.log K * (4 * δ.lam) := hb'
      _ = 4 * δ.lam * (δ.kB * δ.T) * Real.log K := by ring

/-- Kind pin: the row is an equivalence. -/
theorem marcusKashaWindowBridge_kind :
    certificateKind marcusKashaWindowBridge = RelationKind.equivalence := rfl

/-! ## §3 — Kasha / QuantumYield (observational equivalence)

The delivered §15 row `kasha_radBranch_eq_yieldOf` identifies the ladder's radiative branch
with the two-channel quantum yield of `(rad n, ic n)`. The channel observes the yield. -/

/-- Shared context of the Kasha/QuantumYield comparison. -/
structure KashaQyCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  n : ℕ

/-- The two readings compared by the yield identity. -/
def kashaQySetup : ObservationalSetup KashaQyCtx where
  left := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.radBranch" "KashaQyCtx"
    "PhotoLean/Kasha/Basic.lean#radBranch"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "KashaQyCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := KashaQyCtx
  rightState := KashaQyCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The radiative-branch yield channel. -/
noncomputable def kashaQyChannel : Channel KashaQyCtx kashaQySetup ℝ Unit where
  name := "radiativeBranchYield"
  domain := Set.univ
  leftObs := fun δ _ => Kasha.radBranch δ.rad δ.ic δ.n
  rightObs := fun δ _ => QuantumYield.yieldOf ![δ.rad δ.n, δ.ic δ.n] 0

/-- Observational equivalence: the ladder radiative branch is the two-channel yield. -/
noncomputable def kashaRadiativeBranchYieldBridge : Certificate KashaQyCtx :=
  .observationalEquivalence kashaQySetup [] ℝ Unit [kashaQyChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact Relations.kasha_radBranch_eq_yieldOf δ.rad δ.ic δ.n)

/-- Source coherence: the delivered §15 row. -/
theorem kashaRadiativeBranchYieldBridge_source (δ : KashaQyCtx) :
    Kasha.radBranch δ.rad δ.ic δ.n =
      QuantumYield.yieldOf ![δ.rad δ.n, δ.ic δ.n] 0 :=
  Relations.kasha_radBranch_eq_yieldOf δ.rad δ.ic δ.n

/-- Kind pin: the row is an observational equivalence. -/
theorem kashaRadiativeBranchYieldBridge_kind :
    certificateKind kashaRadiativeBranchYieldBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §4 — SternVolmer / QuantumYield (observational equivalence)

The delivered §15 row `sv_quench_dilutes_yield` states that the unquenched yield is the
quenched yield times the Stern–Volmer dynamic ratio. The channel observes the yield. -/

/-- Shared context of the SternVolmer/QuantumYield dilution identity. -/
structure SvQyCtx where
  kr : ℝ
  knr : ℝ
  kq : ℝ
  q : ℝ

/-- The unquenched total rate is positive. -/
def pSvQyTotalPositive : Premise SvQyCtx :=
  mkPremise "sternVolmer.totalRatePositive" fun δ => 0 < δ.kr + δ.knr

/-- The added quench channel is nonnegative. -/
def pSvQyQuenchNonnegative : Premise SvQyCtx :=
  mkPremise "sternVolmer.quenchNonnegative" fun δ => 0 ≤ δ.kq * δ.q

/-- Premise set of the yield-dilution identity. -/
def svQyPremises : List (Premise SvQyCtx) :=
  [pSvQyTotalPositive, pSvQyQuenchNonnegative]

/-- The two readings compared by the dilution identity. -/
def svQySetup : ObservationalSetup SvQyCtx where
  left := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "SvQyCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  right := mkRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.svRatioDyn" "SvQyCtx"
    "PhotoLean/SternVolmer/Basic.lean#svRatioDyn"
  leftState := SvQyCtx
  rightState := SvQyCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The yield channel: unquenched yield against quenched yield times the SV ratio. -/
noncomputable def svQyChannel : Channel SvQyCtx svQySetup ℝ Unit where
  name := "quenchedQuantumYield"
  domain := Set.univ
  leftObs := fun δ _ => QuantumYield.yieldOf ![δ.kr, δ.knr] 0
  rightObs := fun δ _ =>
    QuantumYield.yieldOf ![δ.kr, δ.knr + δ.kq * δ.q] 0 *
      SternVolmer.svRatioDyn (δ.kr + δ.knr) δ.kq δ.q

/-- Observational equivalence: dynamic quenching dilutes the quantum yield. -/
noncomputable def svQuenchDilutesYieldBridge : Certificate SvQyCtx :=
  .observationalEquivalence svQySetup svQyPremises ℝ Unit [svQyChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      have hpos : 0 < δ.kr + δ.knr :=
        hprem pSvQyTotalPositive (by simp [svQyPremises])
      have hq : 0 ≤ δ.kq * δ.q :=
        hprem pSvQyQuenchNonnegative (by simp [svQyPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact Relations.sv_quench_dilutes_yield δ.kr δ.knr δ.kq δ.q hpos hq)

/-- Source coherence: the delivered §15 row. -/
theorem svQuenchDilutesYieldBridge_source (δ : SvQyCtx)
    (hpos : 0 < δ.kr + δ.knr) (hq : 0 ≤ δ.kq * δ.q) :
    QuantumYield.yieldOf ![δ.kr, δ.knr] 0 =
      QuantumYield.yieldOf ![δ.kr, δ.knr + δ.kq * δ.q] 0 *
        SternVolmer.svRatioDyn (δ.kr + δ.knr) δ.kq δ.q :=
  Relations.sv_quench_dilutes_yield δ.kr δ.knr δ.kq δ.q hpos hq

/-- Kind pin: the row is an observational equivalence. -/
theorem svQuenchDilutesYieldBridge_kind :
    certificateKind svQuenchDilutesYieldBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §5 — SternVolmer / FluorPhos (observational equivalence)

The delivered §15 row `fpRatio_invariant_under_quench` states that adding the dynamic-quench
channel `kq·q` to the S₁ nonradiative rate leaves the fluorescence/phosphorescence ratio
unchanged. The shared context explicitly translates the Stern–Volmer quencher concentration
into the added nonradiative channel. -/

/-- Shared context of the SternVolmer/FluorPhos quench-invariance identity. -/
structure SvFpCtx where
  kF : ℝ
  kISC : ℝ
  kIC : ℝ
  kP : ℝ
  kNR : ℝ
  kq : ℝ
  q : ℝ

/-- The S₁ radiative rate is positive. -/
def pSvFpKrPositive : Premise SvFpCtx :=
  mkPremise "fluorPhos.radiativeRatePositive" fun δ => 0 < δ.kF

/-- The unquenched S₁ total decay is positive. -/
def pSvFpS1Positive : Premise SvFpCtx :=
  mkPremise "fluorPhos.s1DecayPositive" fun δ => 0 < FluorPhos.s1Decay δ.kF δ.kISC δ.kIC

/-- The quenched S₁ total decay is positive. -/
def pSvFpS1QuenchedPositive : Premise SvFpCtx :=
  mkPremise "fluorPhos.s1DecayQuenchedPositive" fun δ =>
    0 < FluorPhos.s1Decay δ.kF δ.kISC (δ.kIC + δ.kq * δ.q)

/-- The T₁ total decay is positive. -/
def pSvFpT1Positive : Premise SvFpCtx :=
  mkPremise "fluorPhos.t1DecayPositive" fun δ => 0 < δ.kP + δ.kNR

/-- Premise set of the quench-invariance identity. -/
def svFpPremises : List (Premise SvFpCtx) :=
  [pSvFpKrPositive, pSvFpS1Positive, pSvFpS1QuenchedPositive, pSvFpT1Positive]

/-- The two readings compared by the quench-invariance identity. -/
def svFpSetup : ObservationalSetup SvFpCtx where
  left := mkRef "PhotoLean.FluorPhos" "PhotoLean.FluorPhos.phiP" "SvFpCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiP"
  right := mkRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.dynDecay" "SvFpCtx"
    "PhotoLean/SternVolmer/Basic.lean#dynDecay"
  leftState := SvFpCtx
  rightState := SvFpCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The fluorescence/phosphorescence-ratio channel. -/
noncomputable def svFpChannel : Channel SvFpCtx svFpSetup ℝ Unit where
  name := "fluorescencePhosphorescenceRatio"
  domain := Set.univ
  leftObs := fun δ _ =>
    FluorPhos.phiP δ.kF δ.kISC δ.kIC δ.kP δ.kNR /
      FluorPhos.phiF δ.kF δ.kISC δ.kIC
  rightObs := fun δ _ =>
    FluorPhos.phiP δ.kF δ.kISC (δ.kIC + δ.kq * δ.q) δ.kP δ.kNR /
      FluorPhos.phiF δ.kF δ.kISC (δ.kIC + δ.kq * δ.q)

/-- Observational equivalence: the FP ratio is invariant under the SV quench channel. -/
noncomputable def fpRatioInvariantBridge : Certificate SvFpCtx :=
  .observationalEquivalence svFpSetup svFpPremises ℝ Unit [svFpChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      have hkF : 0 < δ.kF :=
        hprem pSvFpKrPositive (by simp [svFpPremises])
      have hs1 : 0 < FluorPhos.s1Decay δ.kF δ.kISC δ.kIC :=
        hprem pSvFpS1Positive (by simp [svFpPremises])
      have hs1q : 0 < FluorPhos.s1Decay δ.kF δ.kISC (δ.kIC + δ.kq * δ.q) :=
        hprem pSvFpS1QuenchedPositive (by simp [svFpPremises])
      have ht1 : 0 < δ.kP + δ.kNR :=
        hprem pSvFpT1Positive (by simp [svFpPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact (Relations.fpRatio_invariant_under_quench hkF hs1 hs1q ht1).symm)

/-- Source coherence: the delivered §15 row. -/
theorem fpRatioInvariantBridge_source (δ : SvFpCtx)
    (hkF : 0 < δ.kF) (hs1 : 0 < FluorPhos.s1Decay δ.kF δ.kISC δ.kIC)
    (hs1q : 0 < FluorPhos.s1Decay δ.kF δ.kISC (δ.kIC + δ.kq * δ.q))
    (ht1 : 0 < δ.kP + δ.kNR) :
    FluorPhos.phiP δ.kF δ.kISC δ.kIC δ.kP δ.kNR /
        FluorPhos.phiF δ.kF δ.kISC δ.kIC =
      FluorPhos.phiP δ.kF δ.kISC (δ.kIC + δ.kq * δ.q) δ.kP δ.kNR /
        FluorPhos.phiF δ.kF δ.kISC (δ.kIC + δ.kq * δ.q) :=
  (Relations.fpRatio_invariant_under_quench hkF hs1 hs1q ht1).symm

/-- Kind pin: the row is an observational equivalence. -/
theorem fpRatioInvariantBridge_kind :
    certificateKind fpRatioInvariantBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §6 — QuantumYield / FluorPhos (two observational equivalences)

The delivered §15 rows `phiF_eq_yieldOf` and `phiP_eq_yieldOf_cascade` identify the
fluorescence yield with the three-channel quantum yield and the phosphorescence yield with a
cascade of two quantum yields. -/

/-- Shared context of the FluorPhos/QuantumYield fluorescence comparison. -/
structure FpQyCtx where
  kF : ℝ
  kISC : ℝ
  kIC : ℝ

/-- The two readings compared by the fluorescence identity. -/
def fpQySetup : ObservationalSetup FpQyCtx where
  left := mkRef "PhotoLean.FluorPhos" "PhotoLean.FluorPhos.phiF" "FpQyCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiF"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "FpQyCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := FpQyCtx
  rightState := FpQyCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The fluorescence-yield channel. -/
noncomputable def fpQyChannel : Channel FpQyCtx fpQySetup ℝ Unit where
  name := "fluorescenceYield"
  domain := Set.univ
  leftObs := fun δ _ => FluorPhos.phiF δ.kF δ.kISC δ.kIC
  rightObs := fun δ _ => QuantumYield.yieldOf ![δ.kF, δ.kISC, δ.kIC] 0

/-- Observational equivalence: the fluorescence yield is the three-channel yield. -/
noncomputable def fluorPhosPhiFYieldBridge : Certificate FpQyCtx :=
  .observationalEquivalence fpQySetup [] ℝ Unit [fpQyChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact Relations.phiF_eq_yieldOf δ.kF δ.kISC δ.kIC)

/-- Source coherence: the delivered §15 fluorescence row. -/
theorem fluorPhosPhiFYieldBridge_source (δ : FpQyCtx) :
    FluorPhos.phiF δ.kF δ.kISC δ.kIC =
      QuantumYield.yieldOf ![δ.kF, δ.kISC, δ.kIC] 0 :=
  Relations.phiF_eq_yieldOf δ.kF δ.kISC δ.kIC

/-- Kind pin: the row is an observational equivalence. -/
theorem fluorPhosPhiFYieldBridge_kind :
    certificateKind fluorPhosPhiFYieldBridge =
      RelationKind.observationalEquivalence := rfl

/-- Shared context of the FluorPhos/QuantumYield phosphorescence comparison. -/
structure FpQyCascadeCtx where
  kF : ℝ
  kISC : ℝ
  kIC : ℝ
  kP : ℝ
  kNR : ℝ

/-- The two readings compared by the phosphorescence cascade identity. -/
def fpQyCascadeSetup : ObservationalSetup FpQyCascadeCtx where
  left := mkRef "PhotoLean.FluorPhos" "PhotoLean.FluorPhos.phiP" "FpQyCascadeCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiP"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "FpQyCascadeCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := FpQyCascadeCtx
  rightState := FpQyCascadeCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The phosphorescence-yield channel. -/
noncomputable def fpQyCascadeChannel : Channel FpQyCascadeCtx fpQyCascadeSetup ℝ Unit where
  name := "phosphorescenceYield"
  domain := Set.univ
  leftObs := fun δ _ => FluorPhos.phiP δ.kF δ.kISC δ.kIC δ.kP δ.kNR
  rightObs := fun δ _ =>
    QuantumYield.yieldOf ![δ.kF, δ.kISC, δ.kIC] 1 *
      QuantumYield.yieldOf ![δ.kP, δ.kNR] 0

/-- Observational equivalence: the phosphorescence yield is the cascade of two yields. -/
noncomputable def fluorPhosPhiPYieldCascadeBridge : Certificate FpQyCascadeCtx :=
  .observationalEquivalence fpQyCascadeSetup [] ℝ Unit [fpQyCascadeChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact Relations.phiP_eq_yieldOf_cascade δ.kF δ.kISC δ.kIC δ.kP δ.kNR)

/-- Source coherence: the delivered §15 phosphorescence row. -/
theorem fluorPhosPhiPYieldCascadeBridge_source (δ : FpQyCascadeCtx) :
    FluorPhos.phiP δ.kF δ.kISC δ.kIC δ.kP δ.kNR =
      QuantumYield.yieldOf ![δ.kF, δ.kISC, δ.kIC] 1 *
        QuantumYield.yieldOf ![δ.kP, δ.kNR] 0 :=
  Relations.phiP_eq_yieldOf_cascade δ.kF δ.kISC δ.kIC δ.kP δ.kNR

/-- Kind pin: the row is an observational equivalence. -/
theorem fluorPhosPhiPYieldCascadeBridge_kind :
    certificateKind fluorPhosPhiPYieldCascadeBridge =
      RelationKind.observationalEquivalence := rfl

end R3
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the R3 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.marcusSymFactorBarrierBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.marcusKashaWindowBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.kashaRadiativeBranchYieldBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.svQuenchDilutesYieldBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.fpRatioInvariantBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.fluorPhosPhiFYieldBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.R3.fluorPhosPhiPYieldCascadeBridge
