/-
PhotoLean.RelationAudit.BoundedAudit.Rad3 — R5 radiative-energy-transfer-03 screening evidence.

This module is additive. It imports delivered theory modules and the audit semantic core, and it
changes no delivered statement. It carries the certificates required by the thirteen-pair
`WP-radiative-energy-transfer-03` screening package of R5
(`bounded_audit/r5/radiative-03/`) for the pairs whose outcome is `certified`.

The six theories of this work package (FluorPhos, EnergyGapLaw, StokesShift, ICvsISC, Forster,
Einstein) all describe one excited electronic state and its decay channels, but they describe it
with different vocabularies. Each certificate below is a statement-first comparison under an
explicitly declared shared context, translations, and (where needed) load-bearing premises:

* §1 FluorPhos / ICvsISC: the S1 intersystem-crossing branch at a shut radiative channel is the
  normalized ISC channel of the IC-vs-ISC competition.
* §2 FluorPhos / Forster: the Forster transfer efficiency is the fluorescence branch of the donor
  when the transfer channel carries the radiative branch and the donor decay the loss channel.
* §3 FluorPhos / Einstein: the two-channel fluorescence yield is the Einstein radiative yield.
* §4 EnergyGapLaw / StokesShift: the gap-law barrier vanishes exactly at the closed emission
  window, and the barrier is the squared emission gap over four times the reorganization energy.
* §5 EnergyGapLaw / ICvsISC: the IC channel rate is the gap-law nonradiative rate, and the
  IC-vs-ISC crossover reads with the gap-law rate on the IC side (a typed conditional
  composition).
* §6 StokesShift / ICvsISC: the thermoneutral IC barrier is the Stokes ground surface at the
  equal-curvature crossing coordinate.
* §7 Forster / Einstein: at the Einstein radiative lifetime the Forster rate is the Einstein A
  coefficient times the sixth-power geometric factor.

Every declaration is fully proved; there is no unproved placeholder and no custom axiomatic
declaration in this file. No statement is weakened and no delivered file is modified.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.FluorPhos.Basic
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.EnergyGapLaw.Criterion
import PhotoLean.StokesShift.Basic
import PhotoLean.StokesShift.Criterion
import PhotoLean.ICvsISC.Basic
import PhotoLean.ICvsISC.Criterion
import PhotoLean.Forster.Basic
import PhotoLean.Einstein.Basic
import PhotoLean.Einstein.Criterion

set_option autoImplicit false

noncomputable section

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace Rad3

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

/-! ## §1 FluorPhos / ICvsISC — the S1 ISC branch is the normalized ISC channel

FluorPhos writes the S1 branching as `iscBranch kF kISC kIC = kISC/(kF + kISC + kIC)`. ICvsISC
writes the two channel rates `iscRate HSO AS lamS kB T xS` and `icRate AI lamI kB T xI`. With the
radiative channel shut (`kF = 0`) the FluorPhos branch is exactly the normalized ISC channel of
the IC-vs-ISC competition. The identification is the premise-level `kISC` reading of the two
plans turned into a statement-level comparison: the abstract rate constant `kISC` is the
theory-owned `iscRate`, and `kIC` is the theory-owned `icRate`. -/

/-- Shared context: the two microscopic channel rates of one S1 state. -/
structure FiBranchCtx where
  /-- spin-orbit amplitude of the ISC channel -/
  HSO : ℝ
  /-- ISC base prefactor -/
  AS : ℝ
  /-- ISC reorganization energy -/
  lamS : ℝ
  /-- IC prefactor -/
  AI : ℝ
  /-- IC reorganization energy -/
  lamI : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ
  /-- ISC gap coordinate -/
  xS : ℝ
  /-- IC gap coordinate -/
  xI : ℝ

/-- The two readings compared by the branching identity. -/
def fiBranchSetup : ObservationalSetup FiBranchCtx where
  left := mkRef "FluorPhos" "stmt-FluorPhos-PhotoLean-FluorPhos-iscBranch" "FiBranchCtx"
    "PhotoLean/FluorPhos/Basic.lean#iscBranch"
  right := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-iscRate" "FiBranchCtx"
    "PhotoLean/ICvsISC/Basic.lean#iscRate"
  leftState := FiBranchCtx
  rightState := FiBranchCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The S1 branching channel over the single declared configuration. -/
def fiBranchChannel : Channel FiBranchCtx fiBranchSetup ℝ Unit where
  name := "quantum-yield"
  domain := Set.univ
  leftObs := fun δ _ =>
    FluorPhos.iscBranch 0 (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS)
      (ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)
  rightObs := fun δ _ =>
    ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS /
      (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS +
        ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)

/-- Source coherence: the FluorPhos ISC branch at `kF = 0` is the normalized ISC rate. -/
theorem fiBranchBridge_source (δ : FiBranchCtx) :
    FluorPhos.iscBranch 0 (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS)
        (ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)
      = ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS /
        (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS +
          ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI) := by
  unfold FluorPhos.iscBranch FluorPhos.s1Decay
  ring_nf

/-- Observational equivalence: the ISC branch is the normalized ISC channel. -/
def fiBranchBridge : Certificate FiBranchCtx :=
  .observationalEquivalence fiBranchSetup [] ℝ Unit [fiBranchChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact fiBranchBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem fiBranchBridge_kind :
    certificateKind fiBranchBridge = RelationKind.observationalEquivalence := rfl


/-! ## §1b FluorPhos / ICvsISC — the El-Sayed boundary of the phosphorescence cascade

The ICvsISC ISC rate carries the explicit spin-orbit prefactor `HSO^2 * AS`. FluorPhos writes the
phosphorescence yield as the S1->T1 branch times the T1 radiative branch. Substituting the
theory-owned `iscRate` for the abstract `kISC` turns the El-Sayed boundary into a statement-level
equivalence: at a live triplet radiative channel and a live S1 decay, the phosphorescence yield
vanishes exactly when the spin-orbit ISC channel vanishes, i.e. exactly when `HSO = 0`. This is
the substantive cross-theory content of the El-Sayed premise, not a shared notation. -/

/-- Shared context: the FluorPhos cascade with the ICvsISC theory-owned spin-orbit ISC rate. -/
structure FiElSayedCtx where
  /-- fluorescence rate -/
  kF : ℝ
  /-- internal-conversion rate -/
  kIC : ℝ
  /-- triplet radiative rate -/
  kP : ℝ
  /-- triplet nonradiative rate -/
  kNR : ℝ
  /-- ISC base prefactor -/
  AS : ℝ
  /-- ISC reorganization energy -/
  lamS : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ
  /-- ISC gap coordinate -/
  xS : ℝ
  /-- spin-orbit amplitude -/
  HSO : ℝ

/-- Premise: the triplet radiative rate is nonzero (live phosphorescence channel). -/
def pFiesKP : Premise FiElSayedCtx :=
  mkPremise "RAD3-FIES-kP-nonzero" fun δ => δ.kP ≠ 0

/-- Premise: the total triplet decay is nonzero (the T1 branch divides by `kP + kNR`). -/
def pFiesT : Premise FiElSayedCtx :=
  mkPremise "RAD3-FIES-triplet-total-nonzero" fun δ => δ.kP + δ.kNR ≠ 0

/-- Premise: the ISC base prefactor is nonzero (so `HSO^2 * AS = 0` forces `HSO = 0`). -/
def pFiesAS : Premise FiElSayedCtx :=
  mkPremise "RAD3-FIES-AS-nonzero" fun δ => δ.AS ≠ 0

/-- Premise: the S1 total decay is nonzero (the ISC branch divides by `s1Decay`). -/
def pFiesS1 : Premise FiElSayedCtx :=
  mkPremise "RAD3-FIES-s1decay-nonzero" fun δ =>
    FluorPhos.s1Decay δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC ≠ 0

/-- Premise set of the El-Sayed equivalence. -/
def fiesPremises : List (Premise FiElSayedCtx) := [pFiesKP, pFiesT, pFiesAS, pFiesS1]

/-- The El-Sayed comparison: zero phosphorescence yield against a zero spin-orbit amplitude. -/
def fiElSayedCmp : Comparison FiElSayedCtx where
  left := mkRef "FluorPhos" "stmt-FluorPhos-PhotoLean-FluorPhos-phiP" "FiElSayedCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiP"
  right := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-iscRate" "FiElSayedCtx"
    "PhotoLean/ICvsISC/Basic.lean#iscRate"
  leftContext := FiElSayedCtx
  rightContext := FiElSayedCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ =>
    FluorPhos.phiP δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC δ.kP δ.kNR = 0
  rightPredicate := fun δ => δ.HSO = 0

/-- Source coherence: the phosphorescence yield vanishes exactly with the spin-orbit amplitude. -/
theorem fiElSayed_source (δ : FiElSayedCtx) (hkP : δ.kP ≠ 0)
    (ht : δ.kP + δ.kNR ≠ 0) (hAS : δ.AS ≠ 0)
    (hs : FluorPhos.s1Decay δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC ≠ 0) :
    FluorPhos.phiP δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC δ.kP δ.kNR = 0
      ↔ δ.HSO = 0 := by
  unfold FluorPhos.phiP
  constructor
  · intro hP
    have h1 : FluorPhos.iscBranch δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC = 0 ∨
        FluorPhos.t1BranchP δ.kP δ.kNR = 0 := mul_eq_zero.mp hP
    rcases h1 with h1 | h1
    · have hnum : ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS = 0 := by
        unfold FluorPhos.iscBranch at h1
        rcases div_eq_zero_iff.mp h1 with h | h
        · exact h
        · exact absurd h hs
      unfold ICvsISC.iscRate at hnum
      have hexp : Real.exp (-(ICvsISC.fcBarrier δ.lamS δ.xS) / (δ.kB * δ.T)) ≠ 0 :=
        Real.exp_ne_zero _
      have hprod : δ.HSO ^ 2 * δ.AS = 0 := by
        rcases mul_eq_zero.mp hnum with h | h
        · exact h
        · exact absurd h hexp
      rcases mul_eq_zero.mp hprod with h | h
      · exact sq_eq_zero_iff.mp h
      · exact absurd h hAS
    · unfold FluorPhos.t1BranchP at h1
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact absurd h hkP
      · exact absurd h ht
  · intro h
    rw [h]
    have h0 : FluorPhos.iscBranch δ.kF (ICvsISC.iscRate 0 δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC = 0 := by
      unfold FluorPhos.iscBranch ICvsISC.iscRate
      ring
    rw [h0, zero_mul]

/-- The typed equivalence link: zero phosphorescence yield iff zero spin-orbit amplitude. -/
def fiElSayedLink : ParentCertificate FiElSayedCtx :=
  .equivalence "RAD3-FI-02" fiElSayedCmp fiesPremises
    (fun δ hprem => by
      have hkP : δ.kP ≠ 0 := hprem pFiesKP (by simp [fiesPremises])
      have ht : δ.kP + δ.kNR ≠ 0 := hprem pFiesT (by simp [fiesPremises])
      have hAS : δ.AS ≠ 0 := hprem pFiesAS (by simp [fiesPremises])
      have hs : FluorPhos.s1Decay δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC ≠ 0 :=
        hprem pFiesS1 (by simp [fiesPremises])
      exact fiElSayed_source δ hkP ht hAS hs)

/-- Equivalence certificate: the El-Sayed boundary of the phosphorescence cascade. -/
def fiElSayedBridge : Certificate FiElSayedCtx :=
  .equivalence fiElSayedLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem fiElSayedBridge_kind :
    certificateKind fiElSayedBridge = RelationKind.equivalence := rfl

/-! ## §2 FluorPhos / Forster — the transfer efficiency is the donor radiative branch

Forster writes the transfer efficiency as `fretEff6 r6 R = r6/(r6 + R^6)`. The same number is the
FluorPhos fluorescence branch when the transfer channel carries the radiative slot and the
donor decay carries the loss slot: `phiF kF 0 kIC = kF/(kF + kIC)` with `kF = (1/tauD)(r6/R^6)`
and `kIC = 1/tauD`. The identity needs `tauD != 0` and `R != 0`; both premises are load-bearing
(at `tauD = 0` or `R = 0` the two sides differ). -/

/-- Shared context: a donor with lifetime `tauD`, sixth-power radius `r6` and separation `R`. -/
structure FfTransferCtx where
  /-- donor excited-state lifetime -/
  tauD : ℝ
  /-- sixth power of the Forster radius -/
  r6 : ℝ
  /-- donor-acceptor separation -/
  R : ℝ

/-- The two readings compared by the transfer-efficiency identity. -/
def ffTransferSetup : ObservationalSetup FfTransferCtx where
  left := mkRef "Forster" "stmt-Forster-PhotoLean-Forster-fretEff6" "FfTransferCtx"
    "PhotoLean/Forster/Basic.lean#fretEff6"
  right := mkRef "FluorPhos" "stmt-FluorPhos-PhotoLean-FluorPhos-phiF" "FfTransferCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiF"
  leftState := FfTransferCtx
  rightState := FfTransferCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The transfer-efficiency channel over the single declared configuration. -/
def ffTransferChannel : Channel FfTransferCtx ffTransferSetup ℝ Unit where
  name := "transfer-efficiency"
  domain := Set.univ
  leftObs := fun δ _ => Forster.fretEff6 δ.r6 δ.R
  rightObs := fun δ _ =>
    FluorPhos.phiF ((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) 0 (1 / δ.tauD)

/-- Premise: the donor lifetime is nonzero (it is the reciprocal of the loss rate). -/
def pFfTauNonzero : Premise FfTransferCtx :=
  mkPremise "RAD3-FF-tauD-nonzero" fun δ => δ.tauD ≠ 0

/-- Premise: the separation is nonzero (the sixth power is inverted). -/
def pFfRNonzero : Premise FfTransferCtx :=
  mkPremise "RAD3-FF-R-nonzero" fun δ => δ.R ≠ 0

/-- Premise set of the transfer-efficiency identity. -/
def ffPremises : List (Premise FfTransferCtx) := [pFfTauNonzero, pFfRNonzero]

/-- Source coherence: the Forster efficiency is the donor radiative branch. -/
theorem ffTransferBridge_source (δ : FfTransferCtx) (htau : δ.tauD ≠ 0) (hR : δ.R ≠ 0) :
    Forster.fretEff6 δ.r6 δ.R
      = FluorPhos.phiF ((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) 0 (1 / δ.tauD) := by
  have hR6 : δ.R ^ 6 ≠ 0 := pow_ne_zero 6 hR
  have h1 : Forster.fretEff6 δ.r6 δ.R = δ.r6 / (δ.r6 + δ.R ^ 6) := rfl
  have h2 : FluorPhos.phiF ((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) 0 (1 / δ.tauD)
      = ((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) /
        (((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) + 1 / δ.tauD) := by
    unfold FluorPhos.phiF FluorPhos.s1Decay
    ring_nf
  rw [h1, h2]
  by_cases hsum : δ.r6 + δ.R ^ 6 = 0
  · have hr6 : δ.r6 = - δ.R ^ 6 := by linarith
    rw [hr6]
    field_simp
  · have hD : (1 / δ.tauD) * (δ.r6 / δ.R ^ 6) + 1 / δ.tauD ≠ 0 := by
      have heq : (1 / δ.tauD) * (δ.r6 / δ.R ^ 6) + 1 / δ.tauD
          = (δ.r6 + δ.R ^ 6) / (δ.tauD * δ.R ^ 6) := by
        field_simp
        ring
      rw [heq]
      exact div_ne_zero hsum (mul_ne_zero htau hR6)
    rw [div_eq_div_iff hsum hD]
    field_simp
    ring

/-- Observational equivalence: the transfer efficiency is the donor radiative branch. -/
def ffTransferBridge : Certificate FfTransferCtx :=
  .observationalEquivalence ffTransferSetup ffPremises ℝ Unit [ffTransferChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      have htau : δ.tauD ≠ 0 := hprem pFfTauNonzero (by simp [ffPremises])
      have hR : δ.R ≠ 0 := hprem pFfRNonzero (by simp [ffPremises])
      exact ffTransferBridge_source δ htau hR)

/-- Kind pin: the row is an observational equivalence. -/
theorem ffTransferBridge_kind :
    certificateKind ffTransferBridge = RelationKind.observationalEquivalence := rfl

/-! ## §3 FluorPhos / Einstein — the two-channel fluorescence yield is the radiative yield

`Einstein.yield_radiative` states `A * (1/(A + kNR)) = A/(A + kNR)`: the radiative yield of a
two-channel decay. The FluorPhos fluorescence yield with the IC and ISC channels shut and the
nonradiative slot carrying the Einstein `kNR` is the same real number. The identity is
unconditional because division is totalized in both modules. -/

/-- Shared context: a two-channel emitter with radiative rate `A` and nonradiative rate `kNR`. -/
structure FpEinsCtx where
  /-- Einstein A coefficient (radiative rate) -/
  A : ℝ
  /-- nonradiative rate -/
  kNR : ℝ

/-- The two readings compared by the yield identity. -/
def fpEinsSetup : ObservationalSetup FpEinsCtx where
  left := mkRef "FluorPhos" "stmt-FluorPhos-PhotoLean-FluorPhos-phiF" "FpEinsCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiF"
  right := mkRef "Einstein" "stmt-Einstein-PhotoLean-Einstein-yield_radiative" "FpEinsCtx"
    "PhotoLean/Einstein/Criterion.lean#yield_radiative"
  leftState := FpEinsCtx
  rightState := FpEinsCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The quantum-yield channel over the single declared configuration. -/
def fpEinsChannel : Channel FpEinsCtx fpEinsSetup ℝ Unit where
  name := "quantum-yield"
  domain := Set.univ
  leftObs := fun δ _ => FluorPhos.phiF δ.A 0 δ.kNR
  rightObs := fun δ _ => δ.A * (1 / (δ.A + δ.kNR))

/-- Source coherence: the FluorPhos two-channel yield is the Einstein radiative yield. -/
theorem fpEinsBridge_source (δ : FpEinsCtx) :
    FluorPhos.phiF δ.A 0 δ.kNR = δ.A * (1 / (δ.A + δ.kNR)) := by
  unfold FluorPhos.phiF FluorPhos.s1Decay
  rw [Einstein.yield_radiative]
  congr 1
  ring

/-- Observational equivalence: the two-channel fluorescence yield is the radiative yield. -/
def fpEinsBridge : Certificate FpEinsCtx :=
  .observationalEquivalence fpEinsSetup [] ℝ Unit [fpEinsChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact fpEinsBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem fpEinsBridge_kind :
    certificateKind fpEinsBridge = RelationKind.observationalEquivalence := rfl

/-! ## §4 EnergyGapLaw / StokesShift — the barrier and the emission window

The gap-law barrier is `nrBarrier lam x = (lam - x)^2/(4 lam)` and the Stokes emission energy is
`emEnergy lam x = x - lam`. Two statement-level comparisons follow:

* §4a the barrier vanishes exactly when the vertical emission window closes (`x = lam`); the
  premise `lam != 0` is load-bearing (at `lam = 0` the totalized barrier is `0` at every gap while
  the emission energy is `x`);
* §4b the barrier is the squared emission gap over four times the reorganization energy, the
  quantitative bridge between the kinetic and the optical reading of the same two parabolas. -/

/-- Shared context: reorganization energy `lam` and gap `x`. -/
structure EsGapCtx where
  /-- reorganization energy -/
  lam : ℝ
  /-- energy gap (driving-force convention) -/
  x : ℝ

/-- Premise: the reorganization energy is nonzero (load-bearing for the barrier division). -/
def pEsLamNonzero : Premise EsGapCtx :=
  mkPremise "RAD3-ES-lam-nonzero" fun δ => δ.lam ≠ 0

/-- Premise set of the zero-barrier equivalence. -/
def esPremises : List (Premise EsGapCtx) := [pEsLamNonzero]

/-- The zero-barrier comparison: closed barrier versus closed emission window. -/
def esZeroCmp : Comparison EsGapCtx where
  left := mkRef "EnergyGapLaw" "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier" "EsGapCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrBarrier"
  right := mkRef "StokesShift" "stmt-StokesShift-PhotoLean-StokesShift-emEnergy" "EsGapCtx"
    "PhotoLean/StokesShift/Basic.lean#emEnergy"
  leftContext := EsGapCtx
  rightContext := EsGapCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => EnergyGapLaw.nrBarrier δ.lam δ.x = 0
  rightPredicate := fun δ => StokesShift.emEnergy δ.lam δ.x = 0

/-- Source coherence: the gap-law barrier closes exactly with the emission window. -/
theorem esZeroBarrier_source (δ : EsGapCtx) (hlam : δ.lam ≠ 0) :
    EnergyGapLaw.nrBarrier δ.lam δ.x = 0 ↔ StokesShift.emEnergy δ.lam δ.x = 0 := by
  have hden : 4 * δ.lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  rw [StokesShift.emEnergy_eq]
  unfold EnergyGapLaw.nrBarrier
  constructor
  · intro h
    have hnum : (δ.lam - δ.x) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' hden
    have hz : δ.lam - δ.x = 0 := sq_eq_zero_iff.mp hnum
    linarith
  · intro h
    have hx : δ.x = δ.lam := by linarith
    rw [hx]
    ring

/-- The typed equivalence link: zero gap-law barrier iff closed emission window. -/
def esZeroBarrierLink : ParentCertificate EsGapCtx :=
  .equivalence "RAD3-ES-zero-barrier" esZeroCmp esPremises
    (fun δ hprem => by
      have hlam : δ.lam ≠ 0 := hprem pEsLamNonzero (by simp [esPremises])
      exact esZeroBarrier_source δ hlam)

/-- Equivalence certificate: zero gap-law barrier iff closed emission window. -/
def esZeroBarrierBridge : Certificate EsGapCtx :=
  .equivalence esZeroBarrierLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem esZeroBarrierBridge_kind :
    certificateKind esZeroBarrierBridge = RelationKind.equivalence := rfl

/-- The two readings compared by the quantitative barrier/emission identity. -/
def esBarrierSetup : ObservationalSetup EsGapCtx where
  left := mkRef "EnergyGapLaw" "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier" "EsGapCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrBarrier"
  right := mkRef "StokesShift" "stmt-StokesShift-PhotoLean-StokesShift-emEnergy" "EsGapCtx"
    "PhotoLean/StokesShift/Basic.lean#emEnergy"
  leftState := EsGapCtx
  rightState := EsGapCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The barrier-height channel: the barrier versus the squared emission gap over `4 lam`. -/
def esBarrierChannel : Channel EsGapCtx esBarrierSetup ℝ Unit where
  name := "barrier-height"
  domain := Set.univ
  leftObs := fun δ _ => EnergyGapLaw.nrBarrier δ.lam δ.x
  rightObs := fun δ _ => StokesShift.emEnergy δ.lam δ.x ^ 2 / (4 * δ.lam)

/-- Source coherence: the barrier is the squared emission gap over four times `lam`. -/
theorem esBarrierEmission_source (δ : EsGapCtx) (hlam : δ.lam ≠ 0) :
    EnergyGapLaw.nrBarrier δ.lam δ.x
      = StokesShift.emEnergy δ.lam δ.x ^ 2 / (4 * δ.lam) := by
  rw [StokesShift.emEnergy_eq]
  unfold EnergyGapLaw.nrBarrier
  field_simp
  ring

/-- Observational equivalence: the barrier is the squared emission gap over `4 lam`. -/
def esBarrierEmissionBridge : Certificate EsGapCtx :=
  .observationalEquivalence esBarrierSetup esPremises ℝ Unit [esBarrierChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      have hlam : δ.lam ≠ 0 := hprem pEsLamNonzero (by simp [esPremises])
      exact esBarrierEmission_source δ hlam)

/-- Kind pin: the row is an observational equivalence. -/
theorem esBarrierEmissionBridge_kind :
    certificateKind esBarrierEmissionBridge = RelationKind.observationalEquivalence := rfl

/-! ## §5 EnergyGapLaw / ICvsISC — the IC rate is the gap-law rate and the crossover composes

ICvsISC writes `icRate AI lamI kB T xI = AI * exp(-(fcBarrier lamI xI)/(kB*T))`; EnergyGapLaw
writes `nrRate AI lamI kB T xI = AI * exp(-(nrBarrier lamI xI)/(kB*T))`. The two barriers are
the same body `(lam - x)^2/(4 lam)`, so the two rates are definitionally the same function.

The second query reads the IC-vs-ISC crossover with the gap-law rate on the IC side: a typed
conditional composition of the definitional identification (parent 1) with the delivered
`ICvsISC.isc_dominates_iff` (parent 2). The composition's premise set is exactly the premise set
of parent 2 (`FCData` and `0 < HSO`), both load-bearing there. -/

/-- Shared context of the rate identity: the IC channel parameters. -/
structure EiRateCtx where
  /-- IC prefactor -/
  AI : ℝ
  /-- IC reorganization energy -/
  lamI : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ
  /-- IC gap coordinate -/
  xI : ℝ

/-- The definitional pin of the IC rate against the gap-law rate. -/
def eiRatePin : DefinitionalPin EiRateCtx where
  left := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-icRate" "EiRateCtx"
    "PhotoLean/ICvsISC/Basic.lean#icRate"
  right := mkRef "EnergyGapLaw" "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate" "EiRateCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  leftContext := EiRateCtx
  rightContext := EiRateCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI
  rightTerm := fun δ => EnergyGapLaw.nrRate δ.AI δ.lamI δ.kB δ.T δ.xI
  same := DefEq.refl

/-- Source coherence: the kernel definitional equation, stated explicitly. -/
theorem eiRatePin_source (AI lamI kB T xI : ℝ) :
    ICvsISC.icRate AI lamI kB T xI
      = EnergyGapLaw.nrRate AI lamI kB T xI := by
  unfold ICvsISC.icRate EnergyGapLaw.nrRate ICvsISC.fcBarrier EnergyGapLaw.nrBarrier
  rfl

/-- Definitional identity: the IC channel rate is the gap-law nonradiative rate. -/
def eiRateDefinition : Certificate EiRateCtx :=
  .definitionalIdentity eiRatePin []

/-- Kind pin: the row is a definitional identity. -/
theorem eiRateDefinition_kind :
    certificateKind eiRateDefinition = RelationKind.definitionalIdentity := rfl

/-- Shared context of the crossover composition: both channels of the competition. -/
structure EiCrossCtx where
  /-- IC prefactor -/
  AI : ℝ
  /-- ISC base prefactor -/
  AS : ℝ
  /-- IC reorganization energy -/
  lamI : ℝ
  /-- ISC reorganization energy -/
  lamS : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ
  /-- IC gap coordinate -/
  xI : ℝ
  /-- ISC gap coordinate -/
  xS : ℝ
  /-- spin-orbit amplitude -/
  HSO : ℝ

/-- The middle predicate: the IC rate is below the ISC rate. -/
def eiMidPred (δ : EiCrossCtx) : Prop :=
  ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI
    < ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS

/-- The left predicate: the gap-law rate is below the ISC rate. -/
def eiLeftPred (δ : EiCrossCtx) : Prop :=
  EnergyGapLaw.nrRate δ.AI δ.lamI δ.kB δ.T δ.xI
    < ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS

/-- The right predicate: the barrier threshold of the IC-vs-ISC crossover. -/
def eiRightPred (δ : EiCrossCtx) : Prop :=
  ICvsISC.fcBarrier δ.lamS δ.xS - ICvsISC.fcBarrier δ.lamI δ.xI
    < (δ.kB * δ.T) * (2 * Real.log δ.HSO + Real.log (δ.AS / δ.AI))

/-- Premise: the IC-vs-ISC positivity bundle. -/
def pEiFCData : Premise EiCrossCtx :=
  mkPremise "RAD3-EI-fcdata" fun δ =>
    ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T

/-- Premise: the spin-orbit amplitude is positive. -/
def pEiHsoPos : Premise EiCrossCtx :=
  mkPremise "RAD3-EI-hso-positive" fun δ => 0 < δ.HSO

/-- Premise set of the crossover composition. -/
def eiPremises : List (Premise EiCrossCtx) := [pEiFCData, pEiHsoPos]

/-- The first parent: the gap-law rate is the IC rate. -/
def eiRateParentCmp : Comparison EiCrossCtx where
  left := mkRef "EnergyGapLaw" "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate" "EiCrossCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  right := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-iscRate" "EiCrossCtx"
    "PhotoLean/ICvsISC/Basic.lean#iscRate"
  leftContext := EiCrossCtx
  rightContext := EiCrossCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := eiLeftPred
  rightPredicate := eiMidPred

/-- The typed first parent: the gap-law rate is the IC rate. -/
def eiRateParent : ParentCertificate EiCrossCtx :=
  .equivalence "RAD3-EI-rate-identification" eiRateParentCmp []
    (fun δ _ => by
      have h : ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI
          = EnergyGapLaw.nrRate δ.AI δ.lamI δ.kB δ.T δ.xI :=
        eiRatePin_source δ.AI δ.lamI δ.kB δ.T δ.xI
      change eiLeftPred δ ↔ eiMidPred δ
      unfold eiLeftPred eiMidPred
      rw [h])

/-- The second parent: the delivered IC-vs-ISC crossover. -/
def eiDominanceCmp : Comparison EiCrossCtx where
  left := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-iscRate" "EiCrossCtx"
    "PhotoLean/ICvsISC/Basic.lean#iscRate"
  right := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-isc_dominates_iff" "EiCrossCtx"
    "PhotoLean/ICvsISC/Criterion.lean#isc_dominates_iff"
  leftContext := EiCrossCtx
  rightContext := EiCrossCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := eiMidPred
  rightPredicate := eiRightPred

/-- The typed second parent: the delivered IC-vs-ISC crossover. -/
def eiDominanceParent : ParentCertificate EiCrossCtx :=
  .equivalence "RAD3-EI-isc-dominance" eiDominanceCmp eiPremises
    (fun δ hprem => by
      have hFC : ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T :=
        hprem pEiFCData (by simp [eiPremises])
      have hH : 0 < δ.HSO := hprem pEiHsoPos (by simp [eiPremises])
      exact ICvsISC.isc_dominates_iff hFC δ.xI δ.xS δ.HSO hH)

/-- Alignment: the first parent's right predicate is the second's left predicate. -/
def eiMiddleAlignment : MiddleAlignment eiRateParent eiDominanceParent where
  agree := fun _ => Iff.rfl

/-- Premise coverage: both parents' premises are inherited from the child premise list. -/
def eiPremiseCoverage :
    PremiseCoverage EiCrossCtx eiPremises
      (eiRateParent.premises ++ eiDominanceParent.premises) where
  covered := fun _p hp => by
    have hleft : eiRateParent.premises = [] := rfl
    have hright : eiDominanceParent.premises = eiPremises := rfl
    rw [hleft, hright] at hp
    exact PremiseDerivation.inherited (by simpa using hp)

/-- The typed conditional composition: the EGL rate in the IC-vs-ISC crossover. -/
def eiCrossoverComposition : Certificate EiCrossCtx :=
  .conditionalComposition
    { left := eiRateParent
      right := eiDominanceParent
      premises := eiPremises
      bridge := []
      alignment := eiMiddleAlignment
      parentCoverage := eiPremiseCoverage
      bridgeCoverage := by
        intro b hb
        simp at hb
      discharges := [] }

/-- Kind pin: the row is a conditional composition. -/
theorem eiCrossoverComposition_kind :
    certificateKind eiCrossoverComposition = RelationKind.conditionalComposition := rfl

/-! ## §6 StokesShift / ICvsISC — the thermoneutral IC barrier is the crossing surface height

At thermoneutrality (`x = 0`) the IC Franck-Condon barrier is `lam^2/(4 lam) = lam/4`, which is the
Stokes ground surface `s0Surface lam (1/2) = lam*(1/2)^2` at the equal-curvature crossing
coordinate `q = 1/2`. The identity is unconditional (both sides vanish at `lam = 0`). -/

/-- Shared context: reorganization energy `lam`. -/
structure SiSurfaceCtx where
  /-- reorganization energy -/
  lam : ℝ

/-- The two readings compared by the surface-height identity. -/
def siSurfaceSetup : ObservationalSetup SiSurfaceCtx where
  left := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier" "SiSurfaceCtx"
    "PhotoLean/ICvsISC/Basic.lean#fcBarrier"
  right := mkRef "StokesShift" "stmt-StokesShift-PhotoLean-StokesShift-s0Surface" "SiSurfaceCtx"
    "PhotoLean/StokesShift/Basic.lean#s0Surface"
  leftState := SiSurfaceCtx
  rightState := SiSurfaceCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The barrier-height channel over the single declared configuration. -/
def siSurfaceChannel : Channel SiSurfaceCtx siSurfaceSetup ℝ Unit where
  name := "barrier-height"
  domain := Set.univ
  leftObs := fun δ _ => ICvsISC.fcBarrier δ.lam 0
  rightObs := fun δ _ => StokesShift.s0Surface δ.lam (1 / 2)

/-- Source coherence: the thermoneutral IC barrier is the crossing surface height. -/
theorem siSurfaceBridge_source (δ : SiSurfaceCtx) :
    ICvsISC.fcBarrier δ.lam 0 = StokesShift.s0Surface δ.lam (1 / 2) := by
  unfold ICvsISC.fcBarrier StokesShift.s0Surface
  by_cases h : δ.lam = 0
  · rw [h]
    norm_num
  · field_simp
    ring

/-- Observational equivalence: the thermoneutral IC barrier is the crossing surface height. -/
def siSurfaceBridge : Certificate SiSurfaceCtx :=
  .observationalEquivalence siSurfaceSetup [] ℝ Unit [siSurfaceChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact siSurfaceBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem siSurfaceBridge_kind :
    certificateKind siSurfaceBridge = RelationKind.observationalEquivalence := rfl

/-! ## §7 Forster / Einstein — the Forster rate at the radiative lifetime is the A coefficient

The Forster rate is `fretRate tauD r6 R = (1/tauD)*(r6/R^6)`. At the Einstein radiative lifetime
`tauD = tauR A = 1/A` this is `A*(r6/R^6) = aOfB A (r6/R^6)`: the transfer rate of a purely
radiative donor is the Einstein A coefficient times the sixth-power geometric factor. The identity
is unconditional because both reciprocal maps are totalized. -/

/-- Shared context: radiative coefficient `A`, sixth-power radius `r6`, separation `R`. -/
structure FoEinCtx where
  /-- Einstein A coefficient (radiative rate) -/
  A : ℝ
  /-- sixth power of the Forster radius -/
  r6 : ℝ
  /-- donor-acceptor separation -/
  R : ℝ

/-- The two readings compared by the rate identity. -/
def foEinSetup : ObservationalSetup FoEinCtx where
  left := mkRef "Forster" "stmt-Forster-PhotoLean-Forster-fretRate" "FoEinCtx"
    "PhotoLean/Forster/Basic.lean#fretRate"
  right := mkRef "Einstein" "stmt-Einstein-PhotoLean-Einstein-aOfB" "FoEinCtx"
    "PhotoLean/Einstein/Basic.lean#aOfB"
  leftState := FoEinCtx
  rightState := FoEinCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The rate-constant channel over the single declared configuration. -/
def foEinChannel : Channel FoEinCtx foEinSetup ℝ Unit where
  name := "rate-constant"
  domain := Set.univ
  leftObs := fun δ _ => Forster.fretRate (Einstein.tauR δ.A) δ.r6 δ.R
  rightObs := fun δ _ => Einstein.aOfB δ.A (δ.r6 / δ.R ^ 6)

/-- Source coherence: the Forster rate at `tauR A` is the A coefficient times `r6/R^6`. -/
theorem foEinBridge_source (δ : FoEinCtx) :
    Forster.fretRate (Einstein.tauR δ.A) δ.r6 δ.R
      = Einstein.aOfB δ.A (δ.r6 / δ.R ^ 6) := by
  unfold Forster.fretRate Einstein.tauR Einstein.aOfB
  simp only [one_div, inv_inv]

/-- Observational equivalence: the Forster rate at the radiative lifetime is the A term. -/
def foEinBridge : Certificate FoEinCtx :=
  .observationalEquivalence foEinSetup [] ℝ Unit [foEinChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact foEinBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem foEinBridge_kind :
    certificateKind foEinBridge = RelationKind.observationalEquivalence := rfl

/-! ## Machine-checked screening witnesses

The package screening layer declares, for each certified query, the certificate's premise IDs and
(for the one conditional composition) its parent and bridge metadata. The examples below pin those
JSON fields to the Lean-side computable projections, so the package validator can cross-check the
manifest against the kernel-checked certificate rather than against prose. -/

example : certificatePremiseIDs fiBranchBridge = [] := by decide
example : certificatePremiseIDs fiElSayedBridge =
    ["RAD3-FIES-kP-nonzero", "RAD3-FIES-triplet-total-nonzero", "RAD3-FIES-AS-nonzero",
     "RAD3-FIES-s1decay-nonzero"] := by decide
example : certificatePremiseIDs ffTransferBridge =
    ["RAD3-FF-tauD-nonzero", "RAD3-FF-R-nonzero"] := by decide
example : certificatePremiseIDs fpEinsBridge = [] := by decide
example : certificatePremiseIDs esZeroBarrierBridge = ["RAD3-ES-lam-nonzero"] := by decide
example : certificatePremiseIDs esBarrierEmissionBridge = ["RAD3-ES-lam-nonzero"] := by decide
example : certificatePremiseIDs eiRateDefinition = [] := by decide
example : certificatePremiseIDs eiCrossoverComposition =
    ["RAD3-EI-fcdata", "RAD3-EI-hso-positive"] := by decide
example : certificatePremiseIDs siSurfaceBridge = [] := by decide
example : certificatePremiseIDs foEinBridge = [] := by decide

example : (certificateComposition? eiCrossoverComposition).map (fun m => m.parentIDs) =
    some ["RAD3-EI-rate-identification", "RAD3-EI-isc-dominance"] := by decide
example : (certificateComposition? eiCrossoverComposition).map (fun m => m.bridgeIDs) =
    some [] := by decide
example : (certificateComposition? eiCrossoverComposition).map (fun m => m.form) =
    some CompositionForm.equivalence := by decide

end Rad3
end BoundedAudit
end RelationAudit
end PhotoLean


/-! ## Verification print-outs for the RAD3 evidence log -/


#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.fiBranchBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.fiElSayedBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.ffTransferBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.fpEinsBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.esZeroBarrierBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.esBarrierEmissionBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.eiRateDefinition
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.eiCrossoverComposition
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.siSurfaceBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Rad3.foEinBridge
