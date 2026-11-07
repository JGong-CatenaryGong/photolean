/-
PhotoLean.RelationAudit.BoundedAudit.CI — R4 conical-intersection screening evidence.

This module is additive. It imports delivered theory modules and the audit semantic core,
and it changes no delivered statement. It carries the certificates required by the
sixteen-pair `WP-conical-intersection-01` screening package of R4
(`bounded_audit/r4/conical-01/`) for the pairs whose outcome is `certified`.

The RACI theory (`PhotoLean/RACI`) carries two observables that the other sixteen theories
also expose in their own vocabularies:

* the barrier-controlled nonradiative rate `RACI.barrierRate A β B = A·exp(−β·B)`, and
* the two-channel quantum yield `RACI.quantumYield kr knr = kr/(kr + knr)`.

Each certificate below identifies one of those two RACI observables with a partner
statement under an explicitly declared shared context, translations, and (where needed)
load-bearing premises. No statement is weakened, no new physical claim is introduced, and
no delivered file is modified. Every declaration is fully proved; there is no unproved
placeholder and no custom axiomatic declaration in this file.

Sections:

* §1 RACI / Marcus: the RACI barrier channel at `β = 1/(k_B T)` is the Marcus rate.
* §2 RACI / Kasha: the RACI yield is the Kasha radiative branching probability (definitional).
* §3 RACI / QuantumYield: the RACI yield is the two-channel QuantumYield yield.
* §4 RACI / FluorPhos: the two-channel RACI yield aggregates the FluorPhos S₁ channels.
* §5 RACI / SternVolmer: dynamic quenching dilutes the RACI yield by the SV ratio.
* §6 RACI / EnergyGapLaw: the RACI barrier channel at the gap barrier is the gap-law rate.
* §7 RACI / ICvsISC: the RACI barrier channel at the FC barrier is the internal-conversion rate.
* §8 RACI / Einstein: the RACI yield at the Einstein A coefficient is the radiative yield.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.RACI.Main
import PhotoLean.Kasha.Basic
import PhotoLean.QuantumYield.Basic
import PhotoLean.FluorPhos.Basic
import PhotoLean.SternVolmer.Basic
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.ICvsISC.Basic
import PhotoLean.Einstein.Criterion

set_option autoImplicit false

noncomputable section

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace CI

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

/-! ## §1 RACI / Marcus — the barrier channel is the Marcus rate

The Marcus rate is `A·exp(−barrier(lam,x)/(k_B T))` and the RACI barrier channel is
`A·exp(−β·B)`. At `β = 1/(k_B T)` and `B = Marcus.barrier lam x` the two rate laws are the same
real function of the driving force: the RACI conical-intersection channel is the Marcus
two-parabola step written with the transfer rate's barrier. This is a rate-law identification,
not a claim that the Marcus solvent coordinate is the RACI torsion angle. -/

/-- Shared context of the RACI/Marcus rate-law comparison: a single barrier-controlled step. -/
structure MarcusRateCtx where
  /-- pre-exponential factor -/
  A : ℝ
  /-- reorganization energy -/
  lam : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ

/-- The two readings compared by the rate-law identity. -/
def marcusRateSetup : ObservationalSetup MarcusRateCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-barrierRate" "MarcusRateCtx"
    "PhotoLean/RACI/Barrier.lean#barrierRate"
  right := mkRef "Marcus" "stmt-Marcus-PhotoLean-Marcus-rate" "MarcusRateCtx"
    "PhotoLean/Marcus/Basic.lean#rate"
  leftState := MarcusRateCtx
  rightState := MarcusRateCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The rate-constant channel over the driving force. -/
noncomputable def marcusRateChannel : Channel MarcusRateCtx marcusRateSetup ℝ ℝ where
  name := "rate-constant"
  domain := Set.univ
  leftObs := fun δ x =>
    RACI.barrierRate δ.A (1 / (δ.kB * δ.T)) (Marcus.barrier δ.lam x)
  rightObs := fun δ x => Marcus.rate δ.A δ.lam δ.kB δ.T x

/-- Source coherence: the two rate laws agree at every driving force. -/
theorem marcusRateBridge_source (δ : MarcusRateCtx) (x : ℝ) :
    RACI.barrierRate δ.A (1 / (δ.kB * δ.T)) (Marcus.barrier δ.lam x) =
      Marcus.rate δ.A δ.lam δ.kB δ.T x := by
  unfold RACI.barrierRate Marcus.rate
  rw [one_div, inv_mul_eq_div, neg_div]

/-- Observational equivalence: the RACI barrier channel is the Marcus rate law. -/
noncomputable def marcusRateBridge : Certificate MarcusRateCtx :=
  .observationalEquivalence marcusRateSetup [] ℝ ℝ [marcusRateChannel]
    (by decide)
    (fun δ _ c hc x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact marcusRateBridge_source δ x)

/-- Kind pin: the row is an observational equivalence. -/
theorem marcusRateBridge_kind :
    certificateKind marcusRateBridge = RelationKind.observationalEquivalence := rfl

/-! ## §2 RACI / Kasha — the yield is the radiative branching probability

`Kasha.radBranch rad ic n = rad n / decay rad ic n` with `decay = rad n + ic n`, and
`RACI.quantumYield kr knr = kr / (kr + knr)`. With `kr = rad n`, `knr = ic n` the two terms are
the same term up to unfolding the two definitions, so the identity is a fresh kernel `rfl` check:
the RACI emission yield *is* the Kasha radiative branch probability of the same level. -/

/-- Shared context of the RACI/Kasha yield comparison: a ladder level with two channels. -/
structure KashaYieldCtx where
  /-- radiative rate of level `n` -/
  rad : ℕ → ℝ
  /-- internal-conversion rate of level `n` -/
  ic : ℕ → ℝ
  /-- the emitting level -/
  n : ℕ

/-- The definitional pin of the RACI yield against the Kasha radiative branch. -/
def kashaYieldPin : DefinitionalPin KashaYieldCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-quantumYield" "KashaYieldCtx"
    "PhotoLean/RACI/Jablonski.lean#quantumYield"
  right := mkRef "Kasha" "stmt-Kasha-PhotoLean-Kasha-radBranch" "KashaYieldCtx"
    "PhotoLean/Kasha/Basic.lean#radBranch"
  leftContext := KashaYieldCtx
  rightContext := KashaYieldCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => RACI.quantumYield (δ.rad δ.n) (δ.ic δ.n)
  rightTerm := fun δ => Kasha.radBranch δ.rad δ.ic δ.n
  same := DefEq.refl

/-- Source coherence: the kernel `rfl` equation, stated explicitly. -/
theorem kashaYieldPin_source (δ : KashaYieldCtx) :
    RACI.quantumYield (δ.rad δ.n) (δ.ic δ.n) = Kasha.radBranch δ.rad δ.ic δ.n := rfl

/-- Definitional identity: the RACI yield is the Kasha radiative branch. -/
noncomputable def kashaRadiativeBranchPin : Certificate KashaYieldCtx :=
  .definitionalIdentity kashaYieldPin []

/-- Kind pin: the row is a definitional identity. -/
theorem kashaRadiativeBranchPin_kind :
    certificateKind kashaRadiativeBranchPin = RelationKind.definitionalIdentity := rfl

/-! ## §3 RACI / QuantumYield — the two-channel yield of the general calculus

`QuantumYield.yieldOf k i = k i / totalRate k` with `totalRate k = Σ i, k i`. For the channel
vector `![kr, knr]` the observable-0 yield is `kr/(kr + knr)`, i.e. the RACI yield. The RACI
yield is therefore an instance of the general `n`-channel yield calculus at `n = 2`. -/

/-- Shared context of the RACI/QuantumYield comparison: a two-channel emitter. -/
structure QyTwoChannelCtx where
  /-- radiative rate -/
  kr : ℝ
  /-- total nonradiative rate -/
  knr : ℝ

/-- The two readings compared by the two-channel yield identity. -/
def qyTwoChannelSetup : ObservationalSetup QyTwoChannelCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-quantumYield" "QyTwoChannelCtx"
    "PhotoLean/RACI/Jablonski.lean#quantumYield"
  right := mkRef "QuantumYield" "stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf"
    "QyTwoChannelCtx" "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := QyTwoChannelCtx
  rightState := QyTwoChannelCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The quantum-yield channel. -/
noncomputable def qyTwoChannelChannel : Channel QyTwoChannelCtx qyTwoChannelSetup ℝ Unit where
  name := "quantum-yield"
  domain := Set.univ
  leftObs := fun δ _ => RACI.quantumYield δ.kr δ.knr
  rightObs := fun δ _ => QuantumYield.yieldOf ![δ.kr, δ.knr] 0

/-- Source coherence: the RACI yield is the `n = 2` QuantumYield row. -/
theorem qyTwoChannelBridge_source (δ : QyTwoChannelCtx) :
    RACI.quantumYield δ.kr δ.knr = QuantumYield.yieldOf ![δ.kr, δ.knr] 0 := by
  unfold RACI.quantumYield QuantumYield.yieldOf QuantumYield.totalRate
  simp [Fin.sum_univ_two]

/-- Observational equivalence: the RACI yield is the two-channel QuantumYield yield. -/
noncomputable def qyTwoChannelBridge : Certificate QyTwoChannelCtx :=
  .observationalEquivalence qyTwoChannelSetup [] ℝ Unit [qyTwoChannelChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact qyTwoChannelBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem qyTwoChannelBridge_kind :
    certificateKind qyTwoChannelBridge = RelationKind.observationalEquivalence := rfl

/-! ## §4 RACI / FluorPhos — the two-channel yield aggregates the S₁ channels

FluorPhos splits the S₁ nonradiative decay into intersystem crossing and internal conversion:
`phiF kF kISC kIC = kF / (kF + kISC + kIC)`. Aggregating the two nonradiative channels into the
single RACI `knr = kISC + kIC` gives the same fluorescence yield, so the RACI two-channel model
is the FluorPhos S₁ yield with the two nonradiative channels summed. -/

/-- Shared context of the RACI/FluorPhos S₁ yield comparison. -/
structure FluorPhosS1Ctx where
  /-- radiative rate -/
  kF : ℝ
  /-- intersystem-crossing rate -/
  kISC : ℝ
  /-- internal-conversion rate -/
  kIC : ℝ

/-- The two readings compared by the S₁ yield identity. -/
def fluorPhosS1Setup : ObservationalSetup FluorPhosS1Ctx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-quantumYield" "FluorPhosS1Ctx"
    "PhotoLean/RACI/Jablonski.lean#quantumYield"
  right := mkRef "FluorPhos" "stmt-FluorPhos-PhotoLean-FluorPhos-phiF" "FluorPhosS1Ctx"
    "PhotoLean/FluorPhos/Basic.lean#phiF"
  leftState := FluorPhosS1Ctx
  rightState := FluorPhosS1Ctx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The fluorescence-yield channel. -/
noncomputable def fluorPhosS1Channel : Channel FluorPhosS1Ctx fluorPhosS1Setup ℝ Unit where
  name := "quantum-yield"
  domain := Set.univ
  leftObs := fun δ _ => RACI.quantumYield δ.kF (δ.kISC + δ.kIC)
  rightObs := fun δ _ => FluorPhos.phiF δ.kF δ.kISC δ.kIC

/-- Source coherence: the aggregated two-channel yield is the FluorPhos S₁ yield. -/
theorem fluorPhosS1Bridge_source (δ : FluorPhosS1Ctx) :
    RACI.quantumYield δ.kF (δ.kISC + δ.kIC) = FluorPhos.phiF δ.kF δ.kISC δ.kIC := by
  unfold RACI.quantumYield FluorPhos.phiF FluorPhos.s1Decay
  rw [add_assoc]

/-- Observational equivalence: the RACI yield aggregates the FluorPhos S₁ channels. -/
noncomputable def fluorPhosS1Bridge : Certificate FluorPhosS1Ctx :=
  .observationalEquivalence fluorPhosS1Setup [] ℝ Unit [fluorPhosS1Channel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact fluorPhosS1Bridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem fluorPhosS1Bridge_kind :
    certificateKind fluorPhosS1Bridge = RelationKind.observationalEquivalence := rfl

/-! ## §5 RACI / SternVolmer — dynamic quenching dilutes the RACI yield

Stern–Volmer writes the dynamically quenched decay as `dynDecay k0 kq q = k0 + kq·q` with
`k0 = kr + knr`, and the SV intensity ratio as `svRatioDyn k0 kq q = (k0 + kq·q)/k0`. Adding the
collisional channel to the RACI nonradiative rate and dividing by the SV ratio gives back the
quenched RACI yield: `Φ(kr, knr + kq·q) = Φ(kr, knr)/((k0 + kq·q)/k0)`. The two channel lists are
the same emitter, quenched and unquenched.

The premises `0 < kr + knr` and `0 ≤ kq` are load-bearing: they make the unquenched total and
the quenched total positive, which is exactly what the division clearing consumes. The channel
domain `0 ≤ q` is the physical quencher-concentration domain. -/

/-- Shared context of the RACI/SternVolmer quench-dilution comparison. -/
structure SvQuenchCtx where
  /-- radiative rate -/
  kr : ℝ
  /-- intrinsic nonradiative rate -/
  knr : ℝ
  /-- bimolecular quenching rate -/
  kq : ℝ

/-- The unquenched total decay is positive. -/
def pSvIntrinsicPos : Premise SvQuenchCtx :=
  mkPremise "raciSv.intrinsicTotalPos" fun δ => 0 < δ.kr + δ.knr

/-- The bimolecular quenching rate is nonnegative. -/
def pSvKqNonneg : Premise SvQuenchCtx :=
  mkPremise "raciSv.kqNonneg" fun δ => 0 ≤ δ.kq

/-- Premise set of the quench-dilution comparison. -/
def svQuenchPremises : List (Premise SvQuenchCtx) :=
  [pSvIntrinsicPos, pSvKqNonneg]

/-- The two readings compared by the quench-dilution identity. -/
def svQuenchSetup : ObservationalSetup SvQuenchCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-quantumYield" "SvQuenchCtx"
    "PhotoLean/RACI/Jablonski.lean#quantumYield"
  right := mkRef "SternVolmer" "sternvolmer.intensityDyn" "SvQuenchCtx"
    "PhotoLean/SternVolmer/Basic.lean#svRatioDyn"
  leftState := SvQuenchCtx
  rightState := SvQuenchCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The quenched-yield channel over the quencher concentration. -/
noncomputable def svQuenchChannel : Channel SvQuenchCtx svQuenchSetup ℝ ℝ where
  name := "quantum-yield"
  domain := {q : ℝ | 0 ≤ q}
  leftObs := fun δ q => RACI.quantumYield δ.kr (δ.knr + δ.kq * q)
  rightObs := fun δ q =>
    RACI.quantumYield δ.kr δ.knr / SternVolmer.svRatioDyn (δ.kr + δ.knr) δ.kq q

/-- Source coherence: the quenched yield is the unquenched yield divided by the SV ratio. -/
theorem svQuenchBridge_source (δ : SvQuenchCtx) (q : ℝ) (h0 : 0 < δ.kr + δ.knr)
    (hkq : 0 ≤ δ.kq) (hq : 0 ≤ q) :
    RACI.quantumYield δ.kr (δ.knr + δ.kq * q) =
      RACI.quantumYield δ.kr δ.knr /
        SternVolmer.svRatioDyn (δ.kr + δ.knr) δ.kq q := by
  have hden : 0 < δ.kr + δ.knr + δ.kq * q := by nlinarith [mul_nonneg hkq hq]
  have hL : RACI.quantumYield δ.kr (δ.knr + δ.kq * q) =
      δ.kr / (δ.kr + δ.knr + δ.kq * q) := by
    unfold RACI.quantumYield
    rw [show δ.kr + (δ.knr + δ.kq * q) = δ.kr + δ.knr + δ.kq * q by ring]
  have hR : RACI.quantumYield δ.kr δ.knr /
      SternVolmer.svRatioDyn (δ.kr + δ.knr) δ.kq q =
        δ.kr / (δ.kr + δ.knr + δ.kq * q) := by
    unfold RACI.quantumYield SternVolmer.svRatioDyn SternVolmer.dynDecay
    rw [show δ.kr + δ.knr + δ.kq * q = (δ.kr + δ.knr) + δ.kq * q by ring]
    field_simp
  rw [hL, hR]

/-- Observational equivalence: dynamic quenching dilutes the RACI yield by the SV ratio. -/
noncomputable def svQuenchDilutionBridge : Certificate SvQuenchCtx :=
  .observationalEquivalence svQuenchSetup svQuenchPremises ℝ ℝ [svQuenchChannel]
    (by decide)
    (fun δ hprem c hc q hq => by
      have h0 : 0 < δ.kr + δ.knr :=
        hprem pSvIntrinsicPos (by simp [svQuenchPremises])
      have hkq : 0 ≤ δ.kq := hprem pSvKqNonneg (by simp [svQuenchPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact svQuenchBridge_source δ q h0 hkq hq)

/-- Kind pin: the row is an observational equivalence. -/
theorem svQuenchDilutionBridge_kind :
    certificateKind svQuenchDilutionBridge = RelationKind.observationalEquivalence := rfl

/-! ## §6 RACI / EnergyGapLaw — the gap-law nonradiative rate is the RACI channel

`EnergyGapLaw.nrRate A lam kB T x = A·exp(−nrBarrier(lam,x)/(k_B T))` is the theory's
nonradiative rate (the barrier is the crossing barrier `(lam−x)²/(4·lam)`). At `β = 1/(k_B T)` and
`B = nrBarrier lam x` the RACI barrier channel is exactly that rate, so the RACI CI channel is the
gap-law nonradiative rate at the gap-law barrier. -/

/-- Shared context of the RACI/EnergyGapLaw rate comparison. -/
structure EglRateCtx where
  /-- pre-exponential factor -/
  A : ℝ
  /-- reorganization energy -/
  lam : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ

/-- The two readings compared by the gap-law rate identity. -/
def eglRateSetup : ObservationalSetup EglRateCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-barrierRate" "EglRateCtx"
    "PhotoLean/RACI/Barrier.lean#barrierRate"
  right := mkRef "EnergyGapLaw" "stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate" "EglRateCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  leftState := EglRateCtx
  rightState := EglRateCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The rate-constant channel over the driving force. -/
noncomputable def eglRateChannel : Channel EglRateCtx eglRateSetup ℝ ℝ where
  name := "rate-constant"
  domain := Set.univ
  leftObs := fun δ x =>
    RACI.barrierRate δ.A (1 / (δ.kB * δ.T)) (EnergyGapLaw.nrBarrier δ.lam x)
  rightObs := fun δ x => EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T x

/-- Source coherence: the RACI channel at the gap barrier is the gap-law rate. -/
theorem eglRateBridge_source (δ : EglRateCtx) (x : ℝ) :
    RACI.barrierRate δ.A (1 / (δ.kB * δ.T)) (EnergyGapLaw.nrBarrier δ.lam x) =
      EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T x := by
  unfold RACI.barrierRate EnergyGapLaw.nrRate
  rw [one_div, inv_mul_eq_div, neg_div]

/-- Observational equivalence: the RACI channel is the gap-law nonradiative rate. -/
noncomputable def eglRateBridge : Certificate EglRateCtx :=
  .observationalEquivalence eglRateSetup [] ℝ ℝ [eglRateChannel]
    (by decide)
    (fun δ _ c hc x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact eglRateBridge_source δ x)

/-- Kind pin: the row is an observational equivalence. -/
theorem eglRateBridge_kind :
    certificateKind eglRateBridge = RelationKind.observationalEquivalence := rfl

/-! ## §7 RACI / ICvsISC — the internal-conversion rate is the RACI channel

ICvsISC writes the internal-conversion rate as `icRate AI lamI kB T xI =
AI·exp(−fcBarrier(lamI,xI)/(k_B T))`. The RACI barrier channel at the FC barrier is that rate: the
conical-intersection channel of the RACI model is the internal-conversion rate of the ICvsISC
model at the same barrier. -/

/-- Shared context of the RACI/ICvsISC rate comparison. -/
structure IcRateCtx where
  /-- pre-exponential factor of the IC channel -/
  AI : ℝ
  /-- reorganization energy of the IC coordinate -/
  lamI : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- temperature -/
  T : ℝ

/-- The two readings compared by the internal-conversion rate identity. -/
def icRateSetup : ObservationalSetup IcRateCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-barrierRate" "IcRateCtx"
    "PhotoLean/RACI/Barrier.lean#barrierRate"
  right := mkRef "ICvsISC" "stmt-ICvsISC-PhotoLean-ICvsISC-icRate" "IcRateCtx"
    "PhotoLean/ICvsISC/Basic.lean#icRate"
  leftState := IcRateCtx
  rightState := IcRateCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The rate-constant channel over the IC coordinate. -/
noncomputable def icRateChannel : Channel IcRateCtx icRateSetup ℝ ℝ where
  name := "rate-constant"
  domain := Set.univ
  leftObs := fun δ x =>
    RACI.barrierRate δ.AI (1 / (δ.kB * δ.T)) (ICvsISC.fcBarrier δ.lamI x)
  rightObs := fun δ x => ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T x

/-- Source coherence: the RACI channel at the FC barrier is the ICvsISC IC rate. -/
theorem icRateBridge_source (δ : IcRateCtx) (x : ℝ) :
    RACI.barrierRate δ.AI (1 / (δ.kB * δ.T)) (ICvsISC.fcBarrier δ.lamI x) =
      ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T x := by
  unfold RACI.barrierRate ICvsISC.icRate
  rw [one_div, inv_mul_eq_div, neg_div]

/-- Observational equivalence: the RACI channel is the internal-conversion rate. -/
noncomputable def icRateBridge : Certificate IcRateCtx :=
  .observationalEquivalence icRateSetup [] ℝ ℝ [icRateChannel]
    (by decide)
    (fun δ _ c hc x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact icRateBridge_source δ x)

/-- Kind pin: the row is an observational equivalence. -/
theorem icRateBridge_kind :
    certificateKind icRateBridge = RelationKind.observationalEquivalence := rfl

/-! ## §8 RACI / Einstein — the radiative yield at the Einstein A coefficient

`Einstein.yield_radiative` states `A·(1/(A + kNR)) = A/(A + kNR)`: the radiative yield of a
two-channel decay whose radiative rate is the Einstein A coefficient. The RACI two-channel yield
at `kr = A` is that same quantity, so the RACI yield calculus carries the Einstein radiative-yield
anchor as the `kr = A` instance. -/

/-- Shared context of the RACI/Einstein radiative-yield comparison. -/
structure EinsteinYieldCtx where
  /-- the Einstein A coefficient (radiative rate) -/
  A : ℝ
  /-- the nonradiative rate -/
  kNR : ℝ

/-- The two readings compared by the radiative-yield identity. -/
def einsteinYieldSetup : ObservationalSetup EinsteinYieldCtx where
  left := mkRef "RACI" "stmt-RACI-PhotoLean-RACI-quantumYield" "EinsteinYieldCtx"
    "PhotoLean/RACI/Jablonski.lean#quantumYield"
  right := mkRef "Einstein" "stmt-Einstein-PhotoLean-Einstein-yield_radiative"
    "EinsteinYieldCtx" "PhotoLean/Einstein/Criterion.lean#yield_radiative"
  leftState := EinsteinYieldCtx
  rightState := EinsteinYieldCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The radiative-yield channel. -/
noncomputable def einsteinYieldChannel : Channel EinsteinYieldCtx einsteinYieldSetup ℝ Unit where
  name := "quantum-yield"
  domain := Set.univ
  leftObs := fun δ _ => RACI.quantumYield δ.A δ.kNR
  rightObs := fun δ _ => δ.A * (1 / (δ.A + δ.kNR))

/-- Source coherence: the RACI yield at the A coefficient is the Einstein radiative yield. -/
theorem einsteinYieldBridge_source (δ : EinsteinYieldCtx) :
    RACI.quantumYield δ.A δ.kNR = δ.A * (1 / (δ.A + δ.kNR)) := by
  unfold RACI.quantumYield
  rw [mul_one_div]

/-- Observational equivalence: the RACI yield at `kr = A` is the Einstein radiative yield. -/
noncomputable def einsteinYieldBridge : Certificate EinsteinYieldCtx :=
  .observationalEquivalence einsteinYieldSetup [] ℝ Unit [einsteinYieldChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact einsteinYieldBridge_source δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem einsteinYieldBridge_kind :
    certificateKind einsteinYieldBridge = RelationKind.observationalEquivalence := rfl

end CI
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the CI evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.marcusRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.kashaRadiativeBranchPin
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.qyTwoChannelBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.fluorPhosS1Bridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.svQuenchDilutionBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.eglRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.icRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.CI.einsteinYieldBridge
