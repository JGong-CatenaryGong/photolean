/-
PhotoLean.RelationAudit.BoundedAudit.RAD1 — R5 Package RAD1 bounded screening evidence.

This module is additive. It imports delivered theory modules and the audit semantic core, and it
changes no delivered statement. It carries only the certificates needed by the sixteen-pair RAD1
screening package (`WP-radiative-energy-transfer-01`). Every declaration is fully proved; there
is no unfinished-proof placeholder and no custom axiomatic declaration in this file. The
`#print axioms` block at the end is the machine evidence the package validator parses.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Marcus.Basic
import PhotoLean.Kernel
import PhotoLean.EnergyGapLaw.Basic
import PhotoLean.ICvsISC.Basic
import PhotoLean.StokesShift.Criterion
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Compose
import PhotoLean.KashaVavilov.Basic
import PhotoLean.KashaVavilov.Criterion
import PhotoLean.SternVolmer.Basic
import PhotoLean.QuantumYield.Basic
import PhotoLean.FluorPhos.Basic
import PhotoLean.Einstein.Basic
import PhotoLean.Relations

set_option autoImplicit false

noncomputable section

open PhotoLean.RelationAudit

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace RAD1

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

/-! ## §1 — Marcus / EnergyGapLaw: the nonradiative rate IS the Marcus rate

The energy-gap law's nonradiative channel is an Arrhenius step over the equal-curvature crossing
barrier with the same prefactor, reorganization energy, thermal energy and driving force as the
Marcus rate. The two theory copies are definitionally the same rate law; the pin is a fresh
`rfl` check of the two translated terms (not a propositional equality). -/

/-- Shared context of the Marcus/EnergyGapLaw rate comparison. -/
structure EglRateCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- Definitional pin: the energy-gap-law nonradiative rate is the Marcus rate. -/
def marcusEglRatePin : DefinitionalPin EglRateCtx where
  left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "EglRateCtx"
    "PhotoLean/Marcus/Basic.lean#rate"
  right := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrRate" "EglRateCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  leftContext := EglRateCtx
  rightContext := EglRateCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => PhotoLean.Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
  rightTerm := fun δ => PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x
  same := DefEq.refl

/-- The definitional-identity certificate. -/
def marcusEglRateBridge : Certificate EglRateCtx :=
  .definitionalIdentity marcusEglRatePin []

/-- Kind pin: the row is a definitional identity. -/
theorem marcusEglRateBridge_kind :
    certificateKind marcusEglRateBridge = RelationKind.definitionalIdentity := rfl

/-! ## §2 — Marcus / EnergyGapLaw: the inverted-gap predicate IS the Marcus inverted region -/

/-- Shared context of the Marcus/EnergyGapLaw region comparison. -/
structure EglZoneCtx where
  lam : ℝ
  x : ℝ

/-- The Marcus-side predicate after translation. -/
def marcusInvertedOn (δ : EglZoneCtx) : Prop :=
  PhotoLean.Marcus.InvertedRegion δ.lam δ.x

/-- The energy-gap-law-side predicate after translation. -/
def eglInvertedOn (δ : EglZoneCtx) : Prop :=
  PhotoLean.EnergyGapLaw.InvertedGap δ.lam δ.x

/-- Equivalence of the two region predicates on the shared region context. -/
def marcusEglZoneCmp : Comparison EglZoneCtx :=
  Comparison.ofPredicates
    (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.InvertedRegion" "EglZoneCtx"
      "PhotoLean/Marcus/Basic.lean#InvertedRegion")
    (mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.InvertedGap" "EglZoneCtx"
      "PhotoLean/EnergyGapLaw/Basic.lean#InvertedGap")
    marcusInvertedOn eglInvertedOn

/-- The region predicates agree at every reorganization energy and gap. -/
theorem marcusEglZone_iff (δ : EglZoneCtx) :
    marcusInvertedOn δ ↔ eglInvertedOn δ :=
  (PhotoLean.EnergyGapLaw.cert_invertedGap δ.lam δ.x).symm

/-- The equivalence certificate. -/
def marcusEglZoneBridge : Certificate EglZoneCtx :=
  .equivalence
    (.equivalence "RAD1-ME-02-parent" marcusEglZoneCmp [] (fun δ _ => marcusEglZone_iff δ))
    rfl

/-- Kind pin: the row is an equivalence. -/
theorem marcusEglZoneBridge_kind :
    certificateKind marcusEglZoneBridge = RelationKind.equivalence := rfl

/-! ## §3 — Marcus / ICvsISC: the IC rate IS the Marcus rate

The spin-conserving internal-conversion channel of the IC-vs-ISC theory is Arrhenius over its own
copy of the equal-curvature Franck-Condon barrier; the delivered certificate pins that copy to the
Marcus rate body. This is the rate-level identification of the nonradiative IC channel with the
Marcus activated step. -/

/-- Shared context of the Marcus/ICvsISC rate comparison. -/
structure MarcusICCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- Definitional pin: the IC rate is the Marcus rate. -/
def marcusICRatePin : DefinitionalPin MarcusICCtx where
  left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "MarcusICCtx"
    "PhotoLean/Marcus/Basic.lean#rate"
  right := mkRef "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.icRate" "MarcusICCtx"
    "PhotoLean/ICvsISC/Basic.lean#icRate"
  leftContext := MarcusICCtx
  rightContext := MarcusICCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => PhotoLean.Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
  rightTerm := fun δ => PhotoLean.ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x
  same := DefEq.refl

/-- The definitional-identity certificate. -/
def marcusICRateBridge : Certificate MarcusICCtx :=
  .definitionalIdentity marcusICRatePin []

/-- Kind pin: the row is a definitional identity. -/
theorem marcusICRateBridge_kind :
    certificateKind marcusICRateBridge = RelationKind.definitionalIdentity := rfl

/-! ## §4 — Marcus / StokesShift: the emission energy is positive exactly in the inverted region

The Stokes emission energy is `emEnergy = e00 - lam`. It is positive exactly in the Marcus
inverted region (`lam < e00`), negative in the normal region (`e00 < lam`), and zero at
`e00 = lam`. The delivered row SS-C9 is re-used here as the certificate's entailment. -/

/-- Shared context of the Marcus/StokesShift emission-window comparison. -/
structure MarcusSSCtx where
  lam : ℝ
  e00 : ℝ

/-- The Marcus-side predicate after translation. -/
def marcusInvertedSS (δ : MarcusSSCtx) : Prop :=
  PhotoLean.Marcus.InvertedRegion δ.lam δ.e00

/-- The StokesShift-side predicate after translation: the emission energy is positive. -/
def ssEmissionPositive (δ : MarcusSSCtx) : Prop :=
  0 < PhotoLean.StokesShift.emEnergy δ.lam δ.e00

/-- Equivalence of the inverted-region predicate and the emission-window sign. -/
def marcusSSCmp : Comparison MarcusSSCtx :=
  Comparison.ofPredicates
    (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.InvertedRegion" "MarcusSSCtx"
      "PhotoLean/Marcus/Basic.lean#InvertedRegion")
    (mkRef "PhotoLean.StokesShift" "PhotoLean.StokesShift.emEnergy" "MarcusSSCtx"
      "PhotoLean/StokesShift/Basic.lean#emEnergy")
    marcusInvertedSS ssEmissionPositive

/-- The emission window is open exactly in the Marcus inverted region. -/
theorem marcusSS_iff (δ : MarcusSSCtx) :
    marcusInvertedSS δ ↔ ssEmissionPositive δ :=
  (PhotoLean.StokesShift.emEnergy_pos_iff_inverted δ.lam δ.e00).symm

/-- The equivalence certificate. -/
def marcusSSBridge : Certificate MarcusSSCtx :=
  .equivalence
    (.equivalence "RAD1-MS-01-parent" marcusSSCmp [] (fun δ _ => marcusSS_iff δ))
    rfl

/-- Kind pin: the row is an equivalence. -/
theorem marcusSSBridge_kind :
    certificateKind marcusSSBridge = RelationKind.equivalence := rfl

/-! ## §5 — Kasha / KashaVavilov: Kasha's rule gives the spectral Vavilov rule

Under the ladder's standing physical premises, positive fluorescence yields and the exact Kasha
rule (no emission from above the lowest level), the normalized emission spectrum is the same at
every excitation level up to `N`. That is the D2 layer's Vavilov side: the delivered
`specSame_of_kashaRule` is re-used as the certificate's entailment. -/

/-- Shared context of the Kasha/KashaVavilov spectral comparison. -/
structure KashaVavCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  N : ℕ

/-- The ladder's standing physical premises up to level `N`. -/
def pKvRateData : Premise KashaVavCtx :=
  mkPremise "kv.rateData" fun δ => PhotoLean.Kasha.RateData δ.rad δ.ic δ.N

/-- Every level up to `N` has a positive total fluorescence yield. -/
def pKvFluoPos : Premise KashaVavCtx :=
  mkPremise "kv.fluoYieldPositive"
    fun δ => ∀ M, M ≤ δ.N → 0 < PhotoLean.Kasha.fluoYield δ.rad δ.ic M

/-- Premise set of the spectral Vavilov row. -/
def kvPremises : List (Premise KashaVavCtx) := [pKvRateData, pKvFluoPos]

/-- The Kasha-side antecedent: the exact Kasha rule at level `N`. -/
def kashaRuleOn (δ : KashaVavCtx) : Prop :=
  PhotoLean.Kasha.KashaRule δ.rad δ.ic δ.N

/-- The KashaVavilov-side consequent: the spectra agree up to level `N`. -/
def specSameOn (δ : KashaVavCtx) : Prop :=
  ∀ M, M ≤ δ.N → PhotoLean.KashaVavilov.SpecSame δ.rad δ.ic M δ.N

/-- Comparison of the Kasha rule with the spectral Vavilov rule. -/
def kashaVavCmp : Comparison KashaVavCtx :=
  Comparison.ofPredicates
    (mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.KashaRule" "KashaVavCtx"
      "PhotoLean/Kasha/Basic.lean#KashaRule")
    (mkRef "PhotoLean.KashaVavilov" "PhotoLean.KashaVavilov.SpecSame" "KashaVavCtx"
      "PhotoLean/KashaVavilov/Basic.lean#SpecSame")
    kashaRuleOn specSameOn

/-- The exact rule entails spectral excitation-independence. -/
theorem kashaVav_sound (δ : KashaVavCtx)
    (hprem : ∀ p ∈ kvPremises, p.predicate δ) (hK : kashaRuleOn δ) : specSameOn δ :=
  PhotoLean.KashaVavilov.specSame_of_kashaRule
    (hprem pKvRateData (by simp [kvPremises]))
    (hprem pKvFluoPos (by simp [kvPremises])) hK

/-- The implication certificate. -/
def kashaVavBridge : Certificate KashaVavCtx :=
  .implication
    (.implication "RAD1-KV-01-parent" kashaVavCmp kvPremises kashaVav_sound)
    rfl

/-- Kind pin: the row is an implication. -/
theorem kashaVavBridge_kind :
    certificateKind kashaVavBridge = RelationKind.implication := rfl

/-! ## §6 — Kasha / EnergyGapLaw: the ladder's IC channel IS the energy-gap-law rate

The Kasha ladder's declared Marcus-form internal-conversion rate (`Kasha.marcusIC`, the object its
§7 bridge quantifies over) and the energy-gap law's nonradiative rate are the same Arrhenius law
over the same equal-curvature barrier: same prefactor, reorganization energy, thermal energy and
gap. -/

/-- Shared context of the Kasha/EnergyGapLaw IC-rate comparison. -/
structure KashaEglCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- Definitional pin: the ladder's Marcus-form IC rate is the energy-gap-law rate. -/
def kashaEglRatePin : DefinitionalPin KashaEglCtx where
  left := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.marcusIC" "KashaEglCtx"
    "PhotoLean/Kasha/Compose.lean#marcusIC"
  right := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrRate" "KashaEglCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate"
  leftContext := KashaEglCtx
  rightContext := KashaEglCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => PhotoLean.Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x
  rightTerm := fun δ => PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x
  same := DefEq.refl

/-- The definitional-identity certificate. -/
def kashaEglRateBridge : Certificate KashaEglCtx :=
  .definitionalIdentity kashaEglRatePin []

/-- Kind pin: the row is a definitional identity. -/
theorem kashaEglRateBridge_kind :
    certificateKind kashaEglRateBridge = RelationKind.definitionalIdentity := rfl

/-! ## §7 — Kasha / Einstein: the lowest-level radiative branch is `A · τ`

The Kasha ladder's radiative branch at the lowest level, with radiative rate `A` and total
nonradiative loss `kNR`, is `A/(A + kNR)`. The Einstein side writes the same radiative fraction
as the A-coefficient times the observed radiative lifetime `τ = 1/(A + kNR)`. The two readings
observe the same radiative fraction of the same two-channel decay. -/

/-- Shared context of the Kasha/Einstein radiative-fraction comparison. -/
structure KashaEinsteinCtx where
  A : ℝ
  kNR : ℝ

/-- The ladder's constant radiative channel. -/
def constRad (A : ℝ) : ℕ → ℝ := fun _ => A

/-- The ladder's constant nonradiative channel. -/
def constIC (kNR : ℝ) : ℕ → ℝ := fun _ => kNR

/-- The Kasha-side observable: the lowest level's radiative branch. -/
def kashaRadBranchObs (δ : KashaEinsteinCtx) : ℝ :=
  PhotoLean.Kasha.radBranch (constRad δ.A) (constIC δ.kNR) 0

/-- The Einstein-side observable: the A-coefficient times the observed lifetime. -/
def einsteinATauObs (δ : KashaEinsteinCtx) : ℝ :=
  δ.A * PhotoLean.Einstein.tauR (δ.A + δ.kNR)

/-- The radiative branch equals `A · τ` at every `(A, kNR)`. -/
theorem kashaEinstein_eq (δ : KashaEinsteinCtx) :
    kashaRadBranchObs δ = einsteinATauObs δ := by
  unfold kashaRadBranchObs einsteinATauObs constRad constIC
  unfold PhotoLean.Kasha.radBranch PhotoLean.Kasha.decay PhotoLean.Einstein.tauR
  rw [mul_one_div]

/-- The two readings compared by the radiative-fraction row. -/
def kashaEinsteinSetup : ObservationalSetup KashaEinsteinCtx where
  left := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.radBranch" "KashaEinsteinCtx"
    "PhotoLean/Kasha/Basic.lean#radBranch"
  right := mkRef "PhotoLean.Einstein" "PhotoLean.Einstein.tauR" "KashaEinsteinCtx"
    "PhotoLean/Einstein/Basic.lean#tauR"
  leftState := KashaEinsteinCtx
  rightState := KashaEinsteinCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The radiative-fraction channel. -/
def kashaEinsteinChannel : Channel KashaEinsteinCtx kashaEinsteinSetup ℝ Unit where
  name := "lowestLevelRadiativeFraction"
  domain := Set.univ
  leftObs := fun δ _ => kashaRadBranchObs δ
  rightObs := fun δ _ => einsteinATauObs δ

/-- Observational equivalence of the radiative fraction. -/
def kashaEinsteinBridge : Certificate KashaEinsteinCtx :=
  .observationalEquivalence kashaEinsteinSetup [] ℝ Unit [kashaEinsteinChannel] (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact kashaEinstein_eq δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem kashaEinsteinBridge_kind :
    certificateKind kashaEinsteinBridge = RelationKind.observationalEquivalence := rfl


/-! ## §8 — Kasha / KashaVavilov: the ladder yield splits into the level-0 two-channel quantum
yield and the upper-block leak

This is the total-yield form of the D2 layer's own splitting row: the delivered
`KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield` gives `F = emitYield 0 + upperYield`,
and the delivered `Relations.kasha_radBranch_eq_yieldOf` identifies `emitYield 0` with the
two-channel `QuantumYield.yieldOf` of level 0 times the funnel transmission `cascade 0 N`. -/

/-- Shared context of the ladder-yield / quantum-yield decomposition. -/
structure KvQyCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  N : ℕ

/-- The ladder's fluorescence yield is the level-0 two-channel yield transported by the funnel
plus the upper-block leak. -/
theorem kvQy_decomposition (δ : KvQyCtx) :
    PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N =
      PhotoLean.QuantumYield.yieldOf ![δ.rad 0, δ.ic 0] 0 *
          PhotoLean.Kasha.cascade δ.rad δ.ic 0 δ.N +
        PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N := by
  rw [PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield]
  unfold PhotoLean.Kasha.emitYield
  rw [PhotoLean.Relations.kasha_radBranch_eq_yieldOf δ.rad δ.ic 0]

/-- The two readings compared by the decomposition row. -/
def kvQySetup : ObservationalSetup KvQyCtx where
  left := mkRef "PhotoLean.KashaVavilov"
    "PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield" "KvQyCtx"
    "PhotoLean/KashaVavilov/Basic.lean#fluoYield_eq_emitYield_zero_add_upperYield"
  right := mkRef "PhotoLean.QuantumYield" "PhotoLean.QuantumYield.yieldOf" "KvQyCtx"
    "PhotoLean/QuantumYield/Basic.lean#yieldOf"
  leftState := KvQyCtx
  rightState := KvQyCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The ladder-yield decomposition channel. -/
def kvQyChannel : Channel KvQyCtx kvQySetup ℝ Unit where
  name := "levelZeroYieldPlusUpperLeak"
  domain := Set.univ
  leftObs := fun δ _ => PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N
  rightObs := fun δ _ =>
    PhotoLean.QuantumYield.yieldOf ![δ.rad 0, δ.ic 0] 0 *
        PhotoLean.Kasha.cascade δ.rad δ.ic 0 δ.N +
      PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N

/-- Observational equivalence of the ladder-yield decomposition. -/
def kvQyBridge : Certificate KvQyCtx :=
  .observationalEquivalence kvQySetup [] ℝ Unit [kvQyChannel] (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact kvQy_decomposition δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem kvQyBridge_kind :
    certificateKind kvQyBridge = RelationKind.observationalEquivalence := rfl

/-! ## §9 — Kasha / KashaVavilov / FluorPhos: the coarse-grained channel correspondence

FluorPhos resolves the S1 decay into three channels (fluorescence, intersystem crossing, internal
conversion); the Kasha ladder resolves it into two (radiative and nonradiative). At the bottom
level the ladder's fluorescence yield, with `rad 0 = kF` and `ic 0 = kISC + kIC`, is exactly the
FluorPhos fluorescence yield. The lumping of the two nonradiative channels into the ladder's one
nonradiative rate is the declared translation, so the row is an observation of the same
radiative fraction, not an accidental formula match. -/

/-- The ladder's radiative channel with the S1 radiative rate `kF`. -/
def lumpRad (kF : ℝ) : ℕ → ℝ := fun n => if n = 0 then kF else 0

/-- The ladder's nonradiative channel carrying the summed ISC + IC loss. -/
def lumpIC (kISC kIC : ℝ) : ℕ → ℝ := fun n => if n = 0 then kISC + kIC else 0

/-- Shared context of the KashaVavilov/FluorPhos comparison. -/
structure KvFpCtx where
  kF : ℝ
  kISC : ℝ
  kIC : ℝ

/-- The bottom-level ladder fluorescence yield equals the FluorPhos fluorescence yield. -/
theorem kvFp_lumped (δ : KvFpCtx) :
    PhotoLean.Kasha.fluoYield (lumpRad δ.kF) (lumpIC δ.kISC δ.kIC) 0 =
      PhotoLean.FluorPhos.phiF δ.kF δ.kISC δ.kIC := by
  unfold PhotoLean.Kasha.fluoYield PhotoLean.Kasha.emitYield PhotoLean.Kasha.cascade
    PhotoLean.Kasha.radBranch PhotoLean.Kasha.decay
    PhotoLean.FluorPhos.phiF PhotoLean.FluorPhos.s1Decay lumpRad lumpIC
  simp
  ring

/-- The two readings compared by the channel-lumping row. -/
def kvFpSetup : ObservationalSetup KvFpCtx where
  left := mkRef "PhotoLean.KashaVavilov"
    "PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield" "KvFpCtx"
    "PhotoLean/KashaVavilov/Basic.lean#fluoYield_eq_emitYield_zero_add_upperYield"
  right := mkRef "PhotoLean.FluorPhos" "PhotoLean.FluorPhos.phiF" "KvFpCtx"
    "PhotoLean/FluorPhos/Basic.lean#phiF"
  leftState := KvFpCtx
  rightState := KvFpCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The bottom-level radiative-fraction channel. -/
def kvFpChannel : Channel KvFpCtx kvFpSetup ℝ Unit where
  name := "bottomLevelFluorescenceYield"
  domain := Set.univ
  leftObs := fun δ _ =>
    PhotoLean.Kasha.fluoYield (lumpRad δ.kF) (lumpIC δ.kISC δ.kIC) 0
  rightObs := fun δ _ => PhotoLean.FluorPhos.phiF δ.kF δ.kISC δ.kIC

/-- Observational equivalence of the lumped channel correspondence. -/
def kvFpBridge : Certificate KvFpCtx :=
  .observationalEquivalence kvFpSetup [] ℝ Unit [kvFpChannel] (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact kvFp_lumped δ)

/-- Kind pin: the row is an observational equivalence. -/
theorem kvFpBridge_kind :
    certificateKind kvFpBridge = RelationKind.observationalEquivalence := rfl

/-! ## §10 — KashaVavilov / SternVolmer: quenching dilutes only the bottom channel

Dynamic quenching adds `kq·[Q]` to the ladder's **level-0** total decay (the collisional channel
that competes with the bottom level's own decay). The upper levels are untouched, so the
upper-block leak `upperYield` is invariant, while the bottom emission is diluted by exactly the
Stern-Volmer ratio computed from the *unquenched* level-0 decay. The statement compares the
ladder's bottom-emission channel before and after quenching; it is the composition of the D2
splitting row with the Stern-Volmer dynamic ratio. -/

/-- Add the collisional channel to the level-0 nonradiative rate only. -/
def quenchIC (ic : ℕ → ℝ) (kq q : ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then ic 0 + kq * q else ic n

/-- Shared context of the KashaVavilov/SternVolmer comparison. -/
structure KvSvCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  N : ℕ
  kq : ℝ
  q : ℝ

/-- The upper-block leak is invariant under a level-0 quench channel. -/
theorem kvSv_upper_invariant (δ : KvSvCtx) :
    PhotoLean.Kasha.upperYield δ.rad (quenchIC δ.ic δ.kq δ.q) δ.N =
      PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N := by
  have hemit : ∀ i, i ≠ 0 →
      PhotoLean.Kasha.emitYield δ.rad (quenchIC δ.ic δ.kq δ.q) i δ.N =
        PhotoLean.Kasha.emitYield δ.rad δ.ic i δ.N := by
    intro i hi0
    unfold PhotoLean.Kasha.emitYield
    congr 1
    · unfold PhotoLean.Kasha.radBranch PhotoLean.Kasha.decay
      simp [quenchIC, hi0]
    · unfold PhotoLean.Kasha.cascade
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : j ≠ 0 := by omega
      unfold PhotoLean.Kasha.icBranch PhotoLean.Kasha.decay
      simp [quenchIC, hj0]
  unfold PhotoLean.Kasha.upperYield
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact hemit i (by omega)

/-- The funnel transmission is invariant under a level-0 quench channel. -/
theorem kvSv_cascade_invariant (δ : KvSvCtx) :
    PhotoLean.Kasha.cascade δ.rad (quenchIC δ.ic δ.kq δ.q) 0 δ.N =
      PhotoLean.Kasha.cascade δ.rad δ.ic 0 δ.N := by
  unfold PhotoLean.Kasha.cascade
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj0 : j ≠ 0 := by omega
  unfold PhotoLean.Kasha.icBranch PhotoLean.Kasha.decay
  simp [quenchIC, hj0]

/-- The unquenched level-0 radiative branch is the quenched branch times the Stern-Volmer
dynamic ratio. -/
theorem kvSv_branch (δ : KvSvCtx) (h0 : 0 < δ.rad 0 + δ.ic 0) (hqq : 0 ≤ δ.kq * δ.q) :
    PhotoLean.Kasha.radBranch δ.rad δ.ic 0 =
      PhotoLean.Kasha.radBranch δ.rad (quenchIC δ.ic δ.kq δ.q) 0 *
        SternVolmer.svRatioDyn (δ.rad 0 + δ.ic 0) δ.kq δ.q := by
  have h2 : 0 < δ.rad 0 + (δ.ic 0 + δ.kq * δ.q) := by linarith
  have h1 : (δ.rad 0 + δ.ic 0) ≠ 0 := ne_of_gt h0
  have h3 : (δ.rad 0 + (δ.ic 0 + δ.kq * δ.q)) ≠ 0 := ne_of_gt h2
  unfold PhotoLean.Kasha.radBranch PhotoLean.Kasha.decay SternVolmer.svRatioDyn
    SternVolmer.dynDecay quenchIC
  simp only [if_pos rfl]
  field_simp
  ring

/-- Dynamic quenching dilutes the bottom-emission channel by the Stern-Volmer ratio and leaves
the upper-block leak untouched. -/
theorem kvSv_dilution (δ : KvSvCtx) (h0 : 0 < δ.rad 0 + δ.ic 0) (hqq : 0 ≤ δ.kq * δ.q) :
    PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N - PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N =
      (PhotoLean.Kasha.fluoYield δ.rad (quenchIC δ.ic δ.kq δ.q) δ.N -
          PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N) *
        SternVolmer.svRatioDyn (δ.rad 0 + δ.ic 0) δ.kq δ.q := by
  have hU := kvSv_upper_invariant δ
  have hcasc := kvSv_cascade_invariant δ
  have hbranch := kvSv_branch δ h0 hqq
  have hE : PhotoLean.Kasha.emitYield δ.rad δ.ic 0 δ.N =
      PhotoLean.Kasha.emitYield δ.rad (quenchIC δ.ic δ.kq δ.q) 0 δ.N *
        SternVolmer.svRatioDyn (δ.rad 0 + δ.ic 0) δ.kq δ.q := by
    unfold PhotoLean.Kasha.emitYield
    rw [hcasc, hbranch]
    ring
  rw [PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield δ.rad δ.ic δ.N,
    PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield δ.rad
      (quenchIC δ.ic δ.kq δ.q) δ.N, hU, hE]
  ring

/-- The two readings compared by the quench-dilution row. -/
def kvSvSetup : ObservationalSetup KvSvCtx where
  left := mkRef "PhotoLean.KashaVavilov"
    "PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield" "KvSvCtx"
    "PhotoLean/KashaVavilov/Basic.lean#fluoYield_eq_emitYield_zero_add_upperYield"
  right := mkRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.svRatioDyn" "KvSvCtx"
    "PhotoLean/SternVolmer/Basic.lean#svRatioDyn"
  leftState := KvSvCtx
  rightState := KvSvCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The standing positivity premises of the quench-dilution row. -/
def pKvSvK0 : Premise KvSvCtx :=
  mkPremise "kvSv.levelZeroDecayPositive" fun δ => 0 < δ.rad 0 + δ.ic 0

/-- The collisional channel is a loss channel. -/
def pKvSvKq : Premise KvSvCtx :=
  mkPremise "kvSv.quenchChannelNonnegative" fun δ => 0 ≤ δ.kq * δ.q

/-- Premise set of the quench-dilution row. -/
def kvSvPremises : List (Premise KvSvCtx) := [pKvSvK0, pKvSvKq]

/-- The bottom-emission channel. -/
def kvSvChannel : Channel KvSvCtx kvSvSetup ℝ Unit where
  name := "bottomEmissionChannelUnderQuench"
  domain := Set.univ
  leftObs := fun δ _ =>
    PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N - PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N
  rightObs := fun δ _ =>
    (PhotoLean.Kasha.fluoYield δ.rad (quenchIC δ.ic δ.kq δ.q) δ.N -
        PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N) *
      SternVolmer.svRatioDyn (δ.rad 0 + δ.ic 0) δ.kq δ.q

/-- Observational equivalence of the quench-dilution row. -/
def kvSvBridge : Certificate KvSvCtx :=
  .observationalEquivalence kvSvSetup kvSvPremises ℝ Unit [kvSvChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact kvSv_dilution δ (hprem pKvSvK0 (by simp [kvSvPremises]))
        (hprem pKvSvKq (by simp [kvSvPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem kvSvBridge_kind :
    certificateKind kvSvBridge = RelationKind.observationalEquivalence := rfl

/-! ## §11 — Marcus / KashaVavilov: a Marcus-controlled IC channel decides anti-Kasha
observability

If the ladder's `S2 → S1` internal-conversion rate is the Marcus-form rate at the same
reorganization energy and gap, and the squared gap lies **outside** the Kasha window, then the
upper block retains emission: `0 < upperYield`, i.e. (by the D2 boundary row) the Kasha rule fails
and the anti-Kasha emission is observable. The certificate is a typed implication whose antecedent
is a Marcus barrier-window condition and whose consequent is the KashaVavilov anti-Kasha
predicate. It consumes both the delivered window row (`not_kashaWithin_of_gap_far`) and the
delivered D2 boundary row (`antiKasha_observable_iff`). -/

/-- Shared context of the Marcus/KashaVavilov window comparison. -/
structure MarcusKvCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ
  tol : ℝ
  rad : ℕ → ℝ
  ic : ℕ → ℝ

/-- The ladder's standing physical premises at level 1. -/
def pMkvRateData : Premise MarcusKvCtx :=
  mkPremise "mkv.rateData" fun δ => PhotoLean.Kasha.RateData δ.rad δ.ic 1

/-- The tolerance is a physical fraction. -/
def pMkvTol : Premise MarcusKvCtx :=
  mkPremise "mkv.tolerance" fun δ => 0 < δ.tol ∧ δ.tol < 1

/-- Positive pre-exponential factor. -/
def pMkvA : Premise MarcusKvCtx :=
  mkPremise "mkv.prefactorPositive" fun δ => 0 < δ.A

/-- Positive reorganization energy. -/
def pMkvLam : Premise MarcusKvCtx :=
  mkPremise "mkv.lamPositive" fun δ => 0 < δ.lam

/-- Positive thermal energy. -/
def pMkvKT : Premise MarcusKvCtx :=
  mkPremise "mkv.thermalPositive" fun δ => 0 < δ.kB * δ.T

/-- Positive bottom and funnel radiative rates. -/
def pMkvRates : Premise MarcusKvCtx :=
  mkPremise "mkv.ratesPositive" fun δ => 0 < δ.rad 0 ∧ 0 < δ.rad 1

/-- The IC channel is the Marcus-form rate at the same reorganization energy and gap. -/
def pMkvIC : Premise MarcusKvCtx :=
  mkPremise "mkv.icIsMarcusRate"
    fun δ => δ.ic 1 = PhotoLean.Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x

/-- Premise set of the anti-Kasha observability row. -/
def mkvPremises : List (Premise MarcusKvCtx) :=
  [pMkvRateData, pMkvTol, pMkvA, pMkvLam, pMkvKT, pMkvRates, pMkvIC]

/-- The Marcus-side antecedent: the squared gap lies outside the Kasha window. -/
def mkvGapOutside (δ : MarcusKvCtx) : Prop :=
  4 * δ.lam * (δ.kB * δ.T) *
      Real.log (PhotoLean.Kasha.kashaGapThreshold δ.A (δ.rad 0)
        (PhotoLean.Kasha.decay δ.rad δ.ic 0) (δ.rad 1) δ.tol) < (δ.lam - δ.x) ^ 2

/-- The KashaVavilov-side consequent: anti-Kasha emission is observable (the rule fails). -/
def mkvAntiKasha (δ : MarcusKvCtx) : Prop :=
  ¬ PhotoLean.Kasha.KashaRule δ.rad δ.ic 1

/-- Comparison of the Marcus window condition with the KashaVavilov anti-Kasha predicate. -/
def mkvCmp : Comparison MarcusKvCtx :=
  Comparison.ofPredicates
    (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "MarcusKvCtx"
      "PhotoLean/Marcus/Basic.lean#barrier")
    (mkRef "PhotoLean.KashaVavilov" "PhotoLean.KashaVavilov.antiKasha_observable_iff"
      "MarcusKvCtx" "PhotoLean/KashaVavilov/Criterion.lean#antiKasha_observable_iff")
    mkvGapOutside mkvAntiKasha

/-- A gap outside the Marcus window leaves the upper block emitting. -/
theorem mkv_sound (δ : MarcusKvCtx)
    (hprem : ∀ p ∈ mkvPremises, p.predicate δ) (hfar : mkvGapOutside δ) : mkvAntiKasha δ := by
  have hdata : PhotoLean.Kasha.RateData δ.rad δ.ic 1 :=
    hprem pMkvRateData (by simp [mkvPremises])
  have htol : 0 < δ.tol ∧ δ.tol < 1 := hprem pMkvTol (by simp [mkvPremises])
  have hA : 0 < δ.A := hprem pMkvA (by simp [mkvPremises])
  have hlam : 0 < δ.lam := hprem pMkvLam (by simp [mkvPremises])
  have hkT : 0 < δ.kB * δ.T := hprem pMkvKT (by simp [mkvPremises])
  have hr : 0 < δ.rad 0 ∧ 0 < δ.rad 1 := hprem pMkvRates (by simp [mkvPremises])
  have hic : δ.ic 1 = PhotoLean.Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x :=
    hprem pMkvIC (by simp [mkvPremises])
  have hnot : ¬ PhotoLean.Kasha.KashaWithin δ.rad δ.ic δ.tol 1 :=
    PhotoLean.Kasha.not_kashaWithin_of_gap_far hdata htol.1 htol.2 hA hlam hkT hr.1 hr.2 hic
      hfar
  have hlt : δ.tol * PhotoLean.Kasha.fluoYield δ.rad δ.ic 1 <
      PhotoLean.Kasha.upperYield δ.rad δ.ic 1 := not_le.mp hnot
  have hFnn : 0 ≤ PhotoLean.Kasha.fluoYield δ.rad δ.ic 1 :=
    PhotoLean.Kasha.fluoYield_nonneg hdata
  have htnn : 0 ≤ δ.tol := le_of_lt htol.1
  have hpos : 0 < PhotoLean.Kasha.upperYield δ.rad δ.ic 1 := by
    nlinarith [hlt, mul_nonneg htnn hFnn]
  exact (PhotoLean.KashaVavilov.antiKasha_observable_iff hdata).mp hpos

/-- The implication certificate. -/
def mkvBridge : Certificate MarcusKvCtx :=
  .implication
    (.implication "RAD1-MKV-01-parent" mkvCmp mkvPremises mkv_sound)
    rfl

/-- Kind pin: the row is an implication. -/
theorem mkvBridge_kind :
    certificateKind mkvBridge = RelationKind.implication := rfl

end RAD1
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the RAD1 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.marcusEglRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.marcusEglZoneBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.marcusICRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.marcusSSBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kashaVavBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kashaEglRateBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kashaEinsteinBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kvQyBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kvFpBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.kvSvBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.RAD1.mkvBridge
