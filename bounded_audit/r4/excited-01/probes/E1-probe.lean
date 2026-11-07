/-
PhotoLean.RelationAudit.BoundedAudit.R4Excited01 — R4 Package E1 probing evidence.

This module is additive. It imports the delivered theory modules through the audit semantic
core, and it changes no delivered statement, definition, or proof. It carries the certificates
needed by the sixteen-pair R4 E1 screening package (R1 work package
`WP-excited-state-kinetics-01`) when the legacy registry has no certificate of the required kind.

Each certificate is a genuine typed object of `PhotoLean.RelationAudit.Certificate`:

* §1 Hammond / EnergyGapLaw — equivalence: the energy-gap-law nonradiative barrier vanishes
  exactly where the Hammond transition-state coordinate reaches the reactant geometry. The
  proof consumes the delivered boundary row `Relations.eg_boundary_eq_tsCoord_zero`.
* §2 BEP / EnergyGapLaw — equivalence: the energy-gap-law inverted region is exactly where the
  BEP/Brønsted transfer coefficient turns negative. The proof consumes the delivered
  `Relations.transfer_eq_tsCoord_bridge` and `Relations.tsCoord_lt_zero_iff_inverted`.
* §3 Hammond / Kasha — equivalence: the Kasha internal-conversion rate reaches its
  pre-exponential value exactly where the Hammond transition-state coordinate reaches the
  reactant geometry. The proof consumes the delivered `Relations.kernel_marcusIC`.
* §4 Hammond / ICvsISC — definitional identity: the Franck–Condon barrier of the IC channel is
  the Hammond forward reactant gap; both are the shared kernel barrier. The certificate is a
  fresh `rfl`-only `DefEq` pin over the two delivered declarations.
* §5 BEP / Kasha — equivalence: the BEP transfer coefficient vanishes exactly where the Kasha
  internal-conversion rate reaches its pre-exponential value. The proof consumes the delivered
  `Relations.transfer_eq_tsCoord_bridge` and the §3 pin.
* §6 Hammond / StokesShift — observational equivalence: the Stokes vertical absorption energy
  is the gap between the Hammond product surface at `q = 0` and the Hammond reactant surface
  at `q = 0`. The proof consumes the delivered `StokesShift.absEnergy_eq`.

Every declaration is fully proved. There is no unfinished placeholder and no custom axiomatic
declaration in this file. The module ends with `#print axioms` lines that the package validator
parses as the per-declaration footprint gate.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations

set_option autoImplicit false

noncomputable section

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace R4Excited01

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

/-! ## §1 — Hammond / EnergyGapLaw (equivalence)

The energy-gap-law nonradiative barrier `nrBarrier` is the equal-curvature two-parabola forward
barrier. The Hammond forward gap `gapReactant` is the same barrier, and its transition-state
coordinate `tsCoord` vanishes exactly at the barrierless point `x = lam`. The delivered §15
boundary row states `Kernel.tsCoord lam x = 0 ↔ lam = x`. Composing the barrier-zero condition
with that row gives the equivalence. -/

/-- Shared context of the Hammond/EnergyGapLaw barrierless comparison. -/
structure HammondEnergyGapCtx where
  /-- Reorganization energy. -/
  lam : ℝ
  /-- Driving force `x = -ΔG°`. -/
  x : ℝ

/-- The curvature is nonzero so both barrier presentations are well defined. -/
def pHammondEnergyGapLamNeZero : Premise HammondEnergyGapCtx :=
  mkPremise "hammondEnergyGap.lamNeZero" fun δ => δ.lam ≠ 0

/-- Premise set of the barrierless comparison. -/
def hammondEnergyGapPremises : List (Premise HammondEnergyGapCtx) :=
  [pHammondEnergyGapLamNeZero]

/-- The two barrier-zero predicates compared by the equivalence. -/
def hammondEnergyGapComparison : Comparison HammondEnergyGapCtx where
  left := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrBarrier"
    "HammondEnergyGapCtx" "PhotoLean/EnergyGapLaw/Basic.lean#nrBarrier"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord"
    "HammondEnergyGapCtx" "PhotoLean/Hammond/Basic.lean#tsCoord"
  leftContext := HammondEnergyGapCtx
  rightContext := HammondEnergyGapCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => EnergyGapLaw.nrBarrier δ.lam δ.x = 0
  rightPredicate := fun δ => Hammond.tsCoord δ.lam δ.x = 0

/-- Source coherence: the nonradiative barrier vanishes exactly at the Hammond reactant
geometry. -/
theorem hammondEnergyGapBarrierZero_iff {lam x : ℝ} (hlam : lam ≠ 0) :
    EnergyGapLaw.nrBarrier lam x = 0 ↔ Hammond.tsCoord lam x = 0 := by
  have hbar : EnergyGapLaw.nrBarrier lam x = 0 ↔ lam = x := by
    unfold EnergyGapLaw.nrBarrier
    have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
    constructor
    · intro h
      have hsq : (lam - x) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp h with h' | h'
        · exact h'
        · exact absurd h' h4
      have hx : lam - x = 0 := sq_eq_zero_iff.mp hsq
      linarith
    · intro h
      rw [h, sub_self, zero_pow (by norm_num), zero_div]
  rw [hbar]
  exact (Relations.eg_boundary_eq_tsCoord_zero hlam x).symm

/-- The typed equivalence link: the energy-gap-law barrier-zero locus is the Hammond
transition-state boundary. -/
def hammondEnergyGapLink : ParentCertificate HammondEnergyGapCtx :=
  .equivalence "Q-R4-E1-HEG-01" hammondEnergyGapComparison hammondEnergyGapPremises
    (fun δ hprem => by
      have hlam : δ.lam ≠ 0 :=
        hprem pHammondEnergyGapLamNeZero (by simp [hammondEnergyGapPremises])
      exact hammondEnergyGapBarrierZero_iff hlam)

/-- Certificate: an equivalence of the two barrier-zero predicates. -/
def hammondEnergyGapBarrierZeroEquiv : Certificate HammondEnergyGapCtx :=
  .equivalence hammondEnergyGapLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem hammondEnergyGapBarrierZeroEquiv_kind :
    certificateKind hammondEnergyGapBarrierZeroEquiv = RelationKind.equivalence := rfl

/-! ## §2 — BEP / EnergyGapLaw (equivalence)

The BEP transfer coefficient `transfer` is the linear-response coefficient of the same
two-parabola step; the delivered bridge identifies it with the Hammond transition-state
coordinate. The energy-gap-law inverted region is the driving-force range beyond the
reorganization energy. The delivered §2 row states that a negative transition-state coordinate
is exactly the Marcus inverted region, and the energy-gap-law predicate is the same inequality.
So the inverted region is exactly where the BEP coefficient turns negative. -/

/-- Shared context of the BEP/EnergyGapLaw regime comparison. -/
structure BepEnergyGapCtx where
  /-- Reorganization energy. -/
  lam : ℝ
  /-- Driving force `x = -ΔG°`. -/
  x : ℝ

/-- The curvature is positive: the inverted-region boundary is physical. -/
def pBepEnergyGapLamPositive : Premise BepEnergyGapCtx :=
  mkPremise "bepEnergyGap.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the regime comparison. -/
def bepEnergyGapPremises : List (Premise BepEnergyGapCtx) :=
  [pBepEnergyGapLamPositive]

/-- The inverted-region predicate against the negative-transfer predicate. -/
def bepEnergyGapComparison : Comparison BepEnergyGapCtx where
  left := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.InvertedGap"
    "BepEnergyGapCtx" "PhotoLean/EnergyGapLaw/Basic.lean#InvertedGap"
  right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.transfer"
    "BepEnergyGapCtx" "PhotoLean/BEP/Basic.lean#transfer"
  leftContext := BepEnergyGapCtx
  rightContext := BepEnergyGapCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => EnergyGapLaw.InvertedGap δ.lam δ.x
  rightPredicate := fun δ => BEP.transfer δ.lam δ.x < 0

/-- Source coherence: the energy-gap-law inverted region is the negative-transfer region. -/
theorem bepEnergyGapInverted_iff_transfer_neg {lam x : ℝ} (hlam : 0 < lam) :
    EnergyGapLaw.InvertedGap lam x ↔ BEP.transfer lam x < 0 := by
  have htr : BEP.transfer lam x = Hammond.tsCoord lam x :=
    Relations.transfer_eq_tsCoord_bridge (ne_of_gt hlam) x
  rw [htr]
  exact (Relations.tsCoord_lt_zero_iff_inverted hlam).symm

/-- The typed equivalence link. -/
def bepEnergyGapLink : ParentCertificate BepEnergyGapCtx :=
  .equivalence "Q-R4-E1-BEG-01" bepEnergyGapComparison bepEnergyGapPremises
    (fun δ hprem => by
      have hlam : 0 < δ.lam :=
        hprem pBepEnergyGapLamPositive (by simp [bepEnergyGapPremises])
      exact bepEnergyGapInverted_iff_transfer_neg hlam)

/-- Certificate: an equivalence of the inverted-region and negative-transfer predicates. -/
def bepEnergyGapInvertedEquiv : Certificate BepEnergyGapCtx :=
  .equivalence bepEnergyGapLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem bepEnergyGapInvertedEquiv_kind :
    certificateKind bepEnergyGapInvertedEquiv = RelationKind.equivalence := rfl

/-! ## §3 — Hammond / Kasha (equivalence)

Kasha's Marcus-form internal-conversion rate `marcusIC` is `A · exp(-barrier/(kB·T))`; the
delivered `kernel_marcusIC` identifies its barrier with the shared kernel barrier, which is the
Hammond forward gap. The rate reaches its pre-exponential value `A` exactly when the barrier
vanishes, i.e. exactly when the Hammond transition-state coordinate reaches the reactant well.
The equivalence is a genuine rate/geometry identification, not a definitional restatement: the
Kasha side is a rate in `(A, lam, kB, T, x)` and the Hammond side is a crossing coordinate. -/

/-- Shared context of the Kasha/Hammond rate-geometry comparison. -/
structure HammondKashaCtx where
  /-- Pre-exponential factor. -/
  A : ℝ
  /-- Reorganization energy. -/
  lam : ℝ
  /-- Boltzmann constant. -/
  kB : ℝ
  /-- Temperature. -/
  T : ℝ
  /-- Driving force `x = -ΔG°`. -/
  x : ℝ

/-- The pre-exponential factor is positive. -/
def pHammondKashaAPositive : Premise HammondKashaCtx :=
  mkPremise "kasha.preExponentialPositive" fun δ => 0 < δ.A

/-- The thermal energy is positive. -/
def pHammondKashaThermalPositive : Premise HammondKashaCtx :=
  mkPremise "thermal.energyPositive" fun δ => 0 < δ.kB * δ.T

/-- The curvature is positive. -/
def pHammondKashaLamPositive : Premise HammondKashaCtx :=
  mkPremise "hammond.curvaturePositive" fun δ => 0 < δ.lam

/-- Premise set of the rate-geometry comparison. -/
def hammondKashaPremises : List (Premise HammondKashaCtx) :=
  [pHammondKashaAPositive, pHammondKashaThermalPositive, pHammondKashaLamPositive]

/-- The IC-rate maximum against the transition-state boundary. -/
def hammondKashaComparison : Comparison HammondKashaCtx where
  left := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.marcusIC"
    "HammondKashaCtx" "PhotoLean/Kasha/Compose.lean#marcusIC"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord"
    "HammondKashaCtx" "PhotoLean/Hammond/Basic.lean#tsCoord"
  leftContext := HammondKashaCtx
  rightContext := HammondKashaCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x = δ.A
  rightPredicate := fun δ => Hammond.tsCoord δ.lam δ.x = 0

/-- Source coherence: the Kasha IC rate is at its pre-exponential exactly at the Hammond
reactant-geometry boundary. -/
theorem hammondKashaIC_eq_prefactor_iff {A lam kB T x : ℝ}
    (hA : A ≠ 0) (hkT : kB * T ≠ 0) (hlam : lam ≠ 0) :
    Kasha.marcusIC A lam kB T x = A ↔ Hammond.tsCoord lam x = 0 := by
  have hrate : Kasha.marcusIC A lam kB T x = A ↔ (lam - x) ^ 2 / (4 * lam) = 0 := by
    rw [Relations.kernel_marcusIC]
    unfold Kernel.barrier
    constructor
    · intro h
      have hexp : Real.exp (-((lam - x) ^ 2 / (4 * lam)) / (kB * T)) = 1 := by
        have h' : A * Real.exp (-((lam - x) ^ 2 / (4 * lam)) / (kB * T)) = A * 1 := by
          simpa using h
        exact mul_left_cancel₀ hA h'
      have harg : -((lam - x) ^ 2 / (4 * lam)) / (kB * T) = 0 :=
        (Real.exp_eq_one_iff _).mp hexp
      rcases div_eq_zero_iff.mp harg with h' | h'
      · have hdiv : (lam - x) ^ 2 / (4 * lam) = 0 := neg_eq_zero.mp h'
        rcases div_eq_zero_iff.mp hdiv with h'' | h''
        · exact hdiv
        · exact absurd h'' (mul_ne_zero (by norm_num) hlam)
      · exact absurd h' hkT
    · intro h
      rw [h]
      simp
  rw [hrate]
  unfold Hammond.tsCoord
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  have h2 : (2 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  constructor
  · intro h
    have hsq : (lam - x) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' h4
    have hx : lam - x = 0 := sq_eq_zero_iff.mp hsq
    rw [hx, zero_div]
  · intro h
    rcases div_eq_zero_iff.mp h with h' | h'
    · have hx : x = lam := by linarith
      rw [hx, sub_self, zero_pow (by norm_num), zero_div]
    · exact absurd h' h2

/-- The typed equivalence link. -/
def hammondKashaLink : ParentCertificate HammondKashaCtx :=
  .equivalence "Q-R4-E1-HK-01" hammondKashaComparison hammondKashaPremises
    (fun δ hprem => by
      have hA : δ.A ≠ 0 :=
        ne_of_gt (hprem pHammondKashaAPositive (by simp [hammondKashaPremises]))
      have hkT : δ.kB * δ.T ≠ 0 :=
        ne_of_gt (hprem pHammondKashaThermalPositive (by simp [hammondKashaPremises]))
      have hlam : δ.lam ≠ 0 :=
        ne_of_gt (hprem pHammondKashaLamPositive (by simp [hammondKashaPremises]))
      exact hammondKashaIC_eq_prefactor_iff hA hkT hlam)

/-- Certificate: an equivalence of the IC-rate maximum and the transition-state boundary. -/
def hammondKashaICMaxEquiv : Certificate HammondKashaCtx :=
  .equivalence hammondKashaLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem hammondKashaICMaxEquiv_kind :
    certificateKind hammondKashaICMaxEquiv = RelationKind.equivalence := rfl

/-! ## §4 — Hammond / ICvsISC (definitional identity)

The IC channel's Franck–Condon barrier `fcBarrier` is the theory's own copy of the kernel
barrier; the Hammond forward gap `gapReactant` is another copy of the same kernel object. Both
bodies are `(lam - x)^2 / (4 lam)`, so the two translated terms are definitionally equal. The
certificate is a fresh `rfl`-only `DefEq` pin, not a propositional-equality substitution. -/

/-- Shared context of the barrier pin. -/
structure HammondICvsISCCtx where
  /-- Reorganization energy. -/
  lam : ℝ
  /-- Driving force / gap. -/
  x : ℝ

/-- Definitional pin: the IC Franck–Condon barrier is the Hammond forward reactant gap. -/
def hammondICvsISCPin : DefinitionalPin HammondICvsISCCtx where
  left := mkRef "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.fcBarrier"
    "HammondICvsISCCtx" "PhotoLean/ICvsISC/Basic.lean#fcBarrier"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.gapReactant"
    "HammondICvsISCCtx" "PhotoLean/Hammond/Basic.lean#gapReactant"
  leftContext := HammondICvsISCCtx
  rightContext := HammondICvsISCCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => ICvsISC.fcBarrier δ.lam δ.x
  rightTerm := fun δ => Hammond.gapReactant δ.lam δ.x
  same := DefEq.refl

/-- Certificate: a definitional identity over the two barrier copies. -/
def hammondICvsISCBarrierPin : Certificate HammondICvsISCCtx :=
  .definitionalIdentity hammondICvsISCPin []

/-- Kind pin: the row is a definitional identity. -/
theorem hammondICvsISCBarrierPin_kind :
    certificateKind hammondICvsISCBarrierPin = RelationKind.definitionalIdentity := rfl

/-! ## §5 — BEP / Kasha (equivalence)

The BEP transfer coefficient is the Hammond transition-state coordinate of the same step
(delivered bridge). The Kasha IC rate is at its pre-exponential exactly when the barrier
vanishes, i.e. exactly when that coordinate vanishes. So the BEP coefficient is zero exactly
where the Kasha IC rate reaches its maximum. -/

/-- Shared context of the BEP/Kasha coefficient-rate comparison. -/
structure BepKashaCtx where
  /-- Pre-exponential factor. -/
  A : ℝ
  /-- Reorganization energy. -/
  lam : ℝ
  /-- Boltzmann constant. -/
  kB : ℝ
  /-- Temperature. -/
  T : ℝ
  /-- Driving force `x = -ΔG°`. -/
  x : ℝ

/-- The pre-exponential factor is positive. -/
def pBepKashaAPositive : Premise BepKashaCtx :=
  mkPremise "kasha.preExponentialPositive" fun δ => 0 < δ.A

/-- The thermal energy is positive. -/
def pBepKashaThermalPositive : Premise BepKashaCtx :=
  mkPremise "thermal.energyPositive" fun δ => 0 < δ.kB * δ.T

/-- The curvature is positive. -/
def pBepKashaLamPositive : Premise BepKashaCtx :=
  mkPremise "bep.curvaturePositive" fun δ => 0 < δ.lam

/-- Premise set of the coefficient-rate comparison. -/
def bepKashaPremises : List (Premise BepKashaCtx) :=
  [pBepKashaAPositive, pBepKashaThermalPositive, pBepKashaLamPositive]

/-- The transfer-zero predicate against the IC-rate maximum. -/
def bepKashaComparison : Comparison BepKashaCtx where
  left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.transfer"
    "BepKashaCtx" "PhotoLean/BEP/Basic.lean#transfer"
  right := mkRef "PhotoLean.Kasha" "PhotoLean.Kasha.marcusIC"
    "BepKashaCtx" "PhotoLean/Kasha/Compose.lean#marcusIC"
  leftContext := BepKashaCtx
  rightContext := BepKashaCtx
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := fun δ => BEP.transfer δ.lam δ.x = 0
  rightPredicate := fun δ => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x = δ.A

/-- Source coherence: the BEP coefficient vanishes exactly at the Kasha IC-rate maximum. -/
theorem bepKashaTransferZero_iff_icMax {A lam kB T x : ℝ}
    (hA : A ≠ 0) (hkT : kB * T ≠ 0) (hlam : lam ≠ 0) :
    BEP.transfer lam x = 0 ↔ Kasha.marcusIC A lam kB T x = A := by
  have htr : BEP.transfer lam x = Hammond.tsCoord lam x :=
    Relations.transfer_eq_tsCoord_bridge hlam x
  rw [htr]
  exact (hammondKashaIC_eq_prefactor_iff hA hkT hlam).symm

/-- The typed equivalence link. -/
def bepKashaLink : ParentCertificate BepKashaCtx :=
  .equivalence "Q-R4-E1-BK-01" bepKashaComparison bepKashaPremises
    (fun δ hprem => by
      have hA : δ.A ≠ 0 :=
        ne_of_gt (hprem pBepKashaAPositive (by simp [bepKashaPremises]))
      have hkT : δ.kB * δ.T ≠ 0 :=
        ne_of_gt (hprem pBepKashaThermalPositive (by simp [bepKashaPremises]))
      have hlam : δ.lam ≠ 0 :=
        ne_of_gt (hprem pBepKashaLamPositive (by simp [bepKashaPremises]))
      exact bepKashaTransferZero_iff_icMax hA hkT hlam)

/-- Certificate: an equivalence of the transfer-zero and IC-rate-maximum predicates. -/
def bepKashaTransferZeroEquiv : Certificate BepKashaCtx :=
  .equivalence bepKashaLink rfl

/-- Kind pin: the row is an equivalence. -/
theorem bepKashaTransferZeroEquiv_kind :
    certificateKind bepKashaTransferZeroEquiv = RelationKind.equivalence := rfl

/-! ## §6 — Hammond / StokesShift (observational equivalence)

The Stokes theory's vertical absorption energy `absEnergy` is the band maximum measured from
the ground minimum. Hammond's two surfaces are the ground and excited surfaces of the same
equal-curvature displaced oscillator: the excited surface at `q = 0` minus the ground surface
at `q = 0` is exactly that vertical gap. The channel observes the absorption energy. -/

/-- Shared context of the absorption-energy channel. -/
structure HammondStokesCtx where
  /-- Reorganization energy. -/
  lam : ℝ
  /-- 0-0 energy. -/
  e00 : ℝ

/-- The two readings compared by the absorption-energy channel. -/
def hammondStokesSetup : ObservationalSetup HammondStokesCtx where
  left := mkRef "PhotoLean.StokesShift" "PhotoLean.StokesShift.absEnergy"
    "HammondStokesCtx" "PhotoLean/StokesShift/Basic.lean#absEnergy"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.productSurface"
    "HammondStokesCtx" "PhotoLean/Hammond/Basic.lean#productSurface"
  leftState := HammondStokesCtx
  rightState := HammondStokesCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The vertical absorption-energy channel. -/
noncomputable def hammondStokesChannel :
    Channel HammondStokesCtx hammondStokesSetup ℝ Unit where
  name := "absorptionEnergy"
  domain := Set.univ
  leftObs := fun δ _ => StokesShift.absEnergy δ.lam δ.e00
  rightObs := fun δ _ =>
    Hammond.productSurface δ.lam δ.e00 0 - Hammond.reactantSurface δ.lam 0

/-- Source coherence: the Stokes absorption energy is the Hammond vertical surface gap. -/
theorem stokesAbsEnergy_eq_hammondVerticalGap (lam e00 : ℝ) :
    StokesShift.absEnergy lam e00 =
      Hammond.productSurface lam e00 0 - Hammond.reactantSurface lam 0 := by
  rw [StokesShift.absEnergy_eq]
  unfold Hammond.productSurface Hammond.reactantSurface
  norm_num

/-- Certificate: equality of the declared absorption-energy channel on its whole domain. -/
def hammondStokesAbsorptionBridge : Certificate HammondStokesCtx :=
  .observationalEquivalence hammondStokesSetup [] ℝ Unit [hammondStokesChannel]
    (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact stokesAbsEnergy_eq_hammondVerticalGap δ.lam δ.e00)

/-- Kind pin: the row is an observational equivalence. -/
theorem hammondStokesAbsorptionBridge_kind :
    certificateKind hammondStokesAbsorptionBridge =
      RelationKind.observationalEquivalence := rfl

end R4Excited01
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the E1 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.hammondEnergyGapBarrierZeroEquiv
#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.bepEnergyGapInvertedEquiv
#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.hammondKashaICMaxEquiv
#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.hammondICvsISCBarrierPin
#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.bepKashaTransferZeroEquiv
#print axioms PhotoLean.RelationAudit.BoundedAudit.R4Excited01.hammondStokesAbsorptionBridge
