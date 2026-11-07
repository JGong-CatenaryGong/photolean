/-
PhotoLean.RelationAudit.BoundedAudit.E2 — R4 Package E2 bounded screening evidence.

This module is additive. It imports the delivered theory modules and the audit semantic
core, and it changes no delivered statement. It carries only the five certificates needed by
the fourteen-pair E2 screening package when the legacy registry has no certificate of the
required kind. Every declaration is fully proved; there is no unproved placeholder and no
custom axiomatic declaration in this file.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.BEP.Basic
import PhotoLean.StokesShift.Basic
import PhotoLean.ICvsISC.Basic
import PhotoLean.SymmetryFactor.Sharp
import PhotoLean.EnergyGapLaw.Basic

set_option autoImplicit false

noncomputable section

open PhotoLean.RelationAudit

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace E2

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

/-! ## §1 — BEP / StokesShift (observational equivalence)

At thermoneutrality the BEP activation barrier is one eighth of the Stokes shift under the
shared equal-curvature two-parabola reading: `eact lam 0 = lam/4`, `stokesShift = 2*lam`.
The channel observes the barrier height against the optical band separation. -/

/-- Shared context of the BEP/StokesShift thermoneutral comparison. -/
structure BepStokesCtx where
  lam : ℝ
  e00 : ℝ

/-- Thermoneutral barrier versus one eighth of the Stokes shift. -/
theorem bepStokesThermoneutral (lam e00 : ℝ) :
    PhotoLean.BEP.eact lam 0 =
      PhotoLean.StokesShift.stokesShift lam e00 / 8 := by
  unfold PhotoLean.BEP.eact PhotoLean.StokesShift.stokesShift
    PhotoLean.StokesShift.absEnergy PhotoLean.StokesShift.emEnergy
    PhotoLean.StokesShift.s1Surface PhotoLean.StokesShift.s0Surface
  rcases eq_or_ne lam 0 with h | h
  · subst h
    norm_num
  · field_simp
    ring

/-- The two readings compared by the thermoneutral row. -/
def bepStokesSetup : ObservationalSetup BepStokesCtx where
  left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.eact" "BepStokesCtx"
    "PhotoLean/BEP/Basic.lean#eact"
  right := mkRef "PhotoLean.StokesShift" "PhotoLean.StokesShift.stokesShift" "BepStokesCtx"
    "PhotoLean/StokesShift/Basic.lean#stokesShift"
  leftState := BepStokesCtx
  rightState := BepStokesCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The barrier-height / band-separation channel. -/
def bepStokesChannel : Channel BepStokesCtx bepStokesSetup ℝ Unit where
  name := "thermoneutralBarrierVsEighthStokesShift"
  domain := Set.univ
  leftObs := fun δ _ => PhotoLean.BEP.eact δ.lam 0
  rightObs := fun δ _ => PhotoLean.StokesShift.stokesShift δ.lam δ.e00 / 8

/-- Observational equivalence: the thermoneutral barrier is one eighth of the Stokes shift. -/
def bepStokesBridge : Certificate BepStokesCtx :=
  .observationalEquivalence bepStokesSetup [] ℝ Unit [bepStokesChannel] (by decide)
    (fun δ _ c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact bepStokesThermoneutral δ.lam δ.e00)

/-- Kind pin: the row is an observational equivalence. -/
theorem bepStokesBridge_kind :
    certificateKind bepStokesBridge = RelationKind.observationalEquivalence := rfl

/-! ## §2 — BEP / ICvsISC (definitional identity)

The IC channel's Franck–Condon barrier and the BEP activation barrier are the same
equal-curvature crossing object, built by two independent theory copies of the kernel
barrier. The pin is a fresh `rfl` check of the two translated terms. -/

/-- Shared context of the BEP/ICvsISC barrier comparison. -/
structure BepICCtx where
  lam : ℝ
  x : ℝ

/-- Definitional pin: the IC Franck–Condon barrier is the BEP activation barrier. -/
def bepICPin : DefinitionalPin BepICCtx where
  left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.eact" "BepICCtx"
    "PhotoLean/BEP/Basic.lean#eact"
  right := mkRef "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.fcBarrier" "BepICCtx"
    "PhotoLean/ICvsISC/Basic.lean#fcBarrier"
  leftContext := BepICCtx
  rightContext := BepICCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => PhotoLean.BEP.eact δ.lam δ.x
  rightTerm := fun δ => PhotoLean.ICvsISC.fcBarrier δ.lam δ.x
  same := DefEq.refl

/-- The definitional-identity certificate. -/
def bepICBridge : Certificate BepICCtx :=
  .definitionalIdentity bepICPin []

/-- Kind pin: the row is a definitional identity. -/
theorem bepICBridge_kind :
    certificateKind bepICBridge = RelationKind.definitionalIdentity := rfl

/-! ## §3 — SymmetryFactor / StokesShift (definitional identity)

Both theories carry their own copies of the same displaced-parabola surfaces. The Stokes
ground and excited surfaces are the SymmetryFactor reactant and product surfaces at equal
curvature, proved by a fresh `rfl` check of the paired translated terms. -/

/-- Shared context of the SymmetryFactor/StokesShift surface comparison. -/
structure ScStokesCtx where
  lam : ℝ
  e00 : ℝ
  q : ℝ

/-- Definitional pin: the two surface pairs are the same terms. -/
def scStokesPin : DefinitionalPin ScStokesCtx where
  left := mkRef "PhotoLean.StokesShift" "PhotoLean.StokesShift.s0Surface" "ScStokesCtx"
    "PhotoLean/StokesShift/Basic.lean#s0Surface"
  right := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.asymReactantSurface"
    "ScStokesCtx" "PhotoLean/SymmetryFactor/Basic.lean#asymReactantSurface"
  leftContext := ScStokesCtx
  rightContext := ScStokesCtx
  codomain := ℝ × ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ =>
    (PhotoLean.StokesShift.s0Surface δ.lam δ.q,
     PhotoLean.StokesShift.s1Surface δ.lam δ.e00 δ.q)
  rightTerm := fun δ =>
    (PhotoLean.SymmetryFactor.asymReactantSurface δ.lam δ.q,
     PhotoLean.SymmetryFactor.asymProductSurface δ.lam δ.e00 δ.q)
  same := DefEq.refl

/-- The definitional-identity certificate. -/
def scStokesBridge : Certificate ScStokesCtx :=
  .definitionalIdentity scStokesPin []

/-- Kind pin: the row is a definitional identity. -/
theorem scStokesBridge_kind :
    certificateKind scStokesBridge = RelationKind.definitionalIdentity := rfl

/-! ## §4 — SymmetryFactor / EnergyGapLaw (observational equivalence)

At thermoneutral equal curvature the energy-gap-law nonradiative barrier is the
SymmetryFactor reactant-surface height at the β = 1/2 crossing coordinate. This extends the
delivered §11 tie-back (`tsCoordZero lam lam = 1/2`) to the EGL kernel copy. -/

/-- Shared context of the SymmetryFactor/EnergyGapLaw thermoneutral comparison. -/
structure ScEgCtx where
  lam : ℝ

/-- The curvature is physical. -/
def pScEgLamPos : Premise ScEgCtx :=
  mkPremise "scEg.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the thermoneutral barrier comparison. -/
def scEgPremises : List (Premise ScEgCtx) := [pScEgLamPos]

/-- At thermoneutrality the EGL barrier is the SymmetryFactor surface height at β = 1/2. -/
theorem egThermoneutralSurface (lam : ℝ) (hlam : 0 < lam) :
    PhotoLean.EnergyGapLaw.nrBarrier lam 0 =
      PhotoLean.SymmetryFactor.asymReactantSurface lam
        (PhotoLean.SymmetryFactor.tsCoordZero lam lam) := by
  have hhalf : PhotoLean.SymmetryFactor.tsCoordZero lam lam = 1 / 2 := by
    have h := PhotoLean.SymmetryFactor.betaHalf_holds_in_kernel hlam
    unfold PhotoLean.SymmetryFactor.BetaHalfReading at h
    exact h
  rw [hhalf]
  unfold PhotoLean.EnergyGapLaw.nrBarrier PhotoLean.SymmetryFactor.asymReactantSurface
  field_simp
  ring

/-- The two readings compared by the thermoneutral barrier row. -/
def scEgSetup : ObservationalSetup ScEgCtx where
  left := mkRef "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrBarrier" "ScEgCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrBarrier"
  right := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.asymReactantSurface"
    "ScEgCtx" "PhotoLean/SymmetryFactor/Basic.lean#asymReactantSurface"
  leftState := ScEgCtx
  rightState := ScEgCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The thermoneutral barrier-height channel. -/
def scEgChannel : Channel ScEgCtx scEgSetup ℝ Unit where
  name := "thermoneutralBarrierHeight"
  domain := Set.univ
  leftObs := fun δ _ => PhotoLean.EnergyGapLaw.nrBarrier δ.lam 0
  rightObs := fun δ _ =>
    PhotoLean.SymmetryFactor.asymReactantSurface δ.lam
      (PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)

/-- Observational equivalence of the thermoneutral barrier height. -/
def scEgBridge : Certificate ScEgCtx :=
  .observationalEquivalence scEgSetup scEgPremises ℝ Unit [scEgChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact egThermoneutralSurface δ.lam
        (hprem pScEgLamPos (by simp [scEgPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem scEgBridge_kind :
    certificateKind scEgBridge = RelationKind.observationalEquivalence := rfl

/-! ## §5 — SymmetryFactor / ICvsISC (observational equivalence)

At thermoneutral equal curvature the IC channel's Franck–Condon barrier is the
SymmetryFactor reactant-surface height at the β = 1/2 crossing coordinate. -/

/-- Shared context of the SymmetryFactor/ICvsISC thermoneutral comparison. -/
structure ScICCtx where
  lam : ℝ

/-- The curvature is physical. -/
def pScICLamPos : Premise ScICCtx :=
  mkPremise "scIC.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the thermoneutral barrier comparison. -/
def scICPremises : List (Premise ScICCtx) := [pScICLamPos]

/-- At thermoneutrality the IC barrier is the SymmetryFactor surface height at β = 1/2. -/
theorem icThermoneutralSurface (lam : ℝ) (hlam : 0 < lam) :
    PhotoLean.ICvsISC.fcBarrier lam 0 =
      PhotoLean.SymmetryFactor.asymReactantSurface lam
        (PhotoLean.SymmetryFactor.tsCoordZero lam lam) := by
  have hhalf : PhotoLean.SymmetryFactor.tsCoordZero lam lam = 1 / 2 := by
    have h := PhotoLean.SymmetryFactor.betaHalf_holds_in_kernel hlam
    unfold PhotoLean.SymmetryFactor.BetaHalfReading at h
    exact h
  rw [hhalf]
  unfold PhotoLean.ICvsISC.fcBarrier PhotoLean.SymmetryFactor.asymReactantSurface
  field_simp
  ring

/-- The two readings compared by the thermoneutral barrier row. -/
def scICSetup : ObservationalSetup ScICCtx where
  left := mkRef "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.fcBarrier" "ScICCtx"
    "PhotoLean/ICvsISC/Basic.lean#fcBarrier"
  right := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.asymReactantSurface"
    "ScICCtx" "PhotoLean/SymmetryFactor/Basic.lean#asymReactantSurface"
  leftState := ScICCtx
  rightState := ScICCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The thermoneutral barrier-height channel. -/
def scICChannel : Channel ScICCtx scICSetup ℝ Unit where
  name := "thermoneutralBarrierHeight"
  domain := Set.univ
  leftObs := fun δ _ => PhotoLean.ICvsISC.fcBarrier δ.lam 0
  rightObs := fun δ _ =>
    PhotoLean.SymmetryFactor.asymReactantSurface δ.lam
      (PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)

/-- Observational equivalence of the thermoneutral barrier height. -/
def scICBridge : Certificate ScICCtx :=
  .observationalEquivalence scICSetup scICPremises ℝ Unit [scICChannel] (by decide)
    (fun δ hprem c hc _x _hx => by
      rcases List.mem_singleton.mp hc with rfl
      exact icThermoneutralSurface δ.lam
        (hprem pScICLamPos (by simp [scICPremises])))

/-- Kind pin: the row is an observational equivalence. -/
theorem scICBridge_kind :
    certificateKind scICBridge = RelationKind.observationalEquivalence := rfl

end E2
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the E2 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.E2.bepStokesBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.E2.bepICBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.E2.scStokesBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.E2.scEgBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.E2.scICBridge
