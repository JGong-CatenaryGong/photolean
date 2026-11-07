/-
PhotoLean.BoundedAudit.Surface — R2 bounded screening evidence for WP-SURFACE-01.

This module is additive. It imports the delivered theory modules and the audit
semantic core, and it changes no delivered statement. It carries only the new
certificates needed by the ten-pair surface/free-energy screening package when
the legacy registry has no certificate of the required kind.

The certificates here are wrappers around delivered theorems: each one states
the comparison in the typed `Certificate` language of `PhotoLean.RelationAudit`
and reuses the delivered proof. No statement is weakened and no new physical
claim is introduced. Every declaration is fully proved; there is no unproved
placeholder and no custom axiomatic declaration in this file.

Sections:

* §1 Marcus rate / Sabatier activity: the shared Arrhenius body (definitional).
* §2 SymmetryFactor / Hammond: equal-curvature thermoneutral coordinate.
* §3 SymmetryFactor / BEP: equal-curvature thermoneutral transfer coefficient.
* §4 BEP / Sabatier: the linear volcano is the maximum of the BEP tangents.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations

set_option autoImplicit false

namespace PhotoLean
namespace RelationAudit
namespace BoundedAudit
namespace Surface

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

/-! ## §1 — Marcus rate / Sabatier activity (definitional identity)

The delivered theorem `PhotoLean.Relations.marcus_rate_eq_activity` proves that the
Marcus rate is the Sabatier activity functional of the same two-parabola barrier,
scaled by the pre-exponential factor. The proof is `unfold ...; rfl`, so the two
translated terms are definitionally equal; the pin below carries a fresh `DefEq.refl`.
This is the shared functional form ("same shape") of the look-alike pair, not a claim
that the two optima coincide. -/

/-- Shared context of the Marcus-rate / Sabatier-activity comparison. -/
structure RateActivityCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- Definitional pin: the Marcus rate is the Sabatier activity of the kernel barrier. -/
noncomputable def marcusRateSabatierActivityPin : Certificate RateActivityCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "RateActivityCtx"
        "PhotoLean/Marcus/Basic.lean#rate"
      right := mkRef "PhotoLean.Sabatier" "PhotoLean.Sabatier.activity" "RateActivityCtx"
        "PhotoLean/Sabatier/Basic.lean#activity"
      leftContext := RateActivityCtx
      rightContext := RateActivityCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
      rightTerm := fun δ =>
        δ.A * Sabatier.activity (fun y => Kernel.barrier δ.lam y) δ.kB δ.T δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the shared Arrhenius body. -/
theorem marcusRateSabatierActivityPin_defeq :
    DefEq (fun δ : RateActivityCtx => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : RateActivityCtx =>
        δ.A * Sabatier.activity (fun y => Kernel.barrier δ.lam y) δ.kB δ.T δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§9 marcus_rate_eq_activity` row. -/
theorem marcusRateSabatierActivityPin_source (δ : RateActivityCtx) :
    Marcus.rate δ.A δ.lam δ.kB δ.T δ.x =
      δ.A * Sabatier.activity (fun y => Kernel.barrier δ.lam y) δ.kB δ.T δ.x :=
  PhotoLean.Relations.marcus_rate_eq_activity δ.A δ.lam δ.kB δ.T δ.x

/-- Kind pin: the row is a definitional identity. -/
theorem marcusRateSabatierActivityPin_kind :
    certificateKind marcusRateSabatierActivityPin = RelationKind.definitionalIdentity := rfl

/-! ## §2 — SymmetryFactor / Hammond (observational equivalence)

At equal force constants the unequal-curvature model reduces to the kernel model.
The delivered tie-back `SymmetryFactor.tsCoordZero_eq_kernel_thermoneutral` gives the
closed-form thermoneutral coordinate as `Kernel.tsCoord lam 0`, and the delivered
kernel pin `PhotoLean.Relations.kernel_tsCoord_eq_hammond` identifies that term with
`Hammond.tsCoord lam 0`. The channel below observes the thermoneutral transition-state
coordinate on the equal-curvature diagonal. -/

/-- Shared context: the equal-curvature parameter. -/
structure SymFactorHammondCtx where
  lam : ℝ

/-- The curvature is physical. -/
def pSymFactorLamPositive : Premise SymFactorHammondCtx :=
  mkPremise "symmetryFactor.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the equal-curvature tie-back. -/
def symFactorHammondPremises : List (Premise SymFactorHammondCtx) := [pSymFactorLamPositive]

/-- The two readings compared by the tie-back. -/
def symFactorHammondSetup : ObservationalSetup SymFactorHammondCtx where
  left := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.tsCoordZero"
    "SymFactorHammondCtx" "PhotoLean/SymmetryFactor/Basic.lean#tsCoordZero"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord"
    "SymFactorHammondCtx" "PhotoLean/Hammond/Basic.lean#tsCoord"
  leftState := SymFactorHammondCtx
  rightState := SymFactorHammondCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The thermoneutral transition-state coordinate channel. -/
noncomputable def symFactorHammondChannel :
    Channel SymFactorHammondCtx symFactorHammondSetup ℝ Unit where
  name := "thermoneutralTransitionStateCoordinate"
  domain := Set.univ
  leftObs := fun δ _ => SymmetryFactor.tsCoordZero δ.lam δ.lam
  rightObs := fun δ _ => Hammond.tsCoord δ.lam 0

/-- Observational equivalence: equal-curvature SymmetryFactor coordinate equals the Hammond
thermoneutral coordinate. -/
noncomputable def symmetryFactorHammondThermoneutralBridge : Certificate SymFactorHammondCtx :=
  .observationalEquivalence symFactorHammondSetup symFactorHammondPremises ℝ Unit
    [symFactorHammondChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      have hlam : 0 < δ.lam :=
        hprem pSymFactorLamPositive (by simp [symFactorHammondPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact (SymmetryFactor.tsCoordZero_eq_kernel_thermoneutral hlam).trans rfl)

/-- Source coherence: the delivered tie-back plus the kernel/Hammond pin. -/
theorem symmetryFactorHammondThermoneutralBridge_source (δ : SymFactorHammondCtx)
    (hlam : 0 < δ.lam) :
    SymmetryFactor.tsCoordZero δ.lam δ.lam = Hammond.tsCoord δ.lam 0 :=
  (SymmetryFactor.tsCoordZero_eq_kernel_thermoneutral hlam).trans rfl

/-- Kind pin: the row is an observational equivalence. -/
theorem symmetryFactorHammondThermoneutralBridge_kind :
    certificateKind symmetryFactorHammondThermoneutralBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §3 — SymmetryFactor / BEP (observational equivalence)

The delivered tie-back `SymmetryFactor.betaHalf_eq_transfer_thermoneutral` identifies the
equal-curvature thermoneutral coordinate with the BEP transfer coefficient at
thermoneutrality. The channel observes that coefficient on the equal-curvature diagonal. -/

/-- Shared context: the equal-curvature parameter. -/
structure SymFactorBepCtx where
  lam : ℝ

/-- The curvature is physical. -/
def pSymFactorBepLamPositive : Premise SymFactorBepCtx :=
  mkPremise "symmetryFactor.lamPositive" fun δ => 0 < δ.lam

/-- Premise set of the equal-curvature BEP tie-back. -/
def symFactorBepPremises : List (Premise SymFactorBepCtx) := [pSymFactorBepLamPositive]

/-- The two readings compared by the tie-back. -/
def symFactorBepSetup : ObservationalSetup SymFactorBepCtx where
  left := mkRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.tsCoordZero"
    "SymFactorBepCtx" "PhotoLean/SymmetryFactor/Basic.lean#tsCoordZero"
  right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.transfer"
    "SymFactorBepCtx" "PhotoLean/BEP/Basic.lean#transfer"
  leftState := SymFactorBepCtx
  rightState := SymFactorBepCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The thermoneutral transfer-coefficient channel. -/
noncomputable def symFactorBepChannel :
    Channel SymFactorBepCtx symFactorBepSetup ℝ Unit where
  name := "thermoneutralTransferCoefficient"
  domain := Set.univ
  leftObs := fun δ _ => SymmetryFactor.tsCoordZero δ.lam δ.lam
  rightObs := fun δ _ => BEP.transfer δ.lam 0

/-- Observational equivalence: equal-curvature SymmetryFactor coordinate equals the BEP
thermoneutral transfer coefficient. -/
noncomputable def symmetryFactorBepThermoneutralBridge : Certificate SymFactorBepCtx :=
  .observationalEquivalence symFactorBepSetup symFactorBepPremises ℝ Unit
    [symFactorBepChannel]
    (by decide)
    (fun δ hprem c hc _x _hx => by
      have hlam : 0 < δ.lam :=
        hprem pSymFactorBepLamPositive (by simp [symFactorBepPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact SymmetryFactor.betaHalf_eq_transfer_thermoneutral hlam)

/-- Source coherence: the delivered BEP tie-back. -/
theorem symmetryFactorBepThermoneutralBridge_source (δ : SymFactorBepCtx)
    (hlam : 0 < δ.lam) :
    SymmetryFactor.tsCoordZero δ.lam δ.lam = BEP.transfer δ.lam 0 :=
  SymmetryFactor.betaHalf_eq_transfer_thermoneutral hlam

/-- Kind pin: the row is an observational equivalence. -/
theorem symmetryFactorBepThermoneutralBridge_kind :
    certificateKind symmetryFactorBepThermoneutralBridge =
      RelationKind.observationalEquivalence := rfl

/-! ## §4 — BEP / Sabatier (observational equivalence)

The delivered theorem `Sabatier.linearVolcano_eq_bepTangent` states that the literature's
linear volcano is exactly the maximum of the two BEP tangent lines, pointwise in the
descriptor. That is an equality of two real-valued observables over the descriptor axis;
the channel below observes both at every descriptor value. The theorem needs no premise,
so the certificate carries none (the physical positivity of the curvatures belongs to the
chemical reading, not to the load-bearing premise set of this identity). -/

/-- Shared context: the two branch curvatures. -/
structure BepSabatierCtx where
  lam1 : ℝ
  lam2 : ℝ

/-- The two readings compared by the linear-volcano identity. -/
def bepSabatierSetup : ObservationalSetup BepSabatierCtx where
  left := mkRef "PhotoLean.Sabatier" "PhotoLean.Sabatier.volcanoBarrier"
    "BepSabatierCtx" "PhotoLean/Sabatier/Basic.lean#volcanoBarrier"
  right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.bepLine"
    "BepSabatierCtx" "PhotoLean/BEP/Basic.lean#bepLine"
  leftState := BepSabatierCtx
  rightState := BepSabatierCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The descriptor-axis channel: the linear volcano against the maximum of the two tangents. -/
noncomputable def bepSabatierChannel :
    Channel BepSabatierCtx bepSabatierSetup ℝ ℝ where
  name := "descriptorAxisBarrier"
  domain := Set.univ
  leftObs := fun δ dE =>
    Sabatier.volcanoBarrier (1 / 2) (δ.lam1 / 4) (1 / 2) (δ.lam2 / 4) dE
  rightObs := fun δ dE =>
    max (BEP.bepLine δ.lam1 (-dE)) (BEP.bepLine δ.lam2 dE)

/-- Observational equivalence: the linear volcano is the pointwise maximum of the BEP
tangents. -/
noncomputable def bepSabatierLinearVolcanoBridge : Certificate BepSabatierCtx :=
  .observationalEquivalence bepSabatierSetup [] ℝ ℝ [bepSabatierChannel]
    (by decide)
    (fun δ _ c hc dE _hdE => by
      rcases List.mem_singleton.mp hc with rfl
      exact Sabatier.linearVolcano_eq_bepTangent δ.lam1 δ.lam2 dE)

/-- Source coherence: the delivered `§8 linearVolcano_eq_bepTangent` row. -/
theorem bepSabatierLinearVolcanoBridge_source (δ : BepSabatierCtx) (dE : ℝ) :
    Sabatier.volcanoBarrier (1 / 2) (δ.lam1 / 4) (1 / 2) (δ.lam2 / 4) dE =
      max (BEP.bepLine δ.lam1 (-dE)) (BEP.bepLine δ.lam2 dE) :=
  Sabatier.linearVolcano_eq_bepTangent δ.lam1 δ.lam2 dE

/-- Kind pin: the row is an observational equivalence. -/
theorem bepSabatierLinearVolcanoBridge_kind :
    certificateKind bepSabatierLinearVolcanoBridge =
      RelationKind.observationalEquivalence := rfl

end Surface
end BoundedAudit
end RelationAudit
end PhotoLean

/-! ## Verification print-outs for the R2 evidence log -/

#print axioms PhotoLean.RelationAudit.BoundedAudit.Surface.marcusRateSabatierActivityPin
#print axioms PhotoLean.RelationAudit.BoundedAudit.Surface.symmetryFactorHammondThermoneutralBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Surface.symmetryFactorBepThermoneutralBridge
#print axioms PhotoLean.RelationAudit.BoundedAudit.Surface.bepSabatierLinearVolcanoBridge
