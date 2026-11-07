/-
PhotoLean.RelationAudit.Pilot — the pilot certificate set of the relation audit.

This module is additive: it imports the delivered theory modules and `PhotoLean.RelationAudit.Defs`
and changes no delivered statement. Each row re-exports an existing declaration through the
certificate representation, except where the kind-specific proof shape (a separating observation
witness, a decoder, a refutation) has to be assembled from delivered facts.

The seven certified kinds are represented:

* `definitionalIdentity` — the kernel `rfl` pin, `Kernel.barrier` against `Marcus.barrier`;
* `implication` — the one-way Hammond-reaction-region ⇒ Evans–Polanyi-bounds row;
* `equivalence` — the A1 verdict `BetaHalfReading kr kp ↔ kr = kp`, and the Kasha–Marcus row
  reclassified as a conditional equivalence carrying the `hic` premise;
* `conditionalComposition` — a genuine parent-consuming chain: Marcus normal region → Evans–
  Polanyi bounds → the absence of an inverted direction, under the shared positive-curvature
  premise (the Kasha–Marcus row is no longer labelled as a composition);
* `observationalEquivalence` — the Stern–Volmer intensity-only coincidence;
* `distinguishability` — the Stern–Volmer joint intensity–lifetime separator and a decoder form;
* `refutation` — the A2/Kasha–Vavilov counterexample to `KashaRule ⇒ VavilovAt`.

`unresolved` and `notEstablished` are audit statuses, not certificate kinds; they are carried by
`AuditStatus` in `Defs` and by the JSON registry, never by a `Certificate` constructor.

There is no unproved placeholder and no custom axiomatic declaration in this file.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic
import PhotoLean.BEP.Compose
import PhotoLean.Hammond.Basic
import PhotoLean.Kasha.Compose
import PhotoLean.SymmetryFactor.Sharp
import PhotoLean.SternVolmer.Criterion
import PhotoLean.KashaVavilov.Criterion

set_option autoImplicit false

namespace PhotoLean
namespace RelationAudit

/-! ## Shared metadata helpers -/

/-- Artifact version label shared by the pilot rows. The manifest layer owns the content hashes;
this label is the Lean-side snapshot name. -/
def artifactVersion : String := "PhotoLean@0.1.0+lean-toolchain:v4.17.0"

/-- Build a statement reference. -/
def statementRef (theory statementId context provenance : String) : StatementRef where
  theory := theory
  statementId := statementId
  artifactVersion := artifactVersion
  context := context
  provenance := provenance

/-- Build a named premise. -/
def mkPremise {Δ : Type} (id : String) (predicate : Δ → Prop) : Premise Δ :=
  ⟨id, predicate⟩

/-! ## 1. Definitional identity — the kernel `rfl` pin -/

/-- The shared context of a two-parabola step: curvature `lam` and driving force `x`. -/
structure BarrierCtx where
  lam : ℝ
  x : ℝ

/-- Kernel pin: the kernel barrier is *definitionally* the delivered Marcus barrier. The only
`DefEq` constructor is `refl`, so this row fails to compile if the two bodies drift apart. -/
noncomputable def kernelBarrierPin : Certificate BarrierCtx :=
  .definitionalIdentity
    { left := statementRef "PhotoLean.Kernel" "PhotoLean.Kernel.barrier" "BarrierCtx"
        "PhotoLean/Kernel.lean#barrier"
      right := statementRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "BarrierCtx"
        "PhotoLean/Marcus/Basic.lean#barrier"
      leftContext := BarrierCtx
      rightContext := BarrierCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.barrier δ.lam δ.x
      rightTerm := fun δ => Marcus.barrier δ.lam δ.x
      same := DefEq.refl }
    []

/-- Pointwise `rfl` witness of the kernel pin: the two barrier expressions are the same term. -/
theorem kernelBarrierPin_rfl (δ : BarrierCtx) :
    Kernel.barrier δ.lam δ.x = Marcus.barrier δ.lam δ.x := rfl

/-- Function-level `rfl` witness of the kernel pin, in the `DefEq` type carried by the
certificate itself. This is a declaration the manifest can name as the `rflWitness`. -/
theorem kernelBarrierPin_defeq :
    DefEq (fun δ : BarrierCtx => Kernel.barrier δ.lam δ.x)
      (fun δ : BarrierCtx => Marcus.barrier δ.lam δ.x) :=
  DefEq.refl

/-! ## 2. One-way implication — Hammond reaction region ⇒ Evans–Polanyi bounds -/

/-- The premise of the implication: positive curvature. -/
def pBarrierPositive : Premise BarrierCtx :=
  mkPremise "barrier.positiveCurvature" fun δ => 0 < δ.lam

/-- The typed parent link of the Hammond row: reaction region entails the Evans–Polanyi bounds
under positive curvature. -/
noncomputable def hammondEPBoundsLink : ParentCertificate BarrierCtx :=
  .implication "PhotoLean.RelationAudit.epBoundsImplication"
    (Comparison.ofPredicates
      (statementRef "PhotoLean.Hammond" "PhotoLean.Hammond.ReactionRegion" "BarrierCtx"
        "PhotoLean/Hammond/Basic.lean#ReactionRegion")
      (statementRef "PhotoLean.BEP" "PhotoLean.BEP.EPBounds" "BarrierCtx"
        "PhotoLean/BEP/Basic.lean#EPBounds")
      (fun δ => Hammond.ReactionRegion δ.lam δ.x)
      (fun δ => BEP.EPBounds δ.lam δ.x))
    [pBarrierPositive]
    (fun δ hprem hP => BEP.epBounds_of_reactionRegion (hprem pBarrierPositive (by simp)) hP)

/-- One-way entailment: a step inside Hammond's reaction region satisfies the Evans–Polanyi
bounds. The converse is not claimed and is false (the delivered theory has the counterexample
direction as a separate row). -/
noncomputable def epBoundsImplication : Certificate BarrierCtx :=
  .implication hammondEPBoundsLink rfl

/-! ## 3. Equivalence — the A1 verdict -/

/-- The shared context of the A1 comparison: the two force constants. -/
structure CurvatureCtx where
  kr : ℝ
  kp : ℝ

/-- The A1 premise: both force constants are positive. -/
def pCurvaturePositivePair : Premise CurvatureCtx :=
  mkPremise "symmetryFactor.positiveForceConstants" fun δ => 0 < δ.kr ∧ 0 < δ.kp

/-- The typed parent link of the A1 row: the β = 1/2 symmetry-factor reading holds exactly when
the two force constants agree. -/
noncomputable def betaHalfLink : ParentCertificate CurvatureCtx :=
  .equivalence "PhotoLean.RelationAudit.betaHalfEquivalence"
    (Comparison.ofPredicates
      (statementRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.BetaHalfReading"
        "CurvatureCtx" "PhotoLean/SymmetryFactor/Sharp.lean#betaHalf_iff_equalForceConstants")
      (statementRef "PhotoLean.SymmetryFactor" "PhotoLean.SymmetryFactor.equalForceConstants"
        "CurvatureCtx" "PhotoLean/SymmetryFactor/Sharp.lean#betaHalf_iff_equalForceConstants")
      (fun δ => SymmetryFactor.BetaHalfReading δ.kr δ.kp)
      (fun δ => δ.kr = δ.kp))
    [pCurvaturePositivePair]
    (fun δ hprem => by
      have hpos : 0 < δ.kr ∧ 0 < δ.kp :=
        hprem pCurvaturePositivePair (by simp)
      exact SymmetryFactor.betaHalf_iff_equalForceConstants hpos.1 hpos.2)

/-- A1 equivalence: the β = 1/2 symmetry-factor reading holds exactly when the two force
constants agree. -/
noncomputable def betaHalfEquivalence : Certificate CurvatureCtx :=
  .equivalence betaHalfLink rfl

/-! ## 4. Equivalence — Kasha–Marcus with the `hic` bridge

The Kasha–Marcus row is a **conditional equivalence**, not a composition: the delivered theorem
`Kasha.kashaWithin_one_marcus` relates the two predicates directly, with the `hic` identification
as one of its premises. It is therefore registered as an `equivalence` certificate carrying the
full premise set, including `kashaMarcus.icIdentification`; the rate pin below is supporting
definitional evidence, not a composition parent. The genuine composition pilot is section 4b. -/

/-- The shared context of the Kasha–Marcus equivalence: the ladder data and the Marcus
parameters that the internal-conversion rate is identified with. -/
structure KashaMarcusCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ
  tol : ℝ

/-- The premise that the ladder is admissible at excitation level `1`. -/
def pKashaRateData : Premise KashaMarcusCtx :=
  mkPremise "kasha.rateData" fun δ => Kasha.RateData δ.rad δ.ic 1

/-- The tolerance is positive. -/
def pKashaTolPositive : Premise KashaMarcusCtx :=
  mkPremise "kasha.tolerancePositive" fun δ => 0 < δ.tol

/-- The tolerance is below one. -/
def pKashaTolBelowOne : Premise KashaMarcusCtx :=
  mkPremise "kasha.toleranceBelowOne" fun δ => δ.tol < 1

/-- The Marcus pre-exponential factor is positive. -/
def pKashaAPositive : Premise KashaMarcusCtx :=
  mkPremise "kasha.preExponentialPositive" fun δ => 0 < δ.A

/-- The Marcus curvature is positive. -/
def pKashaLamPositive : Premise KashaMarcusCtx :=
  mkPremise "marcus.curvaturePositive" fun δ => 0 < δ.lam

/-- The thermal energy is positive. -/
def pKashaThermalPositive : Premise KashaMarcusCtx :=
  mkPremise "thermal.energyPositive" fun δ => 0 < δ.kB * δ.T

/-- The lowest-state radiative rate is positive. -/
def pKashaRadZeroPositive : Premise KashaMarcusCtx :=
  mkPremise "kasha.radZeroPositive" fun δ => 0 < δ.rad 0

/-- The next-state radiative rate is positive. -/
def pKashaRadOnePositive : Premise KashaMarcusCtx :=
  mkPremise "kasha.radOnePositive" fun δ => 0 < δ.rad 1

/-- **The `hic` bridge premise**: the `S₂ → S₁` internal-conversion rate is the Marcus rate at the
gap `x`. This is a declared modelling premise, not a theorem about nature. -/
def pKashaMarcusIdentification : Premise KashaMarcusCtx :=
  mkPremise "kashaMarcus.icIdentification"
    fun δ => δ.ic 1 = Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x

/-- The full premise set of the Kasha–Marcus row. -/
def kashaMarcusPremises : List (Premise KashaMarcusCtx) :=
  [pKashaRateData, pKashaTolPositive, pKashaTolBelowOne, pKashaAPositive,
    pKashaLamPositive, pKashaThermalPositive, pKashaRadZeroPositive, pKashaRadOnePositive,
    pKashaMarcusIdentification]

/-- The comparison: Kasha conformance against the explicit Marcus window. -/
noncomputable def kashaMarcusComparison : Comparison KashaMarcusCtx :=
  Comparison.ofPredicates
    (statementRef "PhotoLean.Kasha" "PhotoLean.Kasha.KashaWithin" "KashaMarcusCtx"
      "PhotoLean/Kasha/Compose.lean#kashaWithin_one_marcus")
    (statementRef "PhotoLean.Kasha" "PhotoLean.Kasha.MarcusWindow" "KashaMarcusCtx"
      "PhotoLean/Kasha/Compose.lean#kashaWithin_one_marcus")
    (fun δ => Kasha.KashaWithin δ.rad δ.ic δ.tol 1)
    (fun δ =>
      (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) *
        Real.log (Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
          (δ.rad 1) δ.tol))

/-- The delivered Marcus bridge, read through the explicit premise set. -/
theorem kashaMarcusWindow_holds (δ : KashaMarcusCtx)
    (hprem : ∀ p ∈ kashaMarcusPremises, p.predicate δ) :
    Kasha.KashaWithin δ.rad δ.ic δ.tol 1 ↔
      (δ.lam - δ.x) ^ 2 ≤ 4 * δ.lam * (δ.kB * δ.T) *
        Real.log (Kasha.kashaGapThreshold δ.A (δ.rad 0) (Kasha.decay δ.rad δ.ic 0)
          (δ.rad 1) δ.tol) :=
  Kasha.kashaWithin_one_marcus
    (hprem pKashaRateData (by simp [kashaMarcusPremises]))
    (hprem pKashaTolPositive (by simp [kashaMarcusPremises]))
    (hprem pKashaTolBelowOne (by simp [kashaMarcusPremises]))
    (hprem pKashaAPositive (by simp [kashaMarcusPremises]))
    (hprem pKashaLamPositive (by simp [kashaMarcusPremises]))
    (hprem pKashaThermalPositive (by simp [kashaMarcusPremises]))
    (hprem pKashaRadZeroPositive (by simp [kashaMarcusPremises]))
    (hprem pKashaRadOnePositive (by simp [kashaMarcusPremises]))
    (hprem pKashaMarcusIdentification (by simp [kashaMarcusPremises]))

/-- Parent certificate: the Kasha internal-conversion rate is definitionally the Marcus rate at
the gap. This is the mediating definitional bridge of the composition. -/
noncomputable def kashaMarcusRatePin : Certificate KashaMarcusCtx :=
  .definitionalIdentity
    { left := statementRef "PhotoLean.Kasha" "PhotoLean.Kasha.marcusIC" "KashaMarcusCtx"
        "PhotoLean/Kasha/Compose.lean#marcusIC"
      right := statementRef "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "KashaMarcusCtx"
        "PhotoLean/Marcus/Basic.lean#rate"
      leftContext := KashaMarcusCtx
      rightContext := KashaMarcusCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x
      rightTerm := fun δ => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
      same := DefEq.refl }
    []

/-- Pointwise `rfl` witness of the Kasha rate pin. -/
theorem kashaMarcusRatePin_rfl (δ : KashaMarcusCtx) :
    Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x = Marcus.rate δ.A δ.lam δ.kB δ.T δ.x := rfl

/-- Function-level `rfl` witness of the Kasha rate pin. -/
theorem kashaMarcusRatePin_defeq :
    DefEq (fun δ : KashaMarcusCtx => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : KashaMarcusCtx => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x) :=
  DefEq.refl

/-- The typed parent link of the Kasha–Marcus row: the delivered equivalence with its full
premise set, including the `hic` identification. -/
noncomputable def kashaMarcusWindowLink : ParentCertificate KashaMarcusCtx :=
  .equivalence "PhotoLean.RelationAudit.kashaMarcusEquivalence" kashaMarcusComparison
    kashaMarcusPremises (fun δ hprem => kashaMarcusWindow_holds δ hprem)

/-- **Kasha–Marcus as a conditional equivalence** carrying the `hic` premise. This replaces the
former composition label: the delivered theorem proves the equivalence directly, so a
composition representation would misdescribe it. -/
noncomputable def kashaMarcusEquivalence : Certificate KashaMarcusCtx :=
  .equivalence kashaMarcusWindowLink rfl

/-! ## 4b. Genuine conditional composition — Marcus normal direction through EPBounds

Two existing facts are chained, with the middle proposition aligned definitionally:

* parent 1 (implication): `Marcus.NormalRegion lam x → BEP.EPBounds lam x` under positive
  curvature and the reverse-direction premise `-lam ≤ x` (`BEP.epBounds_of_marcus_normal`);
* parent 2 (equivalence): `BEP.EPBounds lam x ↔ ¬(Inverted lam x ∨ Inverted lam (-x))` under
  positive curvature (`BEP.epBounds_iff_no_inverted_direction`);
* child: `Marcus.NormalRegion lam x → ¬(Inverted lam x ∨ Inverted lam (-x))` under the union of
  the two premise sets.

The child comparison and conclusion are computed by `ConditionalComposition`, not supplied by an
independent proof. The bridge list is empty because the middle predicates are the same
proposition after translation. -/

/-- The reverse direction of the step is not inverted: the extra premise of
`BEP.epBounds_of_marcus_normal`. -/
def pMarcusReverseNotInverted : Premise BarrierCtx :=
  mkPremise "marcus.reverseNotInverted" fun δ => -δ.lam ≤ δ.x

/-- The premise set of the Marcus-normal parent. -/
def marcusNormalPremises : List (Premise BarrierCtx) :=
  [pBarrierPositive, pMarcusReverseNotInverted]

/-- The premise set of the EPBounds/no-inverted-direction parent. -/
def epBoundsNoInvertedPremises : List (Premise BarrierCtx) :=
  [pBarrierPositive]

/-- Parent 1 comparison: Marcus normal region against the Evans–Polanyi bounds. -/
noncomputable def marcusNormalToEPBoundsCmp : Comparison BarrierCtx :=
  Comparison.ofPredicates
    (statementRef "PhotoLean.Marcus" "PhotoLean.Marcus.NormalRegion" "BarrierCtx"
      "PhotoLean/Marcus/Basic.lean#NormalRegion")
    (statementRef "PhotoLean.BEP" "PhotoLean.BEP.EPBounds" "BarrierCtx"
      "PhotoLean/BEP/Basic.lean#EPBounds")
    (fun δ => Marcus.NormalRegion δ.lam δ.x)
    (fun δ => BEP.EPBounds δ.lam δ.x)

/-- Parent 2 comparison: the Evans–Polanyi bounds against the absence of an inverted direction. -/
noncomputable def epBoundsNoInvertedCmp : Comparison BarrierCtx :=
  Comparison.ofPredicates
    (statementRef "PhotoLean.BEP" "PhotoLean.BEP.EPBounds" "BarrierCtx"
      "PhotoLean/BEP/Basic.lean#EPBounds")
    (statementRef "PhotoLean.BEP" "PhotoLean.BEP.noInvertedDirection" "BarrierCtx"
      "PhotoLean/BEP/Compose.lean#epBounds_iff_no_inverted_direction")
    (fun δ => BEP.EPBounds δ.lam δ.x)
    (fun δ => ¬ (Marcus.InvertedRegion δ.lam δ.x ∨ Marcus.InvertedRegion δ.lam (-δ.x)))

/-- Typed parent 1: the delivered Marcus-normal bridge `epBounds_of_marcus_normal`. -/
noncomputable def marcusNormalToEPBoundsLink : ParentCertificate BarrierCtx :=
  .implication "PhotoLean.RelationAudit.marcusNormalImplication" marcusNormalToEPBoundsCmp
    marcusNormalPremises
    (fun δ hprem hN =>
      BEP.epBounds_of_marcus_normal
        (hprem pBarrierPositive (by simp [marcusNormalPremises]))
        hN
        (hprem pMarcusReverseNotInverted (by simp [marcusNormalPremises])))

/-- Typed parent 2: the delivered equivalence `epBounds_iff_no_inverted_direction`. -/
noncomputable def epBoundsNoInvertedLink : ParentCertificate BarrierCtx :=
  .equivalence "PhotoLean.RelationAudit.epBoundsNoInvertedEquivalence" epBoundsNoInvertedCmp
    epBoundsNoInvertedPremises
    (fun δ hprem =>
      BEP.epBounds_iff_no_inverted_direction
        (hprem pBarrierPositive (by simp [epBoundsNoInvertedPremises])))

/-- The implication certificate for parent 1, exposed for the manifest. -/
noncomputable def marcusNormalImplication : Certificate BarrierCtx :=
  .implication marcusNormalToEPBoundsLink rfl

/-- The equivalence certificate for parent 2, exposed for the manifest. -/
noncomputable def epBoundsNoInvertedEquivalence : Certificate BarrierCtx :=
  .equivalence epBoundsNoInvertedLink rfl

/-- **The proof-relevant composition derivation.** The child premises are the union of the two
parent premise sets; every parent premise is inherited (the bridge list is empty because the
middle predicate is the same proposition). `ConditionalComposition.sound` derives the child
conclusion from the two parent entailments and the alignment. -/
noncomputable def marcusNormalNoInvertedDerivation : ConditionalComposition BarrierCtx where
  left := marcusNormalToEPBoundsLink
  right := epBoundsNoInvertedLink
  premises := marcusNormalPremises
  bridge := []
  alignment := ⟨fun _ => Iff.rfl⟩
  parentCoverage := by
    refine ⟨fun p hp => PremiseDerivation.inherited ?_⟩
    change p ∈ marcusNormalPremises ++ epBoundsNoInvertedPremises at hp
    simp only [marcusNormalPremises, epBoundsNoInvertedPremises, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false] at hp ⊢
    tauto
  bridgeCoverage := by simp
  discharges := []

/-- **The genuine conditional-composition certificate.** The child conclusion is computed; there
is no independent child-proof field to fill. -/
noncomputable def marcusNormalNoInvertedComposition : Certificate BarrierCtx :=
  .conditionalComposition marcusNormalNoInvertedDerivation

/-- **Self-test of the computed child conclusion**: the implication obtained by composing the two
parents, without any independently supplied proof of the result. -/
theorem marcusNormal_noInverted (δ : BarrierCtx)
    (hprem : ∀ p ∈ marcusNormalPremises, p.predicate δ)
    (hN : Marcus.NormalRegion δ.lam δ.x) :
    ¬ (Marcus.InvertedRegion δ.lam δ.x ∨ Marcus.InvertedRegion δ.lam (-δ.x)) :=
  (marcusNormalNoInvertedDerivation.sound δ hprem) hN

/-- Metadata pin: the composition names its two typed parents. -/
theorem marcusNormalNoInvertedComposition_parentIDs :
    certificateParentIDs marcusNormalNoInvertedComposition =
      ["PhotoLean.RelationAudit.marcusNormalImplication",
       "PhotoLean.RelationAudit.epBoundsNoInvertedEquivalence"] := rfl

/-- Metadata pin: the parent kinds are implication and equivalence. -/
theorem marcusNormalNoInvertedComposition_parentKinds :
    certificateParentKinds marcusNormalNoInvertedComposition =
      [RelationKind.implication, RelationKind.equivalence] := rfl

/-- Metadata pin: the child premise IDs. -/
theorem marcusNormalNoInvertedComposition_premiseIDs :
    certificatePremiseIDs marcusNormalNoInvertedComposition =
      ["barrier.positiveCurvature", "marcus.reverseNotInverted"] := rfl

/-- Metadata pin: the propagated parent premise IDs. -/
theorem marcusNormalNoInvertedComposition_parentPremiseIDs :
    certificateParentPremiseIDs marcusNormalNoInvertedComposition =
      [["barrier.positiveCurvature", "marcus.reverseNotInverted"],
       ["barrier.positiveCurvature"]] := rfl

/-- Metadata pin: the bridge list is empty (the middle predicates align definitionally). -/
theorem marcusNormalNoInvertedComposition_bridgeIDs :
    certificateBridgeIDs marcusNormalNoInvertedComposition = [] := rfl

/-- Metadata pin: no parent premise is discharged. -/
theorem marcusNormalNoInvertedComposition_dischargeIDs :
    certificateDischargeIDs marcusNormalNoInvertedComposition = [] := rfl

/-- Metadata pin: the mediating endpoint is the Evans–Polanyi-bounds statement. -/
theorem marcusNormalNoInvertedComposition_mediating :
    certificateMediating? marcusNormalNoInvertedComposition =
      some (statementRef "PhotoLean.BEP" "PhotoLean.BEP.EPBounds" "BarrierCtx"
        "PhotoLean/BEP/Basic.lean#EPBounds") := rfl

/-- Metadata pin: the computed child form is an implication. -/
theorem marcusNormalNoInvertedComposition_form :
    certificateCompositionForm? marcusNormalNoInvertedComposition =
      some CompositionForm.implication := rfl

/-! ## 5. Observational equivalence — Stern–Volmer intensity only -/

/-- The shared context of the intensity-only Stern–Volmer comparison. -/
structure SVIntensityCtx where
  k0 : ℝ
  kq : ℝ
  Ka : ℝ

/-- The intrinsic decay rate is nonzero. -/
def pSvK0Nonzero : Premise SVIntensityCtx :=
  mkPremise "sternVolmer.k0Nonzero" fun δ => δ.k0 ≠ 0

/-- The parameters are matched: the dynamic Stern–Volmer constant equals the static association
constant. This is the premise under which the intensity channels coincide. -/
def pSvMatched : Premise SVIntensityCtx :=
  mkPremise "sternVolmer.matchedKSV" fun δ => SternVolmer.KSV δ.k0 δ.kq = δ.Ka

/-- The premise set of the intensity-only equivalence. -/
def svIntensityPremises : List (Premise SVIntensityCtx) := [pSvK0Nonzero, pSvMatched]

/-- The two-mechanism interpretation of the intensity comparison. -/
def svIntensitySetup : ObservationalSetup SVIntensityCtx where
  left := statementRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.svRatioDyn"
    "SVIntensityCtx" "PhotoLean/SternVolmer/Basic.lean#svRatioDyn"
  right := statementRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.svRatioStat"
    "SVIntensityCtx" "PhotoLean/SternVolmer/Basic.lean#svRatioStat"
  leftState := SVIntensityCtx
  rightState := SVIntensityCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The intensity channel, declared on the positive concentrations. -/
noncomputable def svIntensityChannel : Channel SVIntensityCtx svIntensitySetup ℝ ℝ where
  name := "intensity"
  domain := {q | 0 < q}
  leftObs := fun δ q => SternVolmer.svRatioDyn δ.k0 δ.kq q
  rightObs := fun δ q => SternVolmer.svRatioStat δ.Ka q

/-- Intensity-only observational equivalence: under matched parameters the two mechanisms have
the same intensity ratio at every positive concentration. This is *not* a lifetime claim. -/
noncomputable def svIntensityObservationalEquivalence : Certificate SVIntensityCtx :=
  .observationalEquivalence svIntensitySetup svIntensityPremises ℝ ℝ [svIntensityChannel]
    (by decide)
    (fun δ hprem c hc x _hx => by
      have hk0 : δ.k0 ≠ 0 := hprem pSvK0Nonzero (by simp [svIntensityPremises])
      have hK : SternVolmer.KSV δ.k0 δ.kq = δ.Ka :=
        hprem pSvMatched (by simp [svIntensityPremises])
      have h := SternVolmer.intensity_curve_coincidence hk0 hK x
      rcases List.mem_singleton.mp hc with rfl
      simpa [svIntensityChannel] using h)

/-! ## 6. Distinguishability — the Stern–Volmer joint channel -/

/-- The joint intensity–lifetime channel: the observed value is the pair of the two channels. -/
noncomputable def svJointChannel : Channel SVIntensityCtx svIntensitySetup (ℝ × ℝ) ℝ where
  name := "jointIntensityLifetime"
  domain := {q | 0 < q}
  leftObs := fun δ q =>
    (SternVolmer.svRatioOf .dyn δ.k0 δ.kq δ.Ka q,
      SternVolmer.tauRatioOf .dyn δ.k0 δ.kq δ.Ka q)
  rightObs := fun δ q =>
    (SternVolmer.svRatioOf .stat δ.k0 δ.kq δ.Ka q,
      SternVolmer.tauRatioOf .stat δ.k0 δ.kq δ.Ka q)

/-- The witness parameters: `k0 = 2`, `kq = 2`, `Ka = 1`, so the Stern–Volmer constant is `1`
and the intensity channels coincide at every concentration. -/
def svJointWitness : SVIntensityCtx where
  k0 := 2
  kq := 2
  Ka := 1

/-- The witness satisfies the stated premises. -/
theorem svJointWitness_premises :
    ∀ p ∈ svIntensityPremises, p.predicate svJointWitness := by
  intro p hp
  simp [svIntensityPremises] at hp
  rcases hp with rfl | rfl
  · norm_num [pSvK0Nonzero, mkPremise, svJointWitness]
  · norm_num [pSvMatched, mkPremise, svJointWitness, SternVolmer.KSV]

/-- At `q = 1` the intensity components of the joint channel agree: the separation proved below
is therefore *not* an intensity-only separation. -/
theorem svJointChannel_intensity_agrees :
    (svJointChannel.leftObs (svIntensitySetup.leftInterp svJointWitness) (1 : ℝ)).1 =
      (svJointChannel.rightObs (svIntensitySetup.rightInterp svJointWitness) (1 : ℝ)).1 := by
  simp only [svJointChannel, svIntensitySetup, svJointWitness, SternVolmer.svRatioOf,
    SternVolmer.svRatioDyn, SternVolmer.svRatioStat, SternVolmer.dynDecay]
  norm_num

/-- At `q = 1` the joint channels separate the two mechanisms: both intensity components agree,
while the lifetime components are `2` and `1`. So the intensity-only equivalence above is
genuinely weaker than the joint-channel discriminator. -/
theorem svJointChannel_separates :
    svJointChannel.leftObs (svIntensitySetup.leftInterp svJointWitness) (1 : ℝ) ≠
      svJointChannel.rightObs (svIntensitySetup.rightInterp svJointWitness) (1 : ℝ) := by
  intro h
  have h2 : (2 : ℝ) = 1 := by
    have h' := congrArg Prod.snd h
    simp [svJointChannel, svIntensitySetup, svJointWitness, SternVolmer.tauRatioOf,
      SternVolmer.tauRatioDyn, SternVolmer.tauRatioStat, SternVolmer.dynDecay] at h'
  norm_num at h2

/-- The named separating-observation witness (the manifest's `semantics.witness`). -/
noncomputable def svJointSeparationWitness : DistinguishabilityWitness SVIntensityCtx :=
  .separatingObservation svIntensitySetup (ℝ × ℝ) ℝ svJointChannel svIntensityPremises
    svJointWitness svJointWitness_premises (1 : ℝ) (by simp [svJointChannel])
    svJointChannel_separates

/-- **Separating-observation form** of joint-channel distinguishability. -/
noncomputable def svJointDistinguishability : Certificate SVIntensityCtx :=
  .distinguishability svJointSeparationWitness

/-- The shared context of the decoder form: the mechanism tag plus the parameters and the
concentration at which the joint observation is taken. -/
structure SVDecoderCtx where
  k0 : ℝ
  kq : ℝ
  Ka : ℝ
  q : ℝ
  m : SternVolmer.Mech

/-- The intrinsic decay rate is positive. -/
def pSvDecoderK0Positive : Premise SVDecoderCtx :=
  mkPremise "sternVolmer.decoderK0Positive" fun δ => 0 < δ.k0

/-- The dynamic quenching constant is nonzero: this is what makes the dynamic lifetime ratio
leave `1`. -/
def pSvDecoderKqNonzero : Premise SVDecoderCtx :=
  mkPremise "sternVolmer.decoderKqNonzero" fun δ => δ.kq ≠ 0

/-- The concentration is positive. -/
def pSvDecoderQPositive : Premise SVDecoderCtx :=
  mkPremise "sternVolmer.decoderQPositive" fun δ => 0 < δ.q

/-- The premise set of the decoder. -/
def svDecoderPremises : List (Premise SVDecoderCtx) :=
  [pSvDecoderK0Positive, pSvDecoderKqNonzero, pSvDecoderQPositive]

/-- The decoder's interpretation. -/
def svDecoderSetup : ObservationalSetup SVDecoderCtx where
  left := statementRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.mechanismDynamic"
    "SVDecoderCtx" "PhotoLean/SternVolmer/Basic.lean#Mech"
  right := statementRef "PhotoLean.SternVolmer" "PhotoLean.SternVolmer.mechanismStatic"
    "SVDecoderCtx" "PhotoLean/SternVolmer/Basic.lean#Mech"
  leftState := SVDecoderCtx
  rightState := SVDecoderCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The joint observation map used by the decoder. -/
noncomputable def svDecoderObserve (δ : SVDecoderCtx) : ℝ × ℝ :=
  (SternVolmer.svRatioOf δ.m δ.k0 δ.kq δ.Ka δ.q,
    SternVolmer.tauRatioOf δ.m δ.k0 δ.kq δ.Ka δ.q)

/-- The decoder: a lifetime ratio equal to `1` is the static branch, anything else the dynamic
branch. -/
noncomputable def svDecoder (obs : ℝ × ℝ) : SternVolmer.Mech :=
  if obs.2 = 1 then .stat else .dyn

/-- The dynamic lifetime ratio is not `1` under the decoder premises. -/
theorem svDecoder_dynamic_tau_ne_one (δ : SVDecoderCtx)
    (hprem : ∀ p ∈ svDecoderPremises, p.predicate δ) :
    SternVolmer.tauRatioOf .dyn δ.k0 δ.kq δ.Ka δ.q ≠ 1 := by
  have hk0 : 0 < δ.k0 := hprem pSvDecoderK0Positive (by simp [svDecoderPremises])
  have hkq : δ.kq ≠ 0 := hprem pSvDecoderKqNonzero (by simp [svDecoderPremises])
  have hq : 0 < δ.q := hprem pSvDecoderQPositive (by simp [svDecoderPremises])
  intro h
  have hk0ne : δ.k0 ≠ 0 := ne_of_gt hk0
  have hsum : δ.k0 + δ.kq * δ.q = δ.k0 := by
    have h' := h
    simp only [SternVolmer.tauRatioOf, SternVolmer.tauRatioDyn, SternVolmer.dynDecay] at h'
    field_simp [hk0ne] at h'
  have hzero : δ.kq * δ.q = 0 := by linarith
  exact mul_ne_zero hkq (ne_of_gt hq) hzero

/-- The decoder recovers the mechanism tag from the joint observation. -/
theorem svDecoder_correct (δ : SVDecoderCtx)
    (hprem : ∀ p ∈ svDecoderPremises, p.predicate δ) :
    svDecoder (svDecoderObserve δ) = δ.m := by
  cases hm : δ.m with
  | dyn =>
    have hne : SternVolmer.tauRatioOf .dyn δ.k0 δ.kq δ.Ka δ.q ≠ 1 :=
      svDecoder_dynamic_tau_ne_one δ hprem
    simp [svDecoder, svDecoderObserve, hm, hne]
  | stat =>
    simp [svDecoder, svDecoderObserve, hm, SternVolmer.tauRatioOf,
      SternVolmer.tauRatioStat]

/-- The named identifiability/decoder witness (the manifest's `semantics.witness`). -/
noncomputable def svJointDecoderWitness : DistinguishabilityWitness SVDecoderCtx :=
  .identifiabilityDecoder svDecoderSetup svDecoderPremises (ℝ × ℝ) SternVolmer.Mech
    svDecoderObserve (fun δ => δ.m) svDecoder svDecoder_correct

/-- **Identifiability/decoder form** of joint-channel distinguishability: the decoder is a left
inverse of the joint observation on the declared model space. -/
noncomputable def svJointIdentifiability : Certificate SVDecoderCtx :=
  .distinguishability svJointDecoderWitness

/-! ## 7. Refutation — the A2 / Kasha–Vavilov counterexample -/

/-- The shared context of the Kasha–Vavilov refutation. -/
structure KVCtx where
  rad : ℕ → ℝ
  ic : ℕ → ℝ

/-- The ladder is admissible at excitation level `2`. -/
def pKvRateData : Premise KVCtx :=
  mkPremise "kashaVavilov.rateData" fun δ => Kasha.RateData δ.rad δ.ic 2

/-- The lowest internal-conversion rate is positive (the lossy regime, not the degenerate
lossless corner). -/
def pKvIcZeroPositive : Premise KVCtx :=
  mkPremise "kashaVavilov.icZeroPositive" fun δ => 0 < δ.ic 0

/-- The premise set of the refutation. -/
def kvPremises : List (Premise KVCtx) := [pKvRateData, pKvIcZeroPositive]

/-- The comparison: Kasha's rule against Vavilov's rule at level `1`. -/
noncomputable def kvComparison : Comparison KVCtx :=
  Comparison.ofPredicates
    (statementRef "PhotoLean.Kasha" "PhotoLean.Kasha.KashaRule" "KVCtx"
      "PhotoLean/Kasha/Basic.lean#KashaRule")
    (statementRef "PhotoLean.Kasha" "PhotoLean.Kasha.VavilovAt" "KVCtx"
      "PhotoLean/Kasha/Basic.lean#VavilovAt")
    (fun δ => Kasha.KashaRule δ.rad δ.ic 1)
    (fun δ => Kasha.VavilovAt δ.rad δ.ic 1)

/-- The delivered A2 witness refutes `KashaRule ⇒ VavilovAt`: a positive-excitation lossy ladder
satisfying Kasha's rule and violating Vavilov's rule. -/
theorem kvRefutationCounterexample :
    ∃ δ : KVCtx,
      (∀ p ∈ kvPremises, p.predicate δ) ∧
        Kasha.KashaRule δ.rad δ.ic 1 ∧ ¬ Kasha.VavilovAt δ.rad δ.ic 1 := by
  obtain ⟨rad, ic, hR, hK, hV, hic⟩ := KashaVavilov.kashaRule_not_implies_vavilovAt
  refine ⟨⟨rad, ic⟩, ?_, hK, hV⟩
  intro p hp
  simp [kvPremises] at hp
  rcases hp with rfl | rfl
  · simpa [pKvRateData] using hR
  · simpa [pKvIcZeroPositive] using hic

/-- **Admissible refutation certificate**: an explicit counterexample satisfying the premises,
the antecedent and the negation of the consequent. -/
noncomputable def kvRefutation : Certificate KVCtx :=
  .refutation kvComparison kvPremises kvRefutationCounterexample

/-! ## 8. Kind pins -/

/-- Kind pin: the kernel `rfl` row is a definitional identity. -/
theorem kernelBarrierPin_kind :
    certificateKind kernelBarrierPin = RelationKind.definitionalIdentity := rfl

/-- Kind pin: the Hammond ⇒ Evans–Polanyi row is an implication. -/
theorem epBoundsImplication_kind :
    certificateKind epBoundsImplication = RelationKind.implication := rfl

/-- Kind pin: the A1 row is an equivalence. -/
theorem betaHalfEquivalence_kind :
    certificateKind betaHalfEquivalence = RelationKind.equivalence := rfl

/-- Kind pin: the Kasha–Marcus row is a conditional **equivalence** carrying the `hic` premise. -/
theorem kashaMarcusEquivalence_kind :
    certificateKind kashaMarcusEquivalence = RelationKind.equivalence := rfl

/-- Supporting-evidence pin: the `hic` identification is in the Kasha–Marcus premise set. -/
theorem kashaMarcusEquivalence_has_hic :
    "kashaMarcus.icIdentification" ∈ certificatePremiseIDs kashaMarcusEquivalence := by
  show "kashaMarcus.icIdentification" ∈ premiseIDs kashaMarcusPremises
  decide

/-- Kind pin: the definitional rate pin remains a definitional identity supporting the Kasha row. -/
theorem kashaMarcusRatePin_kind :
    certificateKind kashaMarcusRatePin = RelationKind.definitionalIdentity := rfl

/-- Kind pin: parent 1 of the genuine composition is an implication. -/
theorem marcusNormalImplication_kind :
    certificateKind marcusNormalImplication = RelationKind.implication := rfl

/-- Kind pin: parent 2 of the genuine composition is an equivalence. -/
theorem epBoundsNoInvertedEquivalence_kind :
    certificateKind epBoundsNoInvertedEquivalence = RelationKind.equivalence := rfl

/-- Kind pin: the Marcus-normal chain is a conditional composition. -/
theorem marcusNormalNoInvertedComposition_kind :
    certificateKind marcusNormalNoInvertedComposition =
      RelationKind.conditionalComposition := rfl

/-- Kind pin: the Stern–Volmer intensity row is an observational equivalence. -/
theorem svIntensityObservationalEquivalence_kind :
    certificateKind svIntensityObservationalEquivalence =
      RelationKind.observationalEquivalence := rfl

/-- Kind pin: the Stern–Volmer joint row is a distinguishability certificate. -/
theorem svJointDistinguishability_kind :
    certificateKind svJointDistinguishability = RelationKind.distinguishability := rfl

/-- Kind pin: the decoder row is also a distinguishability certificate (its form is inspected
separately by `DistinguishabilityWitness.formTag`). -/
theorem svJointIdentifiability_kind :
    certificateKind svJointIdentifiability = RelationKind.distinguishability := rfl

/-- Kind pin: the Kasha–Vavilov row is a refutation. -/
theorem kvRefutation_kind :
    certificateKind kvRefutation = RelationKind.refutation := rfl

/-- The pilot rows in one list, for manifest-side enumeration. -/
def pilotCertificates : List (String × AuditStatus) :=
  [ ("PhotoLean.RelationAudit.kernelBarrierPin", .certified),
    ("PhotoLean.RelationAudit.epBoundsImplication", .certified),
    ("PhotoLean.RelationAudit.betaHalfEquivalence", .certified),
    ("PhotoLean.RelationAudit.kashaMarcusEquivalence", .certified),
    ("PhotoLean.RelationAudit.kashaMarcusRatePin", .certified),
    ("PhotoLean.RelationAudit.marcusNormalNoInvertedComposition", .certified),
    ("PhotoLean.RelationAudit.svIntensityObservationalEquivalence", .certified),
    ("PhotoLean.RelationAudit.svJointDistinguishability", .certified),
    ("PhotoLean.RelationAudit.svJointIdentifiability", .certified),
    ("PhotoLean.RelationAudit.kvRefutation", .certified) ]

end RelationAudit
end PhotoLean
