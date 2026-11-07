/-
PhotoLean.RelationAudit.Full.Sections01_05 — R3 migration certificates for `PhotoLean/Relations.lean`
sections 1 through 5.

This module is additive: it changes no delivered theory module, no `PhotoLean/Relations.lean`
declaration, no R1 artifact and no other section worker's file. It processes exactly the sixteen
R2 `certificate-required` declarations of sections 1–5 and re-expresses each one through the
typed certificate vocabulary of `PhotoLean.RelationAudit.Defs`.

The section pattern is:

* **§1 and §5 (definitional pins).** The source theorems are `rfl`-level equalities between a
  shared-kernel definition and the corresponding theory definition (or between two theory
  definitions with literally identical bodies). Each row is certified as a
  `definitionalIdentity` whose `DefEq` field is inhabited by `DefEq.refl`. The certificate
  therefore re-checks definitional equality in the kernel; it never treats a merely propositional
  equality as definitional. A separate `_source` theorem restates the original delivered theorem
  so the migration is tied to the source declaration, and a `_defeq` witness exposes the fresh
  `rfl` check to the manifest layer.
* **§2 (`↔` rows).** `tsCoord_lt_zero_iff_inverted`, `lefflerSecant_neg_iff_inverted` and
  `hammondZoneQ_beyondReactant_iff_inverted` are genuine non-definitional equivalences with
  explicit premises; they are certified as `equivalence`.
* **§2 (value-level bridge rows).** `transfer_eq_tsCoord_bridge` and
  `secSlope_eq_lefflerSecant` are *non-definitional equalities of real-valued observables*, not
  propositional `↔` statements and not `rfl` identities. They are certified as
  `observationalEquivalence` over an explicit observation channel (the shared input is the driving
  force / the driving-force window). This records exactly the delivered theorem — "the two
  observables agree on every input" — without relabelling it as a propositional equivalence or as
  a definitional identity.
* **§3 (one-way row).** `hammondDescriptor_of_epConformsOnWindow` is a genuine one-way
  entailment; it is certified as `implication`. The disposition notes that the delivered proof
  consumes only the positivity conjunct of `BEP.EPConformsOnWindow`; the certificate keeps the
  full antecedent as the displayed statement and does not claim the converse.

No row here is composed from parents, so no `conditionalComposition` certificate is created in
this fragment. A composition certificate is not manufactured here; any composition claim must
come from the pilot or from another section module that consumes typed parents. No transitive,
one-sided-registration, look-alike, support or intra-theory row is promoted to a direct relation:
those rows are outside the `certificate-required` queue of sections 1–5 (they are §4 support
lemmas and one §5 intra-theory bridge), and this file does not touch them.

There is no unproved placeholder and no custom axiomatic declaration in this file.
-/
import PhotoLean.Relations
import PhotoLean.RelationAudit.Defs

set_option autoImplicit false

namespace PhotoLean
namespace RelationAudit
namespace Full
namespace Sections01_05

/-! ## Shared metadata helpers -/

/-- Artifact version label shared by this section. The manifest layer owns the content hashes;
this label is the Lean-side snapshot name, matching the R1 pilot label. -/
def artifactVersion : String := "PhotoLean@0.1.0+lean-toolchain:v4.17.0"

/-- Build a statement reference. -/
def mkRef (theory statementId context provenance : String) : StatementRef where
  theory := theory
  statementId := statementId
  artifactVersion := artifactVersion
  context := context
  provenance := provenance

/-- Build a named premise. -/
def mkPremise {Δ : Type} (id : String) (predicate : Δ → Prop) : Premise Δ :=
  ⟨id, predicate⟩

/-! ## Shared contexts -/

/-- The equal-curvature two-parabola context: curvature `lam` and driving force `x`. -/
structure TwoParabolaCtx where
  lam : ℝ
  x : ℝ

/-- The reactant-surface context: curvature `lam` and reaction coordinate `q`. -/
structure SurfaceCtx where
  lam : ℝ
  q : ℝ

/-- The product-surface context: curvature `lam`, reaction free energy `dG`, coordinate `q`. -/
structure ProductSurfaceCtx where
  lam : ℝ
  dG : ℝ
  q : ℝ

/-- The Marcus-rate context: pre-exponential factor, curvature, thermal energy and driving force. -/
structure RateCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- The BEP-transfer observation context: only the curvature is fixed; the driving force is the
channel input. -/
structure TransferCtx where
  lam : ℝ

/-- The BEP-secant observation context: only the curvature is fixed; the driving-force window is
the channel input. -/
structure SlopeCtx where
  lam : ℝ

/-- The Hammond secant context: curvature and two distinct driving forces. -/
structure SecantCtx where
  lam : ℝ
  x1 : ℝ
  x2 : ℝ

/-- The rational-side classifier context: rational curvature and rational driving force. -/
structure RatCtx where
  lam : ℚ
  x : ℚ

/-- The BEP window-conformance context: curvature, tolerance and window endpoints. -/
structure WindowCtx where
  lam : ℝ
  tol : ℝ
  a : ℝ
  b : ℝ

/-! ## §1 — kernel definitional pins

Each pin compares the shared-kernel definition with the corresponding delivered theory definition.
The `same` field uses `DefEq.refl`, so the certificate itself fails if the two bodies stop being
definitionally equal. The `_source` theorem restates the original `PhotoLean/Relations.lean` row. -/

/-- Definitional pin: the kernel barrier and the Hammond forward gap are the same term. -/
noncomputable def kernelBarrierHammondPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.barrier" "TwoParabolaCtx"
        "PhotoLean/Kernel.lean#barrier"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.gapReactant" "TwoParabolaCtx"
        "PhotoLean/Hammond/Basic.lean#gapReactant"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.barrier δ.lam δ.x
      rightTerm := fun δ => Hammond.gapReactant δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/Hammond-barrier pin. -/
theorem kernelBarrierHammondPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Kernel.barrier δ.lam δ.x)
      (fun δ : TwoParabolaCtx => Hammond.gapReactant δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_barrier_eq_hammond` row. -/
theorem kernelBarrierHammondPin_source (δ : TwoParabolaCtx) :
    Kernel.barrier δ.lam δ.x = Hammond.gapReactant δ.lam δ.x :=
  PhotoLean.Relations.kernel_barrier_eq_hammond δ.lam δ.x

/-- Definitional pin: the kernel barrier and the BEP activation barrier are the same term. -/
noncomputable def kernelBarrierBepPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.barrier" "TwoParabolaCtx"
        "PhotoLean/Kernel.lean#barrier"
      right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.eact" "TwoParabolaCtx"
        "PhotoLean/BEP/Basic.lean#eact"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.barrier δ.lam δ.x
      rightTerm := fun δ => BEP.eact δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/BEP-barrier pin. -/
theorem kernelBarrierBepPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Kernel.barrier δ.lam δ.x)
      (fun δ : TwoParabolaCtx => BEP.eact δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_barrier_eq_bep` row. -/
theorem kernelBarrierBepPin_source (δ : TwoParabolaCtx) :
    Kernel.barrier δ.lam δ.x = BEP.eact δ.lam δ.x :=
  PhotoLean.Relations.kernel_barrier_eq_bep δ.lam δ.x

/-- Definitional pin: the kernel reverse barrier and the Hammond reverse gap are the same term. -/
noncomputable def kernelReverseBarrierHammondPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.reverseBarrier" "TwoParabolaCtx"
        "PhotoLean/Kernel.lean#reverseBarrier"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.gapProduct" "TwoParabolaCtx"
        "PhotoLean/Hammond/Basic.lean#gapProduct"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.reverseBarrier δ.lam δ.x
      rightTerm := fun δ => Hammond.gapProduct δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/Hammond-reverse-barrier pin. -/
theorem kernelReverseBarrierHammondPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Kernel.reverseBarrier δ.lam δ.x)
      (fun δ : TwoParabolaCtx => Hammond.gapProduct δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_reverseBarrier_eq_hammond` row. -/
theorem kernelReverseBarrierHammondPin_source (δ : TwoParabolaCtx) :
    Kernel.reverseBarrier δ.lam δ.x = Hammond.gapProduct δ.lam δ.x :=
  PhotoLean.Relations.kernel_reverseBarrier_eq_hammond δ.lam δ.x

/-- Definitional pin: the kernel transition-state coordinate and the Hammond coordinate are the
same term. -/
noncomputable def kernelTsCoordHammondPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.tsCoord" "TwoParabolaCtx"
        "PhotoLean/Kernel.lean#tsCoord"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord" "TwoParabolaCtx"
        "PhotoLean/Hammond/Basic.lean#tsCoord"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.tsCoord δ.lam δ.x
      rightTerm := fun δ => Hammond.tsCoord δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/Hammond-coordinate pin. -/
theorem kernelTsCoordHammondPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Kernel.tsCoord δ.lam δ.x)
      (fun δ : TwoParabolaCtx => Hammond.tsCoord δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_tsCoord_eq_hammond` row. -/
theorem kernelTsCoordHammondPin_source (δ : TwoParabolaCtx) :
    Kernel.tsCoord δ.lam δ.x = Hammond.tsCoord δ.lam δ.x :=
  PhotoLean.Relations.kernel_tsCoord_eq_hammond δ.lam δ.x

/-- Definitional pin: the kernel transfer coefficient and the BEP coefficient are the same term. -/
noncomputable def kernelTransferBepPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.transfer" "TwoParabolaCtx"
        "PhotoLean/Kernel.lean#transfer"
      right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.transfer" "TwoParabolaCtx"
        "PhotoLean/BEP/Basic.lean#transfer"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.transfer δ.lam δ.x
      rightTerm := fun δ => BEP.transfer δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/BEP-transfer pin. -/
theorem kernelTransferBepPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Kernel.transfer δ.lam δ.x)
      (fun δ : TwoParabolaCtx => BEP.transfer δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_transfer_eq_bep` row. -/
theorem kernelTransferBepPin_source (δ : TwoParabolaCtx) :
    Kernel.transfer δ.lam δ.x = BEP.transfer δ.lam δ.x :=
  PhotoLean.Relations.kernel_transfer_eq_bep δ.lam δ.x

/-- Definitional pin: the kernel reactant surface and the Hammond reactant surface are the same
term. -/
noncomputable def kernelReactantSurfaceHammondPin : Certificate SurfaceCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.reactantSurface" "SurfaceCtx"
        "PhotoLean/Kernel.lean#reactantSurface"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.reactantSurface" "SurfaceCtx"
        "PhotoLean/Hammond/Basic.lean#reactantSurface"
      leftContext := SurfaceCtx
      rightContext := SurfaceCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.reactantSurface δ.lam δ.q
      rightTerm := fun δ => Hammond.reactantSurface δ.lam δ.q
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/Hammond-reactant-surface pin. -/
theorem kernelReactantSurfaceHammondPin_defeq :
    DefEq (fun δ : SurfaceCtx => Kernel.reactantSurface δ.lam δ.q)
      (fun δ : SurfaceCtx => Hammond.reactantSurface δ.lam δ.q) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_reactantSurface_eq_hammond` row. -/
theorem kernelReactantSurfaceHammondPin_source (δ : SurfaceCtx) :
    Kernel.reactantSurface δ.lam δ.q = Hammond.reactantSurface δ.lam δ.q :=
  PhotoLean.Relations.kernel_reactantSurface_eq_hammond δ.lam δ.q

/-- Definitional pin: the kernel product surface and the Hammond product surface are the same
term. -/
noncomputable def kernelProductSurfaceHammondPin : Certificate ProductSurfaceCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Kernel" "PhotoLean.Kernel.productSurface" "ProductSurfaceCtx"
        "PhotoLean/Kernel.lean#productSurface"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.productSurface" "ProductSurfaceCtx"
        "PhotoLean/Hammond/Basic.lean#productSurface"
      leftContext := ProductSurfaceCtx
      rightContext := ProductSurfaceCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kernel.productSurface δ.lam δ.dG δ.q
      rightTerm := fun δ => Hammond.productSurface δ.lam δ.dG δ.q
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the kernel/Hammond-product-surface pin. -/
theorem kernelProductSurfaceHammondPin_defeq :
    DefEq (fun δ : ProductSurfaceCtx => Kernel.productSurface δ.lam δ.dG δ.q)
      (fun δ : ProductSurfaceCtx => Hammond.productSurface δ.lam δ.dG δ.q) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§1 kernel_productSurface_eq_hammond` row. -/
theorem kernelProductSurfaceHammondPin_source (δ : ProductSurfaceCtx) :
    Kernel.productSurface δ.lam δ.dG δ.q = Hammond.productSurface δ.lam δ.dG δ.q :=
  PhotoLean.Relations.kernel_productSurface_eq_hammond δ.lam δ.dG δ.q

/-! ## §2 — genuine equivalences (`↔`) -/

/-- The Marcus curvature is positive: the premise shared by the real-valued §2 equivalence rows. -/
def pMarcusCurvaturePositive : Premise TwoParabolaCtx :=
  mkPremise "marcus.curvaturePositive" fun δ => 0 < δ.lam

/-- The premise set of the transition-state/inverted-region equivalence. -/
def tsCoordPremises : List (Premise TwoParabolaCtx) := [pMarcusCurvaturePositive]

/-- The typed parent link of `tsCoord_lt_zero_iff_inverted`: the transition state leaves the
reactant side exactly in the Marcus inverted region. -/
noncomputable def tsCoordLtZeroLink : ParentCertificate TwoParabolaCtx :=
  .equivalence "PhotoLean.RelationAudit.Full.Sections01_05.tsCoordLtZeroInvertedEquivalence"
    (Comparison.ofPredicates
      (mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord" "TwoParabolaCtx"
        "PhotoLean/Hammond/Basic.lean#tsCoord")
      (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.InvertedRegion" "TwoParabolaCtx"
        "PhotoLean/Marcus/Basic.lean#InvertedRegion")
      (fun δ => Hammond.tsCoord δ.lam δ.x < 0)
      (fun δ => Marcus.InvertedRegion δ.lam δ.x))
    tsCoordPremises
    (fun δ hprem =>
      PhotoLean.Relations.tsCoord_lt_zero_iff_inverted
        (hprem pMarcusCurvaturePositive (by simp [tsCoordPremises])))

/-- Equivalence certificate for `tsCoord_lt_zero_iff_inverted`. -/
noncomputable def tsCoordLtZeroInvertedEquivalence : Certificate TwoParabolaCtx :=
  .equivalence tsCoordLtZeroLink rfl

/-- Source coherence: the certificate statement is the delivered
`§2 tsCoord_lt_zero_iff_inverted` row. -/
theorem tsCoordLtZeroInvertedEquivalence_source (δ : TwoParabolaCtx) (hlam : 0 < δ.lam) :
    Hammond.tsCoord δ.lam δ.x < 0 ↔ Marcus.InvertedRegion δ.lam δ.x :=
  PhotoLean.Relations.tsCoord_lt_zero_iff_inverted hlam

/-- The curvature is positive: the first premise of the Leffler-secant row. -/
def pSecantCurvaturePositive : Premise SecantCtx :=
  mkPremise "marcus.curvaturePositive" fun δ => 0 < δ.lam

/-- The two driving forces are distinct: the second premise of the Leffler-secant row. -/
def pSecantDistinct : Premise SecantCtx :=
  mkPremise "hammond.distinctDrivingForces" fun δ => δ.x1 ≠ δ.x2

/-- The premise set of the Leffler-secant/inverted-region equivalence. -/
def secantPremises : List (Premise SecantCtx) :=
  [pSecantCurvaturePositive, pSecantDistinct]

/-- The typed parent link of `lefflerSecant_neg_iff_inverted`: a negative Leffler secant is the
Marcus inverted region at the midpoint. -/
noncomputable def lefflerSecantNegInvertedLink : ParentCertificate SecantCtx :=
  .equivalence "PhotoLean.RelationAudit.Full.Sections01_05.lefflerSecantNegInvertedEquivalence"
    (Comparison.ofPredicates
      (mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.lefflerSecant" "SecantCtx"
        "PhotoLean/Hammond/Basic.lean#lefflerSecant")
      (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.InvertedRegion" "SecantCtx"
        "PhotoLean/Marcus/Basic.lean#InvertedRegion")
      (fun δ => Hammond.lefflerSecant δ.lam δ.x1 δ.x2 < 0)
      (fun δ => Marcus.InvertedRegion δ.lam ((δ.x1 + δ.x2) / 2)))
    secantPremises
    (fun δ hprem =>
      PhotoLean.Relations.lefflerSecant_neg_iff_inverted
        (hprem pSecantCurvaturePositive (by simp [secantPremises]))
        (hprem pSecantDistinct (by simp [secantPremises])))

/-- Equivalence certificate for `lefflerSecant_neg_iff_inverted`. -/
noncomputable def lefflerSecantNegInvertedEquivalence : Certificate SecantCtx :=
  .equivalence lefflerSecantNegInvertedLink rfl

/-- Source coherence: the certificate statement is the delivered
`§2 lefflerSecant_neg_iff_inverted` row. -/
theorem lefflerSecantNegInvertedEquivalence_source (δ : SecantCtx) (hlam : 0 < δ.lam)
    (h : δ.x1 ≠ δ.x2) :
    Hammond.lefflerSecant δ.lam δ.x1 δ.x2 < 0 ↔
      Marcus.InvertedRegion δ.lam ((δ.x1 + δ.x2) / 2) :=
  PhotoLean.Relations.lefflerSecant_neg_iff_inverted hlam h

/-- The rational curvature is positive: the premise of the rational classifier equivalence. -/
def pRatCurvaturePositive : Premise RatCtx :=
  mkPremise "marcus.curvaturePositive" fun δ => 0 < δ.lam

/-- The premise set of the rational classifier equivalence. -/
def ratPremises : List (Premise RatCtx) := [pRatCurvaturePositive]

/-- The typed parent link of `hammondZoneQ_beyondReactant_iff_inverted`: over `ℚ`, the Hammond
deep-exergonic classifier and the Marcus rational inverted-region classifier agree. -/
noncomputable def hammondZoneQInvertedLink : ParentCertificate RatCtx :=
  .equivalence "PhotoLean.RelationAudit.Full.Sections01_05.hammondZoneQInvertedEquivalence"
    (Comparison.ofPredicates
      (mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.Rat.hammondZoneQ" "RatCtx"
        "PhotoLean/Hammond/RatModel.lean#hammondZoneQ")
      (mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.Rat.zoneQ" "RatCtx"
        "PhotoLean/Marcus/RatModel.lean#zoneQ")
      (fun δ => Hammond.Rat.hammondZoneQ δ.lam δ.x = Hammond.HZone.beyondReactant)
      (fun δ => Marcus.Rat.zoneQ δ.lam δ.x = Marcus.Zone.inverted))
    ratPremises
    (fun δ hprem =>
      PhotoLean.Relations.hammondZoneQ_beyondReactant_iff_inverted
        (hprem pRatCurvaturePositive (by simp [ratPremises])))

/-- Equivalence certificate for `hammondZoneQ_beyondReactant_iff_inverted`. -/
noncomputable def hammondZoneQInvertedEquivalence : Certificate RatCtx :=
  .equivalence hammondZoneQInvertedLink rfl

/-- Source coherence: the certificate statement is the delivered
`§2 hammondZoneQ_beyondReactant_iff_inverted` row. -/
theorem hammondZoneQInvertedEquivalence_source (δ : RatCtx) (hlam : 0 < δ.lam) :
    Hammond.Rat.hammondZoneQ δ.lam δ.x = Hammond.HZone.beyondReactant ↔
      Marcus.Rat.zoneQ δ.lam δ.x = Marcus.Zone.inverted :=
  PhotoLean.Relations.hammondZoneQ_beyondReactant_iff_inverted hlam

/-! ## §2 — value-level bridge rows certified observationally

`transfer_eq_tsCoord_bridge` and `secSlope_eq_lefflerSecant` state equality of two real-valued
observables, not a propositional `↔` and not a definitional identity (`§2` explicitly says the
bodies differ in sign convention and pair indexing). The faithful certificate kind is
`observationalEquivalence`: over the declared channel input, the two theory observables agree at
every context point satisfying the premises. -/

/-- The BEP transfer coefficient needs a nonzero curvature. -/
def pTransferLamNeZero : Premise TransferCtx :=
  mkPremise "bep.lamNeZero" fun δ => δ.lam ≠ 0

/-- The premise set of the transfer-coordinate bridge. -/
def transferPremises : List (Premise TransferCtx) := [pTransferLamNeZero]

/-- The two readings compared by the transfer-coordinate bridge: BEP's transfer coefficient and
Hammond's transition-state coordinate. -/
def transferSetup : ObservationalSetup TransferCtx where
  left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.transfer" "TransferCtx"
    "PhotoLean/BEP/Basic.lean#transfer"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.tsCoord" "TransferCtx"
    "PhotoLean/Hammond/Basic.lean#tsCoord"
  leftState := TransferCtx
  rightState := TransferCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The transfer-coefficient channel, observed at every driving force. -/
noncomputable def transferChannel : Channel TransferCtx transferSetup ℝ ℝ where
  name := "transferCoefficient"
  domain := Set.univ
  leftObs := fun δ x => BEP.transfer δ.lam x
  rightObs := fun δ x => Hammond.tsCoord δ.lam x

/-- Observational certificate for the non-definitional transfer-coordinate bridge. -/
noncomputable def transferTsCoordBridge : Certificate TransferCtx :=
  .observationalEquivalence transferSetup transferPremises ℝ ℝ [transferChannel]
    (by decide)
    (fun δ hprem c hc x _hx => by
      have hlam : δ.lam ≠ 0 := hprem pTransferLamNeZero (by simp [transferPremises])
      rcases List.mem_singleton.mp hc with rfl
      exact PhotoLean.Relations.transfer_eq_tsCoord_bridge hlam x)

/-- Source coherence: the certificate statement is the delivered
`§2 transfer_eq_tsCoord_bridge` row, for every driving force. -/
theorem transferTsCoordBridge_source (δ : TransferCtx) (hlam : δ.lam ≠ 0) (x : ℝ) :
    BEP.transfer δ.lam x = Hammond.tsCoord δ.lam x :=
  PhotoLean.Relations.transfer_eq_tsCoord_bridge hlam x

/-- The two readings compared by the secant bridge: BEP's observable window slope and Hammond's
Leffler secant over the same window. -/
def secSlopeSetup : ObservationalSetup SlopeCtx where
  left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.secSlope" "SlopeCtx"
    "PhotoLean/BEP/Basic.lean#secSlope"
  right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.lefflerSecant" "SlopeCtx"
    "PhotoLean/Hammond/Basic.lean#lefflerSecant"
  leftState := SlopeCtx
  rightState := SlopeCtx
  leftInterp := fun δ => δ
  rightInterp := fun δ => δ

/-- The window-slope channel: the input is the pair `(x, h)` of window origin and width. -/
noncomputable def secSlopeChannel : Channel SlopeCtx secSlopeSetup ℝ (ℝ × ℝ) where
  name := "windowSecantSlope"
  domain := Set.univ
  leftObs := fun δ p => BEP.secSlope δ.lam p.1 p.2
  rightObs := fun δ p => Hammond.lefflerSecant δ.lam p.1 (p.1 + p.2)

/-- Observational certificate for the non-definitional secant bridge. -/
noncomputable def secSlopeLefflerSecantBridge : Certificate SlopeCtx :=
  .observationalEquivalence secSlopeSetup [] ℝ (ℝ × ℝ) [secSlopeChannel]
    (by decide)
    (fun δ _ c hc p _hp => by
      rcases List.mem_singleton.mp hc with rfl
      exact PhotoLean.Relations.secSlope_eq_lefflerSecant δ.lam p.1 p.2)

/-- Source coherence: the certificate statement is the delivered
`§2 secSlope_eq_lefflerSecant` row, for every window. -/
theorem secSlopeLefflerSecantBridge_source (δ : SlopeCtx) (x h : ℝ) :
    BEP.secSlope δ.lam x h = Hammond.lefflerSecant δ.lam x (x + h) :=
  PhotoLean.Relations.secSlope_eq_lefflerSecant δ.lam x h

/-! ## §3 — one-way entailment from BEP window conformance to the Hammond descriptor -/

/-- The typed parent link of `hammondDescriptor_of_epConformsOnWindow`: BEP line-law conformance
on a window entails the structural Hammond descriptor. One-way only; the converse is not claimed. -/
noncomputable def windowConformanceDescriptorLink : ParentCertificate WindowCtx :=
  .implication
    "PhotoLean.RelationAudit.Full.Sections01_05.windowConformanceDescriptorImplication"
    (Comparison.ofPredicates
      (mkRef "PhotoLean.BEP" "PhotoLean.BEP.EPConformsOnWindow" "WindowCtx"
        "PhotoLean/BEP/Basic.lean#EPConformsOnWindow")
      (mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.HammondDescriptor" "WindowCtx"
        "PhotoLean/Hammond/Basic.lean#HammondDescriptor")
      (fun δ => BEP.EPConformsOnWindow δ.lam δ.tol δ.a δ.b)
      (fun δ => Hammond.HammondDescriptor δ.lam))
    []
    (fun _ _ h => PhotoLean.Relations.hammondDescriptor_of_epConformsOnWindow h)

/-- Implication certificate for `hammondDescriptor_of_epConformsOnWindow`. -/
noncomputable def windowConformanceDescriptorImplication : Certificate WindowCtx :=
  .implication windowConformanceDescriptorLink rfl

/-- Source coherence: the certificate statement is the delivered
`§3 hammondDescriptor_of_epConformsOnWindow` row. -/
theorem windowConformanceDescriptorImplication_source (δ : WindowCtx)
    (h : BEP.EPConformsOnWindow δ.lam δ.tol δ.a δ.b) :
    Hammond.HammondDescriptor δ.lam :=
  PhotoLean.Relations.hammondDescriptor_of_epConformsOnWindow h

/-! ## §5 — remaining ledger aliases

These are `rfl`-level definitional aliases between delivered theory definitions. They are distinct
from the R1 kernel pin: the endpoints here are `BEP.eact`/`Marcus.barrier`, the Marcus rate
rewriting, and `Marcus.barrier`/`Hammond.gapReactant`, not `PhotoLean.Kernel.barrier`. -/

/-- Definitional pin: the BEP activation barrier is the delivered Marcus barrier. -/
noncomputable def bepEactMarcusBarrierPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.BEP" "PhotoLean.BEP.eact" "TwoParabolaCtx"
        "PhotoLean/BEP/Basic.lean#eact"
      right := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "TwoParabolaCtx"
        "PhotoLean/Marcus/Basic.lean#barrier"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => BEP.eact δ.lam δ.x
      rightTerm := fun δ => Marcus.barrier δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the BEP/Marcus-barrier alias. -/
theorem bepEactMarcusBarrierPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => BEP.eact δ.lam δ.x)
      (fun δ : TwoParabolaCtx => Marcus.barrier δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§5 bep_eact_eq_marcus_barrier` row. -/
theorem bepEactMarcusBarrierPin_source (δ : TwoParabolaCtx) :
    BEP.eact δ.lam δ.x = Marcus.barrier δ.lam δ.x :=
  PhotoLean.Relations.bep_eact_eq_marcus_barrier δ.lam δ.x

/-- Definitional pin: the delivered Marcus rate written through the BEP activation barrier. -/
noncomputable def bepRateExpNegEactPin : Certificate RateCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "RateCtx"
        "PhotoLean/Marcus/Basic.lean#rate"
      right := mkRef "PhotoLean.BEP" "PhotoLean.BEP.rateViaEact" "RateCtx"
        "PhotoLean/BEP/Compose.lean#rate_eq_exp_neg_eact"
      leftContext := RateCtx
      rightContext := RateCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
      rightTerm := fun δ => δ.A * Real.exp (-(BEP.eact δ.lam δ.x) / (δ.kB * δ.T))
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the rate rewriting. -/
theorem bepRateExpNegEactPin_defeq :
    DefEq (fun δ : RateCtx => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : RateCtx =>
        δ.A * Real.exp (-(BEP.eact δ.lam δ.x) / (δ.kB * δ.T))) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§5 bep_rate_eq_exp_neg_eact` row. -/
theorem bepRateExpNegEactPin_source (δ : RateCtx) :
    Marcus.rate δ.A δ.lam δ.kB δ.T δ.x =
      δ.A * Real.exp (-(BEP.eact δ.lam δ.x) / (δ.kB * δ.T)) :=
  PhotoLean.Relations.bep_rate_eq_exp_neg_eact δ.A δ.lam δ.kB δ.T δ.x

/-- Definitional pin: the Marcus barrier is literally the Hammond forward gap. -/
noncomputable def hammondBarrierGapReactantPin : Certificate TwoParabolaCtx :=
  .definitionalIdentity
    { left := mkRef "PhotoLean.Marcus" "PhotoLean.Marcus.barrier" "TwoParabolaCtx"
        "PhotoLean/Marcus/Basic.lean#barrier"
      right := mkRef "PhotoLean.Hammond" "PhotoLean.Hammond.gapReactant" "TwoParabolaCtx"
        "PhotoLean/Hammond/Basic.lean#gapReactant"
      leftContext := TwoParabolaCtx
      rightContext := TwoParabolaCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Marcus.barrier δ.lam δ.x
      rightTerm := fun δ => Hammond.gapReactant δ.lam δ.x
      same := DefEq.refl }
    []

/-- Fresh kernel `rfl` witness of the Marcus/Hammond-barrier alias. -/
theorem hammondBarrierGapReactantPin_defeq :
    DefEq (fun δ : TwoParabolaCtx => Marcus.barrier δ.lam δ.x)
      (fun δ : TwoParabolaCtx => Hammond.gapReactant δ.lam δ.x) :=
  DefEq.refl

/-- Source coherence: the pin is the delivered `§5 hammond_barrier_eq_gapReactant` row. -/
theorem hammondBarrierGapReactantPin_source (δ : TwoParabolaCtx) :
    Marcus.barrier δ.lam δ.x = Hammond.gapReactant δ.lam δ.x :=
  PhotoLean.Relations.hammond_barrier_eq_gapReactant δ.lam δ.x

/-! ## Kind pins — one per certificate, so a manifest cannot relabel a row -/

theorem kernelBarrierHammondPin_kind :
    certificateKind kernelBarrierHammondPin = RelationKind.definitionalIdentity := rfl

theorem kernelBarrierBepPin_kind :
    certificateKind kernelBarrierBepPin = RelationKind.definitionalIdentity := rfl

theorem kernelReverseBarrierHammondPin_kind :
    certificateKind kernelReverseBarrierHammondPin = RelationKind.definitionalIdentity := rfl

theorem kernelTsCoordHammondPin_kind :
    certificateKind kernelTsCoordHammondPin = RelationKind.definitionalIdentity := rfl

theorem kernelTransferBepPin_kind :
    certificateKind kernelTransferBepPin = RelationKind.definitionalIdentity := rfl

theorem kernelReactantSurfaceHammondPin_kind :
    certificateKind kernelReactantSurfaceHammondPin = RelationKind.definitionalIdentity := rfl

theorem kernelProductSurfaceHammondPin_kind :
    certificateKind kernelProductSurfaceHammondPin = RelationKind.definitionalIdentity := rfl

theorem transferTsCoordBridge_kind :
    certificateKind transferTsCoordBridge = RelationKind.observationalEquivalence := rfl

theorem secSlopeLefflerSecantBridge_kind :
    certificateKind secSlopeLefflerSecantBridge = RelationKind.observationalEquivalence := rfl

theorem tsCoordLtZeroInvertedEquivalence_kind :
    certificateKind tsCoordLtZeroInvertedEquivalence = RelationKind.equivalence := rfl

theorem lefflerSecantNegInvertedEquivalence_kind :
    certificateKind lefflerSecantNegInvertedEquivalence = RelationKind.equivalence := rfl

theorem hammondZoneQInvertedEquivalence_kind :
    certificateKind hammondZoneQInvertedEquivalence = RelationKind.equivalence := rfl

theorem windowConformanceDescriptorImplication_kind :
    certificateKind windowConformanceDescriptorImplication = RelationKind.implication := rfl

theorem bepEactMarcusBarrierPin_kind :
    certificateKind bepEactMarcusBarrierPin = RelationKind.definitionalIdentity := rfl

theorem bepRateExpNegEactPin_kind :
    certificateKind bepRateExpNegEactPin = RelationKind.definitionalIdentity := rfl

theorem hammondBarrierGapReactantPin_kind :
    certificateKind hammondBarrierGapReactantPin = RelationKind.definitionalIdentity := rfl

/-! ## Premise pins — one per certificate, so a manifest cannot attribute extra premises -/

theorem kernelBarrierHammondPin_premiseIDs :
    certificatePremiseIDs kernelBarrierHammondPin = [] := rfl

theorem kernelBarrierBepPin_premiseIDs :
    certificatePremiseIDs kernelBarrierBepPin = [] := rfl

theorem kernelReverseBarrierHammondPin_premiseIDs :
    certificatePremiseIDs kernelReverseBarrierHammondPin = [] := rfl

theorem kernelTsCoordHammondPin_premiseIDs :
    certificatePremiseIDs kernelTsCoordHammondPin = [] := rfl

theorem kernelTransferBepPin_premiseIDs :
    certificatePremiseIDs kernelTransferBepPin = [] := rfl

theorem kernelReactantSurfaceHammondPin_premiseIDs :
    certificatePremiseIDs kernelReactantSurfaceHammondPin = [] := rfl

theorem kernelProductSurfaceHammondPin_premiseIDs :
    certificatePremiseIDs kernelProductSurfaceHammondPin = [] := rfl

theorem transferTsCoordBridge_premiseIDs :
    certificatePremiseIDs transferTsCoordBridge = ["bep.lamNeZero"] := rfl

theorem secSlopeLefflerSecantBridge_premiseIDs :
    certificatePremiseIDs secSlopeLefflerSecantBridge = [] := rfl

theorem tsCoordLtZeroInvertedEquivalence_premiseIDs :
    certificatePremiseIDs tsCoordLtZeroInvertedEquivalence =
      ["marcus.curvaturePositive"] := rfl

theorem lefflerSecantNegInvertedEquivalence_premiseIDs :
    certificatePremiseIDs lefflerSecantNegInvertedEquivalence =
      ["marcus.curvaturePositive", "hammond.distinctDrivingForces"] := rfl

theorem hammondZoneQInvertedEquivalence_premiseIDs :
    certificatePremiseIDs hammondZoneQInvertedEquivalence =
      ["marcus.curvaturePositive"] := rfl

theorem windowConformanceDescriptorImplication_premiseIDs :
    certificatePremiseIDs windowConformanceDescriptorImplication = [] := rfl

theorem bepEactMarcusBarrierPin_premiseIDs :
    certificatePremiseIDs bepEactMarcusBarrierPin = [] := rfl

theorem bepRateExpNegEactPin_premiseIDs :
    certificatePremiseIDs bepRateExpNegEactPin = [] := rfl

theorem hammondBarrierGapReactantPin_premiseIDs :
    certificatePremiseIDs hammondBarrierGapReactantPin = [] := rfl

end Sections01_05
end Full
end RelationAudit
end PhotoLean
