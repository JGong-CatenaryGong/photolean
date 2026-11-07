/-
PhotoLean.RelationAudit.Full.Sections11_17 — R3 migration of the certificate-required rows of
`PhotoLean/Relations.lean` §§11–17.

This module is additive. It imports the delivered relation rows and the audit `Defs`, and it
changes no delivered statement. It contains only certificates whose semantic shape is actually
present in the delivered mathematics:

* `§12` kernel/Marcus definitional pins (six rows) become `definitionalIdentity` certificates:
  the `DefEq.refl` field is a fresh kernel check that the two translated terms are definitionally
  equal. A propositional equality proved by rewriting is not used for these rows.
* `§12` `eg_invertedGap_iff_marcus` becomes an `equivalence` certificate between the two
  predicates; the soundness field consumes the delivered `EnergyGapLaw.cert_invertedGap` theorem.
* `§15` `egBarrier_zero_iff_emEnergy_zero` becomes an `equivalence` certificate carrying the
  explicit `lam ≠ 0` premise; the soundness field consumes the delivered theorem.
* `§15` `icvscic_icRate_eq_eg_nrRate` becomes a `definitionalIdentity` certificate: the two
  rate bodies are definitionally equal after unfolding the shared barrier.


The remaining rows of §§11–17 are **not** forced into a certificate. They are numeric tie-backs
(§11), algebraic identities/support rows (§15), or model-level identities whose Stern–Volmer
side is encoded as an added rate (§15). None has the shape of a seven-kind certificate in the
delivered row: there is no propositional implication/equivalence between two theory predicates,
no typed composition parent, and no counterexample. The algebraic value identities are not
relabeled as `observationalEquivalence` because their R2 relation role is
`composition`/`model-level-composition` and no typed parent chain or declared observation
channel is delivered; they are preserved as support evidence. Reclassifying them is the honest
outcome; their target categories and rationales are recorded in
`relation_audit/migration/sections11_17.json`.

There is no unproved placeholder and no custom axiomatic declaration in this file. The
allowed-footprint probe for every certificate is recorded in the R3 verification record; every
footprint is within `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations

set_option autoImplicit false

noncomputable section

namespace PhotoLean
namespace RelationAudit
namespace Full
namespace Sections11_17

/-! ## Shared metadata helpers -/

/-- Artifact version label shared by the section certificates. Content hashes remain in the JSON
snapshot layer; this is the Lean-side snapshot label used by the pilot. -/
def artifactVersion : String := "PhotoLean@0.1.0+lean-toolchain:v4.17.0"

/-- Build a statement reference for a section certificate. -/
def sref (theory statementId context provenance : String) : StatementRef where
  theory := theory
  statementId := statementId
  artifactVersion := artifactVersion
  context := context
  provenance := provenance

/-- Build a named premise on a shared context. -/
def mkPremise {Δ : Type} (id : String) (predicate : Δ → Prop) : Premise Δ :=
  ⟨id, predicate⟩

/-! ## §12 — definitional kernel/Marcus pins -/

/-- Shared context of the EnergyGapLaw/kernel barrier pin. -/
structure EGKernelCtx where
  lam : ℝ
  x : ℝ

/-- Shared context of the EnergyGapLaw/Marcus rate pin. -/
structure EGRateCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- Shared context of the StokesShift ground-surface pin. -/
structure SSGroundCtx where
  lam : ℝ
  q : ℝ

/-- Shared context of the StokesShift excited-surface pin. -/
structure SSExcitedCtx where
  lam : ℝ
  e00 : ℝ
  q : ℝ

/-- Shared context of the ICvsISC/kernel barrier pin. -/
structure ICBarrierCtx where
  lam : ℝ
  x : ℝ

/-- Shared context of the ICvsISC/Marcus rate pin. -/
structure ICRateCtx where
  AI : ℝ
  lamI : ℝ
  kB : ℝ
  T : ℝ
  xI : ℝ

/-- Shared context of the ICvsISC/EnergyGapLaw rate pin. -/
structure EGICRateCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- The definitional pin behind `eg_barrier_eq_kernel`: the EnergyGapLaw barrier is the kernel
barrier. -/
def egBarrierEqKernelPin : DefinitionalPin EGKernelCtx where
  left := sref "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrBarrier" "EGKernelCtx"
    "PhotoLean/Relations.lean#eg_barrier_eq_kernel (left: EnergyGapLaw.nrBarrier)"
  right := sref "PhotoLean.Kernel" "PhotoLean.Kernel.barrier" "EGKernelCtx"
    "PhotoLean/Kernel.lean#barrier (right: Kernel.barrier)"
  leftContext := EGKernelCtx
  rightContext := EGKernelCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => EnergyGapLaw.nrBarrier δ.lam δ.x
  rightTerm := fun δ => Kernel.barrier δ.lam δ.x
  same := DefEq.refl

/-- **§12 certificate**: the EnergyGapLaw barrier is definitionally the kernel barrier. -/
def egBarrierEqKernelCertificate : Certificate EGKernelCtx :=
  .definitionalIdentity egBarrierEqKernelPin []

/-- Fresh pointwise `rfl` witness for the EnergyGapLaw/kernel barrier pin. -/
theorem egBarrierEqKernel_rfl (δ : EGKernelCtx) :
    EnergyGapLaw.nrBarrier δ.lam δ.x = Kernel.barrier δ.lam δ.x := rfl

/-- Kind pin for the EnergyGapLaw/kernel barrier certificate. -/
theorem egBarrierEqKernelCertificate_kind :
    certificateKind egBarrierEqKernelCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the EnergyGapLaw/kernel barrier certificate (no premises). -/
theorem egBarrierEqKernelCertificate_premiseIDs :
    certificatePremiseIDs egBarrierEqKernelCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. The
certificate's definitional evidence is the fresh `DefEq.refl` above, not this equality. -/
theorem egBarrierEqKernelCertificate_original (δ : EGKernelCtx) :
    EnergyGapLaw.nrBarrier δ.lam δ.x = Kernel.barrier δ.lam δ.x :=
  Relations.eg_barrier_eq_kernel δ.lam δ.x

/-- The definitional pin behind `eg_rate_eq_marcus`: the EnergyGapLaw rate is the Marcus rate. -/
def egRateEqMarcusPin : DefinitionalPin EGRateCtx where
  left := sref "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrRate" "EGRateCtx"
    "PhotoLean/Relations.lean#eg_rate_eq_marcus (left: EnergyGapLaw.nrRate)"
  right := sref "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "EGRateCtx"
    "PhotoLean/Marcus/Basic.lean#rate (right: Marcus.rate)"
  leftContext := EGRateCtx
  rightContext := EGRateCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x
  rightTerm := fun δ => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x
  same := DefEq.refl

/-- **§12 certificate**: the EnergyGapLaw nonradiative rate is definitionally the Marcus rate. -/
def egRateEqMarcusCertificate : Certificate EGRateCtx :=
  .definitionalIdentity egRateEqMarcusPin []

/-- Fresh pointwise `rfl` witness for the EnergyGapLaw/Marcus rate pin. -/
theorem egRateEqMarcus_rfl (δ : EGRateCtx) :
    EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x =
      Marcus.rate δ.A δ.lam δ.kB δ.T δ.x := rfl

/-- Kind pin for the EnergyGapLaw/Marcus rate certificate. -/
theorem egRateEqMarcusCertificate_kind :
    certificateKind egRateEqMarcusCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the EnergyGapLaw/Marcus rate certificate (no premises). -/
theorem egRateEqMarcusCertificate_premiseIDs :
    certificatePremiseIDs egRateEqMarcusCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem egRateEqMarcusCertificate_original (δ : EGRateCtx) :
    EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x =
      Marcus.rate δ.A δ.lam δ.kB δ.T δ.x :=
  Relations.eg_rate_eq_marcus δ.A δ.lam δ.kB δ.T δ.x

/-- The definitional pin behind `ss_s0Surface_eq_kernel`: the StokesShift ground surface is the
kernel reactant surface. -/
def ssS0SurfaceEqKernelPin : DefinitionalPin SSGroundCtx where
  left := sref "PhotoLean.StokesShift" "PhotoLean.StokesShift.s0Surface" "SSGroundCtx"
    "PhotoLean/Relations.lean#ss_s0Surface_eq_kernel (left: StokesShift.s0Surface)"
  right := sref "PhotoLean.Kernel" "PhotoLean.Kernel.reactantSurface" "SSGroundCtx"
    "PhotoLean/Kernel.lean#reactantSurface (right: Kernel.reactantSurface)"
  leftContext := SSGroundCtx
  rightContext := SSGroundCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => StokesShift.s0Surface δ.lam δ.q
  rightTerm := fun δ => Kernel.reactantSurface δ.lam δ.q
  same := DefEq.refl

/-- **§12 certificate**: the StokesShift ground surface is definitionally the kernel reactant
surface. -/
def ssS0SurfaceEqKernelCertificate : Certificate SSGroundCtx :=
  .definitionalIdentity ssS0SurfaceEqKernelPin []

/-- Fresh pointwise `rfl` witness for the StokesShift ground-surface pin. -/
theorem ssS0SurfaceEqKernel_rfl (δ : SSGroundCtx) :
    StokesShift.s0Surface δ.lam δ.q = Kernel.reactantSurface δ.lam δ.q := rfl

/-- Kind pin for the StokesShift ground-surface certificate. -/
theorem ssS0SurfaceEqKernelCertificate_kind :
    certificateKind ssS0SurfaceEqKernelCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the StokesShift ground-surface certificate (no premises). -/
theorem ssS0SurfaceEqKernelCertificate_premiseIDs :
    certificatePremiseIDs ssS0SurfaceEqKernelCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem ssS0SurfaceEqKernelCertificate_original (δ : SSGroundCtx) :
    StokesShift.s0Surface δ.lam δ.q = Kernel.reactantSurface δ.lam δ.q :=
  Relations.ss_s0Surface_eq_kernel δ.lam δ.q

/-- The definitional pin behind `ss_s1Surface_eq_kernel`: the StokesShift excited surface is the
kernel product surface. -/
def ssS1SurfaceEqKernelPin : DefinitionalPin SSExcitedCtx where
  left := sref "PhotoLean.StokesShift" "PhotoLean.StokesShift.s1Surface" "SSExcitedCtx"
    "PhotoLean/Relations.lean#ss_s1Surface_eq_kernel (left: StokesShift.s1Surface)"
  right := sref "PhotoLean.Kernel" "PhotoLean.Kernel.productSurface" "SSExcitedCtx"
    "PhotoLean/Kernel.lean#productSurface (right: Kernel.productSurface)"
  leftContext := SSExcitedCtx
  rightContext := SSExcitedCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => StokesShift.s1Surface δ.lam δ.e00 δ.q
  rightTerm := fun δ => Kernel.productSurface δ.lam δ.e00 δ.q
  same := DefEq.refl

/-- **§12 certificate**: the StokesShift excited surface is definitionally the kernel product
surface. -/
def ssS1SurfaceEqKernelCertificate : Certificate SSExcitedCtx :=
  .definitionalIdentity ssS1SurfaceEqKernelPin []

/-- Fresh pointwise `rfl` witness for the StokesShift excited-surface pin. -/
theorem ssS1SurfaceEqKernel_rfl (δ : SSExcitedCtx) :
    StokesShift.s1Surface δ.lam δ.e00 δ.q = Kernel.productSurface δ.lam δ.e00 δ.q := rfl

/-- Kind pin for the StokesShift excited-surface certificate. -/
theorem ssS1SurfaceEqKernelCertificate_kind :
    certificateKind ssS1SurfaceEqKernelCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the StokesShift excited-surface certificate (no premises). -/
theorem ssS1SurfaceEqKernelCertificate_premiseIDs :
    certificatePremiseIDs ssS1SurfaceEqKernelCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem ssS1SurfaceEqKernelCertificate_original (δ : SSExcitedCtx) :
    StokesShift.s1Surface δ.lam δ.e00 δ.q = Kernel.productSurface δ.lam δ.e00 δ.q :=
  Relations.ss_s1Surface_eq_kernel δ.lam δ.e00 δ.q

/-- The definitional pin behind `icvscic_barrier_eq_kernel`: the ICvsISC Franck–Condon barrier
is the kernel barrier. -/
def icvscicBarrierEqKernelPin : DefinitionalPin ICBarrierCtx where
  left := sref "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.fcBarrier" "ICBarrierCtx"
    "PhotoLean/Relations.lean#icvscic_barrier_eq_kernel (left: ICvsISC.fcBarrier)"
  right := sref "PhotoLean.Kernel" "PhotoLean.Kernel.barrier" "ICBarrierCtx"
    "PhotoLean/Kernel.lean#barrier (right: Kernel.barrier)"
  leftContext := ICBarrierCtx
  rightContext := ICBarrierCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => ICvsISC.fcBarrier δ.lam δ.x
  rightTerm := fun δ => Kernel.barrier δ.lam δ.x
  same := DefEq.refl

/-- **§12 certificate**: the ICvsISC Franck–Condon barrier is definitionally the kernel barrier. -/
def icvscicBarrierEqKernelCertificate : Certificate ICBarrierCtx :=
  .definitionalIdentity icvscicBarrierEqKernelPin []

/-- Fresh pointwise `rfl` witness for the ICvsISC/kernel barrier pin. -/
theorem icvscicBarrierEqKernel_rfl (δ : ICBarrierCtx) :
    ICvsISC.fcBarrier δ.lam δ.x = Kernel.barrier δ.lam δ.x := rfl

/-- Kind pin for the ICvsISC/kernel barrier certificate. -/
theorem icvscicBarrierEqKernelCertificate_kind :
    certificateKind icvscicBarrierEqKernelCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the ICvsISC/kernel barrier certificate (no premises). -/
theorem icvscicBarrierEqKernelCertificate_premiseIDs :
    certificatePremiseIDs icvscicBarrierEqKernelCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem icvscicBarrierEqKernelCertificate_original (δ : ICBarrierCtx) :
    ICvsISC.fcBarrier δ.lam δ.x = Kernel.barrier δ.lam δ.x :=
  Relations.icvscic_barrier_eq_kernel δ.lam δ.x

/-- The definitional pin behind `icvscic_icRate_eq_marcus`: the ICvsISC internal-conversion rate
is the Marcus rate. -/
def icvscicIcRateEqMarcusPin : DefinitionalPin ICRateCtx where
  left := sref "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.icRate" "ICRateCtx"
    "PhotoLean/Relations.lean#icvscic_icRate_eq_marcus (left: ICvsISC.icRate)"
  right := sref "PhotoLean.Marcus" "PhotoLean.Marcus.rate" "ICRateCtx"
    "PhotoLean/Marcus/Basic.lean#rate (right: Marcus.rate)"
  leftContext := ICRateCtx
  rightContext := ICRateCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI
  rightTerm := fun δ => Marcus.rate δ.AI δ.lamI δ.kB δ.T δ.xI
  same := DefEq.refl

/-- **§12 certificate**: the ICvsISC internal-conversion rate is definitionally the Marcus
rate. -/
def icvscicIcRateEqMarcusCertificate : Certificate ICRateCtx :=
  .definitionalIdentity icvscicIcRateEqMarcusPin []

/-- Fresh pointwise `rfl` witness for the ICvsISC/Marcus rate pin. -/
theorem icvscicIcRateEqMarcus_rfl (δ : ICRateCtx) :
    ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI =
      Marcus.rate δ.AI δ.lamI δ.kB δ.T δ.xI := rfl

/-- Kind pin for the ICvsISC/Marcus rate certificate. -/
theorem icvscicIcRateEqMarcusCertificate_kind :
    certificateKind icvscicIcRateEqMarcusCertificate = RelationKind.definitionalIdentity := rfl

/-- Premise projection for the ICvsISC/Marcus rate certificate (no premises). -/
theorem icvscicIcRateEqMarcusCertificate_premiseIDs :
    certificatePremiseIDs icvscicIcRateEqMarcusCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem icvscicIcRateEqMarcusCertificate_original (δ : ICRateCtx) :
    ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI =
      Marcus.rate δ.AI δ.lamI δ.kB δ.T δ.xI :=
  Relations.icvscic_icRate_eq_marcus δ.AI δ.lamI δ.kB δ.T δ.xI

/-- The definitional pin behind `icvscic_icRate_eq_eg_nrRate`: the ICvsISC internal-conversion
rate is the EnergyGapLaw nonradiative rate. -/
def icvscicIcRateEqEnergyGapLawPin : DefinitionalPin EGICRateCtx where
  left := sref "PhotoLean.ICvsISC" "PhotoLean.ICvsISC.icRate" "EGICRateCtx"
    "PhotoLean/Relations.lean#icvscic_icRate_eq_eg_nrRate (left: ICvsISC.icRate)"
  right := sref "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrRate" "EGICRateCtx"
    "PhotoLean/EnergyGapLaw/Basic.lean#nrRate (right: EnergyGapLaw.nrRate)"
  leftContext := EGICRateCtx
  rightContext := EGICRateCtx
  codomain := ℝ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftTerm := fun δ => ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x
  rightTerm := fun δ => EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x
  same := DefEq.refl

/-- **§15 certificate**: the ICvsISC internal-conversion rate is definitionally the
EnergyGapLaw nonradiative rate. -/
def icvscicIcRateEqEnergyGapLawCertificate : Certificate EGICRateCtx :=
  .definitionalIdentity icvscicIcRateEqEnergyGapLawPin []

/-- Fresh pointwise `rfl` witness for the ICvsISC/EnergyGapLaw rate pin. -/
theorem icvscicIcRateEqEnergyGapLaw_rfl (δ : EGICRateCtx) :
    ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x =
      EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x := rfl

/-- Kind pin for the ICvsISC/EnergyGapLaw rate certificate. -/
theorem icvscicIcRateEqEnergyGapLawCertificate_kind :
    certificateKind icvscicIcRateEqEnergyGapLawCertificate =
      RelationKind.definitionalIdentity := rfl

/-- Premise projection for the ICvsISC/EnergyGapLaw rate certificate (no premises). -/
theorem icvscicIcRateEqEnergyGapLawCertificate_premiseIDs :
    certificatePremiseIDs icvscicIcRateEqEnergyGapLawCertificate = [] := rfl

/-- Reuse witness: the delivered propositional statement behind the definitional pin. -/
theorem icvscicIcRateEqEnergyGapLawCertificate_original (δ : EGICRateCtx) :
    ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x =
      EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x :=
  Relations.icvscic_icRate_eq_eg_nrRate δ.A δ.lam δ.kB δ.T δ.x

/-! ## §12 and §15 — predicate equivalences -/

/-- Shared context of the EnergyGapLaw/Marcus inverted-gap equivalence. -/
structure EGInvertedCtx where
  lam : ℝ
  x : ℝ

/-- Shared context of the EnergyGapLaw/StokesShift emission-window equivalence. -/
structure EGStokesCtx where
  lam : ℝ
  e00 : ℝ

/-- The `lam ≠ 0` premise of the emission-window equivalence. -/
def pEGStokesLambdaNonzero : Premise EGStokesCtx :=
  mkPremise "energyGapLaw.lamNonzero" fun δ => δ.lam ≠ 0

/-- The comparison behind `eg_invertedGap_iff_marcus`: the EnergyGapLaw inverted-gap predicate
against the Marcus inverted region. -/
def egInvertedGapComparison : Comparison EGInvertedCtx :=
  Comparison.ofPredicates
    (sref "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.InvertedGap" "EGInvertedCtx"
      "PhotoLean/Relations.lean#eg_invertedGap_iff_marcus (left: EnergyGapLaw.InvertedGap)")
    (sref "PhotoLean.Marcus" "PhotoLean.Marcus.InvertedRegion" "EGInvertedCtx"
      "PhotoLean/Relations.lean#eg_invertedGap_iff_marcus (right: Marcus.InvertedRegion)")
    (fun δ => EnergyGapLaw.InvertedGap δ.lam δ.x)
    (fun δ => Marcus.InvertedRegion δ.lam δ.x)

/-- Typed equivalence parent for the inverted-gap row, consuming the delivered
`EnergyGapLaw.cert_invertedGap`. -/
def egInvertedGapLink : ParentCertificate EGInvertedCtx :=
  .equivalence "PhotoLean.RelationAudit.Full.Sections11_17.egInvertedGapEquivalenceCertificate"
    egInvertedGapComparison []
    (fun δ _ => EnergyGapLaw.cert_invertedGap δ.lam δ.x)

/-- **§12 certificate**: the EnergyGapLaw inverted-gap predicate is equivalent to the Marcus
inverted region. -/
def egInvertedGapEquivalenceCertificate : Certificate EGInvertedCtx :=
  .equivalence egInvertedGapLink rfl

/-- Kind pin for the inverted-gap equivalence certificate. -/
theorem egInvertedGapEquivalenceCertificate_kind :
    certificateKind egInvertedGapEquivalenceCertificate = RelationKind.equivalence := rfl

/-- Premise projection for the inverted-gap equivalence certificate (no premises). -/
theorem egInvertedGapEquivalenceCertificate_premiseIDs :
    certificatePremiseIDs egInvertedGapEquivalenceCertificate = [] := rfl

/-- Reuse witness: the delivered equivalence statement behind the typed certificate. -/
theorem egInvertedGapEquivalenceCertificate_original (δ : EGInvertedCtx) :
    EnergyGapLaw.InvertedGap δ.lam δ.x ↔ Marcus.InvertedRegion δ.lam δ.x :=
  Relations.eg_invertedGap_iff_marcus δ.lam δ.x

/-- The comparison behind `egBarrier_zero_iff_emEnergy_zero`: vanishing EnergyGapLaw barrier
against the closed Stokes emission window. -/
def egBarrierZeroIffEmEnergyZeroComparison : Comparison EGStokesCtx :=
  Comparison.ofPredicates
    (sref "PhotoLean.EnergyGapLaw" "PhotoLean.EnergyGapLaw.nrBarrier_eq_zero" "EGStokesCtx"
      "PhotoLean/Relations.lean#egBarrier_zero_iff_emEnergy_zero (left: nrBarrier = 0)")
    (sref "PhotoLean.StokesShift" "PhotoLean.StokesShift.emEnergy_eq_zero" "EGStokesCtx"
      "PhotoLean/Relations.lean#egBarrier_zero_iff_emEnergy_zero (right: emEnergy = 0)")
    (fun δ => EnergyGapLaw.nrBarrier δ.lam δ.e00 = 0)
    (fun δ => StokesShift.emEnergy δ.lam δ.e00 = 0)

/-- Typed equivalence parent for the emission-window row, consuming the delivered
`Relations.egBarrier_zero_iff_emEnergy_zero` under the explicit `lam ≠ 0` premise. -/
def egBarrierZeroIffEmEnergyZeroLink : ParentCertificate EGStokesCtx :=
  .equivalence "PhotoLean.RelationAudit.Full.Sections11_17.egBarrierZeroIffEmEnergyZeroCertificate"
    egBarrierZeroIffEmEnergyZeroComparison [pEGStokesLambdaNonzero]
    (fun δ hprem =>
      Relations.egBarrier_zero_iff_emEnergy_zero
        (hprem pEGStokesLambdaNonzero (by simp [pEGStokesLambdaNonzero])))

/-- **§15 certificate**: the EnergyGapLaw barrier vanishes exactly when the Stokes emission
window closes, under `lam ≠ 0`. -/
def egBarrierZeroIffEmEnergyZeroCertificate : Certificate EGStokesCtx :=
  .equivalence egBarrierZeroIffEmEnergyZeroLink rfl

/-- Kind pin for the emission-window equivalence certificate. -/
theorem egBarrierZeroIffEmEnergyZeroCertificate_kind :
    certificateKind egBarrierZeroIffEmEnergyZeroCertificate = RelationKind.equivalence := rfl

/-- Premise projection for the emission-window equivalence certificate. -/
theorem egBarrierZeroIffEmEnergyZeroCertificate_premiseIDs :
    certificatePremiseIDs egBarrierZeroIffEmEnergyZeroCertificate =
      ["energyGapLaw.lamNonzero"] := rfl

/-- Reuse witness: the delivered equivalence statement behind the typed certificate, under the
same explicit `lam ≠ 0` premise. -/
theorem egBarrierZeroIffEmEnergyZeroCertificate_original (δ : EGStokesCtx)
    (hlam : δ.lam ≠ 0) :
    EnergyGapLaw.nrBarrier δ.lam δ.e00 = 0 ↔ StokesShift.emEnergy δ.lam δ.e00 = 0 :=
  Relations.egBarrier_zero_iff_emEnergy_zero hlam

/-! ## Definitional function-level witnesses and reclassification evidence -/

/-- Function-level `DefEq` witness for the EnergyGapLaw/kernel barrier pin. -/
theorem egBarrierEqKernelCertificate_defeq :
    DefEq (fun δ : EGKernelCtx => EnergyGapLaw.nrBarrier δ.lam δ.x)
      (fun δ : EGKernelCtx => Kernel.barrier δ.lam δ.x) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the EnergyGapLaw/Marcus rate pin. -/
theorem egRateEqMarcusCertificate_defeq :
    DefEq (fun δ : EGRateCtx => EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : EGRateCtx => Marcus.rate δ.A δ.lam δ.kB δ.T δ.x) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the StokesShift ground-surface pin. -/
theorem ssS0SurfaceEqKernelCertificate_defeq :
    DefEq (fun δ : SSGroundCtx => StokesShift.s0Surface δ.lam δ.q)
      (fun δ : SSGroundCtx => Kernel.reactantSurface δ.lam δ.q) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the StokesShift excited-surface pin. -/
theorem ssS1SurfaceEqKernelCertificate_defeq :
    DefEq (fun δ : SSExcitedCtx => StokesShift.s1Surface δ.lam δ.e00 δ.q)
      (fun δ : SSExcitedCtx => Kernel.productSurface δ.lam δ.e00 δ.q) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the ICvsISC/kernel barrier pin. -/
theorem icvscicBarrierEqKernelCertificate_defeq :
    DefEq (fun δ : ICBarrierCtx => ICvsISC.fcBarrier δ.lam δ.x)
      (fun δ : ICBarrierCtx => Kernel.barrier δ.lam δ.x) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the ICvsISC/Marcus rate pin. -/
theorem icvscicIcRateEqMarcusCertificate_defeq :
    DefEq (fun δ : ICRateCtx => ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)
      (fun δ : ICRateCtx => Marcus.rate δ.AI δ.lamI δ.kB δ.T δ.xI) :=
  DefEq.refl

/-- Function-level `DefEq` witness for the ICvsISC/EnergyGapLaw rate pin. -/
theorem icvscicIcRateEqEnergyGapLawCertificate_defeq :
    DefEq (fun δ : EGICRateCtx => ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : EGICRateCtx => EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x) :=
  DefEq.refl

/-! ### Re-exported evidence for the reclassified rows

These are deliberately **not** `Certificate` values. They re-export the original delivered theorem
with its explicit binders so the fragment's reclassification evidence has a Lean name to check.
-/

/-- Evidence re-export for the §11 transitive Marcus/kernel tie-back (not a certificate). -/
theorem symmetryFactorTsCoordZeroEqKernel_evidence {lam : ℝ} (hlam : 0 < lam) :
    SymmetryFactor.tsCoordZero lam lam = Kernel.tsCoord lam 0 :=
  Relations.symmetryFactor_tsCoordZero_eq_kernel hlam

/-- Evidence re-export for the §11 transitive BEP/kernel tie-back (not a certificate). -/
theorem symmetryFactorTsCoordZeroEqBepTransfer_evidence {lam : ℝ} (hlam : 0 < lam) :
    SymmetryFactor.tsCoordZero lam lam = BEP.transfer lam 0 :=
  Relations.symmetryFactor_tsCoordZero_eq_bepTransfer hlam

/-- Evidence re-export for the §15 Kasha/QuantumYield algebraic identity (not a certificate). -/
theorem kashaRadBranchEqYieldOf_evidence (rad ic : ℕ → ℝ) (n : ℕ) :
    Kasha.radBranch rad ic n = QuantumYield.yieldOf ![rad n, ic n] 0 :=
  Relations.kasha_radBranch_eq_yieldOf rad ic n

/-- Evidence re-export for the §15 SternVolmer/QuantumYield dilution identity (not a
certificate). -/
theorem svQuenchDilutesYield_evidence (kr knr kq q : ℝ) (hpos : 0 < kr + knr)
    (hq : 0 ≤ kq * q) :
    QuantumYield.yieldOf ![kr, knr] 0 =
      QuantumYield.yieldOf ![kr, knr + kq * q] 0 *
        SternVolmer.svRatioDyn (kr + knr) kq q :=
  Relations.sv_quench_dilutes_yield kr knr kq q hpos hq

/-- Evidence re-export for the §15 FluorPhos/QuantumYield fluorescence identity (not a
certificate). -/
theorem phiFEqYieldOf_evidence (kF kISC kIC : ℝ) :
    FluorPhos.phiF kF kISC kIC = QuantumYield.yieldOf ![kF, kISC, kIC] 0 :=
  Relations.phiF_eq_yieldOf kF kISC kIC

/-- Evidence re-export for the §15 FluorPhos/QuantumYield phosphorescence cascade identity
(not a certificate). -/
theorem phiPEqYieldOfCascade_evidence (kF kISC kIC kP kNR : ℝ) :
    FluorPhos.phiP kF kISC kIC kP kNR =
      QuantumYield.yieldOf ![kF, kISC, kIC] 1 * QuantumYield.yieldOf ![kP, kNR] 0 :=
  Relations.phiP_eq_yieldOf_cascade kF kISC kIC kP kNR

/-- Evidence re-export for the §15 Einstein/QuantumYield anchor identity (not a
certificate). -/
theorem einsteinYieldViaQY_evidence (A kNR : ℝ) :
    A * Einstein.tauR (A + kNR) = QuantumYield.yieldOf ![A, kNR] 0 :=
  Relations.einstein_yield_via_qy A kNR

/-- Evidence re-export for the §15 Forster/QuantumYield efficiency identity (not a
certificate). -/
theorem fretEff6EqOneSubYieldOf_evidence (kD r6 R : ℝ) (hkD : 0 < kD) (hr6 : 0 ≤ r6)
    (hR : R ≠ 0) :
    Forster.fretEff6 r6 R = 1 - QuantumYield.yieldOf ![kD, kD * (r6 / R ^ 6)] 0 :=
  Relations.fretEff6_eq_one_sub_yieldOf kD r6 R hkD hr6 hR

/-- Evidence re-export for the §15 SternVolmer/FluorPhos model-level quench-invariance identity
(not a certificate). -/
theorem fpRatioInvariantUnderQuench_evidence {kF kISC kIC kP kNR kq q : ℝ}
    (hkF : 0 < kF) (hs1 : 0 < FluorPhos.s1Decay kF kISC kIC)
    (hs1q : 0 < FluorPhos.s1Decay kF kISC (kIC + kq * q)) (ht1 : 0 < kP + kNR) :
    FluorPhos.phiP kF kISC (kIC + kq * q) kP kNR /
        FluorPhos.phiF kF kISC (kIC + kq * q) =
      FluorPhos.phiP kF kISC kIC kP kNR / FluorPhos.phiF kF kISC kIC :=
  Relations.fpRatio_invariant_under_quench hkF hs1 hs1q ht1

/-- Evidence re-export for the §17 RACI/QuantumYield algebraic identity (not a
certificate). -/
theorem raciQyEqYieldOfTwoChannel_evidence (kr knr : ℝ) :
    RACI.quantumYield kr knr = QuantumYield.yieldOf ![kr, knr] 0 :=
  Relations.raci_qy_eq_yieldOf_two_channel kr knr

/-! ## Enumeration for the migration fragment -/

/-- The nine certified rows of §§11–17, with the audit status carried beside each name. -/
def sectionCertificates : List (String × AuditStatus) :=
  [ ("PhotoLean.RelationAudit.Full.Sections11_17.egBarrierEqKernelCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.egRateEqMarcusCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.ssS0SurfaceEqKernelCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.ssS1SurfaceEqKernelCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.icvscicBarrierEqKernelCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.icvscicIcRateEqMarcusCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.icvscicIcRateEqEnergyGapLawCertificate",
      .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.egInvertedGapEquivalenceCertificate", .certified),
    ("PhotoLean.RelationAudit.Full.Sections11_17.egBarrierZeroIffEmEnergyZeroCertificate",
      .certified) ]

end Sections11_17
end Full
end RelationAudit
end PhotoLean

end
