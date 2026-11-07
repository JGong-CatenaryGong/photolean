/-
PhotoLean.RelationAudit.Full.Sections06_10 — the R3 migration fragment for `PhotoLean.Relations`
sections 6 through 10.

This module is additive: it imports `PhotoLean.RelationAudit.Defs` and `PhotoLean.Relations` and
changes no delivered statement. It owns the migration of every R2 `certificate-required`
declaration in §§6–10 (`relation_audit/dispositions.json`), reusing the original theorems:

* §6 `hammond_sharp_iff_marcus_sharp` — a genuine cross-theory **equivalence** between the Hammond
  structural descriptor and the Marcus rate descriptor. It is certified as an `equivalence`
  carrying the three explicit positivity premises (`0 < A`, `0 < kB`, `0 < T`). The proof reuses
  the two delivered sharp characterizations; the composition provenance stays visible in the
  source references but the row is not labelled `conditionalComposition`, because the delivered
  theorem is a direct iff and the typed-parent composition combinator is not the proof route.
* §7 `kernel_marcusIC` — a kernel **definitional identity** pinning the Kasha internal-conversion
  rate to the Marcus rate law with the kernel barrier. The pin carries a fresh `DefEq.refl`; it is
  not propositional equality.
* §8 `linearVolcano_eq_bepTangent`, `linearVolcano_le_parabolic`, `parabolic_descriptor`,
  `linearVolcano_apex_exact` — **reclassified**, not certified. These are term-level identities,
  a pointwise order inequality, and a property of the BEP-instantiated composite model. The
  seven-kind taxonomy has no constructor for "value-level identity/order of two model
  functionals", and none of the four theorems is a typed-parent composition: they are proved by
  unfolding and arithmetic (`ring`, `field_simp`, `linarith`) rather than by consuming two typed
  parents. Wrapping them in a `Certificate` would require inventing a statement pair (or a vacuous
  antecedent) and would misdescribe the delivered mathematics. The fragment therefore re-exports
  the four statements as evidence only, with no certificate constructor, and records the target
  category `model-level-composition` in the JSON fragment.

No observation channel or distinguishability witness is migrated here: the §§6–10 queue contains
no `observationalEquivalence` or `distinguishability` row. The §9 look-alike contrasts that do
carry distinguishing content are not certificate-required in R2 and are deliberately left to
their ledger disposition.

There is no unproved placeholder and no custom axiomatic declaration in this file.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.Relations

set_option autoImplicit false

namespace PhotoLean
namespace RelationAudit
namespace Full
namespace Sections06_10

/-! ## Shared metadata helpers

The helpers are local to this fragment so the section module does not depend on the pilot
certificate set. They build the same `StatementRef` / `Premise` records used by the R1 pilot. -/

/-- Lean-side snapshot label shared by the fragment rows. Content hashes remain in the JSON
snapshot layer. -/
def sectionArtifactVersion : String := "PhotoLean@0.1.0+lean-toolchain:v4.17.0"

/-- Build a statement reference for this fragment. -/
def mkStatementRef (theory statementId context provenance : String) : StatementRef where
  theory := theory
  statementId := statementId
  artifactVersion := sectionArtifactVersion
  context := context
  provenance := provenance

/-- Build a named premise for this fragment. -/
def mkPremise {Δ : Type} (id : String) (predicate : Δ → Prop) : Premise Δ :=
  ⟨id, predicate⟩

/-! ## §6 — Hammond structural descriptor ⇔ Marcus rate descriptor (certified equivalence)

The delivered theorem `PhotoLean.Relations.hammond_sharp_iff_marcus_sharp` is a genuine
cross-theory iff under the positivity premises `0 < A`, `0 < kB`, `0 < T`. The shared context is
the four-tuple `(A, kB, T, lam)`; the two statement contexts coincide with it, so both translations
are the identity. The certificate is built on a typed `ParentCertificate.equivalence`, and the
kind-specific proof is the delivered theorem itself. -/

/-- Shared context of the Hammond ⇔ Marcus co-extensiveness row: the Marcus rate parameters and
the curvature. -/
structure HammondMarcusSharpCtx where
  A : ℝ
  kB : ℝ
  T : ℝ
  lam : ℝ

/-- The Marcus pre-exponential factor is positive. -/
def pHammondMarcusAPositive : Premise HammondMarcusSharpCtx :=
  mkPremise "hammondMarcusSharp.preExponentialPositive" fun δ => 0 < δ.A

/-- The Boltzmann constant is positive. -/
def pHammondMarcusKBPositive : Premise HammondMarcusSharpCtx :=
  mkPremise "hammondMarcusSharp.boltzmannPositive" fun δ => 0 < δ.kB

/-- The temperature is positive. -/
def pHammondMarcusTPositive : Premise HammondMarcusSharpCtx :=
  mkPremise "hammondMarcusSharp.temperaturePositive" fun δ => 0 < δ.T

/-- The explicit premise set of the equivalence. -/
def hammondMarcusSharpPremises : List (Premise HammondMarcusSharpCtx) :=
  [pHammondMarcusAPositive, pHammondMarcusKBPositive, pHammondMarcusTPositive]

/-- The comparison: Hammond's structural descriptor against the Marcus rate descriptor
(everywhere-positive rate plus the inverted-region description). -/
def hammondMarcusSharpComparison : Comparison HammondMarcusSharpCtx :=
  Comparison.ofPredicates
    (mkStatementRef "PhotoLean.Hammond" "PhotoLean.Hammond.HammondDescriptor"
      "HammondMarcusSharpCtx"
      "PhotoLean/Hammond/Sharp.lean#hammond_sharp; PhotoLean/Relations.lean §6 hammond_sharp_iff_marcus_sharp")
    (mkStatementRef "PhotoLean.Marcus" "PhotoLean.Marcus.rateDescriptor"
      "HammondMarcusSharpCtx"
      "PhotoLean/Marcus/Sharp.lean#descriptor_sharp; PhotoLean/Relations.lean §6 hammond_sharp_iff_marcus_sharp")
    (fun δ => Hammond.HammondDescriptor δ.lam)
    (fun δ =>
      (∀ x : ℝ, 0 < Marcus.rate δ.A δ.lam δ.kB δ.T x) ∧
        Marcus.InvertedDescriptor δ.A δ.lam δ.kB δ.T)

/-- The typed equivalence link of the row. Its soundness is the delivered theorem
`hammond_sharp_iff_marcus_sharp`, applied to the three explicit premises. -/
noncomputable def hammondMarcusSharpLink : ParentCertificate HammondMarcusSharpCtx :=
  .equivalence
    "PhotoLean.RelationAudit.Full.Sections06_10.hammond_sharp_iff_marcus_sharp"
    hammondMarcusSharpComparison hammondMarcusSharpPremises
    (fun δ hprem =>
      PhotoLean.Relations.hammond_sharp_iff_marcus_sharp
        (hprem pHammondMarcusAPositive (by simp [hammondMarcusSharpPremises]))
        (hprem pHammondMarcusKBPositive (by simp [hammondMarcusSharpPremises]))
        (hprem pHammondMarcusTPositive (by simp [hammondMarcusSharpPremises]))
        δ.lam)

/-- **Certified §6 equivalence**: Hammond's structural descriptor holds exactly when the Marcus
rate is everywhere positive and the inverted-region description holds. -/
noncomputable def hammondMarcusSharpCertificate : Certificate HammondMarcusSharpCtx :=
  .equivalence hammondMarcusSharpLink rfl

/-- Kind pin: the §6 row is a certified equivalence. -/
theorem hammondMarcusSharpCertificate_kind :
    certificateKind hammondMarcusSharpCertificate = RelationKind.equivalence := rfl

/-- Premise pin: the certificate carries exactly the three positivity premises. -/
theorem hammondMarcusSharpCertificate_premiseIDs :
    certificatePremiseIDs hammondMarcusSharpCertificate =
      ["hammondMarcusSharp.preExponentialPositive",
       "hammondMarcusSharp.boltzmannPositive",
       "hammondMarcusSharp.temperaturePositive"] := rfl

/-- Forward direction exercised through the typed parent: at every context point satisfying the
premises, the Hammond descriptor entails the Marcus rate descriptor. -/
theorem hammondMarcusSharpLink_forward (δ : HammondMarcusSharpCtx)
    (hprem : ∀ p ∈ hammondMarcusSharpPremises, p.predicate δ)
    (h : Hammond.HammondDescriptor δ.lam) :
    (∀ x : ℝ, 0 < Marcus.rate δ.A δ.lam δ.kB δ.T x) ∧
      Marcus.InvertedDescriptor δ.A δ.lam δ.kB δ.T :=
  hammondMarcusSharpLink.forward δ hprem h

/-- Backward direction exercised through the typed parent: the Marcus rate descriptor entails the
Hammond descriptor. The `rfl` form proof is the type-level guard that the parent is an
equivalence, so its reverse direction is available. -/
theorem hammondMarcusSharpLink_backward (δ : HammondMarcusSharpCtx)
    (hprem : ∀ p ∈ hammondMarcusSharpPremises, p.predicate δ)
    (h : (∀ x : ℝ, 0 < Marcus.rate δ.A δ.lam δ.kB δ.T x) ∧
      Marcus.InvertedDescriptor δ.A δ.lam δ.kB δ.T) :
    Hammond.HammondDescriptor δ.lam :=
  hammondMarcusSharpLink.backward rfl δ hprem h

/-! ## §7 — Kasha internal-conversion rate is the kernel barrier rate (certified definitional pin)

The delivered theorem `PhotoLean.Relations.kernel_marcusIC` holds by `rfl` after unfolding the
three definitions (`Kasha.marcusIC`, `Kernel.barrier`, `Marcus.barrier`). The pin below carries a
fresh `DefEq.refl` over the five-parameter context; it is a definitional identity, not
propositional equality and not a physical-identity claim. -/

/-- Shared context of the kernel pin: the Kasha/Marcus rate parameters. -/
structure KernelMarcusICCtx where
  A : ℝ
  lam : ℝ
  kB : ℝ
  T : ℝ
  x : ℝ

/-- The definitional pin: the Kasha internal-conversion rate against the Marcus rate law written
with the kernel barrier. -/
noncomputable def kernelMarcusICPin : Certificate KernelMarcusICCtx :=
  .definitionalIdentity
    { left := mkStatementRef "PhotoLean.Kasha" "PhotoLean.Kasha.marcusIC"
        "KernelMarcusICCtx"
        "PhotoLean/Kasha/Compose.lean#marcusIC; PhotoLean/Relations.lean §7 kernel_marcusIC"
      right := mkStatementRef "PhotoLean.Kernel" "PhotoLean.Kernel.barrierRate"
        "KernelMarcusICCtx"
        "PhotoLean/Kernel.lean#barrier; PhotoLean/Relations.lean §7 kernel_marcusIC"
      leftContext := KernelMarcusICCtx
      rightContext := KernelMarcusICCtx
      codomain := ℝ
      leftTranslation := fun δ => δ
      rightTranslation := fun δ => δ
      leftTerm := fun δ => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x
      rightTerm := fun δ =>
        δ.A * Real.exp (-(Kernel.barrier δ.lam δ.x) / (δ.kB * δ.T))
      same := DefEq.refl }
    []

/-- Pointwise `rfl` witness of the kernel pin. -/
theorem kernelMarcusICPin_rfl (δ : KernelMarcusICCtx) :
    Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x =
      δ.A * Real.exp (-(Kernel.barrier δ.lam δ.x) / (δ.kB * δ.T)) := rfl

/-- Function-level `DefEq` witness of the kernel pin, matching the certificate's `same` field. -/
theorem kernelMarcusICPin_defeq :
    DefEq (fun δ : KernelMarcusICCtx => Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x)
      (fun δ : KernelMarcusICCtx =>
        δ.A * Real.exp (-(Kernel.barrier δ.lam δ.x) / (δ.kB * δ.T))) :=
  DefEq.refl

/-- Kind pin: the §7 row is a definitional identity. -/
theorem kernelMarcusICPin_kind :
    certificateKind kernelMarcusICPin = RelationKind.definitionalIdentity := rfl

/-- Premise pin: the definitional pin has no premises. -/
theorem kernelMarcusICPin_premiseIDs :
    certificatePremiseIDs kernelMarcusICPin = [] := rfl

/-! ## §8 — reclassified composition-shaped rows (evidence only, **not** certificates)

The four §8 declarations are preserved verbatim below so a reviewer can see that the statements
elaborate against the delivered modules. They are deliberately **not** wrapped in `Certificate`
constructors. See the JSON fragment for the per-row rationale and target category
`model-level-composition`.

* `linearVolcano_eq_bepTangent` is a term-level identity between the Sabatier linear volcano and
  the maximum of the two BEP tangent lines. The proof is `unfold` plus `ring`; it is not `rfl`, so
  it is not a definitional identity, and it is not a two-parent typed composition.
* `linearVolcano_le_parabolic` is a pointwise order inequality between the linear and the
  two-parabola model functionals; the seven certified kinds have no inequality/order constructor.
* `parabolic_descriptor` asserts that the Sabatier descriptor holds for the BEP-instantiated
  composite barrier; it is a property of one composite model, not a relation between two theory
  predicates.
* `linearVolcano_apex_exact` is a pointwise value identity at the symmetric apex; it consumes
  `BEP.bepLine_at_zero` and `BEP.eact_at_zero`, so it is not definitional either. -/

/-- §8 reclassification evidence: the linear volcano is the maximum of the two BEP tangent lines.
This re-export is **not** a relation certificate. -/
theorem section08_linearVolcano_eq_bepTangent (lam1 lam2 dE : ℝ) :
    Sabatier.volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE =
      max (BEP.bepLine lam1 (-dE)) (BEP.bepLine lam2 dE) :=
  PhotoLean.Relations.linearVolcano_eq_bepTangent lam1 lam2 dE

/-- §8 reclassification evidence: the linear volcano is a pointwise lower bound on the
two-parabola volcano. This re-export is **not** a relation certificate. -/
theorem section08_linearVolcano_le_parabolic {lam1 lam2 : ℝ}
    (h1 : 0 < lam1) (h2 : 0 < lam2) (dE : ℝ) :
    Sabatier.volcanoBarrier (1 / 2) (lam1 / 4) (1 / 2) (lam2 / 4) dE ≤
      Sabatier.parabolicBarrier lam1 lam2 dE :=
  PhotoLean.Relations.linearVolcano_le_parabolic h1 h2 dE

/-- §8 reclassification evidence: the Sabatier descriptor holds in the two-parabola model. This
re-export is **not** a relation certificate. -/
theorem section08_parabolic_descriptor {lam1 lam2 : ℝ}
    (h1 : 0 < lam1) (h2 : 0 < lam2) :
    Sabatier.VolcanoDescriptor (fun dE => Sabatier.parabolicBarrier lam1 lam2 dE)
      (Sabatier.apexPar lam1 lam2) :=
  PhotoLean.Relations.parabolic_descriptor h1 h2

/-- §8 reclassification evidence: at a symmetric cycle's apex the linear and parabolic volcano
models agree exactly. This re-export is **not** a relation certificate. -/
theorem section08_linearVolcano_apex_exact {lam : ℝ} (h : 0 < lam) :
    Sabatier.volcanoBarrier (1 / 2) (lam / 4) (1 / 2) (lam / 4) 0 =
      Sabatier.parabolicBarrier lam lam 0 :=
  PhotoLean.Relations.linearVolcano_apex_exact h

end Sections06_10
end Full
end RelationAudit
end PhotoLean
