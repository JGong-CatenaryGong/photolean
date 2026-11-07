/-
PhotoLean.RelationAudit.Defs — the semantic core of the certified relation layer.

This module is additive: it imports `Mathlib` only and changes no delivered theory module.
It fixes the vocabulary of `docs/RELATION-AUDIT-CONTRACT.md`:

* a statement reference carries theory, stable statement ID, artifact version, context label and
  source provenance;
* a comparison carries a shared context `Δ`, a translation of `Δ` into each statement context,
  and the two predicates after translation;
* a premise is a named predicate on `Δ`, so premise propagation can be tracked by premise ID;
* `Certificate` is a sum type whose seven constructors each carry the kind-specific semantic
  proof. `certificateKind` is a computable projection, so a manifest row can be pinned by
  `example : certificateKind cert = RelationKind.<kind> := rfl`;
* `DefEq` is a **definitional** equality type: its only constructor is `refl`, so an inhabitant
  exists exactly when the elaborator accepts the two translated terms as definitionally equal.
  It is deliberately not propositional equality and is not a physical-identity certificate.

`unresolved`, `notEstablished` and `outOfScope` are audit statuses, not certified relation kinds;
they therefore live in `AuditStatus`, outside `Certificate`.

## Proof-relevant conditional composition

`ConditionalComposition` is not a record of parent names plus an independent child proof. A
parent is a `ParentCertificate`: a type-indexed implication or equivalence that carries its own
premises and entailment proof. The composition stores two such typed parents, a
`MiddleAlignment` relating the right predicate of the left parent to the left predicate of the
right parent, a typed `PremiseCoverage` for premise propagation (inheritance or an explicit
`Discharge`), and the explicitly declared bridge premises. The child comparison and the child
conclusion form are **computed** from the parents, and `ConditionalComposition.sound` derives
the child conclusion by applying the two parent entailments through the alignment. There is no
field into which an unrelated child proof could be placed.

The parent IDs and premise IDs needed by the manifest validator are computable projections:
`certificateParentIDs`, `certificateParentKinds`, `certificateParentPremiseIDs`,
`certificateBridgeIDs`, `certificateDischargeIDs`, `certificateMediating` and
`certificateCompositionForm`.

Representational limitations, stated so the manifest layer does not over-read the Lean side:

* `StatementRef.artifactVersion` is a snapshot label; content hashes remain in the JSON snapshot
  layer and are not computed in Lean;
* `DefinitionalPin` pins translated *terms* (functions), which is the shape of the delivered
  `rfl` certificates; it does not turn propositional equality into definitional equality;
* channel lists are homogeneous in their observed-value and input types, so channels with
  different types need separate certificates;
* the composition parent ID is a stable name string carried by the typed parent; resolving that
  string against the manifest certificate table is the validator's job, not Lean's;
* `Discharge` is part of the representation and is consumed by `PremiseDerivation.discharged`;
  the pilot propagates every parent premise by inheritance, so its discharge lists are empty;
* a `rfl` pin over `ℝ` still reports `propext`, `Classical.choice` and `Quot.sound` in
  `#print axioms` because `ℝ` is a quotient type. The definitional guarantee is the fresh `rfl`
  elaboration, not an empty axiom footprint; the audit applies the same infrastructure-axiom
  whitelist to certificates and definitional witnesses.

There is no unproved placeholder and no custom axiomatic declaration in this file.
-/
import Mathlib

universe u v

namespace PhotoLean
namespace RelationAudit

/-! ## Relation kinds -/

/-- The seven certified relation kinds of the audit contract. -/
inductive RelationKind where
  | definitionalIdentity
  | implication
  | equivalence
  | conditionalComposition
  | observationalEquivalence
  | distinguishability
  | refutation
  deriving DecidableEq, Repr

/-- The manifest tag of a relation kind (the exact camelCase spelling of the contract). -/
def RelationKind.tag : RelationKind → String
  | .definitionalIdentity => "definitionalIdentity"
  | .implication => "implication"
  | .equivalence => "equivalence"
  | .conditionalComposition => "conditionalComposition"
  | .observationalEquivalence => "observationalEquivalence"
  | .distinguishability => "distinguishability"
  | .refutation => "refutation"

/-- Audit statuses. These are **not** certified relation kinds: a record with one of these
statuses is not a certificate, and the validator must not treat it as one. -/
inductive AuditStatus where
  | certified
  | unresolved
  | notEstablished
  | outOfScope
  deriving DecidableEq, Repr

/-! ## Statement references and premises -/

/-- A statement reference: theory, stable statement ID, artifact version/hash, context label and
source provenance. -/
structure StatementRef where
  theory : String
  statementId : String
  artifactVersion : String
  context : String
  provenance : String
  deriving Repr, DecidableEq

/-- A named premise on the shared context. Its ID is the unit of premise propagation. -/
structure Premise (Δ : Type) where
  id : String
  predicate : Δ → Prop

/-- An explicit discharge certificate: an omitted parent premise is derived from a declared list
of retained premises. `PremiseDerivation.discharged` consumes this certificate, so a composition
may omit a parent premise only through typed discharge evidence. -/
structure Discharge (Δ : Type) where
  premise : Premise Δ
  retained : List (Premise Δ)
  entails : ∀ δ, (∀ p ∈ retained, p.predicate δ) → premise.predicate δ

/-- The ID of the premise a discharge certificate removes from the composition's premise set. -/
def Discharge.premiseID {Δ : Type} (d : Discharge Δ) : String := d.premise.id

/-- The premise IDs of a list of premises. -/
def premiseIDs {Δ : Type} (ps : List (Premise Δ)) : List String := ps.map Premise.id

/-! ## Definitional equality and cross-context comparison -/

/-- Definitional equality of dependent functions: the sole constructor is `refl`, so the
elaborator must accept the two functions as definitionally equal. This is the certificate used by
`Certificate.definitionalIdentity`; it is not propositional equality. -/
inductive DefEq {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) :
    ((a : α) → β a) → Prop where
  | refl : DefEq f f

/-- A cross-context definitional pin: a shared context `Δ`, translations into the two statement
contexts, two terms, and a fresh `rfl`-only definitional equality of the translated terms. -/
structure DefinitionalPin (Δ : Type) where
  left : StatementRef
  right : StatementRef
  leftContext : Type
  rightContext : Type
  codomain : Type
  leftTranslation : Δ → leftContext
  rightTranslation : Δ → rightContext
  leftTerm : leftContext → codomain
  rightTerm : rightContext → codomain
  same : DefEq (fun δ => leftTerm (leftTranslation δ))
               (fun δ => rightTerm (rightTranslation δ))

/-- A cross-theory comparison on the shared context `Δ`: a translation into each statement
context and the two predicates after translation. -/
structure Comparison (Δ : Type) where
  left : StatementRef
  right : StatementRef
  leftContext : Type
  rightContext : Type
  leftTranslation : Δ → leftContext
  rightTranslation : Δ → rightContext
  leftPredicate : leftContext → Prop
  rightPredicate : rightContext → Prop

/-- The left predicate after translation. -/
def Comparison.leftOn {Δ : Type} (c : Comparison Δ) (δ : Δ) : Prop :=
  c.leftPredicate (c.leftTranslation δ)

/-- The right predicate after translation. -/
def Comparison.rightOn {Δ : Type} (c : Comparison Δ) (δ : Δ) : Prop :=
  c.rightPredicate (c.rightTranslation δ)

/-- Build a comparison whose two statement contexts ARE the shared context (identity
translations). Used by the pilot rows; the general structure keeps translations explicit. -/
def Comparison.ofPredicates {Δ : Type} (left right : StatementRef) (P Q : Δ → Prop) :
    Comparison Δ where
  left := left
  right := right
  leftContext := Δ
  rightContext := Δ
  leftTranslation := fun δ => δ
  rightTranslation := fun δ => δ
  leftPredicate := P
  rightPredicate := Q

/-! ## Observational channels and distinguishability forms -/

/-- The two interpretations compared by an observational-equivalence or distinguishability row. -/
structure ObservationalSetup (Δ : Type) where
  left : StatementRef
  right : StatementRef
  leftState : Type
  rightState : Type
  leftInterp : Δ → leftState
  rightInterp : Δ → rightState

/-- A declared observation channel. The observed value type and the input type are explicit
parameters, so a certificate's channel list is homogeneous in them; the Stern–Volmer *joint*
intensity–lifetime channel uses the pair type as `Obs`. A certificate that needs channels with
different input or value types must be split into several certificates — a representational
limitation reported to the lead. -/
structure Channel (Δ : Type) (setup : ObservationalSetup Δ) (Obs : Type) (input : Type) where
  name : String
  domain : Set input
  leftObs : setup.leftState → input → Obs
  rightObs : setup.rightState → input → Obs

/-- The two admissible forms of a distinguishability certificate. They are separate constructors,
so the separating-observation form and the identifiability/decoder form remain distinguishable
in the certificate itself (not only in prose). -/
inductive DistinguishabilityWitness (Δ : Type) where
  | separatingObservation
      (setup : ObservationalSetup Δ) (Obs input : Type)
      (channel : Channel Δ setup Obs input)
      (premises : List (Premise Δ)) (witness : Δ)
      (hpremise : ∀ p ∈ premises, p.predicate witness)
      (x : input) (hx : x ∈ channel.domain)
      (separates : channel.leftObs (setup.leftInterp witness) x ≠
        channel.rightObs (setup.rightInterp witness) x)
  | identifiabilityDecoder
      (setup : ObservationalSetup Δ) (premises : List (Premise Δ))
      (Obs Candidate : Type) (observe : Δ → Obs) (candidateOf : Δ → Candidate)
      (decode : Obs → Candidate)
      (correct : ∀ δ, (∀ p ∈ premises, p.predicate δ) → decode (observe δ) = candidateOf δ)

/-- The premise list carried by a distinguishability witness form. -/
def DistinguishabilityWitness.premises {Δ : Type} :
    DistinguishabilityWitness Δ → List (Premise Δ)
  | .separatingObservation _ _ _ _ ps _ _ _ _ _ => ps
  | .identifiabilityDecoder _ ps _ _ _ _ _ _ => ps

/-- Which of the two distinguishability forms is carried. -/
def DistinguishabilityWitness.formTag {Δ : Type} :
    DistinguishabilityWitness Δ → String
  | .separatingObservation .. => "separatingObservation"
  | .identifiabilityDecoder .. => "identifiabilityDecoder"

/-! ## Conditional composition: typed parents, alignment, and premise propagation -/

/-- The two composable link forms. A composition of a chain of implications and equivalences is
an implication unless **both** parents are equivalences, in which case it is an equivalence. -/
inductive CompositionForm where
  | implication
  | equivalence
  deriving DecidableEq, Repr

/-- The relation kind of a composable link form. -/
def CompositionForm.kind : CompositionForm → RelationKind
  | .implication => .implication
  | .equivalence => .equivalence

/-- The conclusion of a link at one context point. -/
def CompositionForm.ConclusionAt {Δ : Type} (f : CompositionForm) (P Q : Δ → Prop)
    (δ : Δ) : Prop :=
  match f with
  | .implication => P δ → Q δ
  | .equivalence => P δ ↔ Q δ

/-- The conclusion form of a chain: only two equivalences compose to an equivalence. -/
def CompositionForm.compose : CompositionForm → CompositionForm → CompositionForm
  | .equivalence, .equivalence => .equivalence
  | _, _ => .implication

/-- A typed parent certificate of a conditional composition. It is not a name: it carries the
parent's comparison, its premise list, its composable form, and the kind-specific entailment that
the composition combinator consumes. A definitional-identity or observational certificate cannot
be used as a parent of an entailment chain. -/
inductive ParentCertificate (Δ : Type) where
  /-- Parent link with kind `implication`: `Π → (P → Q)`. -/
  | implication (id : String) (cmp : Comparison Δ) (premises : List (Premise Δ))
      (sound : ∀ δ, (∀ p ∈ premises, p.predicate δ) → cmp.leftOn δ → cmp.rightOn δ)
  /-- Parent link with kind `equivalence`: `Π → (P ↔ Q)`. -/
  | equivalence (id : String) (cmp : Comparison Δ) (premises : List (Premise Δ))
      (sound : ∀ δ, (∀ p ∈ premises, p.predicate δ) → (cmp.leftOn δ ↔ cmp.rightOn δ))

/-- The stable parent ID carried by a typed parent certificate. -/
def ParentCertificate.id {Δ : Type} : ParentCertificate Δ → String
  | .implication id _ _ _ => id
  | .equivalence id _ _ _ => id

/-- The parent comparison. -/
def ParentCertificate.cmp {Δ : Type} : ParentCertificate Δ → Comparison Δ
  | .implication _ cmp _ _ => cmp
  | .equivalence _ cmp _ _ => cmp

/-- The parent premise list. -/
def ParentCertificate.premises {Δ : Type} : ParentCertificate Δ → List (Premise Δ)
  | .implication _ _ ps _ => ps
  | .equivalence _ _ ps _ => ps

/-- The composable form of a typed parent. -/
def ParentCertificate.form {Δ : Type} : ParentCertificate Δ → CompositionForm
  | .implication .. => .implication
  | .equivalence .. => .equivalence

/-- The relation kind of a typed parent. -/
def ParentCertificate.kind {Δ : Type} (p : ParentCertificate Δ) : RelationKind :=
  p.form.kind

/-- The premise IDs of a typed parent. -/
def ParentCertificate.premiseIDs {Δ : Type} (p : ParentCertificate Δ) : List String :=
  p.premises.map Premise.id

/-- The forward direction of a typed parent, available for both composable forms. -/
def ParentCertificate.forward {Δ : Type} (p : ParentCertificate Δ) (δ : Δ)
    (hprem : ∀ q ∈ p.premises, q.predicate δ) (h : p.cmp.leftOn δ) : p.cmp.rightOn δ := by
  cases p with
  | implication id cmp ps sound => exact sound δ hprem h
  | equivalence id cmp ps sound => exact (sound δ hprem).mp h

/-- The backward direction of an equivalence parent. The proof obligation `p.form = .equivalence`
rules out implication parents at the type level: they cannot be used as the reverse half of an
equivalence chain. -/
def ParentCertificate.backward {Δ : Type} (p : ParentCertificate Δ)
    (hform : p.form = .equivalence) (δ : Δ)
    (hprem : ∀ q ∈ p.premises, q.predicate δ) (h : p.cmp.rightOn δ) : p.cmp.leftOn δ := by
  cases p with
  | implication id cmp ps sound => cases hform
  | equivalence id cmp ps sound => exact (sound δ hprem).mpr h

/-- Typed middle-endpoint alignment: the right predicate of the left parent is the left predicate
of the right parent. This is the connection the composition consumes; a name or an independent
child proof cannot replace it. -/
structure MiddleAlignment {Δ : Type} (left right : ParentCertificate Δ) : Prop where
  agree : ∀ δ, left.cmp.rightOn δ ↔ right.cmp.leftOn δ

/-- A typed derivation that a parent premise follows from the child premise list. The
`inherited` form consumes the actual premise value; the `discharged` form consumes an explicit
`Discharge` and requires every retained premise to be inherited. -/
inductive PremiseDerivation {Δ : Type} (child : List (Premise Δ)) : Premise Δ → Prop where
  | inherited {p : Premise Δ} (h : p ∈ child) : PremiseDerivation child p
  | discharged {p : Premise Δ} (d : Discharge Δ) (hp : p = d.premise)
      (hretained : ∀ q ∈ d.retained, q ∈ child) : PremiseDerivation child p

/-- Semantics of a premise derivation: child premises are enough to satisfy the parent premise. -/
def PremiseDerivation.sound {Δ : Type} {child : List (Premise Δ)} {p : Premise Δ}
    {δ : Δ} (hchild : ∀ q ∈ child, q.predicate δ) (d : PremiseDerivation child p) :
    p.predicate δ := by
  cases d with
  | inherited h => exact hchild p h
  | discharged disch hp hretained =>
      rw [hp]
      exact disch.entails δ (fun q hq => hchild q (hretained q hq))

/-- Premise propagation for a whole parent-premise list: every parent premise is inherited or
explicitly discharged. -/
structure PremiseCoverage (Δ : Type) (child parents : List (Premise Δ)) where
  covered : ∀ p ∈ parents, PremiseDerivation child p

/-- Semantics of premise coverage. -/
def PremiseCoverage.sound {Δ : Type} {child parents : List (Premise Δ)}
    (c : PremiseCoverage Δ child parents) {δ : Δ}
    (hchild : ∀ p ∈ child, p.predicate δ) : ∀ p ∈ parents, p.predicate δ :=
  fun p hp => PremiseDerivation.sound hchild (c.covered p hp)

/-- A proof-relevant conditional composition.

The two parents are typed `ParentCertificate`s, not names. The middle predicate is aligned by
`alignment`; parent premises propagate through `parentCoverage`; bridge premises are explicit and
must occur in the child premise list. The child comparison and child form are computed from the
parents by `ConditionalComposition.cmp` and `ConditionalComposition.form`, and the child proof is
computed by `ConditionalComposition.sound`. There is deliberately no field that accepts an
independent proof of the child conclusion. A bridge list may be empty when the two parent
contexts already align. -/
structure ConditionalComposition (Δ : Type) where
  left : ParentCertificate Δ
  right : ParentCertificate Δ
  premises : List (Premise Δ)
  bridge : List (Premise Δ)
  alignment : MiddleAlignment left right
  parentCoverage : PremiseCoverage Δ premises (left.premises ++ right.premises)
  bridgeCoverage : ∀ b ∈ bridge, b ∈ premises
  discharges : List (Discharge Δ)

namespace ConditionalComposition

/-- The child comparison: the left endpoint of the left parent and the right endpoint of the
right parent. It is computed, not supplied by the caller. -/
def cmp {Δ : Type} (d : ConditionalComposition Δ) : Comparison Δ where
  left := d.left.cmp.left
  right := d.right.cmp.right
  leftContext := d.left.cmp.leftContext
  rightContext := d.right.cmp.rightContext
  leftTranslation := d.left.cmp.leftTranslation
  rightTranslation := d.right.cmp.rightTranslation
  leftPredicate := d.left.cmp.leftPredicate
  rightPredicate := d.right.cmp.rightPredicate

/-- The child form: an equivalence only when both parents are equivalences. -/
def form {Δ : Type} (d : ConditionalComposition Δ) : CompositionForm :=
  d.left.form.compose d.right.form

/-- **The sound composition combinator.** The child conclusion is obtained by applying the left
parent's forward entailment, transporting the aligned middle proposition, and applying the right
parent's forward entailment. In the equivalence case the two backward entailments are used for
the reverse direction. The proof therefore consumes the typed parents, the alignment, and the
propagated premises; it is not an independent proof of the child conclusion. -/
theorem sound {Δ : Type} (d : ConditionalComposition Δ) :
    ∀ δ, (∀ p ∈ d.premises, p.predicate δ) →
      CompositionForm.ConclusionAt d.form d.cmp.leftOn d.cmp.rightOn δ := by
  intro δ hprem
  obtain ⟨left, right, premises, bridge, alignment, parentCoverage, bridgeCoverage,
    discharges⟩ := d
  have hparents : ∀ p ∈ left.premises ++ right.premises, p.predicate δ :=
    parentCoverage.sound hprem
  have hLprem : ∀ p ∈ left.premises, p.predicate δ :=
    fun p hp => hparents p (List.mem_append_left _ hp)
  have hRprem : ∀ p ∈ right.premises, p.predicate δ :=
    fun p hp => hparents p (List.mem_append_right _ hp)
  have halign := alignment.agree δ
  cases left with
  | implication lid lcmp lps lsound =>
    cases right with
    | implication rid rcmp rps rsound =>
      simp only [ConditionalComposition.form, ConditionalComposition.cmp, ParentCertificate.form,
        CompositionForm.compose, CompositionForm.ConclusionAt]
      intro hP
      exact rsound δ hRprem (halign.mp (lsound δ hLprem hP))
    | equivalence rid rcmp rps rsound =>
      simp only [ConditionalComposition.form, ConditionalComposition.cmp, ParentCertificate.form,
        CompositionForm.compose, CompositionForm.ConclusionAt]
      intro hP
      exact (rsound δ hRprem).mp (halign.mp (lsound δ hLprem hP))
  | equivalence lid lcmp lps lsound =>
    cases right with
    | implication rid rcmp rps rsound =>
      simp only [ConditionalComposition.form, ConditionalComposition.cmp, ParentCertificate.form,
        CompositionForm.compose, CompositionForm.ConclusionAt]
      intro hP
      exact rsound δ hRprem (halign.mp ((lsound δ hLprem).mp hP))
    | equivalence rid rcmp rps rsound =>
      simp only [ConditionalComposition.form, ConditionalComposition.cmp, ParentCertificate.form,
        CompositionForm.compose, CompositionForm.ConclusionAt]
      constructor
      · intro hP
        exact (rsound δ hRprem).mp (halign.mp ((lsound δ hLprem).mp hP))
      · intro hS
        exact (lsound δ hLprem).mpr (halign.mpr ((rsound δ hRprem).mpr hS))

end ConditionalComposition

/-! ## The certificate sum type -/

/-- A certified relation record. Every constructor carries the proof shape demanded by the
contract for its kind; the kind is recovered by the computable `certificateKind`. -/
inductive Certificate (Δ : Type) where
  /-- Definitional identity after the declared translation, certified by a fresh `rfl`-only
  `DefEq`. -/
  | definitionalIdentity (pin : DefinitionalPin Δ) (premises : List (Premise Δ))
  /-- One-way implication `Π → (P → Q)`, carried by a typed parent link. -/
  | implication (link : ParentCertificate Δ) (hform : link.form = .implication)
  /-- Equivalence `Π → (P ↔ Q)`, carried by a typed parent link. -/
  | equivalence (link : ParentCertificate Δ) (hform : link.form = .equivalence)
  /-- Conditional composition, carried by the proof-relevant derivation below. -/
  | conditionalComposition (composition : ConditionalComposition Δ)
  /-- Observational equivalence: equality of every declared channel on every input in its
  declared domain, at every context point satisfying the premises. -/
  | observationalEquivalence (setup : ObservationalSetup Δ) (premises : List (Premise Δ))
      (Obs input : Type) (channels : List (Channel Δ setup Obs input))
      (hchannels : 1 ≤ channels.length)
      (sound : ∀ δ, (∀ p ∈ premises, p.predicate δ) →
        ∀ c ∈ channels, ∀ x : input, x ∈ c.domain →
          c.leftObs (setup.leftInterp δ) x = c.rightObs (setup.rightInterp δ) x)
  /-- Distinguishability, in one of the two explicit forms. -/
  | distinguishability (witness : DistinguishabilityWitness Δ)
  /-- Refutation of the implication `P → Q`: an explicit context point satisfying the premises,
  the antecedent and the negation of the consequent. -/
  | refutation (cmp : Comparison Δ) (premises : List (Premise Δ))
      (counterexample : ∃ δ, (∀ p ∈ premises, p.predicate δ) ∧ cmp.leftOn δ ∧ ¬ cmp.rightOn δ)

/-- The certified kind of a certificate. Computable, so a manifest row is pinned by
`example : certificateKind cert = RelationKind.<kind> := rfl`, and an implication cannot be
relabelled as a definitional identity or as an observational equivalence. -/
def certificateKind {Δ : Type} : Certificate Δ → RelationKind
  | .definitionalIdentity .. => .definitionalIdentity
  | .implication .. => .implication
  | .equivalence .. => .equivalence
  | .conditionalComposition .. => .conditionalComposition
  | .observationalEquivalence .. => .observationalEquivalence
  | .distinguishability .. => .distinguishability
  | .refutation .. => .refutation

/-- The premise IDs carried by a certificate. For a composition these are the child premise IDs
(the premises under which the computed child conclusion holds), not the parent-name metadata. -/
def certificatePremiseIDs {Δ : Type} : Certificate Δ → List String
  | .definitionalIdentity _ ps => premiseIDs ps
  | .implication link _ => link.premiseIDs
  | .equivalence link _ => link.premiseIDs
  | .conditionalComposition d => premiseIDs d.premises
  | .observationalEquivalence _ ps _ _ _ _ _ => premiseIDs ps
  | .distinguishability w => premiseIDs (DistinguishabilityWitness.premises w)
  | .refutation _ ps _ => premiseIDs ps

/-- Computable composition metadata exposed for the manifest validator. Parent IDs are the stable
names carried by the typed parents; premise IDs are separated into child, parent and bridge
groups so a validator can pin each group without re-deriving it from prose. -/
structure CompositionMetadata where
  childPremiseIDs : List String
  parentIDs : List String
  parentKinds : List RelationKind
  parentPremiseIDs : List (List String)
  bridgeIDs : List String
  dischargeIDs : List String
  mediating : StatementRef
  form : CompositionForm
  deriving Repr, DecidableEq

/-- The composition metadata of a certificate, if it is a conditional composition. -/
def certificateComposition? {Δ : Type} : Certificate Δ → Option CompositionMetadata
  | .conditionalComposition d =>
      some
        { childPremiseIDs := premiseIDs d.premises
          parentIDs := [d.left.id, d.right.id]
          parentKinds := [d.left.kind, d.right.kind]
          parentPremiseIDs := [d.left.premiseIDs, d.right.premiseIDs]
          bridgeIDs := premiseIDs d.bridge
          dischargeIDs := d.discharges.map Discharge.premiseID
          mediating := d.left.cmp.right
          form := d.form }
  | _ => none

/-- Parent certificate IDs of a composition, in left-to-right order. Empty for other kinds. -/
def certificateParentIDs {Δ : Type} : Certificate Δ → List String
  | .conditionalComposition d => [d.left.id, d.right.id]
  | _ => []

/-- Parent certificate kinds of a composition, in left-to-right order. Empty for other kinds. -/
def certificateParentKinds {Δ : Type} : Certificate Δ → List RelationKind
  | .conditionalComposition d => [d.left.kind, d.right.kind]
  | _ => []

/-- Parent premise IDs of a composition, one list per parent. Empty for other kinds. -/
def certificateParentPremiseIDs {Δ : Type} : Certificate Δ → List (List String)
  | .conditionalComposition d => [d.left.premiseIDs, d.right.premiseIDs]
  | _ => []

/-- Bridge premise IDs of a composition. Empty for other kinds and for empty bridge lists. -/
def certificateBridgeIDs {Δ : Type} : Certificate Δ → List String
  | .conditionalComposition d => premiseIDs d.bridge
  | _ => []

/-- Discharge premise IDs declared by a composition. Empty for other kinds. -/
def certificateDischargeIDs {Δ : Type} : Certificate Δ → List String
  | .conditionalComposition d => d.discharges.map Discharge.premiseID
  | _ => []

/-- The mediating statement of a composition: the right endpoint of the left parent, which the
alignment identifies with the left endpoint of the right parent. -/
def certificateMediating? {Δ : Type} : Certificate Δ → Option StatementRef
  | .conditionalComposition d => some d.left.cmp.right
  | _ => none

/-- The computed child form of a composition. -/
def certificateCompositionForm? {Δ : Type} : Certificate Δ → Option CompositionForm
  | .conditionalComposition d => some d.form
  | _ => none

end RelationAudit
end PhotoLean
