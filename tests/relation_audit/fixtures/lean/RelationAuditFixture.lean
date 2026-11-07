-- Mock certificate module used only by the relation-audit fixture tests.
--
-- It mirrors the shape required by docs/RELATION-AUDIT-CONTRACT.md section 5:
-- a certificate sum type, a computable certificateKind function, and one
-- witness declaration per evidence row referenced by the fixtures.  It is
-- deliberately independent of the delivered PhotoLean theory modules so the
-- validator tests run before PhotoLean/RelationAudit/Defs.lean exists.

namespace RelationAuditFixture

inductive CertificateKind where
  | definitionalIdentity
  | implication
  | equivalence
  | conditionalComposition
  | observationalEquivalence
  | distinguishability
  | refutation
  deriving DecidableEq, Repr

inductive Certificate where
  | defId
  | impl
  | equiv
  | comp
  | obs
  | dist
  | refu

def certificateKind : Certificate -> CertificateKind
  | .defId => .definitionalIdentity
  | .impl => .implication
  | .equiv => .equivalence
  | .comp => .conditionalComposition
  | .obs => .observationalEquivalence
  | .dist => .distinguishability
  | .refu => .refutation

def certDefId : Certificate := .defId
def certImpl : Certificate := .impl
def certEquiv : Certificate := .equiv
def certComp : Certificate := .comp
def certObs : Certificate := .obs
def certDist : Certificate := .dist
def certRefu : Certificate := .refu

def aliasDef : Certificate := .defId

-- Canonical projections of the mock certificate values.  The real
-- `PhotoLean.RelationAudit` layer exposes the same shape; the fixture mirrors it
-- so the validator's generated definitional checks can be exercised without
-- importing the production module.  `cert-comp` is the binary composition of
-- `cert-impl` and `cert-equiv`, with one mediating endpoint.
inductive CompositionForm where
  | implication
  | equivalence

structure StatementRef where
  statementId : String

def certificatePremiseIDs : Certificate -> List String
  | .defId => []
  | .impl => ["p-adj"]
  | .equiv => ["p-pos"]
  | .comp => ["p-adj", "p-pos"]
  | .obs => []
  | .dist => []
  | .refu => []

def certificateParentIDs : Certificate -> List String
  | .comp => ["RelationAuditFixture.certImpl", "RelationAuditFixture.certEquiv"]
  | _ => []

def certificateParentKinds : Certificate -> List CertificateKind
  | .comp => [.implication, .equivalence]
  | _ => []

def certificateParentPremiseIDs : Certificate -> List (List String)
  | .comp => [["p-adj"], ["p-pos"]]
  | _ => []

def certificateBridgeIDs : Certificate -> List String
  | _ => []

def certificateDischargeIDs : Certificate -> List String
  | _ => []

def certificateMediating? : Certificate -> Option StatementRef
  | .comp => some ⟨"PhotoLean.Marcus"⟩
  | _ => none

def certificateCompositionForm? : Certificate -> Option CompositionForm
  | .comp => some .implication
  | _ => none

-- Premise signatures.  Binder names are the ones claimed by the fixtures.
theorem lemmaImpl (hAdj : True) : True := True.intro
theorem lemmaEquiv (hPos : True) : True := True.intro

-- Badge evidence.
theorem witnessImpl : True := True.intro
theorem witnessNoAdj : True := True.intro
theorem witnessEquiv : True := True.intro
theorem witnessNoPos : True := True.intro
theorem minimalityImpl : True := True.intro

-- Kind-specific / composition evidence.
theorem bridgeWitness : True := True.intro
theorem distWitness : True := True.intro
theorem refuWitness : True := True.intro
theorem rflWitness : True := True.intro

-- A definitional witness that legitimately depends on the standard classical
-- axiom.  Contract section 5 applies the usual allowed-axiom whitelist to
-- definitional witnesses; the fresh `rfl` check is what establishes
-- definitional identity, so this must not be rejected for its footprint.
noncomputable def rflWitnessClassical : Certificate :=
  Classical.choice (show Nonempty Certificate from ⟨Certificate.defId⟩)

end RelationAuditFixture
