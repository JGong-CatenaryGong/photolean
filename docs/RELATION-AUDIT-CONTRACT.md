# Relation Audit Contract v1 — Lead Design Freeze

This file is the architecture contract for the isolated implementation. It does not change the delivered theory modules. Implementation deviations must be reported to the lead rather than silently redefining a relation kind.

## 1. Scope and non-claims

PhotoLean formal genealogy is a synchronic relational layer, not a historical reconstruction. Human or AI agents may propose theory readings and candidate relations. The audit decides only whether the registered certificate and metadata satisfy the declared relation semantics. It does not discover all relations, prove source fidelity, prove empirical adequacy, or prove that an unregistered relation cannot exist.

## 2. Artifact layout

- `PhotoLean/RelationAudit/Defs.lean`: common semantic predicates and certificate sum type.
- `PhotoLean/RelationAudit/Pilot.lean`: representative certified records reusing existing declarations.
- `PhotoLean/RelationAudit.lean`: umbrella import.
- `relation_audit/schema.json`: manifest schema.
- `relation_audit/pilot.json`: pilot registry and audit records.
- `tools/relation_audit.py` and `tools/relation_audit/**`: fail-closed validator and exporters.
- `tests/relation_audit/**`: valid and invalid fixtures plus mutation tests.
- `docs/RELATION-AUDIT.md`: user-facing semantics and reproduction guide.

Later full migration adds `relation_audit/registry.json` and generated reports without replacing the original census.

## 3. Certified relation kinds

The seven certified constructor tags are:

- `definitionalIdentity`
- `implication`
- `equivalence`
- `conditionalComposition`
- `observationalEquivalence`
- `distinguishability`
- `refutation`

`unresolved`, `notEstablished`, and `outOfScope` are audit statuses, not certified relation kinds. `adjudication` is a collection of certified relations, not a primitive kind.

## 4. Common semantics

A statement reference identifies a theory, stable statement ID, artifact version/hash, context, and source provenance. A cross-theory comparison uses a shared context `Δ`, translations into the two statement contexts, and an explicit premise predicate `Π : Δ → Prop`.

For predicates `P Q : Δ → Prop` after translation:

- implication: `∀ δ, Π δ → (P δ → Q δ)`;
- equivalence: `∀ δ, Π δ → (P δ ↔ Q δ)`;
- refutation of an implication: `∃ δ, Π δ ∧ P δ ∧ ¬ Q δ`.

Definitional identity requires a fresh kernel `rfl` check after the declared translation. It is not propositional equality and not a physical-identity certificate.

Observational equivalence is universally quantified over the declared observation channels and their input domains. Distinguishability uses either an explicit separating observation witness or an explicit identifiability/decoder certificate; these two forms must remain distinguishable. The current Stern–Volmer result is intensity-only observational equivalence plus a joint intensity–lifetime tracking discriminator, not unconditional lifetime-only injectivity.

Conditional composition must name parent certificates, mediating endpoints, translations, and any bridge premises. The child certificate must be produced by a sound composition combinator that consumes the typed parent proofs; an independent proof of the child conclusion plus a list of parent names is not composition. Parent premises propagate by premise ID union. A premise may be omitted only with a typed discharge certificate. Bridges may be empty when the parent contexts already align; every declared bridge must be explicit and propagated. An arbitrary theorem must not be labelled composition without this evidence.

## 5. Lean certificate representation

Use a Lean certificate sum type (or a formally equivalent dependent representation) whose constructors carry the kind-specific semantic proof. Expose a computable `certificateKind` function. For every manifest certificate row, the validator generates checks equivalent to:

```lean
#check <fully.qualified.certificate>
example : certificateKind <certificate> = <manifest.kind.constructor> := rfl
```

Therefore a manifest cannot relabel an implication as definitional identity or observational equivalence. Definitional-identity constructors must themselves require a fresh `rfl`-only definition-equality certificate.

The validator also checks the axiom footprint of each certificate and definitional witness against `propext`, `Classical.choice`, and `Quot.sound`. No placeholder or custom axiom is accepted. Definitional witnesses are not required to have an empty footprint: their definitional guarantee comes from fresh `rfl` elaboration, while Real-valued declarations can legitimately use the standard infrastructure axioms.

## 6. Premise badges

Badges are independent and evidence-driven:

- `explicit`: present in the checked Lean signature;
- `nonvacuous`: a certificate exhibits a context satisfying all premises;
- `nonredundant`: for each claimed premise, a certificate exhibits a context satisfying all other premises, falsifying that premise, and falsifying the conclusion;
- `weakest`: requires a declared alternative-premise preorder and a separate minimality certificate. Never infer this badge from a failed proof, linter output, or nonredundancy alone.

Every badge witness requires a typed expected-evidence check tied to the record and premise IDs. Declaration existence and an allowed axiom footprint are insufficient. Until such typed evidence is implemented, the validator must reject the corresponding badge rather than accept it.

## 7. Registry and pair coverage

The finite theory inventory contains seventeen theory IDs. The unordered-pair audit universe has `choose(17,2)=136` pairs. Registry completeness means every pair has at least one audit record. Unresolved records count toward registry coverage but are reported separately and block any `resolvedCoverage` claim.

Multiple records per pair are valid. Conflict detection uses `(queryID, statementVersion, scope)`, not pair identity alone, and different certified relation kinds are not inherently contradictory. In particular, a certified relation and an unresolved query about a different statement may coexist, and multiple certified relations may coexist when their scopes or semantic claims differ. `notEstablished` must carry a snapshot, scope, human rationale, and machine-recomputable dependency evidence. It never means logical nonexistence.

There is no `logicalCompleteness` badge.

## 8. Validator acceptance

The validator fails closed with a nonzero exit status unless all applicable checks pass:

1. JSON/schema and unique IDs;
2. endpoint, query, scope, and snapshot resolution;
3. Lean declaration existence and manifest/certificate-kind equality;
4. definitional `rfl` and kind-specific semantic checks;
5. composition parent and premise closure;
6. evidence required by every premise badge;
7. required provenance and manual-status rationale;
8. 136/136 registry coverage when run in full mode;
9. allowed axiom footprints and matching snapshot/toolchain hashes;
10. all invalid mutation fixtures rejected.

The report must distinguish `registryCoverage`, `resolvedCoverage`, counts by relation kind/status, and the current unresolved set. A report exit code of zero is not sufficient unless all requested gates ran; skipped checks are not PASS.

## 9. Pilot acceptance set

The pilot must cover all seven certified kinds and both principal non-certificate statuses using existing mathematics wherever possible:

- a kernel `rfl` pin;
- an existing one-way entailment;
- A1 equivalence;
- Kasha–Marcus with `hic` as a conditional equivalence, plus a genuine parent-consuming implication/equivalence chain for conditional composition;
- Stern–Volmer intensity observational equivalence;
- Stern–Volmer joint-channel distinguishability/identifiability;
- A2 or another explicit admissible counterexample;
- one undelivered candidate as `unresolved`;
- one scoped no-edge registration as `notEstablished`.

Do not change an original theory statement merely to fit the schema. Add a wrapper or report a schema limitation to the lead.

## 10. Review and isolation

All work occurs only in the isolated checkout. Workers own only their assigned write scopes. Do not commit unless the lead explicitly requests it. The lead reviews the integrated diff. An independent read-only verifier reruns the gates before any completion claim.
