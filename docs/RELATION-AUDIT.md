# Relation Audit — Registry Semantics and Acceptance Criterion

**Status.** This is the user-facing semantics and reproduction contract for the isolated relation-audit
layer (`relation_audit/schema.json`, `relation_audit/pilot.json`, the future
`relation_audit/registry.json`, `tools/relation_audit.py`, and `tests/relation_audit/`). It is
subordinate to `docs/RELATION-AUDIT-CONTRACT.md`; if this file and the lead contract disagree, the
lead contract wins and the disagreement must be reported rather than silently reinterpreted. The
schema is versioned **`1.2.0`**. Version 1.1.0 applied the lead-mandated corrections in the lead
review (`LEAD-REVIEW-1.md`, outside this isolated checkout) R2–R4 — the axiom whitelist for
definitional witnesses, typed expected evidence for premise badges and bridge/discharge witnesses,
and status-based rather than kind-based conflict detection — together with an interim R1
combinator interface. Version 1.2.0 completes R1 with the lead's final architecture decision: the Lean `ConditionalComposition` constructor is proof-relevant
and authoritative, so JSON no longer reconstructs a second combinator application. It names the two
parent certificates, the mediator and the translations, and the validator pins the child
certificate's canonical projections (`certificateParentIDs`, `certificateParentKinds`,
`certificateParentPremiseIDs`, `certificateBridgeIDs`, `certificateDischargeIDs`,
`certificateMediating?`, `certificateCompositionForm?`) plus `certificateKind` and
`certificatePremiseIDs`. The changes from `1.0.0` are listed in Section 12; the 1.2.0 composition
interface is Section 13.

**One-sentence version.** The audit checks whether a *declared* relation certificate and its metadata
satisfy a *declared* relation kind; it does not discover relations, and its negative statuses are
scoped bookkeeping, not proofs of logical absence.

---

## 1. Scope and non-claims

The audit universe is the finite inventory of seventeen theory IDs:

```
Marcus Hammond BEP Kasha Sabatier Goldschmidt SymmetryFactor KashaVavilov SternVolmer
QuantumYield FluorPhos EnergyGapLaw StokesShift ICvsISC Forster Einstein RACI
```

The unordered cross-theory universe is `C(17, 2) = 136` pairs. An *intra-theory* adjudication
(one theory compared with itself, for example the A1 equivalence inside `SymmetryFactor`) is a legal
audit record but is **not** one of the 136 pairs.

The audit does **not**:

1. **discover relations automatically.** No step enumerates Lean declarations, looks for shared
   identifiers, follows imports, names, statement shapes, or literature similarity to *propose* an
   edge. Candidate queries and their endpoints are declared by a human or by an AI agent outside the
   validator; the validator only checks the declared material. A validator that invented a relation
   from a name match or an import would be outside this contract.
2. **prove source fidelity or empirical adequacy.** Provenance records where a statement came from;
   it does not prove that the source is represented faithfully or that the theory is true.
3. **prove logical absence or completeness.** `notEstablished`, `outOfScope`, an empty import graph,
   and a failed proof are scoped artifacts. They never mean "no relation exists", "no relation can
   exist", or "all relations have been found". There is no `logicalCompleteness` badge and no
   `logicalAbsence` certificate in this schema.
4. **identify physical quantities.** `definitionalIdentity` is a kernel `rfl` statement about
   declared translations, not a claim of physical identity. It says nothing about whether two
   physical vocabularies denote the same reality.
5. **merge adjudication into a primitive kind.** An adjudication is a collection of certified
   relations (plus, where needed, a counterexample certificate). It is not an eighth relation kind.
6. **replace the existing census.** `tools/counts.py` remains the repository census and reports
   counts; it is not the relation-audit acceptance gate. The relation audit fails closed with a
   nonzero exit status on invalid input.

The three non-certificate statuses mean exactly this:

- `unresolved`: no disposition has been reached. It counts toward registry coverage but does not
  resolve a relation.
- `notEstablished`: within the named scope and snapshot, the declared search found no certificate
  satisfying the requested relation kind, and the dependencies are recorded in a machine-recomputable
  form. It is a *scoped negative registration*, not logical absence.
- `outOfScope`: the query is outside the declared audit jurisdiction (for example, no shared context
  or no declared translation exists). It is not absence either.

---

## 2. Artifact map and ownership

| artifact | owner | role |
|---|---|---|
| `relation_audit/schema.json` | shared task-2 | Structural input contract for manifests. |
| `relation_audit/pilot.json` | pilot worker | Representative audit records; not the full registry. |
| `relation_audit/registry.json` | later migration | Full registry; every one of the 136 pairs must have an audit record. |
| `relation_audit/reports/**` | validator worker | Machine-readable pilot report and the archived generated Lean checks (`production-pilot.json`, `production-pilot-lean-checks.lean`). |
| `PhotoLean/RelationAudit/Defs.lean` | Lean worker | Context/observation predicates, certificate sum type, computable `certificateKind`. |
| `PhotoLean/RelationAudit/Pilot.lean` | Lean worker | Certificates reused by the pilot. |
| `PhotoLean/RelationAudit.lean` | Lean worker | Umbrella import. |
| `tools/relation_audit.py`, `tools/relation_audit/**` | validator worker | Fail-closed validator and reporters. |
| `tests/relation_audit/**` | validator worker | Valid/invalid fixtures and mutation tests. |
| `docs/RELATION-AUDIT.md` | shared task-2 | This document. |

Nothing in the relation audit modifies a delivered theory module. A statement that cannot be fitted
to the schema is reported as a schema limitation to the lead; the original theory statement is not
changed merely to fit the registry.

---

## 3. Manifest at a glance

A manifest is one JSON object with these top-level members:

| member | meaning |
|---|---|
| `schemaVersion` | `"1.2.0"` for this schema. |
| `mode` | `"pilot"` or `"full"`. |
| `theoryInventory` | exactly the seventeen theory IDs, each once. |
| `pairCount` | the constant `136`, i.e. `C(17,2)`; the validator recomputes it from the inventory. |
| `snapshots` | tree/toolchain/schema/artifact hashes. |
| `scopes` | declared audit jurisdictions. |
| `statements` | stable statement references. |
| `queries` | source/target endpoint pairs and their shared context. |
| `certificates` | the Lean certificates, with kind-specific semantics. |
| `records` | the audit outcomes: status, relation kind, certificate reference, premises, badges, composition, dependencies. |

Schematic shape (a reading aid, not a second schema):

```json
{
  "schemaVersion": "1.2.0",
  "mode": "pilot",
  "theoryInventory": ["Marcus", "Hammond", "... fifteen more ..."],
  "pairCount": 136,
  "snapshots": [ { "id": "SN-1", "treeSha": "<40-hex>", "toolchain": "...",
                   "schemaSha256": "<64-hex>", "artifacts": { "path": "<64-hex>" } } ],
  "scopes": [ { "id": "SC-1", "kind": "restricted", "description": "...",
                "theories": ["Marcus", "BEP"], "provenance": { "kind": "source",
                "references": [ { "artifact": "theories/RELATIONS.md" } ] } } ],
  "statements": [ { "id": "STMT-1", "theory": "Marcus", "version": "1.0.0",
                    "artifact": "PhotoLean/Marcus/Basic.lean", "sha256": "<64-hex>",
                    "context": "CTX-KERNEL", "declaration": "PhotoLean.Marcus.barrier",
                    "provenance": { "kind": "source",
                      "references": [ { "artifact": "PhotoLean/Marcus/Basic.lean" } ] } } ],
  "queries": [ { "id": "Q-1", "source": "STMT-1", "target": "STMT-2",
                 "context": "CTX-KERNEL", "provenance": { "kind": "source",
                 "references": [ { "artifact": "theories/RELATIONS.md" } ] } } ],
  "certificates": [ { "id": "CERT-1", "kind": "implication",
                      "module": "PhotoLean.RelationAudit.Pilot",
                      "lean": "PhotoLean.RelationAudit.Pilot.cert",
                      "kindFunction": "PhotoLean.RelationAudit.certificateKind",
                      "constructor": "PhotoLean.RelationAudit.RelationKind.implication",
                      "premises": [], "axiomFootprint": ["propext", "Classical.choice", "Quot.sound"],
                      "semantics": { "context": "CTX-KERNEL",
                        "translations": { "left": "fun d => d", "right": "fun d => d" },
                        "premisePredicate": "fun _ => True" } } ],
  "records": [ { "id": "REL-1", "queryId": "Q-1", "statementVersion": "1.0.0",
                 "scope": "SC-1", "snapshot": "SN-1", "status": "certified",
                 "relationKind": "implication", "certificate": "CERT-1",
                 "premises": [], "badges": {}, "provenance": { "kind": "source",
                 "references": [ { "artifact": "theories/RELATIONS.md" } ] } } ]
}
```

The `theoryInventory` is an enum of the seventeen IDs with `minItems = maxItems = 17` and
`uniqueItems: true`; a theory outside the enum, a duplicate, or a different count is a schema
failure. `pairCount` is a constant and the validator recomputes the universe from the inventory. The
pilot may contain only a subset of the 136 pairs; a full registry must cover all of them.

A **query** has exactly two statement endpoints, `source` and `target`. A cross-theory query has
endpoints from two distinct theory IDs; an intra-theory query has both endpoints from the same
theory. The unordered pair of a cross-theory query is the pair of the endpoint statements'
`theory` fields. There is no separate pair array: the pair is derived so that it cannot drift from
the endpoints. The `source` is the antecedent for `implication` and `refutation`; `target` is the
consequent. `context` names the shared context.

A **record** answers one query in one scope at one snapshot. It carries the audit `status`; only a
`certified` record carries `relationKind`, a `certificate` reference, `premises`, and `badges`.
Relation kind, status, certificate evidence, and provenance are separate fields on purpose
(Section 4).

---

## 4. Orthogonality: kind, status, evidence, provenance

The schema keeps four concerns apart. A validator that lets one substitute for another is wrong.

| concern | field | question it answers | typical values |
|---|---|---|---|
| relation semantics | `record.relationKind` and `certificate.kind` | *what relation is asserted?* | the seven kinds |
| audit status | `record.status` | *what disposition has this query reached?* | `certified`, `unresolved`, `notEstablished`, `outOfScope` |
| evidence | `certificates[*]` plus `record.premises` and `record.badges` | *what machine-checked support exists?* | certificate, premise signatures, witnesses, preorder |
| provenance | `provenance` on statements, queries, scopes and records | *where did the declared material come from?* | source paths/DOIs and locators |

Rules enforced by the schema and the validator:

1. Rule zero: **kind equality is authoritative.** `record.relationKind` and the referenced
   `certificate.kind` must be equal and must be one of the seven certified kinds:
   `definitionalIdentity`, `implication`, `equivalence`, `conditionalComposition`,
   `observationalEquivalence`, `distinguishability`, `refutation`.
2. `unresolved`, `notEstablished`, and `outOfScope` are **not** relation kinds. A non-certified
   record must not carry `relationKind`, `certificate`, `premises`, `badges`, or `composition`.
3. A certified record must carry `relationKind`, `certificate`, `premises`, and `badges`; a status
   alone never certifies anything.
4. A certificate cannot relabel its kind. The validator generates
   `#check @<certificate.lean>` and
   `example : <certificate.kindFunction> <certificate.lean> = <certificate.constructor> := rfl`.
   A mismatch is a hard failure.
5. Provenance never upgrades a status and never substitutes for a certificate. A source citation can
   explain why a negative registration was made; it cannot turn `notEstablished` into a relation.
6. Badges are evidence, not status. An omitted badge is the absence of a claim, not a negative result.
   A claimed badge is a typed obligation (Section 7), not a label.
7. **Different certified kinds are not inherently contradictory.** Multiple certified relations may
   coexist for the same endpoints when they answer different questions (for example an
   intensity-only observational equivalence and a joint-channel distinguishability result) or when
   the scope makes the compared dimension explicit. Conflict detection is about incompatible audit
   *statuses* under one `(queryId, statementVersion, scope)` key (Section 9.4); it is never
   pair-level or kind-level exclusivity, and the schema has no `conflict.kinds` rule.

---

## 5. Statements, contexts, queries, scopes, snapshots

### 5.1 Statements

A statement entry identifies:

- `id`: a stable manifest key. Renaming a statement ID is forbidden; a changed statement keeps the ID
  and changes `version` and `sha256`.
- `theory`: one of the seventeen inventory IDs. This is the theory that owns the proposition. It need
  not be the module directory if an adjudication reads a declaration from a shared module, but the
  pair derivation and the endpoint-to-pair consistency check use this field.
- `version`: a semantic version. The record's `statementVersion` is the snapshot-era label for the
  pair of endpoints (Section 9.4), not the statement `id`.
- `artifact`, `sha256`: repository-relative file path and the SHA-256 of that file at the snapshot.
- `context`: the comparison context label.
- `declaration` (optional): the fully qualified Lean declaration of the statement.
- `provenance`: a provenance kind (`source`, `manual`, `computed`, or `imported`), at least one
  reference with an artifact path/DOI/URL, and a rationale when the kind is `manual`.

### 5.2 Contexts and translations

A context is the shared domain `Δ` on which the two statements are compared. The certificate's
`semantics.context` names it; `semantics.translations.left/right` are the translations into the two
statement contexts; `semantics.premisePredicate` is `Π : Δ → Prop`. The statements' own contexts may
differ; the translations are the declared bridge into the shared context. The Lean type of `Δ` and
the predicates are checked through the certificate, not parsed from prose.

### 5.3 Queries and endpoints

`query.source` and `query.target` are statement IDs. For a cross-theory query the validator requires
the two statements' `theory` fields to be distinct and derives the unordered pair from them. For an
intra-theory query both endpoint theories are equal and the query is excluded from the 136-pair
universe. The endpoint direction is meaningful for `implication` and `refutation`: source is the
antecedent `P`, target is the consequent `Q`. It is symmetric for `equivalence` and
`observationalEquivalence`.

### 5.4 Scopes

A scope states the epistemic and artifact boundary of a record: `kind` (`global`, `restricted`, or
`outOfScope`), `description`, `theories` (one or more IDs; a global scope may name all seventeen),
optional `dimension` (`relation`, `observation`, or `both`), optional
`boundary`/`includes`/`excludes`, and provenance. Every record references a scope. An `outOfScope`
record must reference a scope whose kind is `outOfScope`; an `unresolved` or `notEstablished` record
must not use an `outOfScope` scope. A scope is not a claim that the boundary is exhaustive.

`dimension` makes the relation/observation distinction part of the audit cell when two certified
records would otherwise share `(queryId, statementVersion)`. A relation-only scope and an
observation-only scope may both be certified for the same endpoints without either being a
contradiction; the alternative is a distinct scope whose `description` states the dimension
explicitly. Omitting `dimension` is legal but does not license kind-level exclusivity: different
certified kinds remain compatible (Section 9.4).

### 5.5 Snapshots

A snapshot records:

- `treeSha`: the git commit the audit was run at;
- `toolchain`: the exact `lean-toolchain` text;
- `mathlibRev` (optional): the pinned mathlib revision;
- `schemaSha256`: the SHA-256 of `relation_audit/schema.json`;
- `artifacts`: a map from repository-relative path to SHA-256, covering every statement artifact and
  certificate source;
- `createdAt`, `dirty`, `note` (optional).

The validator recomputes every hash and resolves `treeSha` as a commit. A hash mismatch is fatal. A
`dirty: true` snapshot is legal input only when the artifact hashes match; the report must carry a
`snapshotDirty` caveat, and an independent verifier may reject a full-mode PASS taken on a dirty tree.
A full-mode PASS should normally be taken on a clean snapshot.

### 5.6 Scope of a record vs. scope of a query

A query asks a question; a scope bounds one attempt to answer it; a snapshot fixes the tree. Multiple
records may answer the same query under different scopes or snapshots (for example, a repeated search
after a new module is delivered). That is why the conflict key includes the scope and the
snapshot-era statement version, not just the pair.

---

## 6. Exact relation semantics

Notation. Fix a context `Δ`. Let `Π : Δ → Prop` be the premise predicate. Let
`P := t_L : Δ → Prop` and `Q := t_R : Δ → Prop` be the translated endpoint predicates. All formulas
below are the propositions the Lean certificate must prove (up to the certificate's type encoding).
The manifest's Lean-term fields are checked by the generated Lean commands; the validator does not
implement a second semantics in Python.

Summary:

| kind | exact proposition |
|---|---|
| `definitionalIdentity` | `∀ δ, Π δ → (P δ ≡ Q δ)` by a fresh `rfl` check after the declared translation |
| `implication` | `∀ δ, Π δ → (P δ → Q δ)` |
| `equivalence` | `∀ δ, Π δ → (P δ ↔ Q δ)` |
| `refutation` | `∃ δ, Π δ ∧ P δ ∧ ¬ Q δ` (refutes the implication `P → Q`) |
| `observationalEquivalence` | `∀ δ, Π δ → ∀ c ∈ C, ∀ x ∈ Dom(c), O_L(c,x,δ) = O_R(c,x,δ)` |
| `distinguishability` (witness) | `∃ δ, Π δ ∧ ∃ c ∈ C, ∃ x ∈ Dom(c), O_L(c,x,δ) ≠ O_R(c,x,δ)` |
| `distinguishability` (decoder) | `∃ D, ∀ δ, Π δ → D(prof_L(δ)) = true ∧ D(prof_R(δ)) = false` |
| `conditionalComposition` | the relation computed by the proof-relevant Lean `ConditionalComposition` constructor from two typed parent certificates, a middle alignment, premise coverage and (possibly empty) bridge premises (Section 8) |

### 6.1 `definitionalIdentity`

`definitionalIdentity` is the kernel `rfl` pin. It requires `semantics.rflWitness` (the rfl-only Lean
witness), `semantics.rflWitnessAxiomFootprint` (the exact `#print axioms` output for that witness),
`semantics.translation` (the declared translation term), and `semantics.rflCheck` (`lhs`/`rhs`). The
validator generates a fresh

```lean
example : <rflCheck.lhs> = <rflCheck.rhs> := rfl
```

check in addition to the certificate-kind check. The certificate constructor must itself be a
`rfl`-only definition-equality certificate. It is **not** propositional equality (`P ↔ Q` needs
`equivalence`) and **not** a physical-identity certificate. A definitional drift makes the check
fail; that is the regression-alarm purpose.

The definitional gate is **fresh `rfl` elaboration**, not an empty axiom footprint. Both the
certificate and `semantics.rflWitness` must have a `#print axioms` footprint that is a subset of the
standard whitelist `{propext, Classical.choice, Quot.sound}`, and a declared
`rflWitnessAxiomFootprint` must equal the computed footprint. Real-valued pins legitimately report
`propext`, `Classical.choice`, and `Quot.sound`; requiring an empty list is a false negative and is
not part of this schema.

### 6.2 `implication`

```
∀ δ : Δ, Π δ → (P δ → Q δ)
```

The direction is the query's source-to-target direction. The converse is a separate query (or a
separate `equivalence` row); it is never inferred from this one.

### 6.3 `equivalence`

```
∀ δ : Δ, Π δ → (P δ ↔ Q δ)
```

An equivalence is not a definitional identity. A row that can be closed only by `rfl` may be
`definitionalIdentity`; a row that needs a theorem is `equivalence` even if the theorem is short.

### 6.4 `refutation`

```
∃ δ : Δ, Π δ ∧ P δ ∧ ¬ Q δ
```

This refutes the implication `P → Q`. The certificate's `semantics.counterexample` is the Lean
declaration proving the existential; `semantics.target` states the refuted implication in text so a
human can resolve it to the query endpoints. A refutation of an equivalence needs a one-sided witness
plus a declared direction. A negated universal (`¬∀ ...`) is not by itself this kind: the certificate
must exhibit the admissible `δ`, the premises, `P δ`, and `¬ Q δ`.

### 6.5 `observationalEquivalence`

Declare a family of channels `C`. Each channel `c` has an input domain `Dom(c)` and two observation
maps

```
O_L(c, ·, ·) : Dom(c) → Δ → Obs(c)
O_R(c, ·, ·) : Dom(c) → Δ → Obs(c)
```

(`semantics.channels` names them; the optional `semantics.channelSpecs` records the typed domain and
observation terms). Then:

```
∀ δ : Δ, Π δ → ∀ c : C, ∀ x : Dom(c), O_L(c,x,δ) = O_R(c,x,δ)
```

Observational equivalence is *not* propositional equivalence of `P` and `Q`; it says the declared
observations agree pointwise. The channel list is part of the claim: adding or removing a channel
changes the proposition. The Lean `Channel` type is homogeneous in its observed-value and input
types; channels with different types need separate certificates (a representational limitation
reported in `Defs.lean`).

### 6.6 `distinguishability`

The schema requires `semantics.form` with one of the two exact tags
`separatingObservation` and `identifiabilityDecoder`, and keeps the proof forms distinct.

**Separating observation.** A concrete admissible context, channel, and input on which the
observations differ:

```
∃ δ : Δ, Π δ ∧ ∃ c : C, ∃ x : Dom(c), O_L(c,x,δ) ≠ O_R(c,x,δ)
```

The manifest names `semantics.witness` (Lean declaration) and may also record
`semantics.witnessContext`, `semantics.channelID`, and `semantics.input`.

**Identifiability/decoder certificate.** A declared decoder/classifier `D` on full observation
profiles returns `true` on the left profile and `false` on the right profile, for every admissible
context:

```
∃ D : ((c : C) → Dom(c) → Obs(c)) → Bool,
  ∀ δ : Δ, Π δ → D(prof_L(δ)) = true ∧ D(prof_R(δ)) = false
```

where `prof_L(δ) := fun c x => O_L(c,x,δ)` (and similarly for `R`). The manifest names
`semantics.witness` (the decoder certificate) and may also record `semantics.decoderStatement`. This is the form used
by an identifiability result such as the Stern–Volmer lifetime discriminator: the lifetime channel
recovers the mechanism label. It is distinct from an existential separating witness; the validator
must not accept one form as the other. A decoder result is universally quantified and therefore
stronger than a single witness, but it is still only about the declared channels and model class.

### 6.7 `conditionalComposition`

Composition is a relation produced by the **proof-relevant Lean `ConditionalComposition`
constructor**, not a label for an arbitrary theorem and not a list of parent names attached to an
independent proof. The constructor stores the two typed parent certificates (`ParentCertificate`), a
typed `MiddleAlignment` between the left parent's right endpoint and the right parent's left
endpoint, a typed `PremiseCoverage` (inheritance or an explicit `Discharge`), the explicit bridge
premises, and the declared discharges. It **computes** the child comparison, the child form and the
child conclusion through `ConditionalComposition.sound`; there is deliberately no field into which an
independent proof of the child conclusion could be placed. The child certificate's kind is
`conditionalComposition`.

The JSON manifest does not reconstruct a second combinator application. `record.composition` names
the two parent certificate IDs in left-to-right order, exactly one mediating endpoint, the endpoint
translations, and any bridges/discharges. The validator resolves each parent ID to its Lean
certificate name, resolves the mediator to its Lean declaration, computes the expected form from the
parent kinds (equivalence only when both parents are equivalences), and generates the canonical
definitional checks listed in Section 8. `bridges` may be empty when the parent contexts already
align; an empty list is a legal composition and is not an omission. A parent-name list plus an
independent child proof is not an accepted alternative representation: the schema has no
`combinator`, `application`, `childConclusion` or `parentEvidence` field, and the generated
projections are computed from the child Lean value itself.

`semantics.conclusionKind` optionally records the composed form; the certificate type is
authoritative, and `record.composition.conclusionKind` may repeat it. Either value must agree with
the form computed from the parent kinds.

---

## 7. Premise badges

Let the certified relation declare premises `p_1, ..., p_n` in `certificate.premises` and
`record.premises`, with `Π := ⋀_i p_i` (the certificate names this term in
`semantics.premisePredicate`). The four badges are independent. A badge is either claimed with
**typed expected evidence** or omitted; an omitted badge is the absence of a claim, not a negative
theorem, and an unsupported claim is rejected rather than passed.

| badge | exact obligation | required evidence |
|---|---|---|
| `explicit` | every declared premise appears in the checked Lean signature of the certificate (as a binder/assumption, not merely in a comment) | `badges.explicit.earned`, `badges.explicit.premiseIds` equal to the record premise set; each premise has `explicit: true`, `signatureName`, and `signatureDeclaration` |
| `nonvacuous` | `∃ δ, Π δ` | `badges.nonvacuous.lean`, `.expectedType`, `.premiseIds`; generated `example : <expectedType> := <lean>` |
| `nonredundant` | for each premise `p_i`: `∃ δ, (⋀_{j≠i} p_j δ) ∧ ¬ p_i δ ∧ ¬ Rel δ`, where `Rel` is the certified relation conclusion | `badges.nonredundant.premiseIds` and `.byPremise`: one `{lean, expectedType}` witness per premise ID; generated typed check per premise |
| `weakest` | a declared alternative-premise preorder `≼`, the alternative premise-set IDs, and a minimality certificate; never inferred | `badges.weakest.premiseIds`, `.preorder`, `.alternatives`, `.expectedType`, `.minimality`; generated `example : <expectedType> := <minimality>` |

**Typed evidence is mandatory.** For every `expectedType`/`lean` (or `minimality`) pair the validator
generates

```lean
example : <expectedType> := <lean>
```

and it must also verify that `expectedType` is *the* expected proposition for the record and premise
IDs, for example by a generated `rfl` equality against the canonical formula built from
`semantics.premisePredicate`, the record premise list, and the certified conclusion. Declaration
existence and an allowed axiom footprint are insufficient: a declaration of the right name but the
wrong type does not earn the badge. Until a kind-specific expected-type wrapper is implemented for a
badge, the validator **must reject** that badge (`badge.evidence` / `badge.expectedType`) rather than
accept the declaration on existence alone. The schema therefore requires `expectedType` and
`premiseIds` on every claimed `nonvacuous`, `nonredundant`, and `weakest` witness (the `explicit`
badge is a checked-signature claim and carries `premiseIds` but no proposition witness); a manifest
that omits them is structurally invalid.

The weakest-premise formula used by this document is the minimum (weakest) reading. Let `Alt` be the
declared finite set of alternative premise-set IDs and let

```
Π ≼ Π'   iff   ∀ δ, Π' δ → Π δ
```

(so `Π` is weaker when it assumes less). The certificate must prove

```
∀ Π' ∈ Alt, Π ≼ Π'
```

with `≼` a declared preorder on `Alt`. The schema records the preorder declaration, the alternative
IDs, and the minimality proposition; the validator checks the typed witness against that proposition.
A failed proof, linter output, or `nonredundant` alone is **never** evidence for `weakest`.

A premise set may be empty. Then `explicit` is either omitted (no claim) or claimed only if the
validator accepts the vacuous signature check and the `premiseIds` list is empty; `nonvacuous` is
still meaningful (`∃ δ, True`) but requires its typed witness; `nonredundant` and `weakest` are
omitted. An omitted badge is safer than an unsupported claim.

---

## 8. Composition parents, canonical projections, and premise closure

A `conditionalComposition` certificate/record must name, in `record.composition`:

- `parents`: exactly two parent certificate IDs, unique, in left-to-right order. The Lean
  `ConditionalComposition` constructor is binary. Each parent resolves to a top-level certificate
  whose kind is certified. Parent certificates may be intra-theory; they need not themselves be one
  of the 136 pairs.
- `mediators`: exactly one mediating statement ID. The Lean certificate's `certificateMediating?`
  projection names the right endpoint of the left parent; the alignment identifies it with the left
  endpoint of the right parent. Its `statementId` must be definitionally the manifest mediator
  statement's Lean `declaration`. The remaining `StatementRef` fields (`theory`,
  `artifactVersion`, `context`, `provenance`) are Lean-side metadata and are not reconstructed from
  JSON.
- `translations`: `{from, to, description}` records connecting parent endpoints to mediating
  endpoints and to the child endpoints. Every `from`/`to` must resolve.
- `bridges`: zero or more `{premiseId, statement, expectedType, witness}` bridge premises. An empty
  or omitted list is legal when the parent contexts already align; it is not an omission or a
  closure gap. A declared bridge must be explicit and propagated into the child premise set. The
  typed bridge expected-evidence check is not implemented yet, so every declared bridge is rejected
  (`composition.bridgeUnsupported`) rather than passed on declaration existence.
- `discharges` (optional): `{premiseId, retainedPremiseIds, expectedType, witness, statement?}`
  entries for parent premises that the child does not carry. A parent premise may be omitted only
  through one of these entries. The typed discharge check is not implemented yet, so every declared
  discharge is rejected (`composition.dischargeUnsupported`); an omission without a discharge
  certificate is a closure failure.
- `conclusionKind` (optional): `implication` or `equivalence`, matching the form computed from the
  parent kinds and `certificateCompositionForm?`.

The child certificate must be a `conditionalComposition` certificate. The validator resolves the
parent IDs to their Lean certificate names and generates these definitional checks:

```lean
example : certificateKind <child> = RelationKind.conditionalComposition := rfl
example : certificateParentIDs <child> = [<parent1Lean>, <parent2Lean>] := rfl
example : certificateParentKinds <child> = [<parent1Ctor>, <parent2Ctor>] := rfl
example : certificateParentPremiseIDs <child> = [[<p1 ids>], [<p2 ids>]] := rfl
example : certificateBridgeIDs <child> = [<bridge ids>] := rfl
example : certificateDischargeIDs <child> = [<discharge ids>] := rfl
example : (certificateMediating? <child>).map (fun s => s.statementId) = some "<mediatorLeanDeclaration>" := rfl
example : certificateCompositionForm? <child> = some CompositionForm.<form> := rfl
```

Every certificate row also gets
`example : certificatePremiseIDs <cert> = [<manifest premise ids>] := rfl`. A child proof that does
not consume the parents cannot satisfy these checks, because the projections are computed from the
child Lean value: the left-to-right parent names, their kinds, their premise IDs, the bridge and
discharge premise IDs, the mediating endpoint and the composed form must all be exactly what the
proof-relevant constructor carries. If a theorem can be certified under a weaker kind, use that kind
instead of inflating it to composition. The Kasha–Marcus pilot result is the canonical negative
example: its `hic`-premised result is a conditional equivalence, not a composition; the composition
pilot is the Marcus-normal → Evans–Polanyi-bounds → no-inverted-direction chain.

Let `Cert` be the child certificate's premise-ID set, `Record` the record premise-ID set, `Prem_i`
the premise-ID set of parent `i`, `B` the bridge premise IDs, `D` the discharged premise IDs, and
`Local` any child-local premises. The validator checks:

```
Cert ∪ (⋃_i Prem_i) ∪ B  ⊆  Record ∪ D
B ⊆ Record
D ∩ Record = ∅
```

and every inherited premise ID maps to the same premise statement in parent and child. Extra
child-local premises are allowed only if declared in `record.premises` with `role: local`; they are
not silently attributed to a parent.

---

## 9. Registry, pair coverage, and conflicts

### 9.1 Theory inventory and pair derivation

The inventory is fixed in `schema.json` and in `relation_audit/registry.json`. The 136 unordered pairs
are `{T_i, T_j}` with `i < j` in inventory order. A cross-theory query derives its pair from the two
endpoint statements' `theory` fields; there is no separate pair array to canonicalize. An
intra-theory query compares two statements of one theory and never counts as a pair.

### 9.2 Coverage definitions

Let `R` be the set of records, `Q(r)` the query of record `r`, and `pair(Q)` the pair derived from the
endpoint statements (`⊥` for an intra-theory query). Define:

```
covered(p)        := ∃ r ∈ R, pair(Q(r)) = p
registryCoverage  := |{ p ∈ Pairs : covered(p) }| / 136
certified(p)      := ∃ r ∈ R, pair(Q(r)) = p ∧ status(r) = certified
unresolved(p)     := ∃ r ∈ R, pair(Q(r)) = p ∧ status(r) = unresolved
resolvedCoverage  := |{ p ∈ Pairs : certified(p) }| / 136
certifiedCoverage := resolvedCoverage
```

`registryCoverage` is the fraction of pairs with at least one audit record of any status.
`resolvedCoverage` is the fraction of pairs with at least one **certified relation**; it is the
validator's `resolvedPairs / 136`. A pair with only `notEstablished` or `outOfScope` records counts
toward registry coverage but not toward resolved coverage. `resolvedCoverage = 136/136` is not a
completeness claim about mathematics; it is a count of pairs with a certified relation.

Full-mode PASS requires `registryCoverage = 136/136`, not `resolvedCoverage = 136/136`: a pair may be
legitimately resolved negatively. The report must show both numbers, and it must also report the
current unresolved set. **Any unresolved record blocks a `resolvedCoverage` claim**, even when the
numeric fraction is `136/136`: `resolvedCoverageComplete` is true only when all 136 pairs have a
certified record *and* no unresolved record exists. The unresolved records are counted toward
registry coverage but are never folded into a resolved-coverage claim.

### 9.3 Statuses and coverage

- `unresolved` records count toward `registryCoverage` but not toward `resolvedCoverage`; their pairs
  are reported as unresolved and block any resolved-coverage claim.
- `notEstablished` and `outOfScope` count toward `registryCoverage` but not toward
  `resolvedCoverage`; they never assert a relation. They are scoped and must carry a rationale;
  `notEstablished` additionally carries a snapshot, a scope, a human rationale, and
  machine-recomputable dependency evidence.
- A pair may have several records (for example a certified relation and an unresolved query about a
  different statement version). The pair counts as certified if at least one record is certified; a
  coexisting unresolved record still blocks the resolved-coverage claim, because the pair is not
  fully resolved.

### 9.4 Conflict key and multiple records

Multiple records per pair are valid. The audit cell is identified by

```
K(r) = (queryId(r), statementVersion(r), scope(r))
```

exactly the fields on `record`. Conflict detection is **status-based, not kind-based**:

- A `K` may hold several certified records. Different certified relation kinds are not inherently
  contradictory: an intensity-only observational equivalence and a joint-channel distinguishability
  result, for example, answer different questions about the same endpoints. The report counts each
  certified kind and does not emit a kind conflict.
- A `K` may not hold a certified record together with a non-certified disposition, and it may not
  hold two different non-certified dispositions. Those are incompatible audit statuses for the same
  query, statement version, and scope, and they are the only conflict class at `K`.
- When two certified records would otherwise share a cell, the scope must make the compared
  relation/observation dimension explicit (`scope.dimension` is `relation`, `observation`, or
  `both`, or the scope `description` states it). That is a scope distinction, not pair-level or
  kind-level exclusivity.

Records with the same pair but different queries, statement versions, or scopes may coexist,
including a certified relation and an unresolved query about a *different* statement.
`statementVersion` is the snapshot-era label for both endpoints, for example
`Marcus.InvertedRegion@1.0.0|BEP.eact@1.0.0`; the validator uses it as part of the conflict key and
does not re-derive it from the statement rows. Pair identity alone is never used for conflict
detection. The schema also has no `conflict.kinds` rule and no pair-level uniqueness rule.

### 9.5 What must appear in the report

The report must distinguish at least:

- `status`, `exitCode`, `mode`, and the manifest/schema/snapshot identity;
- `coverage.registryCoverage` and `coverage.resolvedCoverage`, with `coverage.coveredPairs` and
  `coverage.resolvedPairs` as integer numerators over 136, and `coverage.resolvedCoverageComplete`
  (true only when every pair is certified **and** no unresolved record exists);
- `coverage.missingPairs` in full mode, and `coverage.unresolvedRecords`;
- `counts.byStatus` and `counts.certifiedByKind`;
- `unresolved`, the current unresolved set, with record/query/version/scope;
- `gates[name].status` and `gates[name].findings`, with `SKIP` distinct from `PASS`;
- caveats such as `snapshotDirty` or a schema limitation.

There is no `logicalCompleteness` field or badge, and no `conflict.kinds` finding: differing
certified kinds are counted, not treated as a conflict. A report that prints `136/136` without the
certified kind counts and the negative-status counts is incomplete reporting, not a stronger result.

---

## 10. Executable acceptance criterion

The validator exposes this interface:

```bash
# pilot acceptance (Lean checks enabled; the generated Lean checks are archived)
python3 tools/relation_audit.py \
    --manifest relation_audit/pilot.json \
    --schema relation_audit/schema.json \
    --mode pilot \
    --keep-temps \
    --lean-source-out relation_audit/reports/production-pilot-lean-checks.lean \
    --json-out relation_audit/reports/production-pilot.json

# full acceptance, after the migration
python3 tools/relation_audit.py \
    --manifest relation_audit/registry.json \
    --schema relation_audit/schema.json \
    --mode full \
    --json-out relation_audit/reports/production-full.json

# mutation fixtures: every valid fixture accepted, every invalid fixture rejected
python3 tests/relation_audit/run_tests.py
```

Exit codes: `0` = PASS; `1` = at least one requested check failed; `2` = the run is incomplete
(unloadable input, a skipped Lean gate, or a request that could not run). A non-zero exit is
fail-closed. A skipped check is not a PASS: the report records each gate's `status`
(`PASS`, `FAIL`, `SKIP`, or `NOT_APPLICABLE`) and every finding, and the overall `status` is `PASS`
only when every applicable gate has at least one passing check and no failure or skip. Passing
`--no-lean` while certificates are present yields `INCOMPLETE` (exit 2), never PASS.

### 10.1 Applicable gates

| gate | exact condition |
|---|---|
| G1 schema and IDs | Manifest validates against `relation_audit/schema.json`; IDs are unique in their collections; the inventory is the seventeen IDs and `pairCount = 136`. |
| G2 resolution | Every `source`, `target`, `queryId`, `scope`, `snapshot`, premise, certificate, parent certificate, mediator, and scope theory resolves. |
| G3 Lean declarations | Every certificate `lean` and module exists; the generated `#check` succeeds; evidence declarations exist. |
| G4 kind equality and semantics | `record.relationKind = certificate.kind`; generated `certificateKind` and `certificatePremiseIDs` equalities pass; the kind-specific semantics (rfl, implication, equivalence, refutation, observation, decoder, composition) pass; a definitional witness is checked for the standard axiom whitelist, not for an empty footprint. |
| G5 composition closure | Parent certificates are certified; the child certificate's generated `certificateKind` and canonical projections (`certificateParentIDs`, `certificateParentKinds`, `certificateParentPremiseIDs`, `certificateBridgeIDs`, `certificateDischargeIDs`, `certificateMediating?`, `certificateCompositionForm?`) pass by `rfl`; mediators and translations resolve; parent and bridge premises are present or discharged with typed evidence; an empty bridge list is accepted; the composition graph is acyclic. |
| G6 badges | `explicit` covers every premise and has checked signatures. The schema requires the typed expected proposition (`expectedType`), the premise IDs and a witness for `nonvacuous`, `nonredundant` and `weakest`; until the validator implements their canonical expected-type check, every such claim is rejected (`badge.*Unsupported`), not accepted on declaration existence or axiom footprint. |
| G7 provenance and rationale | Every statement and record has provenance; every non-certified record has `record.rationale`; every `notEstablished` has at least one dependency record. |
| G8 coverage | In `full` mode, `registryCoverage = 136/136`; in `pilot` mode, all seven certified kinds plus `unresolved` and `notEstablished` are present. `resolvedCoverage` is reported but a full PASS does not require it to be 136/136; any unresolved record blocks a resolved-coverage claim. |
| G9 axioms and snapshot | Every certificate's and definitional witness's `#print axioms` is a subset of `{propext, Classical.choice, Quot.sound}`; no `sorryAx`, no custom axiom; every snapshot/toolchain/schema/artifact hash matches; a dirty snapshot carries a report caveat. |
| G10 mutation rejection | The fixture suite accepts all valid fixtures and rejects every invalid fixture with a non-zero exit and a specific gate error. |

### 10.2 Pilot acceptance set

In `mode: "pilot"`, the manifest must contain at least one certified record for **each** of the seven
kinds, at least one `unresolved` record, and at least one `notEstablished` record. It need not cover
the 136 pairs and must not claim full coverage. The intended reuse (names are examples, not a mandated
manifest) is:

| pilot slot | existing declaration family |
|---|---|
| kernel `rfl` pin | `PhotoLean.Relations.bep_eact_eq_marcus_barrier` (pair `Marcus`/`BEP`) |
| one-way entailment | `PhotoLean.Relations.epBounds_of_reactionRegion` (pair `Hammond`/`BEP`) |
| A1 equivalence | `PhotoLean.Relations.symmetryFactor_betaHalf_iff` (intra `SymmetryFactor`) |
| Kasha–Marcus conditional equivalence with `hic` | `PhotoLean.Relations.kashaWithin_one_marcus` represented as an `equivalence` under the `hic` premise, not as a composition |
| conditional composition | a genuine parent-proof-consuming implication/equivalence chain: two certified parent certificates with a shared mediating endpoint and a child `ConditionalComposition` certificate whose canonical projections match the manifest (an empty bridge list is allowed) |
| Stern–Volmer intensity observational equivalence | `PhotoLean.SternVolmer.intensity_curve_coincidence` (intra `SternVolmer`) |
| Stern–Volmer joint-channel distinguishability/identifiability | `PhotoLean.SternVolmer.lifetimeTracks_iff_dyn` / `sv_identifiability_boundary` (decoder form) |
| A2 counterexample | `PhotoLean.KashaVavilov.Criterion.kashaRule_not_implies_vavilovAt` (refutation of an implication) |
| undelivered candidate | an explicitly registered query with `status: unresolved` and a `candidate` kind |
| scoped no-edge | a pair such as Kasha/Hammond with `status: notEstablished`, dependency records, and a boundary |

The A1, Stern–Volmer observational, and Stern–Volmer distinguishability adjudications are
conceptually intra-theory. The schema represents them with two same-theory endpoints: such a query is
a legal record but does not enter the 136-pair coverage numerator. The production pilot
(`relation_audit/pilot.json`) uses this intra-theory representation for A1 and the two Stern–Volmer
rows; the test fixture uses a cross-theory representation for its mock composition and equivalence
rows. The validator accepts both, counts only cross-theory queries toward the pair universe, and
never rejects a legal same-theory endpoint pair.

### 10.3 Invalid mutation fixtures the fixture suite must include

At minimum: relabelled kind (implication certificate claimed as a definitional identity); a non-`rfl`
certificate claimed as a definitional identity; a missing parent certificate; a parent premise
omitted without a typed discharge certificate; a `conditionalComposition` child proved independently
of its parents (parent names plus an unrelated child proof) rejected by the canonical projection
checks; a composition whose parent order, parent kinds, parent premise IDs, bridge IDs, discharge IDs,
mediating endpoint or computed form does not match the child certificate; an attempt to re-add
`composition.combinator`/`application`/`childConclusion`/`parentEvidence` rejected as a schema
violation; a bridge or discharge witness with the wrong expected type; a claimed badge with no
`expectedType`; a `nonvacuous`/`nonredundant`/`weakest` witness whose `expectedType` is not the
canonical proposition; `weakest` inferred from `nonredundant`; missing provenance; `notEstablished`
without dependency evidence; an `unresolved` record without a `candidate`; incompatible statuses
(a certified record and a non-certified disposition) under one `(queryId, statementVersion, scope)`;
a duplicate record ID; 135/136 coverage; an extra axiom or `sorryAx`; a definitional witness outside
the allowed axiom whitelist; a snapshot or artifact hash mismatch; a dangling reference; a theory
outside the inventory; and a plain schema violation.

The suite must also contain the positive controls that guard against over-rejection: an empty or
omitted `bridges` list on a genuine parent-consuming composition is accepted; two certified records with
different certified kinds under distinct relation/observation scopes are accepted and are not
reported as a conflict; a Real-valued definitional witness that reports `propext`,
`Classical.choice`, and `Quot.sound` is accepted and is not required to be axiom-free; two certified
records with different certified kinds under the same key are accepted and are not reported as a
conflict. The typed `nonvacuous`/`nonredundant`/`weakest` expected-evidence checks are not implemented,
so those claims are rejected explicitly (`badge.*Unsupported`) rather than accepted; that rejection
is the current fail-closed positive control, not a silent pass. Every invalid fixture must be
rejected with exit code `1` and a gate-specific message, not a traceback or an unhandled exception.

### 10.4 Independent verification

Passing the validator is not a self-certified completion. The lead reviews the semantic claims and an
independent read-only verifier reruns the commands above in the isolated checkout. The verifier
records the exact tree state, the report path, the exit code, and any skipped gate. The author of a
certificate or a registry row does not declare the final PASS.

### 10.5 Checker integration boundary

The schema is the input source of truth; a checker that keeps a flatter internal model must map the
fields explicitly and fail closed when a field is absent. The required checker mapping is explicit:
`theoryInventory`, `certificates`, `records[*].relationKind/certificate/premises/badges`,
`records[*].composition.parents/mediators/translations/bridges/discharges`,
`queries[*].source/target/context`, `scopes[*].dimension`,
`snapshots[*].treeSha/schemaSha256/artifacts`, `record.rationale`, and
`provenance.kind/references` are the exact spellings it reads, together with the child
certificate's `certificateParentIDs`/`certificateParentKinds`/`certificateParentPremiseIDs`/
`certificateBridgeIDs`/`certificateDischargeIDs`/`certificateMediating?`/
`certificateCompositionForm?` projections. The schema version is `1.2.0`; a validator that still
accepts `1.0.0` or `1.1.0` composition shapes, or ignores the canonical projections, is not
compatible with this document.

Integration points that deserve explicit warning:

1. **Intra-theory records.** If the pilot represents the A1, Stern–Volmer observational, or
   Stern–Volmer distinguishability adjudication with two statements of one theory, the schema uses
   `source` and `target` statements whose `theory` fields are equal. A checker that rejects every
   same-theory endpoint pair (`pair.self`) cannot validate that representation. Such a checker must
   accept an explicitly intra-theory query, exclude it from the 136-pair numerator, and keep the
   conflict key and provenance checks unchanged; otherwise the pilot must use the cross-theory
   representation described in Section 10.2.
2. **Statement theory vs. module path.** A pair is derived from the statements' `theory` field, not
   from the path of the declaration. An adjudication may read a declaration from a shared module
   while assigning the proposition to the theory it adjudicates; the pair check must use the
   conceptual theory field.
3. **Composition is a canonical certificate projection, not metadata.** A checker must require
   `composition.parents` (exactly two), `composition.mediators` (exactly one) and
   `composition.translations`; resolve parent IDs to Lean certificate names; and generate the
   definitional checks for `certificateParentIDs`, `certificateParentKinds`,
   `certificateParentPremiseIDs`, `certificateBridgeIDs`, `certificateDischargeIDs`,
   `certificateMediating?` and `certificateCompositionForm?`, in addition to
   `certificateKind <child> = conditionalComposition`. Checking that parent IDs resolve, or that a
   separately named child proof has the right kind, is not sufficient. The JSON must not reconstruct
   a second combinator application (`combinator`, `application`, `childConclusion` and
   `parentEvidence` are not fields of this schema). `composition.bridges` may be empty; rejecting an
   empty list, or requiring at least one bridge, is a compatibility bug against this version.
4. **Badges are typed proofs.** A checker must generate the `example : <expectedType> := <witness>`
   check for every claimed badge, bridge, and discharge, and verify that `expectedType` is the
   canonical proposition for the record and premise IDs. It must not accept a badge on declaration
   existence or axiom footprint alone. Until that check is implemented, the badge is rejected.
5. **No kind conflicts.** A checker must not report differing certified kinds under one
   `(queryId, statementVersion, scope)` as a conflict. Conflict detection is status-based:
   incompatible statuses at one key fail; multiple certified records with different kinds are valid
   when their scopes make the compared dimension explicit. `conflict.kinds` is not part of this
   contract.

These points are not optional for pilot acceptance.

---

## 11. Limitations and open integration points

1. **The validator is not part of this document.** This document fixes the input semantics and the
   acceptance interface; it does not contain the checker. The commands above are the executable
   interface; the checker's internals and error taxonomy are its own.
2. **The schema is structural, not semantic.** JSON Schema cannot prove that a Lean term has the
   claimed type, that a premise is load-bearing, or that all 136 pairs are covered. Those are
   validator and Lean-kernel obligations, and the report must name which gate checked them.
3. **`resolvedCoverage` is not completeness.** It counts pairs with a certified relation, and any
   unresolved record blocks a resolved-coverage claim. `notEstablished` is a scoped search result;
   `outOfScope` is a jurisdiction statement. Neither is logical absence. The audit never claims that
   an unregistered relation is impossible.
4. **No automatic discovery.** Candidate relations are declared outside the validator. Import graphs,
   name similarity, statement shape, and literature resemblance are at most provenance or motivation;
   they are not certificates.
5. **Full migration is a later task.** `relation_audit/pilot.json` is the pilot only. The 136-pair
   registry is not created by this schema, and the pilot must not pretend to be the full graph.
6. **The schema may need a compatibility wrapper.** If an existing statement cannot be expressed
   without changing a delivered theory, add a wrapper statement or report a schema limitation; do not
   change the theory statement to fit the registry.
7. **Homogeneous channels.** `PhotoLean.RelationAudit.Channel` fixes one observed-value type and one
   input type per certificate. A joint channel with a product observation type is fine; channels with
   different types require separate certificates. The schema records one `channels` list per
   certificate (with optional `channelSpecs` detail) and does not pretend to solve that
   representational limit.
8. **Typed badge evidence is interface-level until implemented.** The schema requires
   `expectedType`/`premiseIds` on the `nonvacuous`, `nonredundant`, and `weakest` badges,
   `expectedType` on bridge witnesses, and `expectedType`/`retainedPremiseIds` on discharge
   witnesses, but JSON Schema cannot type-check a Lean term. The validator must generate the
   expected-type checks; while a badge's check is unimplemented, the badge is rejected rather than
   passed. This is a validator obligation, not an optional schema suggestion.
9. **Composition is Lean-side proof-relevant.** The Lean `ConditionalComposition` constructor is
   authoritative: it carries the typed parents, alignment, premise coverage, bridges and discharges,
   and computes the child conclusion. The schema fixes only the manifest-side evidence (parents,
   mediator, translations, bridges, discharges) and the validator pins the canonical projections.
   The remaining `StatementRef` fields of the mediator are Lean metadata; the
   `certificateMediating?` check pins its `statementId`. A schema-complete row with an independent
   child proof is rejected by these projections.
10. **Definitional witnesses use the axiom whitelist.** An empty `#print axioms` footprint is not a
    definitional-identity requirement and must not be enforced. Real-valued pins legitimately report
    `propext`, `Classical.choice`, and `Quot.sound`; the whitelist, plus fresh `rfl` elaboration, is
    the gate.

---

## 12. Revision 1.1.0 — lead-mandated corrections and integration interface

This section records the deliberate, documented changes from schema `1.0.0` to `1.1.0`. They
implemented the lead review (`LEAD-REVIEW-1.md`, outside this isolated checkout) R1–R4 and the
updated `docs/RELATION-AUDIT-CONTRACT.md`. **The composition interface in §12.1–§12.3 is historical:
Section 13 replaces the `combinator`/`application`/`childConclusion`/`parentEvidence` shape with
canonical certificate projections.** The R2–R4 parts remain current.

### 12.1 Schema changes

| area | `1.0.0` | `1.1.0` |
|---|---|---|
| `schemaVersion` | `"1.0.0"` | `"1.1.0"` (required constant) |
| `composition` required members | `parents`, `mediators`, `translations`, `bridges` | adds `combinator`, `application`, `childConclusion`, `parentEvidence` |
| `composition.bridges` | `minItems: 1` | `minItems: 0`; empty bridges are legal |
| `composition.parents` | at least two | at least two, `uniqueItems: true`, order is the combinator argument order |
| `composition.parentEvidence` | absent | new required array of `{parent, conclusion, proof}` typed parent proofs, positionally matched to `parents` |
| `composition.childConclusion` | absent | new required composed-conclusion proposition, definitionally the child certificate's conclusion |
| `composition.bridges[]` | `premiseId`, `statement`, `witness` | adds required `expectedType`; witness must inhabit it |
| `composition.discharges[]` | `premiseId`, `witness` | adds required `retainedPremiseIds`, `expectedType`; typed entailment |
| `semantics` for `definitionalIdentity` | `rflWitness`, `translation`, `rflCheck` | adds required `rflWitnessAxiomFootprint` (same whitelist as certificates; empty allowed) |
| `badges.explicit` | `earned` | adds required `premiseIds` |
| `badges.nonvacuous` | `lean` | adds required `expectedType`, `premiseIds` |
| `badges.nonredundant` | `byPremise` values were declaration strings | `byPremise` values are `{lean, expectedType}` objects; adds required `premiseIds` |
| `badges.weakest` | `preorder`, `alternatives`, `minimality` | adds required `premiseIds`, `expectedType`; `minimality` is the typed witness |
| `scope` | `kind`, `description`, `theories`, ... | adds optional `dimension` (`relation`, `observation`, `both`) |
| conflicts | validator emitted `conflict.kinds` for differing certified kinds | status-based conflicts only; different certified kinds are not conflicts |

### 12.2 Validator interface changes the integration worker must implement

1. **Composition:** require `composition.combinator`, `composition.childConclusion`,
   `composition.parentEvidence`, and `composition.application`; generate the typed check
   `example : <parentConclusion> := <parentProof>` for every parent, then
   `example : <application> = <combinator> <parentProof_1> ... := rfl` and
   `example : <childConclusion> := <application>`. Require `parentEvidence` to match `parents`
   positionally, each parent conclusion to be definitionally the parent certificate's conclusion, and
   the child conclusion to be definitionally the child certificate's conclusion. Do not accept a
   `conditionalComposition` record whose child proof is independent of the parent proofs. Do not
   reject an empty `bridges` list. Resolve `parents` in the declared order.
2. **Bridge and discharge evidence:** require `expectedType`; generate
   `example : <expectedType> := <witness>`; for bridges, require `expectedType` to be the
   `leanProposition` of the record premise with the same `premiseId`; for discharges, require the
   typed entailment from `retainedPremiseIds` to the discharged premise.
3. **Badges:** require `expectedType` and `premiseIds`; generate the typed expected-evidence check and
   verify `expectedType` is the canonical proposition for the record and premise IDs. If the
   validator cannot yet generate a badge's canonical expected type, it must reject the badge
   (`badge.expectedType`/`badge.evidence`) rather than pass it on declaration existence or axiom
   footprint. `nonredundant.byPremise` values are now objects, not declaration strings.
4. **Definitional witnesses:** remove the `allow_empty_axioms=True` path and the
   `lean.rflAxioms` empty-footprint requirement. Compute `#print axioms` for
   `semantics.rflWitness`, require a subset of `{propext, Classical.choice, Quot.sound}`, and require
   it to equal `semantics.rflWitnessAxiomFootprint`. Keep the generated `rflCheck` elaboration.
5. **Conflicts:** delete `conflict.kinds` or stop emitting it. Group by
   `(queryId, statementVersion, scope)` and fail only on incompatible audit statuses. Do not enforce
   pair-level uniqueness or kind-level exclusivity. Multiple certified records under one key are
   valid when their scopes make the compared dimension explicit.
6. **Coverage:** report `resolvedCoverageComplete = (resolvedPairs == 136 && unresolvedRecords == 0)`;
   any unresolved record blocks a resolved-coverage claim even when the numeric fraction is 136/136.
7. **Schema version:** accept `schemaVersion == "1.1.0"`; a `1.0.0` manifest is not schema-valid.

### 12.3 Lean interface changes the certificate worker must implement

1. `Certificate.conditionalComposition` must carry a soundness proof produced by a combinator that
   consumes the typed parent proof terms and yields the child conclusion, with middle-endpoint
   alignment and premise propagation in the combinator, not in a separate independent `sound` proof.
   The certificate layer must expose the parent-proof projections and the child conclusion so the
   validator can generate the typed checks; the child certificate's soundness field must be the
   declared `application` term. The combinator, the parent proof declarations, and the child
   certificate's composition proof must be transparent `def`s so the generated `rfl` check can unfold
   them.
2. Remove the non-empty bridge requirement (`hbridge : 1 ≤ bridge.length`). A composition with no
   bridge premises is legal when the parent contexts already align.
3. `Defs.lean` must not document or enforce an axiom-free `rflWitness`; the definitional guarantee is
   fresh `rfl` elaboration plus the standard axiom whitelist.
4. The Kasha–Marcus pilot result must be registered as a conditional `equivalence` under `hic`, not
   as `conditionalComposition`; a separate genuine implication/equivalence chain supplies the
   composition pilot.

---

## 13. Revision 1.2.0 — proof-relevant composition without a second application

Version 1.2.0 implements the lead's final architecture decision on R1. The Lean
`ConditionalComposition` constructor is proof-relevant and authoritative; JSON must not reconstruct
a second combinator application. The breaking changes from 1.1.0 are:

| area | `1.1.0` | `1.2.0` |
|---|---|---|
| `schemaVersion` | `"1.1.0"` | `"1.2.0"` |
| `composition` required members | `combinator`, `application`, `childConclusion`, `parents`, `parentEvidence`, `mediators`, `translations`, `bridges` | `parents`, `mediators`, `translations` |
| removed `composition` members | — | `combinator`, `application`, `childConclusion`, `parentEvidence` (and the `compositionParentEvidence` definition) |
| `composition.parents` | at least two | exactly two (`minItems = maxItems = 2`), ordered left-to-right |
| `composition.mediators` | at least one | exactly one (the binary composition's middle proposition) |
| `composition.bridges` | required, empty allowed | optional, empty allowed |
| composed form | `childConclusion` text plus `conclusionKind` | computed from the parent kinds and pinned by `certificateCompositionForm?` |
| validator composition checks | typed parent-proof/application checks | `certificateKind` plus `certificateParentIDs`, `certificateParentKinds`, `certificateParentPremiseIDs`, `certificateBridgeIDs`, `certificateDischargeIDs`, `certificateMediating?`, `certificateCompositionForm?` |
| all certificates | kind equality only | kind equality plus `certificatePremiseIDs` |

The validator resolves each manifest parent ID to the parent row's `lean` declaration and builds
the generated checks of Section 8. A composition whose JSON parent order, parent kinds, parent
premise IDs, bridge IDs, discharge IDs, mediating endpoint or computed form differs from the child
Lean value fails with `lean.compositionParentIDs`, `lean.compositionParentKinds`,
`lean.compositionParentPremiseIDs`, `lean.compositionBridgeIDs`,
`lean.compositionDischargeIDs`, `lean.compositionMediating` or `lean.compositionForm`. A manifest
that still carries `combinator`, `application`, `childConclusion` or `parentEvidence` is rejected by
the schema (`schema.invalid`), not silently ignored.

The `certificateMediating?` check is
`example : (certificateMediating? <child>).map (fun s => s.statementId) = some "<declaration>" := rfl`.
This pins the mediating endpoint to the resolved statement's Lean declaration; the other
`StatementRef` fields (`theory`, `artifactVersion`, `context`, `provenance`) are fixed in the Lean
pilot module. Deriving them from JSON would duplicate Lean-side metadata, which is exactly the R1
problem the 1.2.0 interface removes.

The pilot (`relation_audit/pilot.json`) uses this interface with the delivered certificates:
`kernelBarrierPin` (definitional identity), `epBoundsImplication` (implication),
`betaHalfEquivalence` (A1 equivalence), `kashaMarcusEquivalence` (Kasha–Marcus conditional
equivalence with the `hic` premise), `marcusNormalNoInvertedComposition` with its two parents
`marcusNormalImplication` and `epBoundsNoInvertedEquivalence` (conditional composition, empty
bridge list), `svIntensityObservationalEquivalence` (observational equivalence),
`svJointDistinguishability` and `svJointIdentifiability` (the two distinguishability forms), and
`kvRefutation` (refutation). The snapshot is `dirty: true` because the relation layer is
uncommitted in the isolated checkout; the report carries the `snapshotDirty` caveat.
