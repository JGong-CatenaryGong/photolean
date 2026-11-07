# Relation audit validator interface

`tools/relation_audit.py` is the fail-closed validator for the certified
relation manifest described by `docs/RELATION-AUDIT-CONTRACT.md`.  It adapts to
the checked-in `relation_audit/schema.json`; it never edits the schema, the
manifest, or any Lean source file.  This document is the exact interface the
validator expects, so a lead can reconcile it with the schema/pilot task before
the full pilot lands.

## Running it

```bash
# production pilot, once relation_audit/{schema.json,pilot.json} exist
python3 tools/relation_audit.py --manifest relation_audit/pilot.json --mode pilot

# full registry (136 unordered theory pairs)
python3 tools/relation_audit.py --manifest relation_audit/pilot.json --mode full

# machine-readable report, with the generated Lean checks archived
python3 tools/relation_audit.py --manifest relation_audit/pilot.json --mode pilot \
    --lean-source-out relation_audit/reports/production-pilot-lean-checks.lean \
    --json-out relation_audit/reports/production-pilot.json

# fixtures before the pilot exists
python3 tests/relation_audit/run_tests.py
```

Exit codes:

| code | meaning |
|---|---|
| `0` | every requested gate ran and passed |
| `1` | at least one requested check failed |
| `2` | input/schema cannot be loaded, or a requested gate was skipped |

A skipped check is never PASS.  `--no-lean` therefore exits `2` whenever the
manifest contains certificates (`lean.notRequested`); if there are no
certificates the Lean gate is `NOT_APPLICABLE` and does not block a pass.

## Gates and failure codes

| gate | what it enforces |
|---|---|
| `structure` | JSON parses, the schema subset validator accepts the manifest, ids are unique, the 17-theory inventory is exact, schema enums match the contract |
| `references` | statement/query/scope/snapshot/certificate/parent/mediator resolution, distinct-theory pairs |
| `semantics` | statuses, scope kinds, `(queryId, statementVersion, scope)` conflicts, premise closure, badges, composition, kind-specific evidence |
| `provenance` | source references exist, manual/non-certified rationale, dependency evidence |
| `snapshot` | commit exists, toolchain and schema hashes match, every pinned artifact hash matches the snapshot commit |
| `coverage` | 136/136 pairs in `full` mode; seven kinds + `unresolved` + `notEstablished` in `pilot` mode |
| `lean` | generated `#check`, `certificateKind ... = ... := rfl`, `#print axioms` checks |

Representative failure codes: `schema.invalid`, `schema.interface`,
`schema.statusEnum`, `id.duplicate`, `ref.certificate`, `ref.parent`,
`status.certificateMismatch`, `kind.adjudication`, `scope.outOfScopeMismatch`,
`conflict.statuses`, `premise.closure`, `premise.unknown`,
`composition.parents`, `composition.mediators`,
`composition.mediatorDeclaration`, `composition.translations`,
`composition.bridge`, `composition.bridgeWitness`,
`composition.bridgeUnsupported`,
`composition.discharge`, `composition.dischargeWitness`,
`composition.dischargeUnsupported`, `composition.conclusionKind`,
`semantics.conclusionKind`,
`badge.explicitSignature`, `badge.explicitPremiseIds`,
`badge.nonvacuousUnsupported`,
`badge.nonredundantUnsupported`, `badge.weakestUnsupported`,
`semantics.rflWitness`, `semantics.rflWitnessAxiomFootprint`,
`semantics.channels`,
`semantics.form`, `snapshot.unknownCommit`, `snapshot.staleArtifact`,
`snapshot.hashMismatch`, `snapshot.toolchain`, `snapshot.schemaHash`,
`provenance.missing`, `provenance.rationale`, `status.dependencies`,
`coverage.missingPair`, `lean.existence`, `lean.certificateKind`,
`lean.certificatePremiseIDs`,
`lean.compositionParentIDs`, `lean.compositionParentKinds`,
`lean.compositionParentPremiseIDs`, `lean.compositionBridgeIDs`,
`lean.compositionDischargeIDs`, `lean.compositionMediating`,
`lean.compositionForm`,
`lean.axioms`, `lean.axiomFootprint`, `lean.premiseSignature`, `lean.timeout`.

## Manifest interface

Canonical property names are listed first; the schema adapter
(`tools/relation_audit/interface.py`) also accepts the spellings in
`ALIASES`, so a schema author may use e.g. `theories` for `theoryInventory` or
`auditRecords` for `records` without breaking the validator.

### Top level

| field | type | meaning |
|---|---|---|
| `schemaVersion` | string | manifest version, reported only |
| `mode` | `pilot` or `full` | must match the run mode; the CLI defaults to this field |
| `pairCount` | integer | must be 136 |
| `snapshots` | array | pinned source snapshots (at least one) |
| `scopes` | array | declared comparison scopes |
| `theoryInventory` | array of 17 strings | finite theory universe |
| `statements` | array | stable statement references |
| `queries` | array | cross-theory queries with endpoints and context |
| `certificates` | array | Lean certificate rows |
| `records` | array | audit records (one or more per theory pair) |

### `snapshots[]`

```json
{
  "id": "snap-source-7ad25a5",
  "treeSha": "7ad25a5f03a88acc3af03f65149cf2ac102e7dac",
  "toolchain": "leanprover/lean4:v4.17.0",
  "schemaSha256": "<sha256 of the checked-in schema file>",
  "artifacts": {"PhotoLean/Marcus/Barrier.lean": "<sha256 at treeSha>"}
}
```

`treeSha` must resolve to a commit in this repository.  Historical snapshots
remain valid provenance pins: artifact content is read with
`git show <treeSha>:<path>`, so advancing `HEAD` does not by itself make a
pinned snapshot stale.  A snapshot is stale when its commit is unknown, its
toolchain differs from `lean-toolchain`, its schema hash differs from the
schema file, or a pinned artifact hash differs from the commit content.
Every statement artifact and every certificate `sourcePath` must be pinned by
at least one snapshot (`snapshot.statementPin`,
`snapshot.certificateSourceMissing`); a statement's declared `sha256` must
equal the hash pinned for the snapshot used by its records
(`snapshot.hashMismatch`).

A snapshot with `dirty: true` is checked against the **working tree** rather
than the commit content; the run records a `snapshot.dirty` gate finding, a
`caveats[]` entry with code `snapshotDirty`, and `metadata.snapshotDirty`.
A `mathlibRev`, when present, must match `lake-manifest.json`.  This is
the supported mode while the relation layer itself is still uncommitted.  A
clean snapshot uses `git show <treeSha>:<path>` and is the mode a full-mode PASS
should normally be taken in.

### `scopes[]`

```json
{"id": "global", "kind": "global", "description": "...", "provenance": {...}}
```

`kind` is one of `global`, `restricted`, `outOfScope`.  An `outOfScope` record
must reference a scope whose kind is `outOfScope`; certified and
`notEstablished` records must not.  When `theories` is present, a record's two
endpoint theories must both be listed (`scope.jurisdiction`).

### `statements[]`

```json
{
  "id": "marcus.barrier",
  "theory": "Marcus",
  "artifact": "PhotoLean/Marcus/Barrier.lean",
  "version": "1.0.0",
  "sha256": "<artifact hash>",
  "context": "...",
  "declaration": "PhotoLean.Marcus",
  "provenance": {"kind": "source", "references": [{"artifact": "...", "locator": "..."}]}
}
```

`artifact` is repository-relative and `sha256` must equal the record snapshot's
pinned hash for the same path.

### `queries[]`

```json
{"id": "q-impl", "source": "bep.transfer", "target": "hammond.gap",
 "context": "...", "provenance": {...}}
```

`source` and `target` resolve to distinct statement ids.  A record's pair is the
unordered pair of the two endpoint theories.  Intra-theory records (both
endpoints on the same theory) are legal in the schema but do not cover any of
the 136 cross-theory pairs.

### `certificates[]`

```json
{
  "id": "cert-impl",
  "kind": "implication",
  "module": "PhotoLean.RelationAudit",
  "lean": "PhotoLean.RelationAudit.Pilot.certImpl",
  "kindFunction": "PhotoLean.RelationAudit.certificateKind",
  "constructor": "PhotoLean.RelationAudit.RelationKind.implication",
  "premises": [
    {"id": "p-adj", "statement": "...", "explicit": true,
     "signatureName": "hAdj",
     "signatureDeclaration": "PhotoLean.RelationAudit.Pilot.lemmaImpl"}
  ],
  "semantics": {"translation": "..."}
}
```

All certificates — referenced or not — are Lean-checked.  `kind` is one of the
seven constructors from contract §3; `adjudication` is rejected as a primitive
kind.  Every certificate declares the shared context `semantics.context`, the
`semantics.translations.left`/`right` endpoint translations and the
`semantics.premisePredicate` (contract §4).  `axiomFootprint` is the exact
`#print axioms` list; the validator compares it with Lean's actual output and
fails on any drift (`lean.axiomFootprint`).  Kind-specific `semantics`
requirements:

| kind | required `semantics` evidence |
|---|---|
| `definitionalIdentity` | `rflWitness` (Lean declaration, standard allowed-axiom whitelist), `rflWitnessAxiomFootprint` when the schema provides it (exact `#print axioms` match, still inside the whitelist), `translation`, and `rflCheck` with `lhs`/`rhs` (generated `example : lhs = rhs := rfl`); the fresh `rfl` check, not an empty footprint, establishes definitional identity |
| `implication`, `equivalence` | none beyond the certificate proof |
| `conditionalComposition` | `translation`; composition evidence lives on the record and is pinned by the child certificate's canonical projections |
| `observationalEquivalence` | non-empty `channels` list |
| `distinguishability` | `form` in `separatingObservation` / `identifiabilityDecoder`, plus `witness` |
| `refutation` | `counterexample` declaration |

`module` is imported by the generated Lean file.  Lean-checked evidence
declarations (premise signatures, `rflWitness`, kind-specific witnesses) are
assumed to be imported by one of the certificate modules; the usual umbrella
module `PhotoLean.RelationAudit` satisfies this.  Rejected badge, bridge and
discharge declarations are never `#check`ed, because their existence would not
be evidence for the claim.

### `records[]`

```json
{
  "id": "rec-impl",
  "queryId": "q-impl",
  "statementVersion": "bep.transfer@7ad25a5",
  "scope": "global",
  "status": "certified",
  "relationKind": "implication",
  "certificate": "cert-impl",
  "snapshot": "snap-source-7ad25a5",
  "premises": [ /* same premise ids as the certificate */ ],
  "badges": {
    "explicit": {"earned": true, "premiseIds": ["p-adj"]}
  },
  "provenance": {"kind": "source", "references": [...]}
}
```

Only badges that are actually claimed appear.  `nonvacuous`, `nonredundant`
and `weakest` are rejected until typed expected-evidence checks exist (see
"Premise badges" below).

Status rules:

* `certified`: `relationKind` is one of the seven kinds, `certificate` resolves,
  and the record kind equals the certificate kind.  `premises` and `badges`
  must be present (empty values are legal when nothing is claimed), and
  `candidate`/`dependencies` must be absent.  The record's premise set must
  equal the certificate premise set, except for composition records (see
  below).
* `unresolved`: no kind/certificate/premises/badges/composition; `candidate`
  is one of the seven kinds; human `rationale` and provenance are required.
  Unresolved records count
  toward registry coverage and are listed in the report's `unresolved` set.
* `notEstablished`: no kind/certificate/premises/badges/composition;
  `rationale`; at least one
  `dependencies[]` entry of the form
  `{"kind": "leanProbe|sourceScan|census|search", "reference": "...",
    "recompute": "<command>", "sha256": "..."}`.  `leanProbe` references are
  additionally Lean-checked; file references must exist.  This status never
  means logical non-existence.
* `outOfScope`: no kind/certificate; `rationale`; scope kind `outOfScope`.

Conflict detection groups records by `(queryId, statementVersion, scope)`.
Different statuses in one group produce `conflict.statuses`.  Different
certified relation kinds are **not** a conflict (contract sections 7-8):
multiple certified relations may coexist, including under one
`(queryId, statementVersion, scope)` when their semantic or observational
contexts differ, and a certified relation may coexist with an unresolved query
about a different statement version or scope.  There is no `conflict.kinds`
code and no pair-level or kind-level exclusivity.  Multiple records per theory
pair are valid.

### Composition records

A `conditionalComposition` record must carry `composition.parents` (exactly
two parent certificate IDs, left-to-right), `composition.mediators` (exactly
one mediating statement ID), and `composition.translations` (at least one
resolving endpoint translation). `composition.bridges` may be omitted or
empty; an empty list is the correct representation when the parent contexts
already align. `composition.discharges` is optional. `composition.conclusionKind`
is optional and must equal the form computed from the parent kinds.

```json
"composition": {
  "parents": ["cert-impl", "cert-equiv"],
  "mediators": ["bep.epBounds"],
  "translations": [
    {"from": "marcus.normalRegion", "to": "bep.epBounds",
     "description": "..."},
    {"from": "bep.epBounds", "to": "bep.noInvertedDirection",
     "description": "..."}
  ],
  "bridges": [],
  "discharges": []
}
```

**Canonical certificate checks.** The Lean `ConditionalComposition`
constructor is proof-relevant and authoritative: it stores the two typed
parents, the middle-endpoint alignment, premise propagation (inheritance or an
explicit `Discharge`), bridges and discharges, and **computes** the child
comparison and child conclusion through
`ConditionalComposition.sound`. The manifest does not reconstruct a second
combinator application: there is no `combinator`, `application`,
`childConclusion` or `parentEvidence` field, and a parent-name list plus an
independent child proof is not an accepted alternative representation.

Instead, the validator resolves each manifest parent ID to its Lean
certificate name (the parent row's `lean` declaration), resolves the mediator
to its statement declaration, computes the expected form from the parent
certificate kinds (equivalence only when both parents are equivalences), and
generates these definitional checks against the child certificate:

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

Every certificate row, composition or not, also gets
`example : certificatePremiseIDs <cert> = [<manifest premise ids>] := rfl`, so
a manifest cannot attribute premises a Lean certificate value does not carry.

`certificateParentIDs` compares against the Lean certificate names, because
the Lean typed parent carries a stable ID string that the pilot module sets to
the parent declaration name. `certificateMediating?` is pinned through its
`statementId` projection: that is the mediating endpoint's Lean declaration.
The remaining `StatementRef` fields (`theory`, `artifactVersion`, `context`,
`provenance`) are metadata fixed in the Lean pilot module and are not
reconstructed from JSON. This is deliberate: deriving them from the manifest
would duplicate Lean-side metadata and reintroduce the R1 problem.

Premise closure is unchanged: `Cert ∪ (⋃_i Prem_i) ⊆ Record ∪ D`, and every
declared bridge must be in `Record`. `bridges` may be empty when the parent
contexts already align; a declared bridge or discharge is still rejected until
typed evidence tied to the record and premise IDs is implemented
(`composition.bridgeUnsupported`, `composition.dischargeUnsupported`).

## Premise badges

Badges are independent; absent means "not claimed".

* `explicit`: the badge object carries `earned: true` and a `premiseIds` list
  equal to the record premise set (`badge.explicitPremiseIds`); every premise
  must set `explicit: true`, carry `signatureName` + `signatureDeclaration`, and
  the generated `#check <signatureDeclaration>` output must contain the binder
  name.  This is the documented signature check and is retained.
* `nonvacuous`: rejected (`badge.nonvacuousUnsupported`).  Contract section 6
  requires typed evidence of `exists delta, Pi delta` tied to the record and
  premise IDs; declaration existence and an allowed axiom footprint are not
  accepted.
* `nonredundant`: rejected (`badge.nonredundantUnsupported`).  It requires a
  typed residual-context countermodel for each premise tied to the record and
  premise IDs.
* `weakest`: rejected (`badge.weakestUnsupported`).  It requires a typed
  minimality proof over the declared alternative-premise preorder.  It is never
  inferred from non-redundancy, proof failure or linter output.

A bare `true`/string badge value is also rejected by the schema and still
produces the corresponding `badge.*Unsupported` failure.

## Lean certificate checks

For every certificate the validator generates, into a temporary file under
`.lake/tmp/relation-audit/` (or the system temporary directory):

```lean
import <certificate modules>
#check <fully.qualified.certificate>
example : <kindFunction> <certificate> = <constructor> := rfl
#print axioms <certificate>
```

Certificate and kind-specific evidence declarations (`rflWitness`, the
distinguishability witness, the refutation counterexample) get `#check` and
`#print axioms`.  Definitional `rflWitness` declarations use the **standard
allowed-axiom whitelist**, not an empty-footprint requirement, and a
definitional certificate's `semantics.rflCheck.lhs`/`rhs` generate the fresh
`example : lhs = rhs := rfl`.  Every certificate also gets the canonical
`certificatePremiseIDs` equality, and every composition gets the canonical
parent/bridge/discharge/mediator/form equalities listed above.  Allowed axioms
are exactly `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` and custom
axioms fail, and a declared `axiomFootprint` must equal the actual
`#print axioms` set.  The file is removed after the run (use `--keep-temps` to
retain it).

`--lean-root PATH` adds an import root and is intended for fixture modules; it
does not weaken any check, because Lean must still elaborate the exact
declaration and kind equality.

## Schema adapter

`relation_audit/schema.json` (v1.2.0) is read, never written.  The validator:

1. validates the manifest with a standard-library JSON-Schema 2020-12 subset;
2. discovers the definitions for `manifest`, `snapshot`, `scope`, `statement`,
   `query`, `certificate` and `record` by name and distinguishing properties;
3. resolves canonical fields through `ALIASES`, and uses the schema's enum for
   `status`/`relationKind` when present (it must equal the contract set).

Unsupported schema keywords are a hard error (`schema` is not usable, exit 2),
never silently ignored.  If the production schema uses a structure outside this
adapter's alias table, the run fails at `schema.interface` and the lead must
either adjust `ALIASES` or align the schema; a silent fallback is deliberately
not provided.

## Report

`--json-out` writes sorted, deterministic JSON containing:

* `status`, `exitCode`, `mode`, `manifest`, `schema`;
* `coverage`: `theoryCount`, `pairUniverse`, `coveredPairs`, `missingPairs`,
  `registryCoverage`, `resolvedPairs`, `resolvedCoverage`,
  `resolvedCoverageComplete`, `unresolvedRecords`;
* `counts`: records by status and certified records by kind;
* `unresolved`: the current unresolved set;
* `gates`: per-gate status, counts and findings;
* `caveats`: for example `snapshotDirty` when a snapshot's artifact hashes were
  matched against the working tree;
* `metadata`: schema/toolchain/HEAD hashes, adapter discovery, Lean run status.

`resolvedCoverageComplete` is true only when all 136 pairs have a certified
record **and** no unresolved record exists; unresolved records block any
resolved-coverage claim.  No `logicalCompleteness` badge exists.

## Known limitations

* Kind-specific witnesses are checked for existence and axiom footprint, not
  for the full semantic statement (e.g. that an observational-equivalence
  certificate quantifies over exactly the declared channels).  That remains the
  certificate module's responsibility.
* Typed expected-evidence checks for `nonvacuous`, `nonredundant`, `weakest`,
  bridge and discharge claims are not implemented.  Those claims are therefore
  rejected explicitly (`badge.*Unsupported`,
  `composition.bridgeUnsupported`, `composition.dischargeUnsupported`) instead
  of being passed on declaration existence.  Implementing them is the way to
  make the badges earnable.
* Composition JSON no longer duplicates the Lean parent-consuming
  application.  The schema (v1.2.0) requires the two parent IDs, one mediator
  and the translations, and the validator pins the child certificate's
  canonical projections (`certificateParentIDs`, `certificateParentKinds`,
  `certificateParentPremiseIDs`, `certificateBridgeIDs`,
  `certificateDischargeIDs`, `certificateMediating?`,
  `certificateCompositionForm?`) plus `certificateKind` and
  `certificatePremiseIDs`.  `certificateMediating?` is pinned through its
  `statementId` projection; the other `StatementRef` fields are Lean-side
  metadata and are not reconstructed from JSON.
* `search` dependencies are not fetched (no network); only their declared
  `recompute` command and non-empty reference are validated.
* A dirty snapshot is legal and reported as a caveat; it must not be presented
  as a clean full-registry PASS.
* Premise binder discovery is textual on the `#check` output, which is the
  contract's own "checked Lean signature" notion; alpha-renaming the binder in
  Lean without updating the manifest is reported as a failure.
* The fixture snapshot is pinned to `7ad25a5f...`; a shallow clone without that
  commit cannot run the fixture tests.  The production pilot should pin the
  snapshot it actually audited.
