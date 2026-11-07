# Bounded Relation-Audit Boundary — R1 Frozen Contract

Status: **R1 boundary contract**, frozen on 2026-11-04. This document defines what the bounded
audit may compare, which statements are eligible, how a query is formed, and what a later outcome
may mean. It does not certify any relation and it does not replace the legacy registry.

The companion artifacts are:

- `statement-inventory.json` — the frozen eligible statement set;
- `pair-queue.json` — the 136-pair screening queue;
- `cluster-plan.json` — the disjoint chemical work packages;
- `validate_boundary.py` — the fail-closed validator.

## 1. Frozen universe

### 1.1 Theory set

The universe is exactly the seventeen theory identifiers below, in this order. The order is part of
the contract because pair identifiers are canonicalized with it.

| index | theory identifier | module directory | theory leaf directory |
|---:|---|---|---|
| 1 | `Marcus` | `PhotoLean/Marcus` | `theories/Marcus` |
| 2 | `Hammond` | `PhotoLean/Hammond` | `theories/hammond` |
| 3 | `BEP` | `PhotoLean/BEP` | `theories/BEP` |
| 4 | `Kasha` | `PhotoLean/Kasha` | `theories/kasha` |
| 5 | `Sabatier` | `PhotoLean/Sabatier` | `theories/Sabatier` |
| 6 | `Goldschmidt` | `PhotoLean/Goldschmidt` | `theories/goldschmidt` |
| 7 | `SymmetryFactor` | `PhotoLean/SymmetryFactor` | `theories/SymmetryFactor` |
| 8 | `KashaVavilov` | `PhotoLean/KashaVavilov` | `theories/KashaVavilov` |
| 9 | `SternVolmer` | `PhotoLean/SternVolmer` | `theories/SternVolmer` |
| 10 | `QuantumYield` | `PhotoLean/QuantumYield` | `theories/QuantumYield` |
| 11 | `FluorPhos` | `PhotoLean/FluorPhos` | `theories/FluorPhos` |
| 12 | `EnergyGapLaw` | `PhotoLean/EnergyGapLaw` | `theories/EnergyGapLaw` |
| 13 | `StokesShift` | `PhotoLean/StokesShift` | `theories/StokesShift` |
| 14 | `ICvsISC` | `PhotoLean/ICvsISC` | `theories/ICvsISC` |
| 15 | `Forster` | `PhotoLean/Forster` | `theories/Forster` |
| 16 | `Einstein` | `PhotoLean/Einstein` | `theories/Einstein` |
| 17 | `RACI` | `PhotoLean/RACI` | `theories/RACI` |

No eighteenth theory is admitted in R1. `PhotoLean/Kernel.lean` is a shared definitional kernel, not
a theory; it appears in the inventory only through the declaration the legacy registry already
uses as a kernel pin.

### 1.2 Pair universe

There are exactly `choose(17, 2) = 136` unordered cross-theory pairs. A pair identifier has the
form `P-<left>-<right>`, where the left theory has the smaller index in Section 1.1. Intra-theory
comparisons are not pair rows: they belong to one theory's own adjudication and are reported
separately in the legacy coverage summary.

The pair universe is frozen. A pair is not removed because it looks cross-domain, and it is not
added because a relation is convenient. Every pair must later produce either a named
proposition-level query or an explicit statement-level `outOfScope` justification.

### 1.3 Legacy registry baseline

The accepted legacy registry is `relation_audit/registry.json` with SHA-256:

```
25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0
```

The R1 inventory reads, but never edits, that file. The registry's historical counts are:
52 statement objects — 35 declared rows containing 34 unique declarations (one duplicate
`PhotoLean.Marcus.barrier` row), plus 17 theory-level anchors — 151 queries, 151 records, 38
certificates, 125 pair-level anchors, 26 named proposition-level queries, and 24 certified records
(19 cross-theory and 5 intra-theory). Legacy labels are census metadata, not audit verdicts.

The R1 inventory found four legacy statement objects whose `declaration` names do not occur in the
delivered Lean sources:

- `stmt-BEP-PhotoLean-BEP-rateViaEact` (`PhotoLean.BEP.rateViaEact`);
- `stmt-Marcus-PhotoLean-Marcus-rateDescriptor` (`PhotoLean.Marcus.rateDescriptor`);
- `stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier-eq-zero`
  (`PhotoLean.EnergyGapLaw.nrBarrier_eq_zero`);
- `stmt-StokesShift-PhotoLean-StokesShift-emEnergy-eq-zero`
  (`PhotoLean.StokesShift.emEnergy_eq_zero`).

They are recorded as *dangling legacy metadata* in `statement-inventory.json`
(`legacyDanglingStatements`), not as eligible statements. Three legacy certified queries and
records use them as endpoints
(`q-D-S05-bep-rate-eq-exp-neg-eact`, `q-D-S06-hammond-sharp-iff-marcus-sharp`,
`q-D-S15-egBarrier-zero-iff-emEnergy-zero`); those records remain legacy coverage history but
their endpoints must not be cited as inventory statements in later rounds. Repairing the legacy
registry is outside R1.

### 1.4 Outside the frozen universe

Anything outside the seventeen theories, the 136 pairs, and the eligible statement inventory is
outside this contract. R1 makes no claim about a theory not listed, a declaration not inventoried,
an intra-theory relation not registered, or a physical relation that the corpus does not express.

## 2. Eligible statement authorities

### 2.1 Authority sources

Each theory's statement authority is its `theories/<theory>/probes/<name>-statement-skeleton.lean`
file. The delivered modules are the authority's word-for-word copies. The authority files are
outside `SOURCE_DIRS`, so their Phase-1 placeholder bodies never enter the delivered tree; the
inventory points only at delivered declarations.

| theory | statement authority | declarations | authority SHA-256 (prefix) |
|---|---|---:|---|
| Marcus | `theories/Marcus/probes/marcus-statement-skeleton.lean` | 51 | `1e1ef771f051e2e2…` |
| Hammond | `theories/hammond/probes/hammond-statement-skeleton.lean` | 102 | `579e6da183e87f4e…` |
| BEP | `theories/BEP/probes/bep-statement-skeleton.lean` | 191 | `c9aa2cb1f82b8bcc…` |
| Kasha | `theories/kasha/probes/kasha-statement-skeleton.lean` | 151 | `8c5ed93b14d96c2d…` |
| Sabatier | `theories/Sabatier/probes/sabatier-statement-skeleton.lean` | 132 | `4c9ef109be2a9311…` |
| Goldschmidt | `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` | 139 | `3fbabbd4f1f2234d…` |
| SymmetryFactor | `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` | 35 | `457ff8ff4314cce9…` |
| KashaVavilov | `theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` | 29 | `2e8bdca363d888e6…` |
| SternVolmer | `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` | 46 | `4c44e22a415e62e0…` |
| QuantumYield | `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` | 29 | `d8305be36f01f4f7…` |
| FluorPhos | `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` | 30 | `2a717f1f51fd0f26…` |
| EnergyGapLaw | `theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` | 26 | `d217e8e99b965af9…` |
| StokesShift | `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` | 36 | `c2372a2e7cd57e5e…` |
| ICvsISC | `theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` | 20 | `43c1824acae752c7…` |
| Forster | `theories/Forster/probes/Forster-statement-skeleton.lean` | 32 | `cb9be602b7e3a57f…` |
| Einstein | `theories/Einstein/probes/Einstein-statement-skeleton.lean` | 33 | `eb8226a4b07df315…` |
| RACI | `theories/RACI/probes/RACI-statement-skeleton.lean` | 71 | `3a32abbabe98ced4…` |

Total: 1,153 authority declarations. The inventory adds one shared-kernel declaration,
`PhotoLean.Kernel.barrier`, because the legacy registry already uses it as a definitional pin.
Thus the inventory contains 1,154 statement rows: 1,153 authority rows plus 1 shared-kernel row.
Of these, 1,134 are screening-eligible (`theorem`/`def`); the other 20 are context-type rows
(`structure`/`inductive`) retained with `screeningEligible: false`. The source manifest pins the
complete delivered Lean tree: 102 `.lean` files under `PhotoLean/`.

### 2.2 Eligibility rule

A statement is eligible for bounded screening when all of the following hold:

1. it is declared in a theory statement authority;
2. its delivered declaration matches the authority signature word for word after whitespace
   normalization;
3. its source artifact exists in the delivered tree and its SHA-256 matches the inventory;
4. its declaration is not `private` and is not a proof placeholder;
5. its declaration kind is `theorem` or `def` (propositional claims and definitions). `structure`
   and `inductive` declarations are retained as `contextType` rows with
   `screeningEligible: false`, because they describe contexts and premises rather than relation
   endpoints.

The shared-kernel row is eligible as a definitional endpoint only. It is not a theory-owned claim.

### 2.3 Versioning and hashing

Every row carries these content-addressed fields:

```
signatureSha256 = SHA-256("<kind> <fully-qualified-declaration> <normalised-signature>")
sourceArtifactSha256 = SHA-256(delivered Lean source file bytes)
authoritySha256 = SHA-256(theory statement-skeleton file bytes)
version = "1.0.0" for the frozen R1 authority
```

`sourceFileManifest` pins every `.lean` file under `PhotoLean/` to a SHA-256. The validator fails if
a file is added, removed, or changed. A signature change requires a new statement version, a new
inventory row hash, and a new round; silently renaming or restating a declaration is forbidden.
The inventory introduces no new theorem, definition, axiom, or certificate.

## 3. Context and translation library

A query is meaningless until it declares a shared context and explicit translations into the two
statement contexts. The library below names the accepted context families. A later query may
introduce a new context only by declaring its fields, its physical reading, and its provenance;
it may not treat a shared context as implicit.

| context family | source structures | intended use |
|---|---|---|
| two-parabola barrier | `BarrierCtx`, `TwoParabolaCtx` | barrier heights, Marcus normal/inverted regions, driving-force comparisons |
| surface | `SurfaceCtx`, `ProductSurfaceCtx` | reactant/product surfaces, coordinate shifts, reaction free energy |
| rate | `RateCtx`, `TransferCtx`, `SlopeCtx`, `SecantCtx` | rate constants, transfer channels, secants and slopes |
| rational | `RatCtx` | exact rational checks and cast lemmas |
| window | `WindowCtx` | BEP conformance on a declared driving-force window |
| Kasha–Marcus | `KashaMarcusCtx` | the declared `hic` identification between ladder and Marcus window |
| curvature | `CurvatureCtx` | symmetry-factor and force-constant comparisons |
| Stern–Volmer | `SVIntensityCtx`, `SVDecoderCtx` | intensity and lifetime channels, joint observation, decoder |
| Kasha–Vavilov | `KVCtx` | ladder endpoints and lossless separation |
| Hammond–Marcus sharp | `HammondMarcusSharpCtx` | sharp descriptor and rate-positivity comparisons |
| kernel–Marcus–IC | `KernelMarcusICCtx` | shared-kernel and internal-conversion pins |
| energy-gap kernel/rate | `EGKernelCtx`, `EGRateCtx` | energy-gap law barrier and rate endpoints |
| Stokes surfaces | `SSGroundCtx`, `SSExcitedCtx` | ground/excited surfaces and emission windows |
| internal conversion | `ICBarrierCtx`, `ICRateCtx` | IC barrier and rate comparisons |
| energy-gap/IC rate | `EGICRateCtx` | the three-way energy-gap/IC rate comparison |
| energy-gap inverted | `EGInvertedCtx` | inverted-gap predicate comparisons |
| energy-gap/Stokes | `EGStokesCtx` | zero-barrier and zero-emission-window equivalence |

The translation library records the admissible translation *forms*:

| translation id | form | requirement |
|---|---|---|
| `identity` | `fun δ => δ` on both sides | both statement contexts are the shared context |
| `rfl-pin` | identity translations plus a fresh kernel `rfl` check | definitionalIdentity only |
| `coordinate-map` | an explicit map between two coordinate fields | map must be total on the declared domain |
| `rat-to-real` | `fun δ => (δ.lam : ℝ, δ.x : ℝ)` | cast lemmas must be cited |
| `surface-to-barrier` | `fun δ => (δ.lam, δ.q)` or its declared inverse | the physical coordinate reading must be stated |
| `descriptor-endpoint` | maps `(A,lam,kB,T,x)` to the two descriptor contexts | all five fields must be accounted for |
| `energy-window` | maps `(lam,e00)` to the two spectral contexts | the open/closed window boundary must be stated |
| `observational-setup` | maps a shared `Δ` to two state spaces via `leftInterp`/`rightInterp` | both interpretations must be total |

A translation is not a physical-identity claim. `definitionalIdentity` is a kernel `rfl` statement
about the declared translations; it is not propositional equality and not a statement that two
physical vocabularies denote the same reality.

## 4. Observation-channel library

Observational equivalence and distinguishability compare declared channels, not bare predicates.
A channel has a name, an input domain, and two observation functions `leftObs` and `rightObs` that
return the same observed-value type. Channels with different observed-value types require
separate certificates; the Lean representation does not silently mix them.

| channel id | observed value | input domain | use |
|---|---|---|---|
| `intensity-ratio` | `ℝ` | quencher concentration `q ≥ 0` | Stern–Volmer intensity channel |
| `lifetime-ratio` | `ℝ` | quencher concentration `q ≥ 0` | Stern–Volmer lifetime channel |
| `joint-intensity-lifetime` | `ℝ × ℝ` | quencher concentration `q ≥ 0` | joint observation and decoder |
| `rate-constant` | `ℝ` | driving force or reaction coordinate | Marcus/BEP/energy-gap/IC rates |
| `barrier-height` | `ℝ` | driving force or reaction coordinate | barrier and activation-energy comparisons |
| `quantum-yield` | `ℝ` | quencher concentration or ladder index | Kasha/quantum-yield/fluorophore channels |
| `transfer-efficiency` | `ℝ` | donor–acceptor separation | Förster transfer |
| `emission-energy` | `ℝ` | nuclear coordinate or emission energy | Stokes-shift and energy-gap endpoints |
| `spectral-intensity` | `ℝ` | wavelength or emission energy | radiative/spectral comparisons |
| `zone-tag` | finite tag type | driving-force pair or ladder index | normal/inverted/late/early classification |

A query that uses `observationalEquivalence` must list at least one channel. A query that uses
`distinguishability` must choose exactly one of the two admissible forms: an explicit separating
observation witness, or an explicit identifiability/decoder certificate. The two forms remain
distinguishable in the certificate; a decoder does not count as a separating witness.

## 5. Query-generation rules

### 5.1 Named proposition-level query

A named proposition-level query is a chemically meaningful question about two inventory
statements. It must carry:

1. **Endpoints.** Two statement IDs from `statement-inventory.json`. For a cross-theory pair the
   endpoints belong to the two distinct theories of the pair. A pair-level anchor is not an
   endpoint.
2. **Chemical rationale.** The physical quantity and mechanism that connect the endpoints, in one
   or more sentences. Naming similarity, shared notation, or both being "about photophysics" is
   not a rationale.
3. **Context and translations.** A shared context and explicit translations into both statement
   contexts, or a statement-level reason why neither exists.
4. **Premises.** An explicit premise predicate and premise IDs. Premises must be load-bearing:
   a premise that the intended evidence does not consume is not admitted as a premise.
5. **Scope and snapshot.** A declared scope ID and a pinned snapshot. A global scope is allowed
   only when the shared context is genuinely global.
6. **Provenance.** Source artifact, locator or line, and the statement version/hash for each
   endpoint.
7. **Expected evidence.** One of the seven evidence kinds in Section 7, and one of the five
   outcomes in Section 6. The expected kind is fixed before the evidence is produced.
8. **Falsification condition.** For a `refutation` candidacy, the explicit witness shape
   `∃ δ, Π δ ∧ P δ ∧ ¬ Q δ`; for an implication or equivalence, the counterexample shape that
   would refute it.
9. **Observation channels.** For observational equivalence or distinguishability, the channel IDs
   and their input domains.

### 5.2 Pair-level anchor

A pair-level anchor is a legacy coverage row, for example the `q-pair-P-<A>-<B>` queries in the
registry. It has two theory-level endpoints and a generic question ("Is a direct certified
relation registered for this pair?"). It records coverage or a scoped absence; it is not a
chemical screening query. An anchor does **not** satisfy the named-query requirement and may not
be cited as a named proposition-level query.

The legacy registry currently has 125 pair-level anchors and 26 named proposition-level queries.
Eleven pairs have at least one named query; the remaining 125 pairs have an anchor only. The R1
queue nevertheless requires a named query (or a statement-level `outOfScope` justification) for
all 136 pairs.

### 5.3 No forced edges

No pair may be forced into a relation merely to improve coverage. A scoped `notEstablished` or
`outOfScope` outcome is an acceptable result when the evidence and the statement-level reason are
explicit. The audit has no pair-count target, no edge-count target, and no completeness badge.

## 6. Outcome statuses

The five outcome statuses are fixed. They describe what a later record has established; they do
not describe a relation kind.

| status | meaning | required evidence |
|---|---|---|
| `certified` | the query is answered by a checked certificate of the declared evidence kind | one of the seven evidence kinds, with a Lean certificate and allowed axiom footprint |
| `refuted` | the query's claimed implication/equivalence is false under the declared premises | a `refutation` certificate: an explicit counterexample witness, not a failed proof |
| `unresolved` | no disposition has been reached | candidate metadata and a rationale; no negative claim |
| `notEstablished` | within the named scope and snapshot, the declared search found no certificate of the requested kind | scope, snapshot, rationale, and machine-recomputable dependency evidence |
| `outOfScope` | the query is outside the declared audit jurisdiction, for example no shared context or no declared translation exists | a statement-level reason, scope, and provenance; not logical absence |

`refuted` is an outcome, not an eighth relation kind. Its evidence kind is `refutation`. A failed
proof attempt, a `sorry`, a timeout, or a missing certificate never produces `refuted`.

## 7. Evidence kinds

The seven evidence kinds are fixed. An eighth kind is not admitted in R1.

| kind | semantic obligation |
|---|---|
| `definitionalIdentity` | after the declared translations, a fresh kernel `rfl` check proves the two terms definitionally equal |
| `implication` | `∀ δ, Π δ → (P δ → Q δ)` for the translated predicates |
| `equivalence` | `∀ δ, Π δ → (P δ ↔ Q δ)` for the translated predicates |
| `conditionalComposition` | a typed composition consuming named parent certificates, with mediators, bridges, and premise closure |
| `observationalEquivalence` | equality of every declared channel on every input in its domain, under the premises |
| `distinguishability` | either an explicit separating observation witness or an explicit identifiability/decoder certificate |
| `refutation` | `∃ δ, Π δ ∧ P δ ∧ ¬ Q δ` (a one-sided counterexample witness) |

`conditionalComposition` is not a list of parent names attached to an independently proved child.
It must consume the typed parent proofs through a sound composition combinator and propagate
premises. `definitionalIdentity` is not propositional equality. `observationalEquivalence` is not
equality of the underlying predicates.

## 8. Queue and cluster plan

`pair-queue.json` contains all 136 pairs. Each row has:

- a canonical pair ID and the two theory identifiers;
- exactly one `screeningCluster`;
- a requirement object whose `requiredOutcome` is `namedQuery`, whose permitted alternative is
  `outOfScope`, and whose `outcomeAssigned` is `null` in R1;
- a legacy coverage summary: census label/subtype/citation, record counts by status and kind,
  pair-level anchors, named queries, certified/unresolved record IDs, and any dangling endpoint;
- an empty `candidateQueryIds` list and a `null` `adjudicationOutcome`.

No certified, refuted, unresolved, notEstablished, or outOfScope outcome is assigned to a queue
row in R1. Legacy statuses are coverage history, not R1 verdicts.

`cluster-plan.json` partitions the 136 pairs into six disjoint primary clusters:

1. `surface-free-energy`;
2. `excited-state-kinetics`;
3. `quenching-quantum-yield`;
4. `radiative-energy-transfer`;
5. `conical-intersection`;
6. `cross-domain-screening`.

A pair belongs to exactly one primary cluster. Work packages are execution batches inside a
cluster; every pair belongs to exactly one work package. Cluster membership is a work-package
assignment, not a chemical verdict and not an audit outcome. A cross-domain pair is not thereby
out of scope; it still needs a named query or a statement-level justification.

## 9. Validation and reproducibility

The validator is run from the repository root:

```bash
python3 audit_boundary/validate_boundary.py
```

It checks, fail-closed:

- the exact seventeen-theory universe and the exact 136-pair universe;
- identifier uniqueness and every pair/cluster/statement reference;
- the five-status and seven-kind vocabularies, including the prohibition on `refuted` as a kind
  and on `adjudication` as a kind;
- statement source metadata: authority resolution, delivered signature, source line, and every
  SHA-256 in the inventory;
- the complete `PhotoLean/**/*.lean` source manifest, so no Lean file or declaration can change
  unnoticed;
- cluster disjointness, coverage, and work-package coverage;
- every queue row's requirement and legacy coverage summary against the frozen registry;
- the unchanged legacy-registry hash.

A missing file, a duplicate identifier, an unresolved reference, a hash drift, or an extra/missing
Lean source is a failure, not a warning. The validator exits `0` only when every check passes.

## 10. Non-exhaustiveness

This is a bounded audit. It is not a completeness theorem.

- The inventory is the fixed statement authority plus one shared kernel endpoint; it is not a
  claim that no other statement could be written.
- The 136 pairs are a finite universe; it is not a claim that no other pair of theories could be
  compared.
- A `certified` record is a checked relation under its declared context and premises; it is not a
  claim that the relation is physically universal.
- A `notEstablished` or `outOfScope` record is a scoped negative registration; it is not logical
  non-existence.
- The audit does not prove source fidelity, empirical adequacy, or historical genealogy.
- No pair is forced into a relation, and no relation count is a target.

Outside the frozen universe, nothing is assessed in R1.
