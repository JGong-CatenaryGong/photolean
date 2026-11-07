# Relation-Audit Migration Inventory Report (R2)

Status: **inventory only** — this is not a production registry and not an audit verdict.

## Source of truth

- scanner: `tools/counts.py` (`4c9423d3e074…`)
- relations module: `PhotoLean/Relations.lean` (`a50f4bc4c24c…`)
- disposition ledger: `relation_audit/dispositions.json` (`d9d2c7a4f9d4…`)

## Counts

| item | value |
|---|---|
| declarations | 78 |
| sections | 17 |
| sectionsWithDeclarations | 15 |
| pairs | 136 |
| legacyEdges | 26 |
| legacyUniqueAbsences | 110 |
| legacyRawAbsenceRegistryRows | 114 |
| legacyCoveredPairs | 136 |
| unaccountedPairs | 0 |
| bothEdgeAndAbsencePairs | 0 |
| duplicateRegistryRows | 4 |
| ambiguousPairs | 1 |
| completionBlockPairs | 26 |
| dispositionEntries | 78 |
| intraTheoryDeclarations | 7 |
| pilotMappedDeclarations | 7 |
| unresolvedCandidateDeclarations | 0 |

## Dispositions

| disposition | declarations |
|---|---|
| `pilot-certificate` | 7 |
| `certificate-required` | 41 |
| `support-lemma` | 13 |
| `intra-theory-adjudication` | 4 |
| `look-alike-non-relation` | 8 |
| `metadata-only` | 2 |
| `scoped-relation-documentation` | 3 |
| `unresolved-candidate` | 0 |

## Pair association

| association | declarations |
|---|---|
| `direct` | 32 |
| `supporting` | 17 |
| `look-alike` | 8 |
| `intra-theory` | 7 |
| `transitive` | 2 |
| `none` | 12 |

## Legacy pair census

26 edges + 110 unique absences = 136/136 covered (legacy census, not audit coverage); unaccounted 0, edge∩absence 0.

## Legacy declaration class mapping (non-audit)

| class | quoted | computed | verdict |
|---|---|---|---|
| `RACI` | 5 | 5 | MATCH |
| `adjudication` | 8 | 6 | DIFF |
| `certificate` | 15 | 15 | MATCH |
| `composition` | 26 | 30 | DIFF |
| `equivalence/entailment/bridge` | 22 | 22 | MATCH |
| `other` | 2 | 0 | DIFF |

## Exceptional classifications

- `adjudication`: `P-Kasha-KashaVavilov`
- `composition`: `P-BEP-Sabatier`, `P-Kasha-QuantumYield`, `P-SternVolmer-QuantumYield`, `P-QuantumYield-FluorPhos`, `P-QuantumYield-Forster`, `P-QuantumYield-Einstein`, `P-QuantumYield-RACI`
- `conditional-premise`: `P-Marcus-Kasha`
- `definitional`: `P-Marcus-EnergyGapLaw`, `P-Marcus-ICvsISC`, `P-EnergyGapLaw-ICvsISC`
- `in-module`: `P-Marcus-StokesShift`
- `look-alike`: `P-Marcus-Sabatier`, `P-Marcus-RACI`, `P-Sabatier-Goldschmidt`, `P-Goldschmidt-Forster`, `P-SternVolmer-Forster`
- `model-level-composition`: `P-SternVolmer-FluorPhos`
- `one-sided`: `P-Kasha-EnergyGapLaw`, `P-EnergyGapLaw-RACI`, `P-ICvsISC-RACI`
- `predicate-equivalence`: `P-EnergyGapLaw-StokesShift`
- `premise-level`: `P-FluorPhos-ICvsISC`
- `shape`: `P-Hammond-EnergyGapLaw`, `P-BEP-EnergyGapLaw`
- `transitive-registry-only`: `P-Hammond-SymmetryFactor`
- `transitive-via-kernel`: `P-Marcus-SymmetryFactor`, `P-BEP-SymmetryFactor`
- `undelivered-candidate`: `P-Kasha-SternVolmer`, `P-Kasha-FluorPhos`, `P-KashaVavilov-SternVolmer`, `P-KashaVavilov-QuantumYield`, `P-KashaVavilov-FluorPhos`, `P-KashaVavilov-EnergyGapLaw`

## Undelivered candidates

- `P-Kasha-SternVolmer` (Kasha / SternVolmer): Section 16: 'Kasha against SternVolmer - no edge (registered candidate, not delivered)'.
- `P-Kasha-FluorPhos` (Kasha / FluorPhos): Section 16: 'FluorPhos against Kasha / KashaVavilov - no edge (undelivered candidate compositions)'.
- `P-KashaVavilov-SternVolmer` (KashaVavilov / SternVolmer): Section 16: 'KashaVavilov against SternVolmer / QuantumYield - undelivered candidate compositions'.
- `P-KashaVavilov-QuantumYield` (KashaVavilov / QuantumYield): Section 16: 'KashaVavilov against SternVolmer / QuantumYield - undelivered candidate compositions'.
- `P-KashaVavilov-FluorPhos` (KashaVavilov / FluorPhos): Section 16: 'FluorPhos against Kasha / KashaVavilov - no edge (undelivered candidate compositions)'.
- `P-KashaVavilov-EnergyGapLaw` (KashaVavilov / EnergyGapLaw): Section 16 completion block: EnergyGapLaw against KashaVavilov is registered as a no-edge pair, and the EnergyGapLaw bullet calls KashaVavilov an undelivered composition candidate.

## Ambiguous cases

- `P-Marcus-RACI` counted as `absence`: none (the pair is covered either way); counting it as an edge would give 27 edges + 109 absences

## Duplicate registry rows

- `P-FluorPhos-StokesShift`: listed 2 times
- `P-StokesShift-Forster`: listed 2 times
- `P-StokesShift-Einstein`: listed 2 times
- `P-ICvsISC-Forster`: listed 2 times

## Non-claims

- This inventory is not a production full registry; relation_audit/registry.json is not created.
- No 136/136 resolved-coverage claim is made; the pair list is a legacy census universe.
- Legacy edge/absence labels are not audit judgments and are not mapped to certified/notEstablished/outOfScope.
- No new Lean certificate wrapper is added and no legacy edge is claimed migrated.
- Undelivered candidates are migration items only; they are not audit `unresolved` records.
- An inventory --check exit code 0 means the artifacts are consistent with tools/counts.py, not that the relation audit passed.
- The census remains a report, not an acceptance gate.
