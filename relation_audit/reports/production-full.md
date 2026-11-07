# Production Full Validator Report

- status: `PASS` (exit 0)
- mode: `full`
- manifest: `relation_audit/registry.json`
- schema: `relation_audit/schema.json`

## Gates

| gate | status | findings |
|---|---|---|
| `coverage` | PASS | 2 |
| `lean` | PASS | 223 |
| `provenance` | PASS | 1 |
| `references` | PASS | 2 |
| `semantics` | PASS | 2 |
| `snapshot` | PASS | 2 |
| `structure` | PASS | 3 |

## Coverage

- theories: 17/17
- registry: 136/136 pairs
- resolved: 9/136 pairs (complete=false)
- unresolved records: 6

## Counts

- records: 151
- by status: `{'certified': 24, 'notEstablished': 121, 'outOfScope': 0, 'unresolved': 6}`
- certified by kind: `{'conditionalComposition': 1, 'definitionalIdentity': 7, 'distinguishability': 2, 'equivalence': 8, 'implication': 2, 'observationalEquivalence': 3, 'refutation': 1}`
- certificates: 38

## Caveats

- `snapshotDirty`: dirty snapshot(s) 'snap-relation-audit-2026-10-31': artifact hashes were matched against the working tree; a full-mode PASS on a dirty tree needs independent review.
