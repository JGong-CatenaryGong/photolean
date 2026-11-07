# R4 cumulative coverage — integration notes

Status: **accepted-R4** after four independent K3 PASS verdicts. The cumulative ledger
`bounded_audit/coverage.json` now records all 46 R4 rows as `accepted-R4`. The historical
`submittedPairs`/`submittedWorkPackages` key names and package fragments remain unchanged as
submission-layout snapshots; acceptance is carried by each row's `acceptance` field. Package
queries, evidence, and source hashes were not changed during acceptance.

Round: R4. Snapshot: `snap-bounded-audit-2026-11-04` (E1/E2/CI reuse it; E2 additionally
uses the package-local id `snap-bounded-audit-2026-11-04-r4e2`). Date: 2026-11-04.

## 1. Contents

| path | owner | content |
|---|---|---|
| `r4/excited-01/` | E1 execution agent | 16 excited-state-kinetics pairs: `screening.json`, `search-log.json`, `coverage-fragment.json`, `validate.py`, `probes/E1-probe.lean`, `evidence/` |
| `r4/excited-02/` | E2 execution agent | 14 excited-state-kinetics pairs, same artifact set (`probes/E2-probe.lean`) |
| `r4/conical-01/` | CI execution agent | 16 conical-intersection pairs, same artifact set (`probes/R4-CI-probe.lean`) |
| `r4/validate_coverage.py` | integration agent | cumulative-ledger gate (this round) |
| `r4/validate_r3_content.py` | integration agent (planning correction, plan step 8) | derived R3 package-content gate: the accepted `validate_r3.py` minus exactly seven current-ledger freshness checks (§7.2) |
| `r4/README.md` | integration agent | this file |
| `bounded_audit/coverage.json` | integration agent | cumulative ledger, 67/136 screened, 69 remaining |

The integration agent **did not** modify any package query, evidence, probe, report or
validator, any accepted R1/R2/R3 artifact, `PhotoLean/**`, the legacy registry, the original
repositories, the manuscript, or `backup/`. The only file added after the first integration
pass is the derived `r4/validate_r3_content.py`, required by the amended plan step 8; it
does not edit the accepted R3 package.

## 2. Package boundaries

| package | R1 work package | pairs | queries | certified | refuted | unresolved | notEstablished | outOfScope | probe certificates |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| E1 `excited-01` | `WP-excited-state-kinetics-01` | 16 | 16 | 6 | 0 | 9 | 0 | 1 | 6 |
| E2 `excited-02` | `WP-excited-state-kinetics-02` | 14 | 14 | 5 | 0 | 4 | 0 | 5 | 5 |
| CI `conical-01` | `WP-conical-intersection-01` | 16 | 16 | 8 | 0 | 6 | 1 | 1 | 8 |
| **R4 total** | — | **46** | **46** | **19** | **0** | **19** | **1** | **7** | **19** |

Every pair carries exactly one named statement-level query; every non-certified query (27)
is backed by exactly one `search-log.json` entry. The three pair sets are pairwise disjoint
and disjoint from the accepted R2 (10) and R3 (11) pairs; they are a subset of the 115 pairs
left unscreened after R3.

`outOfScope` is a jurisdiction finding, never a claim of logical absence;
`notEstablished` is a scoped negative search; `unresolved` is a named candidate with a
recorded missing bridge; `certified` is a checked Lean certificate under its declared
premises and context. No failed proof is relabelled as `refuted`; the R4 packages contain
no `refuted` outcome.

## 3. Cumulative state

| quantity | value |
|---|---:|
| universe | 136 pairs (17 theories) |
| accepted before R4 (R2 + R3) | 21 (10 + 11) |
| submitted in R4 | 46 (16 + 14 + 16) |
| **cumulative screened** | **67** |
| **remaining** | **69** |
| by round | `R2: 10, R3: 11, R4: 46` |
| named queries over the 67 pairs | 77 (19 + 12 + 46) |
| query outcomes over those 77 | certified 42, refuted 0, unresolved 27, notEstablished 1, outOfScope 7 |

Ledger shape (`bounded_audit/coverage.json`):

- `screenedPairs` — the **21 accepted** R2/R3 entries, preserved verbatim with their
  acceptance statuses, query counts and per-status counts;
- `submittedPairs` — the **46 R4** entries, every one marked
  `submitted-R4-pending-review`, with the per-pair query ids and status counts;
- `cumulative` — counts *both* lists (`screenedPairCount = 67`), which is what the ledger
  has always meant by "screened": a pair with a submitted or accepted screening package,
  not a pair with a certified relation;
- `roundHistory` — `R2 10/126`, `R3 21/115`, `R4 67/69`;
- `remainingPairIds` — the 69 pairs left after R4, in R1 queue order.

Why two lists instead of one 67-entry `screenedPairs`: the accepted R3 package and the CI
package validator both pin the *accepted* set (`screenedPairs ==` the 21 accepted R2/R3
pairs), while the R4 plan requires the cumulative count to become 67. Keeping the accepted
entries in `screenedPairs` and the pending ones in `submittedPairs` satisfies both, keeps
the accepted entries' hashes/statuses untouched, and keeps the accepted R2 and CI package
validators green (`bounded_audit/r4/conical-01/validate.py` explicitly allows
`screenedPairCount ∈ {21, 67}`). The accepted R3 validator's round-frozen ledger checks are
a separate ledger-version seam, resolved by the derived content validator in §7.2; no R3
artifact is edited.

## 4. Hash-cycle rules

The ledger is the only artifact whose content necessarily changes after packages are
accepted, so its hash edges are one-directional by design.

- The ledger **records** the R2 package hash (R2 does not pin the ledger) and the three R4
  package hashes: screening, search log, fragment, probe and validator per package.
- The ledger **records no hash of itself** and **no hash of `bounded_audit/r3/screening.json`**.
  The accepted R3 package pins the ledger twice (`snapshot.coverageLedgerSha256` and
  `coverageReference.sha256`); recording the R3 screening hash back would close a cycle, and
  the R3 work-package entry therefore carries no `sha256` field.
- No R4 package may pin the ledger. `excited-02` and `conical-01` assert this themselves; E1
  references the ledger only as read-only prose.
- The derived `validate_r3_content.py` is not recorded in the ledger and records no hashes
  back into it; it excludes the ledger hash pin and therefore adds no cycle edge.
- `validate_coverage.py` enforces all of the above: it fails on a self-hash slot
  (`cycle.selfKey`), on the ledger's own SHA-256 or the R3 screening SHA-256 appearing in the
  ledger text (`cycle.selfPin`, `cycle.r3ScreeningPin`), on an R3 work-package hash
  (`cycle.r3WpPin`), and on any R4 package that pins the ledger
  (`pkg.<tag>.ledgerPinned`, `cycle.packagePinsLedger`, `pkg.<tag>.coverageReferenceSha`).

Do not "fix" a future mismatch by adding a self-hash or an R3 hash. Adjust the relevant
validator constants deliberately in a new plan, or add a derived historical gate as §7.2
does; never edit the accepted R3 package or `bounded_audit/r3/screening.json`.

## 5. Reproduction

From `bounded-relation-audit-2026-11-04/photolean`:

```bash
python3 bounded_audit/r4/validate_coverage.py                 # integration gate
python3 bounded_audit/r4/excited-01/validate.py               # package gates
python3 bounded_audit/r4/excited-02/validate.py
python3 bounded_audit/r4/conical-01/validate.py
python3 audit_boundary/validate_boundary.py                   # R1
python3 bounded_audit/validate_screening.py                   # R2
python3 bounded_audit/validate_r3.py                          # accepted R3 historical gate: expects exactly 7 stale-ledger failures (§7.2)
python3 bounded_audit/r4/validate_r3_content.py               # derived R3 content gate: exit 0 (§7.2)
proofs/scripts/check.sh --strict                              # build + sorry/axiom scan
proofs/scripts/lake env lean bounded_audit/r4/excited-01/probes/E1-probe.lean
proofs/scripts/lake env lean bounded_audit/r4/excited-02/probes/E2-probe.lean
proofs/scripts/lake env lean bounded_audit/r4/conical-01/probes/R4-CI-probe.lean
sha256sum relation_audit/registry.json                        # 25d38791…ecbf0
find PhotoLean -name '*.lean' | wc -l                         # 102
```

Run the three probe compilations **serially** and not while `check.sh --strict` is running:
they all use Lake, and concurrent runs can fail with a lock error (observed once; serial
re-runs exit 0). Do not delete Lake lock files.

`validate_coverage.py` supports `--root DIR`, `--coverage PATH`, `--override REL=PATH` and
`--skip-package-validators`; the override hook exists so mutation tests can mutate copies
under `/tmp` without touching package content.

## 6. Verification matrix (real results at submission)

| gate | command | result |
|---|---|---|
| R1 boundary | `audit_boundary/validate_boundary.py` | exit 0, PASS, 136 pairs, 102 Lean files |
| R2 package | `bounded_audit/validate_screening.py` | exit 0, PASS |
| R3 package (historical) | `bounded_audit/validate_r3.py` | **exit 1, exactly the 7 ledger-freshness checks — see §7.2** |
| R3 package content (derived) | `bounded_audit/r4/validate_r3_content.py` | exit 0, PASS, 7 checks excluded, no content failure |
| E1 package | `bounded_audit/r4/excited-01/validate.py` | exit 0, PASS |
| E2 package | `bounded_audit/r4/excited-02/validate.py` | exit 0, PASS |
| CI package | `bounded_audit/r4/conical-01/validate.py` | exit 0, PASS |
| coverage | `bounded_audit/r4/validate_coverage.py` | exit 0, PASS, 846 checks |
| strict build/scan | `proofs/scripts/check.sh --strict` | exit 0, `build: OK`, scan `clean`, `verdict: PASS` |
| probes (19 declarations) | `lake env lean …/E1-probe.lean`, `…/E2-probe.lean`, `…/R4-CI-probe.lean` | exit 0 ×3; 6 + 5 + 8 `#print axioms` blocks, each `[propext, Classical.choice, Quot.sound]` |
| legacy registry | `sha256sum relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| frozen Lean tree | `find PhotoLean -name '*.lean' \| wc -l` | 102 |
| coverage mutations | 15 fail-closed mutations under `/tmp` | all exit 1 on the expected check, unmutated copy exit 0 |
| R3 content mutations | 4 fail-closed mutations under `/tmp` (§7.2) | baseline exit 0; query, endpoint-provenance, search-log-evidence and probe-source drift each exit 1 on the expected code |

## 7. Known seams

These are recorded, not papered over. None of them is repaired by editing an accepted
artifact from this directory.

### 7.1 R3 report-vs-current hashes (accepted-status/hash synchronization)

The accepted R3 report (`loop/产出.md` of R3) records
`587b867f…` for `bounded_audit/r3/screening.json` and `1c526971…` for
`bounded_audit/coverage.json`. The files on disk at R4 submission hash
`452d213c…` and (before this integration) `a584d38e…`. The difference is not a content
change: when R3 was accepted the lead synchronized the accepted-status fields, which changed
`coverage.json`, which forced a re-pin of the R3 screening snapshot
(`coverageLedgerSha256` / `coverageReference.sha256`) and therefore changed the R3 screening
file too (R3 log: "lead 已将 coverage ledger 的 R3 状态从 submitted 更新为 accepted-R3，并复跑
R3 validator"). The R3 report's hash table is consequently a pre-synchronization snapshot.
Both values are recorded here for traceability; no screening content differs.

### 7.2 The R3 validator pins the R3 ledger state; derived content gate

`validate_r3.py` hard-pins the ledger's hash **and** its R3 state (`round == R3`,
`cumulative 21/115`, `byRound {R2:10, R3:11}`, `remainingPairIds` = queue minus 21). R4
integration advances the same ledger to 67/69, so those checks cannot stay green while the
accepted R3 package and the accepted ledger entries stay untouched. This is a ledger-version
seam, not R3 content drift. The amended R4 plan (step 8) resolves it by adding
`r4/validate_r3_content.py`, a derived historical-package validator.

The original accepted validator is unchanged (`sha256 2e306da6…`) and still reports exactly
the seven enumerated stale-ledger checks and no content check:

```text
$ python3 bounded_audit/validate_r3.py            # exit 1
R3 bounded screening validation
  root: …/photolean
  checks failed: 7
FAIL [snapshot.coverageLedgerSha256] bounded_audit/coverage.json hash drift: a584d38e… != dd9cffbf…
FAIL [coverage.round] coverage ledger round drift
FAIL [coverage.cumulative] cumulative screened count drift
FAIL [coverage.remaining] cumulative remaining count drift
FAIL [coverage.byRound] coverage by-round counts drift
FAIL [coverage.remainingCount] remainingPairIds has 69 entries, expected 115
FAIL [coverage.remainingSet] remainingPairIds is not the queue minus the screened pairs
RESULT: FAIL (7 failed checks)
```

The failure-code set was also asserted programmatically to equal exactly those seven codes,
with an empty content/package-failure set.

The derived validator keeps every other R3 check unchanged and prints the seven excluded
freshness checks with their pinned-vs-current values:

```text
$ python3 bounded_audit/r4/validate_r3_content.py  # exit 0
R3 bounded screening content validation (derived)
  root: …/photolean
  excluded current-ledger freshness checks: 7
EXCLUDED [snapshot.coverageLedgerSha256] current-ledger hash pin on bounded_audit/coverage.json (accepted pin a584d38e…, current dd9cffbf…; owned by r4/validate_coverage.py)
EXCLUDED [coverage.round] current-ledger round: accepted package pinned R3, current 'R4' (owned by r4/validate_coverage.py)
EXCLUDED [coverage.cumulative] current-ledger cumulative screened count: pinned 21, current 67 (owned by r4/validate_coverage.py)
EXCLUDED [coverage.remaining] current-ledger cumulative remaining count: pinned 115, current 69 (owned by r4/validate_coverage.py)
EXCLUDED [coverage.byRound] current-ledger by-round counts: pinned {'R2': 10, 'R3': 11}, current {'R2': 10, 'R3': 11, 'R4': 46} (owned by r4/validate_coverage.py)
EXCLUDED [coverage.remainingCount] current-ledger remaining list length: pinned 115, current 69 (owned by r4/validate_coverage.py)
EXCLUDED [coverage.remainingSet] current-ledger remaining list contents: pinned queue-minus-screened (115), current 69 (owned by r4/validate_coverage.py)
  checks failed: 0
RESULT: PASS (all R3 package-content checks passed; 7 current-ledger freshness checks excluded)
```

`diff -u bounded_audit/validate_r3.py bounded_audit/r4/validate_r3_content.py` contains only:
the root path (the derived file is one directory deeper), the docstring, the
`EXCLUDED_CHECKS` registry, the `Checker.exclude`/`EXCLUDED` printout, the seven
`c.check(...)` calls replaced by `c.exclude(...)`, and a final `validator.exclusions` check
that fails if the exclusion list is not exactly those seven codes. The ledger is still read
and every non-freshness ledger check still runs: accepted-entry acceptance status, package
path, round, queryCount, byStatus, the accepted R2/R3 pair sets, the surface-gap and
early-cross-domain annotations, and the two accepted work-package entries.

Current cumulative coverage remains owned by `r4/validate_coverage.py`, which re-derives the
accepted 21 entries pair-by-pair from the R2/R3 packages (`accepted.pairSet`,
`accepted.queryCount`, `accepted.byStatus`, `accepted.status`, `accepted.packagePath`,
`accepted.earlyCrossDomain`, `accepted.surfaceGap`) and independently checks the R4
partition and the 67/69, 10/11/46 and 42/0/27/1/7 arithmetic.

Mutation evidence (all mutation inputs under `/tmp`; the untouched sandbox baseline exits 0):

| mutation | expected failure | observed |
|---|---|---|
| blank one query's `chemicalQuestion` | `query.chemicalQuestion` | exit 1, exact code |
| corrupt a source endpoint `signatureSha256` | `endpoint.signatureSha256` | exit 1, exact code |
| empty a search-log entry's `commands` and re-pin `searchLogReference.sha256` | `search.commands` | exit 1, exact code |
| rename a certified probe `def` and re-pin `probeReference.sha256` + evidence probe hashes | `evidence.probeDeclMissing` | exit 1, exact code |

The re-pinned mutations keep the corresponding hash check green, so each rejection is
semantic (query, provenance, evidence record, probe source), not merely a hash mismatch. The
mutation harness lives only in `/tmp`; it modifies only sandbox copies and touches no
repository file. The harness source and its raw transcript are recorded in the round report
`loop/产出.md` §6.1.

Do **not** rewrite `bounded_audit/r3/screening.json` to re-pin the new ledger hash:
`excited-02` pins the current R3 screening hash (`acceptedR3Sha256 = 452d213c…`) and the R3
package pins the ledger, so editing it would cascade into E2. The derived validator is the
approved historical/content gate; the original validator remains the unchanged accepted
artifact that documents the seam.

### 7.3 E1 report records the pre-integration ledger hash

`r4/excited-01/REPORT.md` §6 lists `bounded_audit/coverage.json` at `a584d38e…` as a
read-only reference taken by that package. The integration then rewrote the ledger, so that
recorded value is historical. E1's validator does not read or pin the ledger, so this is a
documentation drift only.

### 7.4 E2 pins the current R3 screening hash

`r4/excited-02/screening.json` snapshot pins `acceptedR3Sha256 = 452d213c…`. That is valid
today; it becomes a downstream edge to re-sync only if the lead ever re-baselines R3 (see
§7.2). The R4 planning correction adds a derived content validator rather than re-baselining
the accepted R3 package, so this edge stays untouched.

## 8. Non-claims

- Screened is not certified; the 67/136 count is coverage, not classification.
- The 46 R4 pairs are submitted, not accepted; this integration does not self-accept and does
  not flip statuses.
- A `certified` row is a checked relation under its declared context, premises and snapshot,
  not a claim of physical universality.
- `unresolved` / `notEstablished` / `outOfScope` records are not negative existence claims.
- The derived R3 content validator does not accept, re-accept or re-open R3; it only proves
  that the accepted R3 package content still passes every non-freshness R3 check against the
  current ledger.
- The cumulative ledger is not a completeness claim about the 136-pair universe.
