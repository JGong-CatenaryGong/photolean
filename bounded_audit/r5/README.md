# R5 cumulative coverage — integration notes

Status: **submitted-R5-pending-review**. The five R5 packages are complete and pass their own
gates, and the cumulative ledger now covers **136/136** pairs. That is **submitted coverage**:
before independent K3 review, **accepted coverage is 67/136** (R2 10 + R3 11 + R4 46). The 69
R5 rows stay `submitted-R5-pending-review` until the lead flips them after the six independent
reviews (five packages + this integration). Nothing in this directory self-accepts.

Round: R5. Date: 2026-11-04. Snapshots: package-local (`snap-bounded-audit-2026-11-04-r5rad1`,
`…-r5rad2`) plus the shared R1 id (`snap-bounded-audit-2026-11-04`) reused by RAD3/XD1/XD2.

**R6 resynchronization (2026-11-04).** RAD1 was repaired in R6: the `Q-RAD1-MSS-01` regime prose,
the `Q-RAD1-KKV-01` kind rationale and the `mkvCmp` left StatementRef were corrected, and
`screening.json`, `coverage-fragment.json`, the probe and `validate.py` were regenerated. The RAD1
counts did not move (16 pairs / 17 queries / 11 certified / 2 unresolved / 4 outOfScope / 0 refuted
/ 0 notEstablished), no theorem, proof, relation kind or outcome changed, and the other four R5
packages are untouched. This README and the ledger's RAD1 record now carry the repaired hashes
(§7); all 69 R5 rows remain `submitted-R5-pending-review`, accepted stays 67/136 and nothing here
self-accepts. The R6 resynchronization wrote only `bounded_audit/coverage.json`, this README and
`loop/产出.md`.

**R7 resynchronization (2026-11-04).** RAD1's last reversed Marcus–StokesShift wording — the §4
probe block comment, which said the emission energy becomes negative in the inverted region — was
corrected to the delivered three-regime reading (`emEnergy = e00 - lam`, positive exactly in the
inverted region `lam < e00`, negative in the normal region `e00 < lam`, zero at `e00 = lam`).
`validate.py` now pins that comment (and rejects the old reversed phrasing), with mutations M13/M14
proving the pin fails closed; `screening.json`, `coverage-fragment.json`, the probe and
`validate.py` were regenerated, while `search-log.json` is unchanged. RAD1 counts again did not
move (16 pairs / 17 queries / 11 certified / 2 unresolved / 4 outOfScope / 0 refuted / 0
notEstablished), no theorem, proof, relation kind or outcome changed, and the other four R5
packages are untouched. This README and the ledger's RAD1 record now carry the R7 hashes (§7); all
69 R5 rows remain `submitted-R5-pending-review`, accepted stays 67/136 and nothing here
self-accepts. The R7 resynchronization wrote only `bounded_audit/coverage.json`, this README and
`loop/产出.md`.

## 1. Contents

| path | owner | content |
|---|---|---|
| `r5/radiative-01/` | RAD1 execution agent | 16 radiative-energy-transfer pairs: `screening.json` (17 queries), `search-log.json` (6 entries), `coverage-fragment.json`, `validate.py`, `build_screening.py`, `probes/RAD1-probe.lean` (11 certificates), `evidence/` |
| `r5/radiative-02/` | RAD2 execution agent | 16 radiative-energy-transfer pairs, same artifact set (16 queries, 12 search entries, `probes/RAD2-probe.lean`, 4 certificates) |
| `r5/radiative-03/` | RAD3 execution agent | 13 radiative-energy-transfer pairs (16 queries, 6 search entries, `probes/RAD3-probe.lean`, 10 certificates) |
| `r5/cross-domain-01/` | XD1 execution agent | 15 cross-domain pairs (16 R1 work-package pairs minus the accepted `P-Kasha-Sabatier`), 15 queries, 15 search entries, `probes/XD1-probe.lean` (3 candidate identities, **no certified outcome**) |
| `r5/cross-domain-02/` | XD2 execution agent | 9 cross-domain pairs, 11 queries, 11 search entries, **no probe** and no certified outcome |
| `r5/validate_r4_ci_content.py` | integration agent | derived R4 CI package-content gate: the accepted `r4/conical-01/validate.py` minus exactly one stale current-ledger check (§4) |
| `r5/validate_coverage.py` | integration agent | R5 cumulative coverage gate (this round): 136-pair universe, all eight packages, hashes, cycle rules, acceptance-neutral R5 totals |
| `r5/README.md` | integration agent | this file |
| `bounded_audit/coverage.json` | integration agent | cumulative ledger: 136/136 screened, 0 remaining, 67 accepted + 69 submitted |

The integration agent **did not** modify any R5 package query, evidence, probe, report, builder or
validator, any accepted R1–R4 artifact, `PhotoLean/**`, the legacy registry, the original
repositories, the manuscript, or `backup/`. Files written in the integration step are exactly:
`bounded_audit/coverage.json`, `bounded_audit/r5/validate_r4_ci_content.py`,
`bounded_audit/r5/validate_coverage.py`, `bounded_audit/r5/README.md`, `loop/产出.md`. The R5
packages were read only; their recorded hashes are the ones their REPORTs declare
(§7).

## 2. Package boundaries

| package | R1 work package | pairs | queries | certified | refuted | unresolved | notEstablished | outOfScope | probe declarations |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| RAD1 `radiative-01` | `WP-radiative-energy-transfer-01` | 16 | 17 | 11 | 0 | 2 | 0 | 4 | 11 |
| RAD2 `radiative-02` | `WP-radiative-energy-transfer-02` | 16 | 16 | 4 | 0 | 6 | 0 | 6 | 4 |
| RAD3 `radiative-03` | `WP-radiative-energy-transfer-03` | 13 | 16 | 10 | 0 | 1 | 1 | 4 | 10 |
| XD1 `cross-domain-01` | `WP-cross-domain-screening-01` minus `P-Kasha-Sabatier` | 15 | 15 | 0 | 0 | 3 | 0 | 12 | 3 (candidate, not certified) |
| XD2 `cross-domain-02` | `WP-cross-domain-screening-02` | 9 | 11 | 0 | 0 | 0 | 0 | 11 | 0 (no probe) |
| **R5 total** | — | **69** | **75** | **25** | **0** | **12** | **1** | **37** | **28 declarations, 25 certificates** |

Every pair carries at least one named statement-level query; exactly six pairs carry a second,
chemically distinct query (`P-Marcus-EnergyGapLaw`; `P-FluorPhos-ICvsISC`;
`P-EnergyGapLaw-StokesShift`; `P-EnergyGapLaw-ICvsISC`; `P-Goldschmidt-EnergyGapLaw`;
`P-Goldschmidt-Forster`). Every one of the 50 non-certified R5 queries — 6 + 12 + 6 + 15 + 11 for
RAD1, RAD2, RAD3, XD1, XD2 — is backed by exactly one `search-log.json` entry with a
back-reference, searched statements/kinds/contexts, real commands and results, attempted
strategies, a candidate record, the exact remaining gap or jurisdiction reason and recompute
commands. No R5 package has a `refuted` outcome; no failed proof is relabelled.

The five pair sets are pairwise disjoint, disjoint from the accepted 67, disjoint from each other
and cover exactly the 69 pairs left after R4. `P-Kasha-Sabatier` (accepted in R2) is not rescreened.
`XD1`'s screening `workPackage.id` is `XD1-CROSS-DOMAIN-01`; the ledger records both that id and
the R1 work package `WP-cross-domain-screening-01`.

`outOfScope` is a statement-level jurisdiction finding, never a claim of logical absence;
`notEstablished` is a scoped negative search; `unresolved` names a concrete candidate and the
missing bridge; `certified` is a checked typed Lean certificate under its declared premises and
context.

## 3. Cumulative state

| quantity | value |
|---|---:|
| universe | 136 pairs (17 theories) |
| accepted before R5 (R2 + R3 + R4) | 67 (10 + 11 + 46) |
| submitted in R5 | 69 (16 + 16 + 13 + 15 + 9) |
| **cumulative submitted coverage** | **136 / 136** |
| **accepted coverage before review** | **67 / 136** |
| **remaining** | **0** |
| by round | `R2: 10, R3: 11, R4: 46, R5: 69` |
| named queries over the 136 pairs | 152 (19 + 12 + 46 + 75) |
| cumulative query outcomes | certified 67, refuted 0, unresolved 39, notEstablished 2, outOfScope 44 |

Screened ≠ certified: of the 136 covered pairs, 67 certified queries exist, but the pair-level
coverage includes unresolved, notEstablished and outOfScope records. The 136/136 number is a
bounded-audit coverage count, not an exhaustive classification.

Ledger shape (`bounded_audit/coverage.json`):

- `screenedPairs` — the **21 accepted R2/R3** entries, preserved verbatim (content-equal to the
  frozen R4 snapshot's block), with their acceptance statuses, query counts and per-status counts;
- `submittedPairs` — the **46 R4** entries, preserved verbatim, every one `accepted-R4`; the key
  name is the R4 submission-layout name and acceptance is carried by the row field;
- `r5SubmittedPairs` — the **69 R5** entries, every one `submitted-R5-pending-review`, with
  per-pair query ids, query counts and status counts;
- `r5WorkPackages` — the five R5 package records (screening/search-log/fragment/probe/validator
  SHA-256, pair/query counts, uniform acceptance);
- `cumulative` — counts all three lists (`screenedPairCount = 136`), with
  `acceptedPairCount`/`submittedPairCount` derived from the row states (67/69 before review);
- `roundHistory` — `R2 10/126`, `R3 21/115`, `R4 67/69`, `R5 136/0`;
- `remainingPairIds` — empty;
- `frozenSnapshots` — the frozen R4 accepted-ledger snapshot `r4/coverage-accepted.json`
  (`d1e44bf7…32fa`), recorded but not rewritten.

### 3.1 Acceptance protocol (no validator edit required)

The R5 coverage validator computes `acceptedPairCount`/`submittedPairCount` from the R5 row
states; it does not hardcode either. To record lead acceptance, flip **uniformly**:

1. all 69 `r5SubmittedPairs[].acceptance` → `accepted-R5`;
2. all five `r5WorkPackages[].acceptance` → `accepted-R5`;
3. `cumulative.acceptedPairCount` → 136, `cumulative.submittedPairCount` → 0;
4. `roundHistory[R5].acceptance` → `accepted-R5`.

Package frames stay untouched: the five `coverage-fragment.json` files remain immutable
`submitted-R5-pending-review` submission snapshots, which the validator requires. A rows-only flip
(without the work-package block and the cumulative counts) is rejected as an inconsistent ledger.
Before review the same validator passes with the 67/69 state; both states were exercised by
mutation tests (§6). `acceptedBeforeReviewPairCount` stays 67 in both states as the historical
fact.

## 4. Hash-cycle rules

The ledger is the only artifact whose content necessarily changes after packages are accepted, so
its hash edges are one-directional by design.

- The ledger **records** the R2 package hash (R2 does not pin the ledger) and, for each R4 and R5
  package, the screening, search-log, fragment, probe and validator hashes.
- The ledger **records no hash of itself** and **no hash of `bounded_audit/r3/screening.json`**.
  The accepted R3 package pins the ledger twice (`snapshot.coverageLedgerSha256`,
  `coverageReference.sha256`); recording the R3 screening hash back would close a cycle. The R3
  work-package entry therefore carries no `sha256` field.
- No R5 package may read, pin or hash the mutable ledger. Each R5 screening package derives its
  prior count (67) from the five accepted screening packages themselves and asserts the
  abstention; their fragments carry no cumulative count and no ledger hash.
- `validate_coverage.py` enforces all of the above: it fails on a self-hash slot
  (`cycle.selfKey`), on the ledger's own SHA-256 or the R3 screening SHA-256 appearing in the
  ledger (`cycle.selfPin`, `cycle.r3ScreeningPin`), on a ledger hash in a package screening,
  search log or fragment (`cycle.packagePinsLedger`, `cycle.searchLogPinsLedger`,
  `cycle.fragmentPinsLedger`), and on any R5 snapshot that pins the ledger
  (`pkg.<tag>.ledgerPinned`).
- `validate_r4_ci_content.py` merely *reads* the current ledger; it records no hash back and adds
  no cycle edge.

Do not "fix" a future mismatch by adding a self-hash or an R3 hash. Adjust the relevant validator
constants deliberately in a new plan, or add a derived historical gate as §5 does; never edit the
accepted R3 package or `bounded_audit/r3/screening.json`.

## 5. Historical gates and the exact stale-ledger exclusions

The R5 plan enumerates the historical gates explicitly. Two accepted validators pin the *mutable*
ledger to an older round state and therefore cannot be green against the 136/136 ledger without
editing accepted artifacts; the plan resolves this with derived content gates, and this section
records exactly what is excluded. **No one claims that the original R3/R4 current-ledger
validators remain green.**

### 5.1 R3: `bounded_audit/validate_r3.py` (accepted, unchanged) — 7 stale checks

The accepted R3 validator pins the ledger hash and the R3 round state. Against this ledger it
exits 1 with exactly the seven enumerated codes and **no content failure**:

```text
snapshot.coverageLedgerSha256   coverage.round        coverage.cumulative
coverage.remaining              coverage.byRound      coverage.remainingCount
coverage.remainingSet
```

`bounded_audit/r4/validate_r3_content.py` (accepted in R4) keeps every other R3 check and passes:
exit 0, 7 `EXCLUDED` lines, 0 failures. Its excluded set is asserted to be exactly those seven.

### 5.2 R4 CI: `bounded_audit/r4/conical-01/validate.py` (accepted, unchanged) — 1 stale check

The accepted CI package validator pins `cumulative.screenedPairCount ∈ {21, 67}`. R5 advances the
same ledger to 136, so it exits 1 with exactly one failure:

```text
FAIL [coverage.cumulative] cumulative screened count is neither the accepted 21 nor the integrated 67
```

`bounded_audit/r5/validate_r4_ci_content.py` is derived from that accepted validator (the diff is
only the docstring, the root path, the package-relative path constant, the exclusion registry, the
`EXCLUDED` printout, that one `c.check` replaced by `c.exclude`, and a final fail-closed
`validator.exclusions` assertion). It passes with 0 failures and exactly one `EXCLUDED` line. All
CI content/evidence checks remain, including the accepted-R2/R3 pair-set checks
(`coverage.acceptedSet` still compares `screenedPairs` to the 21 accepted R2/R3 pairs) and the
probe, search-log, endpoint and fragment checks.

### 5.3 R4 integration: `bounded_audit/r4/validate_coverage.py` (accepted, R4-frozen)

This gate is round-frozen: its own content checks target the frozen snapshot
`bounded_audit/r4/coverage-accepted.json`. It is run as

```bash
python3 bounded_audit/r4/validate_coverage.py \
    --coverage bounded_audit/r4/coverage-accepted.json --skip-package-validators
```

→ exit 0, 840 checks passed, 67/136 screened, 69 remaining.

`--skip-package-validators` suppresses only that gate's **embedded re-runs** of the three R4
package validators; those three gates are enumerated and run separately: E1 and E2 directly
(exit 0 each), and the CI package through §5.2's derived content validator. Without the flag the
frozen gate exits 1 with exactly two failures, both from the embedded CI subprocess reading the
advanced ledger:

```text
FAIL [validator.CI.exit]   CI validator exited 1
FAIL [validator.CI.result] CI validator did not print RESULT: PASS
```

That is the only exclusion at this gate; its 840 own checks (including the accepted R2/R3 entries,
the R4 partition, hashes and cycle rules) all run.

### 5.4 Gates that are current and green

| gate | result |
|---|---|
| R1 `audit_boundary/validate_boundary.py` | exit 0, PASS, 17 theories / 136 unique pairs / 1,154 statement rows |
| R2 `bounded_audit/validate_screening.py` | exit 0, PASS |
| R3 derived content `r4/validate_r3_content.py` | exit 0, PASS, 7 enumerated exclusions |
| R4 frozen integration `r4/validate_coverage.py --coverage … --skip-package-validators` | exit 0, PASS, 840 checks |
| R4 E1 `r4/excited-01/validate.py` | exit 0, PASS |
| R4 E2 `r4/excited-02/validate.py` | exit 0, PASS |
| R4 CI derived content `r5/validate_r4_ci_content.py` | exit 0, PASS, 1 enumerated exclusion |
| five R5 package gates | exit 0 ×5, PASS |
| R5 coverage `r5/validate_coverage.py` | exit 0, PASS, 10,600 checks |

## 6. Reproduction

From `bounded-relation-audit-2026-11-04/photolean`:

```bash
python3 audit_boundary/validate_boundary.py                                   # R1
python3 bounded_audit/validate_screening.py                                   # R2
python3 bounded_audit/validate_r3.py                                          # accepted R3: expects exactly 7 stale-ledger failures
python3 bounded_audit/r4/validate_r3_content.py                               # derived R3 content gate: exit 0
python3 bounded_audit/r4/validate_coverage.py \
    --coverage bounded_audit/r4/coverage-accepted.json --skip-package-validators  # R4 frozen integration
python3 bounded_audit/r4/excited-01/validate.py                               # R4 E1
python3 bounded_audit/r4/excited-02/validate.py                               # R4 E2
python3 bounded_audit/r4/conical-01/validate.py                               # accepted R4 CI: expects exactly 1 stale-ledger failure
python3 bounded_audit/r5/validate_r4_ci_content.py                            # derived R4 CI content gate: exit 0
python3 bounded_audit/r5/radiative-01/validate.py                             # five R5 package gates
python3 bounded_audit/r5/radiative-02/validate.py
python3 bounded_audit/r5/radiative-03/validate.py
python3 bounded_audit/r5/cross-domain-01/validate.py
python3 bounded_audit/r5/cross-domain-02/validate.py
python3 bounded_audit/r5/validate_coverage.py                                 # current R5 coverage gate
proofs/scripts/check.sh --strict                                              # build + sorry/custom-axiom scan
proofs/scripts/lake env lean bounded_audit/r5/radiative-01/probes/RAD1-probe.lean
proofs/scripts/lake env lean bounded_audit/r5/radiative-02/probes/RAD2-probe.lean
proofs/scripts/lake env lean bounded_audit/r5/radiative-03/probes/RAD3-probe.lean
proofs/scripts/lake env lean bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean
sha256sum relation_audit/registry.json                                        # 25d38791…ecbf0
find PhotoLean -name '*.lean' | wc -l                                         # 102
```

Run the four probe compilations **serially** and not while `check.sh --strict` is running: they all
use Lake, and concurrent runs can fail with a lock error. Do not delete Lake lock files. XD2 ships
no probe and no certified/refuted outcome, so it has no probe compilation.

`validate_coverage.py` supports `--root DIR`, `--coverage PATH`, `--override REL=PATH` and
`--skip-package-validators`; the override hook exists so mutation tests can mutate copies under
`/tmp` without touching package content. `validate_r4_ci_content.py` supports `--screening`,
`--search-log` and `--fragment` overrides for the same reason.

## 7. Verification matrix (real results at submission and after the R6/R7 repairs)

| gate | command | result |
|---|---|---|
| R1 boundary | `audit_boundary/validate_boundary.py` | exit 0, PASS, 17 theories / 136 unique pairs / 1,154 rows |
| R2 package | `bounded_audit/validate_screening.py` | exit 0, PASS, 0 failures |
| R3 package (historical) | `bounded_audit/validate_r3.py` | **exit 1, exactly the 7 enumerated ledger-freshness checks, 0 content failures** |
| R3 package content (derived) | `bounded_audit/r4/validate_r3_content.py` | exit 0, PASS, 7 exclusions |
| R4 frozen snapshot | `r4/validate_coverage.py --coverage r4/coverage-accepted.json --skip-package-validators` | exit 0, PASS, 840 checks, 67/136 + 69 remaining |
| R4 E1 | `r4/excited-01/validate.py` | exit 0, PASS |
| R4 E2 | `r4/excited-02/validate.py` | exit 0, PASS |
| R4 CI (historical) | `r4/conical-01/validate.py` | **exit 1, exactly `coverage.cumulative`** |
| R4 CI content (derived) | `r5/validate_r4_ci_content.py` | exit 0, PASS, 1 exclusion |
| RAD1 | `r5/radiative-01/validate.py` | exit 0, PASS, 0 failures (re-run after the R7 repair) |
| RAD2 | `r5/radiative-02/validate.py` | exit 0, PASS, 2,480 checks |
| RAD3 | `r5/radiative-03/validate.py` | exit 0, PASS |
| XD1 | `r5/cross-domain-01/validate.py` | exit 0, PASS |
| XD2 | `r5/cross-domain-02/validate.py` | exit 0, PASS |
| R5 coverage | `r5/validate_coverage.py` | exit 0, PASS, 10,600 checks |
| strict build/scan | `proofs/scripts/check.sh --strict` | exit 0, `build: OK`, scan `clean`, `verdict: PASS` |
| probes | `lake env lean …/RAD1-probe.lean`, `…/RAD2-probe.lean`, `…/RAD3-probe.lean`, `…/XD1-probe.lean` | exit 0 ×4; 11 + 4 + 10 + 3 `#print axioms` blocks, every one exactly `[propext, Classical.choice, Quot.sound]` |
| legacy registry | `sha256sum relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| frozen Lean tree | `find PhotoLean -name '*.lean' \| wc -l` | 102 |
| frozen R4 snapshot | `sha256sum bounded_audit/r4/coverage-accepted.json` | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |
| R5 ledger | `sha256sum bounded_audit/coverage.json` | `4c216fb3d760d358f936e94e71ba56ed34fb0afd9fc9ad077e4ceb3a094c2e0c` |

Package artifact hashes recorded in the ledger match the package REPORT tables exactly (RAD1
against its R7 REPORT):

| package | screening.json | search-log.json | coverage-fragment.json | probe |
|---|---|---|---|---|
| RAD1 | `a5ad482e…b837` | `1b711c1d…bf3a` | `38ab39d7…80ad` | `38cc6056…cfeb` |
| RAD2 | `fcb16837…83c6` | `9a28cd2d…84e5` | `2292f2b0…561e` | `36a5ae42…ef2b` |
| RAD3 | `34da3a26…c55b` | `5c35aa15…a756` | `a63d1454…7a90` | `c693f198…5f09` |
| XD1 | `fa096f59…dfd3` | `0bf725db…26d7` | `7ace5775…c87f` | `f5668397…07f1` |
| XD2 | `02456b78…c80f` | `391d616e…fcb6` | `325fba38…674a` | — (no probe) |

RAD1's fifth ledger-recorded hash, `validate.py`, is `98c82e25…1cfd` after the R7 repair. The
immediately preceding R6 values (`screening.json` `4fd11f24…a828`, `coverage-fragment.json`
`b6e8b668…d251`, probe `61acc8f8…b74a`, `validate.py` `00cedb6a…20bd`) are rejected by
`validate_coverage.py`: a ledger copy carrying them fails exactly the four
`r5wp.RAD1.{sha256,fragmentSha256,validateSha256,probeSha}` checks (§7.2). A single-field drift of
any of RAD1's five recorded hashes likewise fails exactly one check. The RAD1 `search-log.json`
hash is unchanged across R6 and R7 at `1b711c1d…bf3a`.

### 7.1 R6 repair: hash resynchronization and gate re-run

The R6 integration changed only the RAD1 hash record in the ledger, the hashes above, and
`loop/产出.md`; no pair, query, status, accepted/submitted count, package content or other gate was
touched. The complete matrix was re-run serially against the repaired tree:

| gate | result |
|---|---|
| R1 boundary | exit 0, PASS, 17 theories / 136 unique pairs / 1,154 rows |
| R2 package | exit 0, PASS, 0 failures |
| R3 accepted (historical) | exit 1, exactly the 7 enumerated ledger-freshness checks, 0 content failures |
| R3 derived content | exit 0, PASS, 7 exclusions |
| R4 frozen snapshot (`--skip-package-validators`) | exit 0, PASS, 840 checks, 67/136 + 69 remaining |
| R4 E1 / E2 | exit 0 ×2, PASS |
| R4 CI accepted (historical) | exit 1, exactly `coverage.cumulative` |
| R4 CI derived content | exit 0, PASS, 1 exclusion |
| five R5 packages | exit 0 ×5, PASS (RAD2 2,480 checks) |
| R5 current coverage | exit 0, PASS, 10,600 checks, 0 failures, 136/136 + 0 remaining, 152 queries |
| strict build/scan | exit 0, `build: OK`, scan `clean`, `verdict: PASS` |
| four probes (serial) | exit 0 ×4; 11 + 4 + 10 + 3 `#print axioms` blocks, all exactly `[propext, Classical.choice, Quot.sound]` |
| legacy registry / Lean tree / R4 snapshot | `25d38791…ecbf0` / 102 files / `d1e44bf7…32fa`, all unchanged |
| RAD1 package mutations | 13/13 as expected: control PASS, 12 mutations fail closed including the four semantic pins M9–M12 |
| ledger mutations | old RAD1 hashes → 4 fails; one-row acceptance, 135 screened, dropped/duplicated row, certified 66 each rejected on the expected check |

The ledger state is unchanged: 136/136 **submitted**, remaining 0, accepted 67/136, 69 rows
`submitted-R5-pending-review`; cumulative queries 152 with certified 67 / refuted 0 / unresolved 39 /
notEstablished 2 / outOfScope 44.

Mutation tests (all inputs under `/tmp`; see `loop/产出.md` §6 for the transcripts):

- **R5 coverage, 19 cases:** unmutated baseline PASS; full uniform `accepted-R5` flip PASS
  (acceptance needs no validator edit); rows-only acceptance, dropped/duplicated row, per-row
  status drift, mixed states, self-hash slot, R3-screening hash, non-empty remaining, cumulative
  drift, re-introduced `P-Kasha-Sabatier`, work-package hash drift, accepted fragment state,
  status relabel, endpoint-signature drift, missing search entry and probe-hash drift each exit 1
  on the expected check.
- **Derived R4 CI content, 5 cases:** baseline PASS; blanked `chemicalQuestion`,
  corrupted endpoint signature, forged probe declaration and a deleted search-log entry (with the
  screening hash re-pinned) each exit 1 on the expected content check.

### 7.2 R7 repair: §4 probe-comment direction, hash resynchronization and gate re-run

The R7 repair touched only RAD1's §4 block comment and the comment pin in `validate.py`, then
regenerated `screening.json`, `coverage-fragment.json` and `probes/RAD1-probe.lean`;
`search-log.json` is unchanged. No theorem, proof term, relation kind, query ID, pair set or outcome
changed, and no other package was touched. The integration step changed only the RAD1 hash record
in the ledger, the hashes above and `loop/产出.md`. The complete matrix was re-run serially against
the repaired tree:

| gate | result |
|---|---|
| R1 boundary | exit 0, PASS, 17 theories / 136 unique pairs / 1,154 rows |
| R2 package | exit 0, PASS, 0 failures |
| R3 accepted (historical) | exit 1, exactly the 7 enumerated ledger-freshness checks, 0 content failures |
| R3 derived content | exit 0, PASS, 7 exclusions |
| R4 frozen snapshot (`--skip-package-validators`) | exit 0, PASS, 840 checks, 67/136 + 69 remaining |
| R4 E1 / E2 | exit 0 ×2, PASS |
| R4 CI accepted (historical) | exit 1, exactly `coverage.cumulative` |
| R4 CI derived content | exit 0, PASS, 1 exclusion |
| five R5 packages | exit 0 ×5, PASS (RAD2 2,480 checks) |
| R5 current coverage | exit 0, PASS, 10,600 checks, 0 failures, 136/136 + 0 remaining, 152 queries |
| strict build/scan | exit 0, `build: OK`, scan `clean`, `verdict: PASS` |
| four probes (serial) | exit 0 ×4; 11 + 4 + 10 + 3 `#print axioms` blocks, all exactly `[propext, Classical.choice, Quot.sound]` |
| legacy registry / Lean tree / R4 snapshot | `25d38791…ecbf0` / 102 files / `d1e44bf7…32fa`, all unchanged |
| original repository | HEAD `7ad25a5f…dac`, `git status --porcelain` empty |
| RAD1 package mutations | 15/15 as expected: control PASS, 14 mutations fail closed including the §4 comment pins M13/M14 |
| ledger hash-drift mutations | R6 RAD1 values → exactly 4 fails; a single-field drift of `screening` / `fragment` / `probe` / `validate` / `search-log` → exactly 1 fail each |

The ledger state is unchanged: 136/136 **submitted**, remaining 0, accepted 67/136, 69 rows
`submitted-R5-pending-review`; cumulative queries 152 with certified 67 / refuted 0 / unresolved 39 /
notEstablished 2 / outOfScope 44. The R7 ledger SHA-256 is `4c216fb3…2e0c`.

Mutation transcripts (all inputs under `/tmp`; see `loop/产出.md` §6): the RAD1 suite is 15/15
(control + M1–M14), with M13 reinstating the old reversed §4 comment and M14 dropping the
normal-region sentence; both exit 1 on the expected `pin.ssProbeComment.*` checks. The ledger
mutations above show that neither the previous hashes nor any single-field drift can pass the
current-coverage gate, while the unmutated R7 ledger passes all 10,600 checks.

## 8. Known seams

Recorded, not papered over. None is repaired by editing an accepted artifact from this directory.

1. **R3 accepted validator is stale by design.** It pins the ledger hash and the R3 round state;
   against the R5 ledger it reports exactly its seven enumerated freshness checks and no content
   failure. `r4/validate_r3_content.py` is the historical content gate (§5.1).
2. **R4 CI accepted validator is stale by exactly one check.** It pins
   `screenedPairCount ∈ {21, 67}`; `r5/validate_r4_ci_content.py` excludes exactly
   `coverage.cumulative` and keeps everything else (§5.2).
3. **R4 frozen integration gate's embedded CI subprocess.** The frozen gate's own 840 checks pass
   against `r4/coverage-accepted.json`; its embedded re-run of the CI package validator reads the
   current ledger and fails exactly `validator.CI.exit`/`validator.CI.result`. The three embedded
   package gates are enumerated and run separately, so the gate is run with
   `--skip-package-validators` (§5.3). Its embedded E1/E2 re-runs are covered by the separate E1/E2
   gates and by `validate_coverage.py`, which re-runs all five R5 package validators.
4. **Snapshot drift in package prose.** The RAD2/RAD3/XD1/XD2 REPORTs record the ledger at its
   pre-integration R4 hash `d1e44bf7…32fa`; that value is historical, and no package validator
   reads or pins the ledger. RAD1's REPORT was regenerated in R7 and records the repaired package
   hashes instead; it also does not read or pin the mutable ledger.
5. **Probe location vs the strict scan range.** `proofs/ENGINE.yml` sets the scan source dirs to
   `PhotoLean`, so `check.sh --strict` does not scan `bounded_audit/r5/**/probes/*.lean`. The probes
   are covered by the real compile gate, by live `#print axioms` parsing in `validate_coverage.py`
   (which checks every certified and candidate declaration against its compile-log block), and by
   per-package forbidden-token scans. This limitation is inherited from the accepted R4 packages and
   is stated rather than hidden.
6. **Registry integration debt (not this round's).** The 30 accepted probe certificates from
   R2/R3/R4 and the legacy dangling endpoint aliases are still not merged into the formal registry;
   R5 adds 28 probe declarations (25 certificates + 3 candidates) as package-local evidence. The
   registry remains read-only and unchanged.

## 9. Non-claims

- Screened is not certified; the 136/136 count is bounded coverage, not classification.
- **136/136 is submitted coverage; accepted coverage is 67/136 before independent review.** The R5
  rows are `submitted-R5-pending-review`; this integration does not self-accept and does not flip
  statuses.
- A `certified` row is a checked relation under its declared context, premises and snapshot, not a
  claim of physical universality.
- `unresolved` / `notEstablished` / `outOfScope` records are not negative existence claims. The
  three XD1 candidate identities are formula-level kernel facts, not claims that the catalytic and
  optical/IC processes are the same physical process.
- One named query per pair does not exhaust the conceivable relations outside the frozen bounded
  query protocol.
- The derived validators do not accept, re-accept or re-open R3/R4; they prove that the accepted
  packages' content still passes every non-freshness check against the current ledger.
- The cumulative ledger is not a completeness claim about the 136-pair universe beyond the frozen
  query protocol.
