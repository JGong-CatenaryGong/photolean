# R5 Package XD2 — Cross-domain screening of the nine remaining Goldschmidt pairs

`bounded_audit/r5/cross-domain-02/` — round R5, work package `WP-cross-domain-screening-02`,
snapshot `snap-bounded-audit-2026-11-04`, status **submitted-R5-pending-review**.

This package is an English repository artifact. It screens exactly the nine pairs that
`audit_boundary/cluster-plan.json` assigns to `WP-cross-domain-screening-02`, and it touches no
other pair, no accepted artifact and no cumulative ledger.

## 1. Assignment and boundary

| item | value |
|---|---|
| work package | `WP-cross-domain-screening-02` (R1 `cluster-plan.json`) |
| primary cluster | `cross-domain-screening` |
| pairs | 9 |
| named statement-level queries | 11 |
| outcomes | `outOfScope` 11, `certified` 0, `refuted` 0, `unresolved` 0, `notEstablished` 0 |
| Lean certificates introduced | 0 |
| prior accepted coverage (derived, not pinned) | 67 / 136 |
| accepted packages the prior coverage is derived from | `wp-surface-01`, `r3`, `r4/excited-01`, `r4/excited-02`, `r4/conical-01` |

The nine pairs are `Goldschmidt` against `KashaVavilov`, `SternVolmer`, `QuantumYield`,
`FluorPhos`, `EnergyGapLaw`, `StokesShift`, `ICvsISC`, `Forster` and `Einstein`. None of them is in
the accepted R2/R3/R4 pair sets, and `P-Kasha-Sabatier` (accepted in R2) is not rescreened.

This package never reads and never pins the mutable R5 cumulative ledger
`bounded_audit/coverage.json`. Prior coverage is derived by `validate.py` from the pair rows of the
five accepted screening packages; a ledger that later appends the R5 entries cannot break this
package validator, and this package cannot pin a ledger that later changes.

## 2. What was screened, and why every outcome is `outOfScope`

Goldschmidt is a purely geometric theory. Each of its 139 statement rows is a predicate or a
definition about the tolerance factor built from ionic radii `(rA, rB, rO)`, a band or window on that
factor, or a radius/charge substitution rule. Its declaration signatures contain no `energy`, no
`rate`, no `yield`, no `coupling`, no `life` and no `transfer` token (checked over the inventory
signature column), and no natural-number ladder index. The nine partner theories, by contrast, state
facts about energies, rates, yields, ladders, slopes, transfer efficiencies or lifetimes. The screening question for each pair is therefore not "are the names
alike" but "is there one delivered statement on each side that speaks about the same measured
quantity, in a context both can share, with a total translation into both statement contexts".

For each pair the answer is no, and the reason is recorded at the statement level, not at the
cluster or theory-name level. Concretely, each query names:

* one Goldschmidt endpoint and one partner endpoint, with declaration, kind, source artifact,
  source line, statement version, signature SHA-256 and source-file SHA-256 pulled from the frozen
  inventory;
* the candidate shared context that would be needed — a union context holding both sides' fields —
  with a physical reading and a provenance note;
* two `none-declared` translations with separate reasons (what object the other authority lacks);
* a premise predicate (`fun _ : <candidate context> => True`, no premise ids: no premise is
  claimed to be load-bearing for a relation that is not asserted);
* a scope, a snapshot, an expected evidence kind, an expected-kind rationale, a falsification
  condition and an explicit statement-level jurisdiction reason naming both endpoint declarations.

The eleven queries, by pair:

| pair | query | endpoint (Goldschmidt) | endpoint (partner) | expected kind | outcome |
|---|---|---|---|---|---|
| `P-Goldschmidt-KashaVavilov` | `Q-XD2-KV-01` | `GoldschmidtConforms` | `lossless_separates_kasha_vavilov` | implication | outOfScope |
| `P-Goldschmidt-SternVolmer` | `Q-XD2-SV-01` | `goldschmidtZone` | `svZoneQ` | equivalence | outOfScope |
| `P-Goldschmidt-QuantumYield` | `Q-XD2-QY-01` | `InBand` | `yieldOf` | implication | outOfScope |
| `P-Goldschmidt-FluorPhos` | `Q-XD2-FP-01` | `goldschmidtZone` | `fpZoneQ` | equivalence | outOfScope |
| `P-Goldschmidt-EnergyGapLaw` | `Q-XD2-EG-01` | `gapA` | `nrBarrier` | definitionalIdentity | outOfScope |
| `P-Goldschmidt-EnergyGapLaw` | `Q-XD2-EG-02` | `goldschmidtZone` | `egZoneQ` | equivalence | outOfScope |
| `P-Goldschmidt-StokesShift` | `Q-XD2-SS-01` | `tolFac` | `emEnergy` | implication | outOfScope |
| `P-Goldschmidt-ICvsISC` | `Q-XD2-IC-01` | `GoldschmidtConforms` | `spin_discount` | implication | outOfScope |
| `P-Goldschmidt-Forster` | `Q-XD2-FR-01` | `contact_iff_tolFac_one` | `fretEff_self` | equivalence | outOfScope |
| `P-Goldschmidt-Forster` | `Q-XD2-FR-02` | `latticeOf` | `r0six` | definitionalIdentity | outOfScope |
| `P-Goldschmidt-Einstein` | `Q-XD2-EI-01` | `tauGoldschmidt` | `tauR` | definitionalIdentity | outOfScope |

Two pairs carry a second query because they contain a genuinely distinct near-miss that deserved
its own record rather than a footnote: `EnergyGapLaw` (a naming collision — "gap"/"barrier" — and,
separately, two three-way classifiers) and `Forster` (the legacy-registered threshold look-alike,
and, separately, two characteristic length scales).

### 2.1 Why the near-misses are rejected, in chemical terms

* **Naming collisions are not statements.** `gapA` is a signed length (the A–O contact excess in
  ångström); `nrBarrier` is the Marcus crossing energy `(lam − x)²/(4 lam)`. `tauGoldschmidt` is the
  dimensionless `3/20` of the radius rule; `tauR` is the radiative lifetime `1/A`. `tolFac` is a
  dimensionless packing ratio; `emEnergy` is a vertical emission energy. In each case the shared
  word or symbol is notation, and the two declarations differ in dimension and in argument
  dependence.
* **Shape-only coincidences are not relations.** `goldschmidtZone` and the partner zone classifiers
  (`svZoneQ`, `fpZoneQ`, `egZoneQ`) are all "classify a scalar against a band", but the inputs are a
  real radius ratio versus a rational slope pair, a five-rate product comparison, or an energy pair;
  `svZoneQ` even has four verdicts where Goldschmidt has three. `InBand` and `yieldOf` share a
  "part of a whole" shape but one is unnormalised and geometric and the other is a normalised rate
  share. The threshold look-alike on the `Forster` pair is the same situation: `t = 1` certifies an
  ionic contact, `R = R0` certifies half transfer, and the two thresholds are 1 and 1/2 over
  unrelated lengths.
* **Classifier internals matter.** `fpZoneQ` takes `kIC` as an argument but its decision body does
  not consume it; the strict build gate records the unused-variable linter note at
  `PhotoLean/FluorPhos/RatModel.lean:89:21`. So even the partner classifier is not a statement about
  an internal-conversion rate, which is one more reason the Goldschmidt band verdict cannot be
  identified with it.

### 2.2 Machine-recomputable jurisdiction evidence

For every pair the validator re-derives three statement-level facts from the frozen artifacts
(`screening.json#jurisdictionEvidence` records the vocabulary; `validate.py` hard-codes an
independent copy):

1. **Signature scan.** Over all 139 Goldschmidt declaration signatures and all partner declaration
   signatures (29/46/29/30/26/36/20/32/33 rows), zero shared identifiers in both directions.
   Evidence: `evidence/signature_scan.py`, transcript in `evidence/jurisdiction-scans.log`.
2. **Import closure.** The Goldschmidt modules import `Mathlib` plus their own five modules only;
   no partner module imports a Goldschmidt module and no Goldschmidt module imports a partner
   module; the non-own import sets do not intersect.
3. **Legacy disposition.** The pair's legacy record is a pair-level `notEstablished` anchor with
   `relationKind` null and `certificate` null — coverage history, not a named chemical query and not
   an audit verdict. The register `PhotoLean/Relations.lean` §16 records the absence (lines 942,
   945, 948, 952, 969, 991, 998, 1002, 1021); §16 also records the `Forster` pair as a *look-alike*
   with no machine row.

A signature scan is a necessary condition, not a proof of non-existence; the semantic argument in
each query's statement-level reason is the load-bearing part, and the scan is what makes it
recomputable. Nothing here is a claim of logical absence, and no relation is forced.

## 3. Deliverables

| artifact | role |
|---|---|
| `screening.json` | the package: work package, snapshot, inventory/queue/cluster/boundary/registry pins, context and scope libraries, jurisdiction evidence, 9 pair rows, 11 query rows, counts, non-claims |
| `search-log.json` | 11 scoped search entries, one per non-certified query: searched statements/kinds/contexts, consulted dependencies, real commands and results, attempted strategies, rejected candidate, remaining gap, recompute commands |
| `coverage-fragment.json` | submission snapshot: 9 pairs / 11 queries, `submitted-R5-pending-review`, prior accepted count 67 derived from the accepted packages, no ledger hash |
| `validate.py` | fail-closed package validator (see §4) |
| `build_package.py` | deterministic builder; pulls every endpoint field from the frozen inventory |
| `evidence/signature_scan.py` | the machine signature scan used by the search log and re-derived by the validator |
| `evidence/jurisdiction-scans.log` | verbatim transcript of the pair scans, import closures and legacy dispositions |
| `evidence/gates.log` | verbatim transcript of every gate run, with exit codes |
| `evidence/mutation-tests.log` | verbatim transcript of the `/tmp` mutation tests |

There is no `probes/` directory. The package claims no `certified` and no `refuted` outcome, so it
introduces no Lean certificate: a certificate for an `outOfScope` registration would be a category
mistake, and shipping an unused probe would invite the reader to mistake it for evidence of a
relation. The validator fails if a probe directory, a `.lean` file or a probe reference appears.

## 4. What `validate.py` checks (fail-closed)

Run from the repository root:

```bash
python3 bounded_audit/r5/cross-domain-02/validate.py
```

It re-derives, without trusting the package's own counts or prose:

* the exact nine assigned pairs, their queue rows, their theories and their cluster;
* every endpoint field, source line and source SHA-256 from the frozen inventory, and that no
  endpoint is a dangling legacy alias;
* the exact number of queries (11), unique query ids, one-to-one `queryIds`, and that every pair has
  at least one named query or statement-level `outOfScope` record;
* semantic completeness of every query: title, chemical question and rationale, shared context with
  fields/reading/provenance, both translations with reasons, premise predicate and premise ids,
  scope with description/domain/snapshot, expected kind (never `refuted` as a kind), expected-kind
  rationale, falsification condition, observation channels (none for a jurisdiction record);
* that every query carries exactly one of the five outcomes, that the statement-level reason is at
  least 200 characters and names **both** endpoint declarations, and that the package claims no
  `certified`/`refuted` outcome and ships no probe;
* the statement-level jurisdiction facts for all nine pairs: signature scan, import closure, legacy
  disposition;
* the one-to-one correspondence between the 11 non-certified queries and the 11 search-log entries,
  including back-references, at least four recorded commands per entry with nonempty results, at
  least three attempted strategies, a rejected candidate, a remaining gap and a recompute command;
* the snapshot hashes (inventory, pair queue, cluster plan, boundary, legacy registry), the accepted
  registry pin `25d38791…ecbf0`, and the 102-file delivered Lean tree;
* **prior coverage derived from the five accepted packages** (67 pairs) and zero overlap with the
  nine assigned pairs — and that the mutable R5 ledger was never opened (`READ_PATHS` assertion) and
  is not pinned;
* the coverage fragment as a pure submission snapshot: state, screening hash, per-pair counts,
  `screenedDelta` 9, empty overlap, universe 136 and the queue hash;
* the non-claims (at least three per artifact) and the presence of the gate transcript in
  `evidence/gates.log` and of the gate commands plus the mutation verdict in this report.

Optional overrides `--screening`, `--search-log`, `--fragment` exist so the mutation tests can run
on `/tmp` copies without touching the package.

## 5. Gates actually run

The transcript with exit codes is `evidence/gates.log`. Summary:

| gate | command | result |
|---|---|---|
| R1 boundary | `python3 audit_boundary/validate_boundary.py` | PASS, exit 0 (17 theories, 136 pairs, 1,154 statement rows) |
| R2 screening | `python3 bounded_audit/validate_screening.py` | PASS, exit 0 |
| R3 historical content | `python3 bounded_audit/r4/validate_r3_content.py` | PASS, exit 0 (7 current-ledger freshness checks excluded, exactly as the plan enumerates; content checks zero failures) |
| R4 historical snapshot | `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json` | PASS, exit 0 (846 checks; 67/136 screened, 69 remaining) |
| strict build/scan | `proofs/scripts/check.sh --strict` | PASS: build OK, `sorry`/custom-axiom scan `clean` |
| package validator | `python3 bounded_audit/r5/cross-domain-02/validate.py` | PASS, exit 0 (see §8) |
| probe compilation / axiom audit | not applicable | no probe is introduced; the package claims no certificate |

Lake commands were run strictly one at a time (the only Lake-touching gate is
`proofs/scripts/check.sh --strict`); no lock file was deleted.

The strict gate reports three pre-existing linter notes in accepted modules
(`PhotoLean/SternVolmer/Basic.lean:65:32,65:35`, `PhotoLean/SternVolmer/RatModel.lean:61:22,61:25`,
`PhotoLean/FluorPhos/RatModel.lean:89:21`). They are unrelated to this package; the `kIC` one is
cited in `Q-XD2-FP-01` as a statement-level fact, not as a defect.

## 6. Mutation tests (`/tmp`)

Each mutation copies the three JSON artifacts to `/tmp`, mutates one thing, and runs `validate.py`
against the copies. A mutation that still passes would be a validator defect; every one of them must
be **FAIL-CLOSED** (exit 1 with a named failure code). Transcript:
`evidence/mutation-tests.log`.

| mutation | expected | actual (exit 1, named codes) |
|---|---|---|
| M0 baseline, unmutated copies | PASS | exit 0 |
| M1 drop one assigned pair | FAIL-CLOSED | `pairs.order`, `pairs.coverage`, `queries.count`, `counts.*`, `search.oneToOne`, `fragment.*` |
| M2 add an accepted R2 pair | FAIL-CLOSED | `pair.unknown`, `pair.partner`, `pairs.order`, `endpoint.partnerTheory`, `queries.duplicate`, … |
| M3 duplicate a query id | FAIL-CLOSED | `queries.duplicate`, `pair.queryIds`, `search.mismatch`, `search.queryMissing` |
| M4 forge a certified outcome | FAIL-CLOSED | `outcome.certifiedUnsupported`, `outcome.noCertified`, `search.certifiedEntry`, `counts.certified` |
| M5 tamper an endpoint signature hash | FAIL-CLOSED | `endpoint.signatureSha256` |
| M6 mislabel an expected kind | FAIL-CLOSED | `counts.byExpectedKind` |
| M7 strip an outOfScope translation reason | FAIL-CLOSED | `translation.reason`, `translation.reasonLength` |
| M8 delete a search-log entry | FAIL-CLOSED | `search.missing`, `search.oneToOne`, `searchLogReference.entryCount`, `counts.searchEntries` |
| M9 pin the mutable R5 ledger in the snapshot | FAIL-CLOSED | `self.ledgerPinned` |
| M10 drift the coverage fragment | FAIL-CLOSED | `fragment.counts.delta` |
| M11 replace a statement-level reason with a theory-name contrast | FAIL-CLOSED | `evidence.statementLevelLength`, `evidence.statementLevelNames` |

Harness exit 0: twelve cases, one required pass (M0) and eleven required fail-closed results, all as
specified. The M2 case also exercises the hardened unknown-pair path: before the hardening it
raised a `KeyError` traceback instead of a named failure, which is fail-closed but not a clean
verdict, so the validator now emits `pair.unknown` and keeps going.

## 7. Hashes

Package artifacts (SHA-256), as built by `build_package.py`:

```
screening.json         02456b78ee5852a306652901085e31a2387045faaf30f0b3566f2a6bac22c80f
search-log.json        391d616e18dd355272eab65eb8adbeae330a25ea33b1246b0764789161dbfcb6
coverage-fragment.json 325fba38c6defd81953b6ef964155c0c88d87db254eaf694a65b34717ab2674a
```

Frozen inputs pinned by the package:

```
audit_boundary/statement-inventory.json
audit_boundary/pair-queue.json
audit_boundary/cluster-plan.json
audit_boundary/BOUNDARY.md
relation_audit/registry.json  25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0
```

Accepted artifacts, re-hashed in `evidence/gates.log` and unchanged:

```
bounded_audit/r4/coverage-accepted.json              d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa
bounded_audit/r4/conical-01/screening.json           f368b9b1f1ded5800419a5283b541363e83f37c4b8ef54aa641890cb54615487
bounded_audit/r4/conical-01/search-log.json          2b349272ad948309909bc8022f488147730104e02b21fa792b9aaa23f29d6b53
bounded_audit/r4/conical-01/coverage-fragment.json   0efa855f60b26452a4daf0c0e6ed48cc31f9f1c826a80c0cab5a17e1605d379b
bounded_audit/r4/conical-01/validate.py              5a258939048a3d8890449712b7c084e003224ecb8dce8ff90920faee8a5876cf
bounded_audit/r4/conical-01/probes/R4-CI-probe.lean  33cf7fe66d3c3cee3431f9ace125259bca3c36ef798d9f5324154b817ce80572
bounded_audit/r4/excited-01/probes/E1-probe.lean     b2c702d21d96d03b664700fe7c18282b4b989bd9052cca031e357fb5b29cb0e2
bounded_audit/r4/excited-02/probes/E2-probe.lean     69a7889f458558c78701883774c22fe4868fdca48626c3e846d1427457524c11
bounded_audit/r3/probes/R3-probe.lean                16d5b8424d17e1e608c9780a0e6fbebb5838a80e59fb57b6d52fe3e70e7fb368
```

`git status --porcelain` shows only untracked directories created by earlier rounds plus the two
pre-existing tracked modifications `lakefile.toml` and `proofs/EXPERIENCE.md` (mtime 2026-10-31,
before this session); `git diff --stat` lists only those two files. This package's own files are all
under `bounded_audit/r5/cross-domain-02/`.

## 8. Reproduce

```bash
cd bounded-relation-audit-2026-11-04/photolean

python3 bounded_audit/r5/cross-domain-02/evidence/signature_scan.py KashaVavilov
python3 tools/relation_audit_registry.py --explain-pair P-Goldschmidt-Forster
python3 bounded_audit/r5/cross-domain-02/validate.py

python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py
python3 bounded_audit/r4/validate_r3_content.py
python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json
proofs/scripts/check.sh --strict
```

`build_package.py` is deterministic: re-running it rewrites the same three JSON artifacts with the
same hashes (the search log is written first, then the screening package pins its hash, then the
fragment pins the screening hash).

## 9. Deviations from the plan

1. **No Lean probe.** The plan requires genuine typed Lean certificates for new
   `certified`/`refuted` outcomes. This package produces none, because the nine pairs admit no
   statement-level relation under the frozen inventory: every outcome is `outOfScope`. The
   certificate requirement is therefore vacuous here, and the package ships no probe rather than a
   decorative one (§3). The strict build/scan gate and the unchanged 102-file Lean tree are recorded
   instead.
2. **Two pairs carry two queries each.** The plan allows multiple chemically distinct queries per
   pair; `EnergyGapLaw` and `Forster` use that allowance because each contains a second, independent
   near-miss (naming collision / classifier shape; threshold look-alike / length scale) that would
   have been under-recorded in a single row.
3. **Prior coverage is derived, not read from the ledger.** The plan for R5 requires package
   validators not to read or pin the mutable cumulative ledger; this package derives 67 from the
   five accepted screening packages and asserts that the ledger was never opened.
4. **`evidence/gates.log` records a pre-existing dirty tree.** The checkout carries earlier-round
   untracked directories and two tracked modifications. They are outside this package's write scope
   and are documented in §7 rather than reverted (reverting accepted work is forbidden).

## 10. Open items and blockers

* **No blocker.** All nine assigned pairs have a statement-level outcome and a scoped search log;
  the package validator and all five historical gates pass; the mutation tests fail closed.
* **Standing integration debt (not this package's).** The 30 accepted probe certificates from
  R2/R3/R4 and the legacy dangling endpoint aliases are still not merged into the formal registry;
  this package adds no certificate, so it neither increases nor discharges that debt.
* **Reviewability note.** `outOfScope` is a jurisdiction verdict, not a chemical dismissal: the
  package claims only that the frozen authorities of these two theories share no context,
  translation or observable, and it names the statement-level reason for each pair. A later round
  that adds a delivered bridging statement to either authority would remove the reason for that
  pair, which is exactly what the falsification condition of each query states.
