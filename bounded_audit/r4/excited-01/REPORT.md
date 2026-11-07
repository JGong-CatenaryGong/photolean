# R4 Package E1 — Excited-state kinetics (WP-excited-state-kinetics-01)

Status: **submitted-R4-pending-review**. This package screens exactly the sixteen R1
`WP-excited-state-kinetics-01` pairs. It does not write `bounded_audit/coverage.json`,
`loop/产出.md`, any accepted R1/R2/R3 artifact, any `PhotoLean/**` source, the legacy
registry, the original repositories, the manuscript, or the backup.

## 1. Counts

| quantity | value |
|---|---:|
| pairs screened | 16 |
| named statement-level queries | 16 |
| certified | 6 |
| refuted | 0 |
| unresolved | 9 |
| notEstablished | 0 |
| outOfScope | 1 |
| search-log entries | 10 |

Expected-kind counts: `equivalence` 4, `definitionalIdentity` 1,
`observationalEquivalence` 1, `conditionalComposition` 2, `implication` 8.

Every pair has exactly one named query; no query uses a pair-level anchor as an endpoint.
No pair from the accepted R2 (10 pairs) or R3 (11 pairs) is rescreened.

## 2. Pair and query table

| pair | query | status | expected kind | evidence |
|---|---|---|---|---|
| P-Hammond-Kasha | Q-R4-E1-HK-01 | certified | equivalence | probe `hammondKashaICMaxEquiv` |
| P-Hammond-KashaVavilov | Q-R4-E1-HKV-01 | unresolved | conditionalComposition | search `SL-R4-E1-HKV-01` |
| P-Hammond-SternVolmer | Q-R4-E1-HSV-01 | unresolved | implication | search `SL-R4-E1-HSV-01` |
| P-Hammond-QuantumYield | Q-R4-E1-HQY-01 | unresolved | implication | search `SL-R4-E1-HQY-01` |
| P-Hammond-FluorPhos | Q-R4-E1-HFP-01 | unresolved | implication | search `SL-R4-E1-HFP-01` |
| P-Hammond-EnergyGapLaw | Q-R4-E1-HEG-01 | certified | equivalence | probe `hammondEnergyGapBarrierZeroEquiv` |
| P-Hammond-StokesShift | Q-R4-E1-HSS-01 | certified | observationalEquivalence | probe `hammondStokesAbsorptionBridge` |
| P-Hammond-ICvsISC | Q-R4-E1-HIC-01 | certified | definitionalIdentity | probe `hammondICvsISCBarrierPin` |
| P-Hammond-Forster | Q-R4-E1-HFO-01 | outOfScope | implication | jurisdiction `SL-R4-E1-HFO-01` |
| P-Hammond-Einstein | Q-R4-E1-HEIN-01 | unresolved | implication | search `SL-R4-E1-HEIN-01` |
| P-BEP-Kasha | Q-R4-E1-BK-01 | certified | equivalence | probe `bepKashaTransferZeroEquiv` |
| P-BEP-KashaVavilov | Q-R4-E1-BKV-01 | unresolved | conditionalComposition | search `SL-R4-E1-BKV-01` |
| P-BEP-SternVolmer | Q-R4-E1-BSV-01 | unresolved | implication | search `SL-R4-E1-BSV-01` |
| P-BEP-QuantumYield | Q-R4-E1-BQY-01 | unresolved | implication | search `SL-R4-E1-BQY-01` |
| P-BEP-FluorPhos | Q-R4-E1-BFP-01 | unresolved | implication | search `SL-R4-E1-BFP-01` |
| P-BEP-EnergyGapLaw | Q-R4-E1-BEG-01 | certified | equivalence | probe `bepEnergyGapInvertedEquiv` |

## 3. New evidence

All six certified outcomes use **new** typed Lean certificates in
`bounded_audit/r4/excited-01/probes/E1-probe.lean`. No legacy certificate was reused for
these pairs: the accepted registry contains only pair-level `notEstablished` anchors for
them (`rec-notestablished-P-*`), and no certified record.

| query | certificate | kind | statement |
|---|---|---|---|
| Q-R4-E1-HEG-01 | `hammondEnergyGapBarrierZeroEquiv` | equivalence | `nrBarrier lam x = 0 ↔ Hammond.tsCoord lam x = 0` under `lam ≠ 0` |
| Q-R4-E1-BEG-01 | `bepEnergyGapInvertedEquiv` | equivalence | `EnergyGapLaw.InvertedGap lam x ↔ BEP.transfer lam x < 0` under `0 < lam` |
| Q-R4-E1-HK-01 | `hammondKashaICMaxEquiv` | equivalence | `Kasha.marcusIC A lam kB T x = A ↔ Hammond.tsCoord lam x = 0` under `A > 0`, `kB·T > 0`, `lam > 0` |
| Q-R4-E1-HIC-01 | `hammondICvsISCBarrierPin` | definitionalIdentity | `ICvsISC.fcBarrier = Hammond.gapReactant` (fresh `rfl`-only `DefEq` pin) |
| Q-R4-E1-BK-01 | `bepKashaTransferZeroEquiv` | equivalence | `BEP.transfer lam x = 0 ↔ Kasha.marcusIC A lam kB T x = A` under the same positivity premises |
| Q-R4-E1-HSS-01 | `hammondStokesAbsorptionBridge` | observationalEquivalence | `StokesShift.absEnergy lam e00 = Hammond.productSurface lam e00 0 - Hammond.reactantSurface lam 0` |

The probe consumes delivered cross-theory rows: `Relations.eg_boundary_eq_tsCoord_zero`
(§15 boundary row), `Relations.transfer_eq_tsCoord_bridge` and
`Relations.tsCoord_lt_zero_iff_inverted` (§2), `Relations.kernel_marcusIC` (§7),
`Relations.kernel_barrier_eq_hammond` / `kernel_productSurface_eq_hammond` (§1),
`EnergyGapLaw.cert_nrBarrier`, `ICvsISC.cert_fcBarrier`, and
`StokesShift.absEnergy_eq`.

Gate results (real outputs in `probes/compile.log` and `probes/scan.log`):

- `proofs/scripts/lake env lean bounded_audit/r4/excited-01/probes/E1-probe.lean`
  exits 0; the six `#print axioms` lines list only `propext`, `Classical.choice`,
  `Quot.sound`.
- The forbidden-token scan over the probe reports `# no hits` / `# verdict: PASS (clean)`.

## 4. Non-certified records

Nine `unresolved` queries name a precise chemical candidate and record the missing
bridge:

- `P-Hammond/BEP-KashaVavilov`: the ladder's free `SpecSame` predicate is not connected
  to a barrier window; the only registered contact runs through `Kasha.marcusIC`.
- `P-Hammond/BEP-SternVolmer`: the SV added channel `kq·q` is not identified with an
  Arrhenius rate over the barrier, and there is no total translation `[Q] ↔ x`.
- `P-Hammond/BEP-QuantumYield`: no yield theorem fills a channel with the
  barrier-controlled rate; `QuantumYield` leaves every channel rate free.
- `P-Hammond/BEP-FluorPhos`: `kIC` is a free rate; no delivered identification with the
  barrier-controlled rate.
- `P-Hammond-Einstein`: `kNR` in `yield_radiative` is a free rate; no delivered
  identification with the barrier-controlled rate.

One `outOfScope` query (`P-Hammond-Forster`) is a statement-level jurisdiction finding:
the Förster transfer geometry and the Hammond two-parabola coordinates share no scalar
and no total translation exists. The finding cites the delivered §16 register
(`PhotoLean/Relations.lean:964`, "the transfer geometry shares no scalar with the
energy-surface family"); it is not logical absence. It also carries a search-log entry,
as required for every non-certified outcome.

Each of the ten non-certified queries has a `search-log.json` entry with the searched
statements/kinds/contexts, dependencies, real commands and results, attempted
strategies, candidate evidence, and the exact remaining gap or jurisdiction reason.
No failed proof is relabelled as a refutation; there are no `refuted` outcomes.

## 5. Commands and results

All commands run from the photolean repository root. The full transcript is in
`evidence/gates.log`; mutation output is in `evidence/mutation-tests.log`.

| command | result |
|---|---|
| `python3 audit_boundary/validate_boundary.py` | exit 0, R1 PASS |
| `python3 bounded_audit/validate_screening.py` | exit 0, R2 PASS |
| `python3 bounded_audit/validate_r3.py` | exit 0, R3 PASS |
| `python3 bounded_audit/r4/excited-01/validate.py` | exit 0, R4 E1 PASS |
| `proofs/scripts/check.sh --strict` | exit 0, build OK, scan clean, verdict PASS |
| `proofs/scripts/lake env lean bounded_audit/r4/excited-01/probes/E1-probe.lean` | exit 0, six clean axiom footprints |
| `python3 bounded_audit/r4/excited-01/evidence/mutation_tests.py` | 6/6 mutations fail closed |

Mutation tests (each runs the real validator with `--package` on a mutated copy under
`/tmp`):

1. duplicate pair row — FAIL `pairs.duplicate`, `pairs.count`, `counts.pairs`;
2. pair with no query row — FAIL `pair.noQuery`, `pair.noQueryRow`, counts;
3. certified query with a corrupted probe hash — FAIL `evidence.probeHash`,
   `fragment.screeningHash`;
4. endpoint signature hash drift — FAIL `endpoint.signatureSha256`,
   `fragment.screeningHash`;
5. missing search-log entry for an unresolved query — FAIL `search.missing`,
   `search.count`, `search.counts`;
6. certified query relabelled unresolved without evidence — FAIL `evidence.searchType`,
   `evidence.searchRef`, `evidence.candidateSummary`, `search.missing`.

No Lake build lock was encountered. If one occurs, wait and retry; lock files are not
deleted.

## 6. Hashes (SHA-256)

| artifact | SHA-256 |
|---|---|
| `bounded_audit/r4/excited-01/screening.json` | `9a096648063cda57f484f0ecddb802ebf6aa34fb115b26c31e187e75941ef60b` |
| `bounded_audit/r4/excited-01/search-log.json` | `1a18a2a3bc5d23e62622dd87aa4cd76da4d9edfa98f64a137f0af786645d08f7` |
| `bounded_audit/r4/excited-01/coverage-fragment.json` | `ae20cedb9cef742e9cfc8e242a5b268f5d770098d781105535aa4cad8e9793cd` |
| `bounded_audit/r4/excited-01/probes/E1-probe.lean` | `b2c702d21d96d03b664700fe7c18282b4b989bd9052cca031e357fb5b29cb0e2` |
| `bounded_audit/r4/excited-01/validate.py` | `a0cc305dee96530b25c65b062bbf812d386297bfa9cf1e92f0823993d5b4d47c` |
| `audit_boundary/statement-inventory.json` | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| `audit_boundary/pair-queue.json` | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| `audit_boundary/cluster-plan.json` | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| `audit_boundary/BOUNDARY.md` | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| `relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| `bounded_audit/coverage.json` (read-only) | `a584d38e9318704e3cfa5ea482da09aaa88edaa066e61084dfbd834d502e09fd` |

The legacy registry hash is the accepted hash; `coverage.json` is unchanged and is not
written by this package. The delivered `PhotoLean/**/*.lean` tree still has 102 files.

Reproducibility helpers (not part of the screening content):
`build_package.py` `8f519b11420865d1abe66170f7aa28b3673c90c0fa423a11b93020959de83384`;
`evidence/mutation_tests.py` `2c199cb97d233d8226d192a6ce06f4ff94781602cff2917e80ff9274d448f8d8`.

## 7. Deviations and blockers

- **Coverage shape.** The package screens the exact R1 work-package list; it has 6
  certified, 9 unresolved, and 1 outOfScope query. This is not a forced-edge package:
  every certified row has a real typed certificate, and every unresolved row names a
  concrete missing bridge.
- **outOfScope.** `P-Hammond-Forster` is the only outOfScope record. The reason is
  statement-level (no shared scalar, no total translation) and is supported by the
  delivered §16 register. It is not used to avoid a difficult proof; the pair has no
  shared coordinate on which a query could be stated.
- **No legacy evidence reused.** The legacy registry has no certified record for these
  16 pairs, so all certified evidence is new. The registry remains read-only.
- **No alias resolutions.** None of the four R1 dangling legacy aliases is used as an
  endpoint; `aliasResolutions` is empty.
- **No coverage ledger write.** The package emits a fragment only; the integration agent
  owns `coverage.json`, `validate_coverage.py`, `bounded_audit/r4/README.md`, and
  `loop/产出.md`.
- **Blockers.** None.

## 8. Non-claims

The certified rows are model-internal statements under their declared contexts and
premises; they are not claims of physical universality. The definitional identity is a
kernel `rfl` pin, not propositional equality of physical vocabularies. The unresolved
rows are candidate registrations, not negative claims. The outOfScope row is a
jurisdiction finding, not logical absence. The package makes no pair-count or edge-count
target claim, and it does not assert that the bounded universe is exhaustive.
