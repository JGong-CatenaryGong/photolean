# R5 Package RAD2 — Radiative and energy-transfer relations, second block

Status: **submitted-R5-pending-review**. This package screens exactly the sixteen R1
`WP-radiative-energy-transfer-02` pairs. It does not write `bounded_audit/coverage.json`,
`loop/产出.md`, any accepted R1–R4 artifact, any `PhotoLean/**` source, the legacy
registry, the original repositories, the manuscript, or the backup.

## 1. Counts

| quantity | value |
|---|---:|
| pairs screened | 16 |
| named statement-level queries | 16 |
| certified | 4 |
| refuted | 0 |
| unresolved | 6 |
| notEstablished | 0 |
| outOfScope | 6 |
| search-log entries | 12 |

Expected-kind counts: `observationalEquivalence` 4, `conditionalComposition` 6,
`implication` 6. Every pair has exactly one named query; no query uses a pair-level
anchor as an endpoint. No pair from the accepted R2 (10), R3 (11) or R4 (46) packages is
rescreened: prior coverage is derived directly from those five accepted screening
packages (16 + 10 + 11 + 16 + 14 + 16 = 67 accepted pairs; the R5 mutable ledger is never
read or pinned).

## 2. Pair and query table

| pair | query | status | expected kind | evidence |
|---|---|---|---|---|
| P-KashaVavilov-StokesShift | Q-RAD2-KVS-01 | outOfScope | implication | jurisdiction `SL-RAD2-KVS-01` |
| P-KashaVavilov-ICvsISC | Q-RAD2-KVI-01 | unresolved | conditionalComposition | search `SL-RAD2-KVI-01` |
| P-KashaVavilov-Forster | Q-RAD2-KVF-01 | outOfScope | implication | jurisdiction `SL-RAD2-KVF-01` |
| P-KashaVavilov-Einstein | Q-RAD2-KVE-01 | unresolved | conditionalComposition | search `SL-RAD2-KVE-01` |
| P-SternVolmer-EnergyGapLaw | Q-RAD2-SVE-01 | unresolved | conditionalComposition | search `SL-RAD2-SVE-01` |
| P-SternVolmer-StokesShift | Q-RAD2-SVS-01 | outOfScope | implication | jurisdiction `SL-RAD2-SVS-01` |
| P-SternVolmer-ICvsISC | Q-RAD2-SVI-01 | unresolved | conditionalComposition | search `SL-RAD2-SVI-01` |
| P-SternVolmer-Forster | Q-RAD2-SVF-01 | outOfScope | implication | jurisdiction `SL-RAD2-SVF-01` |
| P-SternVolmer-Einstein | Q-RAD2-SVEb-01 | unresolved | conditionalComposition | search `SL-RAD2-SVEb-01` |
| P-QuantumYield-EnergyGapLaw | Q-RAD2-QYE-01 | certified | observationalEquivalence | probe `qyEgBridge` |
| P-QuantumYield-StokesShift | Q-RAD2-QYS-01 | outOfScope | implication | jurisdiction `SL-RAD2-QYS-01` |
| P-QuantumYield-ICvsISC | Q-RAD2-QYI-01 | certified | observationalEquivalence | probe `qyIcBridge` |
| P-QuantumYield-Forster | Q-RAD2-QYF-01 | certified | observationalEquivalence | probe `qyFoBridge` |
| P-QuantumYield-Einstein | Q-RAD2-QYEB-01 | certified | observationalEquivalence | probe `qyEbBridge` |
| P-FluorPhos-EnergyGapLaw | Q-RAD2-FPE-01 | unresolved | conditionalComposition | search `SL-RAD2-FPE-01` |
| P-FluorPhos-StokesShift | Q-RAD2-FPS-01 | outOfScope | implication | jurisdiction `SL-RAD2-FPS-01` |

## 3. New evidence

All four certified outcomes use **new** typed Lean certificates in
`probes/RAD2-probe.lean` (namespace
`PhotoLean.RelationAudit.BoundedAudit.RAD2`). No legacy certificate is reused: the legacy
registry has only pair-level `notEstablished` anchors (and, for
`P-SternVolmer-Forster`, a `look-alike` shape-note disposition) for these pairs.

| query | certificate | statement |
|---|---|---|
| Q-RAD2-QYE-01 | `qyEgBridge` | `yieldOf ![kr, nrRate …] 0 / yieldOf ![kr, nrRate …] 1 = (kr/A)·exp(nrBarrier/(kB·T))` under `kr > 0`, `A > 0` |
| Q-RAD2-QYI-01 | `qyIcBridge` | `yieldOf ![icRate, iscRate] 1 / yieldOf ![icRate, iscRate] 0 = (HSO²·AS/AI)·exp((fcBarrier_I − fcBarrier_S)/(kB·T))` under `FCData`, `HSO > 0` |
| Q-RAD2-QYF-01 | `qyFoBridge` | `fretEff6 r6 R = 1 − yieldOf ![kD, kD·(r6/R⁶)] 0` under `kD > 0`, `r6 ≥ 0`, `R ≠ 0` |
| Q-RAD2-QYEB-01 | `qyEbBridge` | `A·tauR(A + kNR) = yieldOf ![A, kNR] 0` (totalized, no premise) |

Each certificate is a typed `Certificate.observationalEquivalence` with an explicit
`ObservationalSetup`, shared context, `Channel` with a declared observed-value type and
input domain, and a `kindCheckTheorem` (`certificateKind cert =
RelationKind.observationalEquivalence := rfl`). The certificates consume delivered rows:

- `PhotoLean.QuantumYield.yieldOf_div_yieldOf`
  (`PhotoLean/QuantumYield/Criterion.lean:96`),
- `PhotoLean.EnergyGapLaw.cert_nrRate` / `cert_nrBarrier`
  (`PhotoLean/EnergyGapLaw/Basic.lean:80,67`),
- `PhotoLean.ICvsISC.rate_ratio_eq` (`PhotoLean/ICvsISC/Criterion.lean:80`),
- `PhotoLean.Relations.fretEff6_eq_one_sub_yieldOf` (`PhotoLean/Relations.lean:836`),
- `PhotoLean.Relations.einstein_yield_via_qy` (`PhotoLean/Relations.lean:826`).

The `Q-RAD2-QYE-01` certificate deliberately declares only `kr > 0` and `A > 0`: the
totalized division makes `kB·T > 0` non-load-bearing for this identity, so it is not a
declared premise (weakest-premise standard). The `Q-RAD2-QYEB-01` identity is totalized
over ℝ² and declares no premise. In the probe, `set_option linter.unusedVariables` is not
disabled and the compile log has no warning, so every declared premise is consumed.

Probe gates (real outputs in `probes/compile.log`, `probes/axioms.log`,
`probes/scan.log`):

- `proofs/scripts/lake env lean bounded_audit/r5/radiative-02/probes/RAD2-probe.lean`
  exits 0; the four `#print axioms` lines list only `propext`, `Classical.choice`,
  `Quot.sound`.
- The forbidden-token scan over the probe reports `CLEAN (no sorry, admit, custom axiom or
  constant)` and a clean whole-word scan for the two placeholder keywords.

## 4. Non-certified records

Six `unresolved` queries name a precise chemical candidate and the exact missing bridge:

- `P-KashaVavilov-ICvsISC`: the ladder `ic 1` would be `ICvsISC.icRate`, but KashaVavilov
  imports only `Kasha.Basic/Criterion` (not `Kasha.Compose` where `marcusIC` lives) and no
  delivered statement instantiates a ladder level with `icRate`.
- `P-KashaVavilov-Einstein`: the ladder `rad n` would be an Einstein coefficient, but the
  ladder quantifies over an arbitrary rate function and no delivered identification exists.
- `P-SternVolmer-EnergyGapLaw`: `kq·q` would be an EGL `nrRate`, but SV has no gap
  coordinate and EGL has no concentration axis.
- `P-SternVolmer-ICvsISC`: `kq·q` would be an IC/ISC channel at an encounter geometry, but
  neither side declares the other coordinate.
- `P-SternVolmer-Einstein`: `k0` would split as `A + kNR`, but SV keeps `k0` whole.
- `P-FluorPhos-EnergyGapLaw`: `kIC` would be an EGL `nrRate` at the S1→S0 gap, but `kIC`
  is a free FP rate and FP has no barrier/gap premise.

Six `outOfScope` queries are statement-level jurisdiction findings, not cluster-name
dissimilarity:

- `P-KashaVavilov-StokesShift`, `P-SternVolmer-StokesShift`, `P-QuantumYield-StokesShift`,
  `P-FluorPhos-StokesShift`: a dimensionless ladder/ratio/partition observable versus a
  band-position energy; no total translation.
- `P-KashaVavilov-Forster`: a level-indexed spectral predicate versus a donor–acceptor
  distance/orientation geometry.
- `P-SternVolmer-Forster`: the delivered shape row `fretEff6_inv_eq_one_plus`
  (`PhotoLean/Relations.lean:908`) shares only the `1 + control` form; the controls are
  `KSV·q` (concentration × rate constant) and `R⁶/r6` (sixth-power distance ratio). The
  legacy ledger itself records the pair as `look-alike` / `shape-note`
  (`D-S15-fretEff6_inv_eq_one_plus`), not an edge. Declaring the shape an identity would
  be exactly the forced shape-only relation the audit forbids.

Each of the twelve non-certified queries has a `search-log.json` entry with searched
statements/kinds/contexts, dependencies, real commands and results, attempted strategies,
candidate evidence, the exact remaining gap or jurisdiction reason, and recompute
commands. The raw command transcript is in `evidence/search-commands.log` and
`evidence/search-supplement.log`. No failed proof is relabelled as a refutation; the
package has `refuted = 0`.

## 5. Commands and results

All commands run from the photolean repository root. Full transcripts:
`evidence/gates-python.log`, `evidence/gates-lake.log`,
`evidence/mutation-tests.log`.

| command | result |
|---|---|
| `python3 bounded_audit/r5/radiative-02/validate.py` | exit 0, 2480 checks run, 0 failed |
| `python3 audit_boundary/validate_boundary.py` | exit 0, R1 PASS |
| `python3 bounded_audit/validate_screening.py` | exit 0, R2 PASS |
| `python3 bounded_audit/r4/validate_r3_content.py` | exit 0, 7 expected ledger-freshness exclusions, 0 content failures |
| `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json` | exit 0, 846 checks, 67/136 accepted snapshot |
| `proofs/scripts/check.sh --strict` | exit 0, build OK, scan clean, verdict PASS |
| `proofs/scripts/lake env lean bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | exit 0, four clean axiom footprints |
| `python3 bounded_audit/r5/radiative-02/evidence/mutation_tests.py` | control PASS, 7/7 mutations fail closed |

Lake commands were serialized: the probe compile and the strict build were run one after
the other; no lock file was deleted.

Mutation tests (each runs the real `validate.py` against a mutated copy under `/tmp`):

1. duplicate pair row — FAIL `pairs.duplicate`, `pairs.count`;
2. pair with no query row — FAIL `pair.noQuery`;
3. certified query with a corrupted probe hash — FAIL `evidence.probeHash`;
4. endpoint signature hash drift — FAIL `endpoint.signatureSha256`;
5. missing search-log entry — FAIL `search.missing`, `searchLogReference.sha256`;
6. outOfScope relabelled certified without evidence — FAIL `evidence.type`,
   `search.certifiedEntry`;
7. coverage fragment pair count drift — FAIL `fragment.pairCount`.

The repository builder `build_package.py` reproduces the three JSON artifacts
byte-for-byte (re-run yields the same SHA-256 values).

## 6. Hashes (SHA-256)

| artifact | SHA-256 |
|---|---|
| `bounded_audit/r5/radiative-02/screening.json` | `fcb1683765fca39abace7299b09436d39aefa943b96aa515a96f2dab548c83c6` |
| `bounded_audit/r5/radiative-02/search-log.json` | `9a28cd2df5e0ab0aa3863efaab1648279df76192929fbb4d9495ed7d9adf84e5` |
| `bounded_audit/r5/radiative-02/coverage-fragment.json` | `2292f2b02509e6bc535655ea5ce0e100622ad8706ab27eb331b68489ab93561e` |
| `bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | `36a5ae42f68a6112f466f067a713d6b2a8f2e781bbc18bb735e8dc3ddabbef2b` |
| `bounded_audit/r5/radiative-02/probes/compile.log` | `ce2b95d2c3ba07255415f4eaf33111e18f2f310f5ab2b2c7f74e15b895838077` |
| `bounded_audit/r5/radiative-02/validate.py` | `bc36b826cc402fa0314f4e797c3e7568630e8fa616baa76f0366111ec8a18d04` |
| `bounded_audit/r5/radiative-02/build_package.py` | `2f9941c9ccc4490cb99d1fbf886e86d5cc0dfe393ad981dcd7ccd052ac5e3b0d` |
| `bounded_audit/r5/radiative-02/evidence/mutation_tests.py` | `74730b75ecab285f1b0186a7709a3913186f54a809bf6a9e6f05306de279b614` |
| `audit_boundary/statement-inventory.json` | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| `audit_boundary/pair-queue.json` | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| `audit_boundary/cluster-plan.json` | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| `audit_boundary/BOUNDARY.md` | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| `relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| `bounded_audit/r4/coverage-accepted.json` | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |
| `bounded_audit/coverage.json` (read-only, unchanged) | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |

The legacy registry hash is the accepted hash; the mutable `bounded_audit/coverage.json`
is unchanged and is neither read nor pinned by this package. The delivered
`PhotoLean/**/*.lean` tree still has 102 files.

## 7. Deviations and blockers

- **Coverage shape.** The package screens the exact R1 work-package list: 4 certified,
  6 unresolved, 6 outOfScope. This is not a forced-edge package; every certified row has
  a real typed certificate and every unresolved row names a concrete missing bridge.
- **outOfScope density.** Six of sixteen pairs are jurisdiction findings. They are
  statement-level (explicit endpoints, observables, no total translation) and are not
  based on cluster or theory-name dissimilarity. The `P-SternVolmer-Forster` finding
  explicitly refuses a shape-only identity that the legacy ledger itself labels a
  `look-alike` / `shape-note`.
- **No legacy evidence reused.** The legacy registry has no certified record for these
  pairs, so all certified evidence is new. The registry remains read-only.
- **No alias resolutions.** None of the four R1 dangling legacy aliases is used as an
  endpoint; `aliasResolutions` is empty.
- **No coverage ledger write.** The package emits a fragment only; the integration agent
  owns the R5 cumulative ledger, the coverage validator and the aggregate report.
- **Blockers.** None.

## 8. Non-claims

The certified rows are model-internal statements under their declared contexts and
premises; they are not claims of physical universality. The observational equivalences
are equalities of declared real-valued channels, not claims that two physical vocabularies
denote the same reality. The unresolved rows are candidate registrations, not negative
claims. The outOfScope rows are jurisdiction findings, not logical absence. The package
makes no pair-count or edge-count target claim, and it does not assert that the bounded
query set is exhaustive.
