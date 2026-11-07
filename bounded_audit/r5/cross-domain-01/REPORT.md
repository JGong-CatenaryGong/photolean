# R5 XD1 — Cross-domain screening package

Status: `submitted-R5-pending-review`
Round: R5
Package: `bounded_audit/r5/cross-domain-01/`
Snapshot: `snap-bounded-audit-2026-11-04`
Work package: `XD1-CROSS-DOMAIN-01` (R1 `WP-cross-domain-screening-01` minus the accepted
`P-Kasha-Sabatier` pair)

## 1. Scope and boundary

This package screens exactly the fifteen pairs named in `loop/计划.md` Package XD1:

`P-Marcus-Goldschmidt`, `P-Hammond-Goldschmidt`, `P-BEP-Goldschmidt`,
`P-Kasha-Goldschmidt`, `P-Sabatier-Goldschmidt`, `P-Sabatier-KashaVavilov`,
`P-Sabatier-SternVolmer`, `P-Sabatier-QuantumYield`, `P-Sabatier-FluorPhos`,
`P-Sabatier-EnergyGapLaw`, `P-Sabatier-StokesShift`, `P-Sabatier-ICvsISC`,
`P-Sabatier-Forster`, `P-Sabatier-Einstein`, `P-Goldschmidt-SymmetryFactor`.

The R1 work package `WP-cross-domain-screening-01` has sixteen pairs; the sixteenth,
`P-Kasha-Sabatier`, was screened and accepted in R2 (`Q-WPS01-KS-01`) and is not rescreened.
The package is exactly the R1 work package minus that accepted pair. No pair outside the
fifteen is touched, and no accepted R2/R3/R4 pair is rescreened.

Prior coverage is derived from the accepted screening packages themselves:

| round | package | pairs |
|---|---|---:|
| R2 | `bounded_audit/wp-surface-01/screening.json` | 10 |
| R3 | `bounded_audit/r3/screening.json` | 11 |
| R4 E1 | `bounded_audit/r4/excited-01/screening.json` | 16 |
| R4 E2 | `bounded_audit/r4/excited-02/screening.json` | 14 |
| R4 CI | `bounded_audit/r4/conical-01/screening.json` | 16 |
| **total** |  | **67** |

The mutable R5 cumulative ledger `bounded_audit/coverage.json` is neither read nor pinned by
`validate.py` or `build_package.py`. The package's `snapshot` carries only the frozen R1
artifacts, the legacy registry, and the five accepted package hashes above.

## 2. Counts

| item | count |
|---|---:|
| assigned pairs | 15 |
| named statement-level queries | 15 |
| `certified` | 0 |
| `refuted` | 0 |
| `unresolved` | 3 |
| `notEstablished` | 0 |
| `outOfScope` | 12 |

Pair-level outcomes and endpoints:

| pair | outcome | source endpoint | target endpoint |
|---|---|---|---|
| P-Marcus-Goldschmidt | outOfScope | `Marcus.InvertedRegion` | `Goldschmidt.tolFac` |
| P-Hammond-Goldschmidt | outOfScope | `Hammond.tsCoord` | `Goldschmidt.tolFac` |
| P-BEP-Goldschmidt | outOfScope | `BEP.bepRadius` | `Goldschmidt.GoldschmidtConforms` |
| P-Kasha-Goldschmidt | outOfScope | `Kasha.KashaRule` | `Goldschmidt.GoldschmidtConforms` |
| P-Sabatier-Goldschmidt | outOfScope | `Sabatier.NearOptimal` | `Goldschmidt.GoldschmidtConforms` |
| P-Sabatier-KashaVavilov | outOfScope | `Sabatier.activity` | `KashaVavilov.SpecSame` |
| P-Sabatier-SternVolmer | outOfScope | `Sabatier.activity` | `SternVolmer.svRatioDyn` |
| P-Sabatier-QuantumYield | outOfScope | `Sabatier.activity` | `QuantumYield.yieldOf` |
| P-Sabatier-FluorPhos | outOfScope | `Sabatier.activity` | `FluorPhos.phiF` |
| P-Sabatier-EnergyGapLaw | unresolved | `Sabatier.parabolicBarrier` | `EnergyGapLaw.nrBarrier` |
| P-Sabatier-StokesShift | unresolved | `Sabatier.parabolicBarrier` | `StokesShift.stokesShift` |
| P-Sabatier-ICvsISC | unresolved | `Sabatier.activity` | `ICvsISC.icRate` |
| P-Sabatier-Forster | outOfScope | `Sabatier.activity` | `Forster.fretRate` |
| P-Sabatier-Einstein | outOfScope | `Sabatier.activity` | `Einstein.tauR` |
| P-Goldschmidt-SymmetryFactor | outOfScope | `Goldschmidt.tolFac` | `SymmetryFactor.tsCoordZero` |

The 12 `outOfScope` records are statement-level jurisdiction registrations, not
theory-name dissimilarity. Each names the two endpoint declarations, the types of their
arguments, the absence of a total translation, and the source/dependency facts that would
remove the jurisdiction reason. The six Goldschmidt pairs are geometric/radius statements
versus energy, ladder, yield or curvature statements. The six Sabatier pairs have a
catalytic descriptor axis versus a ladder, concentration axis, finite channel set, distance
or radiative lifetime.

The 3 `unresolved` records are the only pairs with a concrete formula-level candidate:

* `P-Sabatier-EnergyGapLaw`: the descending Sabatier branch `parabolaDown lam2 dE` is the
  energy-gap barrier `nrBarrier lam2 dE`; the full effective barrier is a maximum of two
  branches and the catalytic descriptor is not identified with the optical gap.
* `P-Sabatier-StokesShift`: the symmetric apex barrier is one eighth of the Stokes shift,
  `parabolicBarrier lam lam 0 = stokesShift lam e00 / 8`; the optical and catalytic
  reorganization energies are not identified.
* `P-Sabatier-ICvsISC`: the IC rate is the Sabatier activity functional at the FC barrier
  with the same prefactor; the rate-law substitution does not identify the IC channel with
  the catalytic step.

These three are deliberately **not** certified. The plan warning is applied: an Arrhenius
shape alone does not identify a reaction barrier with an optical/IC parameter, and a
formula-level branch identity or symmetric specialization is not a shared physical context.

## 3. Query protocol

Every query carries the fields required by the R1 boundary:

* `queryId`, `pairId`, `title`, `chemicalQuestion`, `chemicalRationale`;
* two inventory endpoints with `statementId`, `theory`, `declaration`, `declarationKind`,
  `sourceArtifact`, `sourceLine`, `version`, `signatureSha256`,
  `sourceArtifactSha256`, `endpointForm`;
* a declared shared/candidate context with fields, physical reading and provenance;
* explicit left/right translations (`none-declared` for jurisdiction records,
  `candidate-not-total` for the three open candidates) with reasons;
* a premise predicate and premise-ID list (empty and `True` where the search, not a proof,
  is the evidence; no non-load-bearing premise is admitted);
* a scope ID, description, domain and snapshot;
* an expected kind, expected-kind rationale and a falsification condition;
* a provenance record (search-log locator and legacy disposition);
* one and only one outcome status.

No query uses `observationalEquivalence` or `distinguishability` as its expected kind, so no
observation channel is required. The three candidate identities are recorded as scoped
searches with a candidate probe, not as certified observational equivalences.

## 4. Evidence and local probe

There are no new `certified` or `refuted` outcomes. No legacy certificate is reused as a new
certified outcome. The local probe `probes/XD1-probe.lean` is additive and contains three
typed candidate identities:

| declaration | candidate identity | axiom footprint |
|---|---|---|
| `sabatierStrongBranch_eq_eglBarrier` | `parabolaDown lam dE = nrBarrier lam dE` | `propext`, `Classical.choice`, `Quot.sound` |
| `sabatierSymmetricApex_eq_stokesEighth` | `parabolicBarrier lam lam 0 = stokesShift lam e00 / 8` | `propext`, `Classical.choice`, `Quot.sound` |
| `sabatierActivity_eq_icRate` | `icRate A lam kB T x = A * activity (fcBarrier lam) kB T x` | `propext`, `Classical.choice`, `Quot.sound` |

The probe compiles with exit 0 under
`proofs/scripts/lake env lean bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean`.
Its `#print axioms` blocks contain only `propext`, `Classical.choice` and `Quot.sound`.
The source contains no `sorry`, `admit`, custom `axiom` or `constant` declaration. The
probe is referenced by the package as `candidate-evidence`, not as a certified-outcome
probe; the validator checks every candidate declaration against the axiom log and rejects a
certified outcome that lacks a genuine certificate.

## 5. Search log

`search-log.json` has 15 entries, one per query. Each entry records:

* the searched inventory statements and searched evidence kinds;
* the considered contexts and the dependency artifacts with locators and findings;
* the actual serialized commands and their actual results (5 commands per outOfScope
  entry, 7 per unresolved entry);
* the attempted strategies and their outcomes;
* candidate evidence and the exact remaining gap or jurisdiction reason;
* recompute commands and a rationale.

The commands are real greps, import measurements and
`python3 tools/relation_audit_registry.py --explain-pair` calls, run in this checkout. The
legacy no-edge register (`PhotoLean/Relations.lean` §10 and §16) and the legacy pair-level
`notEstablished` anchors are recorded as census history, not as audit verdicts.

## 6. Gates

All commands were run from the PhotoLean repository root. Lake commands were serialized;
no two Lake invocations ran at the same time.

| gate | command | result |
|---|---|---|
| R1 boundary | `python3 audit_boundary/validate_boundary.py` | exit 0; 17 theories, 136 pairs, 1154 statement rows |
| R2 current | `python3 bounded_audit/validate_screening.py` | exit 0; 0 failed checks |
| R3 historical content | `python3 bounded_audit/r4/validate_r3_content.py` | exit 0; 0 failed checks, 7 enumerated ledger-freshness exclusions |
| R4 frozen snapshot | `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json` | exit 0; 846 checks; 21 accepted + 46 submitted = 67/136, 69 remaining |
| R4 E1 | `python3 bounded_audit/r4/excited-01/validate.py` | exit 0; PASS |
| R4 E2 | `python3 bounded_audit/r4/excited-02/validate.py` | exit 0; PASS |
| R4 CI | `python3 bounded_audit/r4/conical-01/validate.py` | exit 0; PASS |
| **XD1 package** | `python3 bounded_audit/r5/cross-domain-01/validate.py` | **exit 0; PASS, 0 failed checks** |
| strict build/scan | `proofs/scripts/check.sh --strict` | exit 0; build OK, `sorry`/custom-axiom scan clean, verdict PASS |
| probe compile | `proofs/scripts/lake env lean bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean` | exit 0; 3 declarations, allowed axioms only |

The strict scan covers `PhotoLean/**/*.lean`; the local probe is outside that tree, so it was
also scanned directly for forbidden tokens (clean) and its `#print axioms` output was parsed
by the package validator.

Machine-readable captures of this gate run and of the mutation run are stored in
`evidence/gates.log` and `evidence/mutations.log`.

## 7. Mutation tests

Seven independent `/tmp` mutations were run against copies; every one made the validator
exit 1. The intended check was hit in each case.

| mutation | injected change | first failures |
|---|---|---|
| M1 | replace a pair ID with the excluded `P-Kasha-Sabatier` | `pairs.coverage`, `pairs.acceptedOverlap`, `pairs.excluded` |
| M2 | replace an endpoint statement ID with a non-inventory value | `endpoint.missing` |
| M3 | flip an outcome to `certified` with no certificate | `evidence.type`, `evidence.kindMatch`, `evidence.probe*` |
| M4 | drift a shared-context field list | `context.fieldsMatch` |
| M5 | remove the last search-log entry | `search.missing`, `searchLogReference.sha256` |
| M6 | change the fragment's screening hash | `fragment.sha` |
| M7 | change a query scope description | `scope.descriptionMatch` |

## 8. Hashes

| artifact | SHA-256 |
|---|---|
| `screening.json` | `fa096f5932a2871847cb67e0a94a7190516cd94f0bd7c7b57d329a34e24cdfd3` |
| `search-log.json` | `0bf725db10525b5a519e696845a0f2bcf40185fe81f9e34c7df708531d5c26d7` |
| `coverage-fragment.json` | `7ace5775895aab795a76e0cf9d2be30c491b90a6cfcfe30b207532c639b7c87f` |
| `validate.py` | `3cef2a80dc273911df4083643fd9acedcb097e0fad608b341294f2b85edb0fc6` |
| `build_package.py` | `23b278fe00ffe1d1ba50b1958f93b33ae82034eb9193ac0dfc10ccf786b4519a` |
| `probes/XD1-probe.lean` | `f5668397e57c44266dc70fc0195061f780b5171bf860cd533986e9c57d1f07f1` |
| `probes/compile.log` | `93845f661463b2cf2a0f618510804ee6f4d2b83393ab1ba582b269c1f67ce4eb` |
| `evidence/gates.log` | `9947ba1112419c455dfab341787c74068b358ec1fb44c3008faab0480be5b5e5` |
| `evidence/mutations.log` | `459e32b9e898489e6b8ae3276eff0beb05c7d595e0be0e2c9b3ea01b02146d7e` |

Frozen inputs and prior packages:

| artifact | SHA-256 |
|---|---|
| `audit_boundary/statement-inventory.json` | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| `audit_boundary/pair-queue.json` | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| `audit_boundary/cluster-plan.json` | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| `audit_boundary/BOUNDARY.md` | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| `relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| `bounded_audit/r4/coverage-accepted.json` | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |

## 9. Deviations

1. **No certified or refuted outcome.** The package deliberately certifies nothing. The
   three candidate identities are genuine kernel facts, but each is branch-level, a
   symmetric specialization, or a rate-law substitution; none supplies the statement-level
   identification of the catalytic process with the optical/IC process. Certifying them
   would be a forced or shape-only relation, which the plan forbids.
2. **The local probe is candidate evidence, not a certificate set.** The validator's
   `probeReference.role` is `candidate-evidence`; the probe declarations are checked against
   the axiom log and are cited by the three `unresolved` queries, but they do not back a
   `certified` outcome.
3. **`notEstablished` is unused.** The non-certified outcomes are either a statement-level
   jurisdiction record (`outOfScope`) or an open candidate (`unresolved`); no pair required
   a scoped negative registration of the `notEstablished` form.
4. **Ordering.** `workPackage.pairIds` follows the fifteen-pair list in `loop/计划.md`; the
   nested R1 reference preserves the sixteen-pair R1 order including `P-Kasha-Sabatier`.
   The validator checks the set difference and the exact R1 list, not an order that would
   silently rescreen the excluded pair.

## 10. Blockers

None. The 15-pair package is complete, the package validator passes, all historical content
gates pass, the strict build/scan passes, the probe compiles with an allowed axiom footprint,
and the seven mutation tests fail closed.

## 11. Non-claims

* This package is a bounded screening of fifteen pairs; it is not a completeness claim over
  the corpus or over conceivable relations outside the frozen query protocol.
* An `outOfScope` record is a statement-level jurisdiction registration, not a claim of
  logical non-existence.
* An `unresolved` record names a remaining candidate/gap; it is not a negative claim.
* The candidate probe identities are formula-level facts; they are not claims that the
  catalytic and optical/IC processes are the same physical process.
* The package does not assign acceptance; it remains `submitted-R5-pending-review` until
  independent K3 review.
