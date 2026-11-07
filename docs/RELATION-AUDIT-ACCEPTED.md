# Accepted bounded relation-audit registry (R8 submission)

**Acceptance state: `accepted-R8`.** Two independent K3.1 Pro reviews passed and the lead recorded the uniform registry/disposition acceptance flip. The registry and the disposition ledger share this state.

## What this snapshot is

The registry is a deterministic, machine-auditable integration of the accepted R1 boundary, the accepted R2-R5 screening packages, the final R7 coverage ledger and the unchanged legacy registry. It separates three dimensions that must not be conflated:

- **Pair coverage:** 136/136 pairs have a named statement-level query or a statement-level `outOfScope` record. This is not a certification count.
- **Query outcomes:** 152 active named queries: 67 certified, 0 refuted, 39 unresolved, 2 notEstablished, 44 outOfScope.
- **Certified relation discovery:** 67 certified queries over 53 distinct pairs, with 7 declared relation kinds available and no `refuted` outcome in this snapshot.

## Counts

| Dimension | Value |
| --- | ---: |
| Accepted screening packages | 10 |
| Pair universe / pairs with screening | 136 / 136 |
| Active named queries | 152 |
| Active records | 152 |
| Certified / refuted / unresolved / notEstablished / outOfScope | 67 / 0 / 39 / 2 / 44 |
| Pairs with at least one certified relation | 53 |
| Certificate library (total / deliveredModule / boundedProbe) | 93 / 38 / 55 |
| Active certified evidence (probe / reused legacy) | 55 / 12 |
| XD1 candidate declarations (not certificates) | 3 |
| Probe files / reviewed declarations | 9 / 58 |
| Evidence references (supporting delivered theorems) | 77 |
| Legacy records disposed / named / pair anchors | 151 / 26 / 125 |
| Legacy alias repairs / corrected certified records | 4 / 3 |
| Old absence/new evidence reconciliations | 44 |

Note on the package count: the plan's prose says "eight accepted R2-R5 screening packages". The actual accepted artifacts contain **ten** packages (R2 one, R3 one, R4 three, R5 five), and all ten are required to reach the contract's 136 pairs / 152 queries. No package was dropped or invented; this is a reported plan-metadata deviation, not a data substitution.

## Five outcomes and seven kinds

The schema and records implement the five outcomes `certified`, `refuted`, `unresolved`, `notEstablished`, `outOfScope` and the seven relation kinds `definitionalIdentity`, `implication`, `equivalence`, `conditionalComposition`, `observationalEquivalence`, `distinguishability`, `refutation`.

- `certified` requires a library certificate and a non-refutation relation kind.
- `refuted` requires a refutation certificate and is an outcome; it is not an eighth kind. No active query is refuted in this snapshot.
- `unresolved` requires a named remaining candidate/gap and a search-log entry.
- `notEstablished` requires machine-recomputable scoped dependency evidence.
- `outOfScope` requires a statement-level jurisdiction finding and provenance.

Contexts, translations, premise predicates and IDs, versions, scopes and snapshots, observation channels/domains, falsification conditions and provenance are preserved from the accepted query objects.

The 77 unique supporting theorems cited inside accepted evidence are resolved in `evidenceReferences`: 54 are R1 inventory rows and 23 are delivered `PhotoLean/Relations.lean` theorems outside the seventeen-theory statement authority. They are supporting evidence, not active statement endpoints; every active endpoint still resolves to an R1 inventory declaration.

## Evidence classes

### deliveredModule

A certificate declared in the frozen `PhotoLean/**/*.lean` tree. The legacy full-registry validator remains the evidence gate. All 38 legacy certificates are retained in the library; 12 are directly reused by active certified queries and 26 remain explicit retained legacy/support evidence without creating fake active pair queries.

### boundedProbe

A package-local certificate compiled directly from an accepted probe file under `bounded_audit/`, outside the frozen default build targets. Each entry carries its accepted package provenance, exact probe path and SHA-256, certificate declaration and kind-check theorem, direct serial compile command, compile/axiom log, live allowed-axiom footprint (`propext`, `Classical.choice`, `Quot.sound`) and package review reference.

The nine probe files contain 58 reviewed declarations: 55 certificate declarations and 3 XD1 candidate declarations. The candidates are attached only to unresolved queries and are excluded from the certificate library by construction. The integrated validator must serially compile all nine probes, audit all 58 declarations, run the package placeholder/custom-axiom gates and the original legacy full validator.

| Probe file | Certificates | Candidates | Reviewed |
| --- | ---: | ---: | ---: |
| `bounded_audit/r3/probes/R3-probe.lean` | 7 | 0 | 7 |
| `bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | 8 | 0 | 8 |
| `bounded_audit/r4/excited-01/probes/E1-probe.lean` | 6 | 0 | 6 |
| `bounded_audit/r4/excited-02/probes/E2-probe.lean` | 5 | 0 | 5 |
| `bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean` | 0 | 3 | 3 |
| `bounded_audit/r5/radiative-01/probes/RAD1-probe.lean` | 11 | 0 | 11 |
| `bounded_audit/r5/radiative-02/probes/RAD2-probe.lean` | 4 | 0 | 4 |
| `bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | 10 | 0 | 10 |
| `bounded_audit/wp-surface-01/probes/Surface-probe.lean` | 4 | 0 | 4 |

## Legacy reconciliation

The companion `relation_audit/legacy-dispositions.accepted.json` disposes every one of the 151 unchanged legacy records exactly once: 26 named queries and 125 pair anchors. Legacy prose is retained verbatim in the ledger; no old record is deleted or rewritten.

Four R1 legacy statement IDs are metadata aliases, not delivered declarations: `PhotoLean.BEP.rateViaEact`, `PhotoLean.Marcus.rateDescriptor`, `PhotoLean.EnergyGapLaw.nrBarrier_eq_zero` and `PhotoLean.StokesShift.emEnergy_eq_zero`. They affect three certified legacy records (`rec-D-S05-bep-rate-eq-exp-neg-eact`, `rec-D-S06-hammond-sharp-iff-marcus-sharp`, `rec-D-S15-egBarrier-zero-iff-emEnergy-zero`). The disposition ledger records all four alias-to-real mappings with inventory and package source evidence, and gives each affected record an explicit corrected query/record view with real endpoint statement IDs and corrected `statementVersion`, linked to the unchanged legacy certificate and to the corresponding active bounded query.

For the 41 old `notEstablished` pair anchors whose pair now has checked evidence, the ledger records the active query IDs and the precise relationship `superseded-in-named-scope`: the old statement was only a snapshot absence and is superseded within the named statement scope, while the old prose remains a historical record outside it. For the three legacy undelivered-candidate anchors that now have checked evidence, the relationship is `coexists-different-scope`: the old candidate and the new statement-level relation are different scopes, so neither silently overwrites the other. No failed search is converted into a refutation.

The 125 legacy pair anchors and the five intra-theory legacy records contribute **zero** active pair or query coverage. Pair anchors are coverage history; intra-theory records are retained support evidence.

## Deterministic generation

Run from the isolated PhotoLean repository root:

```bash
python3 tools/relation_audit_bounded/build.py --acceptance accepted-R8
```

The default acceptance state remains `submitted-R8-pending-review`; the accepted artifact is regenerated only with the explicit `--acceptance accepted-R8` state.

The builder reads only frozen/accepted inputs, sorts every collection deterministically, uses no wall clock or random state, and writes with `sort_keys=True`, two-space indentation, UTF-8 and a final newline. It contains no output self-hash and creates no hash cycle. It never edits the legacy registry, accepted packages, frozen PhotoLean tree or backup.

## Input references

| Input | SHA-256 |
| --- | --- |
| R1 boundary (`audit_boundary/BOUNDARY.md`) | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| R1 statement inventory (`audit_boundary/statement-inventory.json`) | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| R1 pair queue (`audit_boundary/pair-queue.json`) | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| R1 cluster plan (`audit_boundary/cluster-plan.json`) | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| R7 coverage ledger (`bounded_audit/coverage.json`) | `7d4c4f2f6df6a50e3aa20ac510dddaebf3e0d63272cb8c9d3a83e90022b48e2d` |
| Legacy registry (`relation_audit/registry.json`) | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| R4 frozen coverage (`bounded_audit/r4/coverage-accepted.json`) | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |
| R2 WP-SURFACE-01 screening (`bounded_audit/wp-surface-01/screening.json`) | `2a98dac9d75d76782a307bd6903dd6adec6dcc946f09e186c07895e3bee1b49c` |
| R3 R3-QUENCH-01 screening (`bounded_audit/r3/screening.json`) | `452d213c5a142b4910f7adcf1e4efd433d02be83f538510992a2dfe758ed262c` |
| R4 R4-E1-EXCITED-01 screening (`bounded_audit/r4/excited-01/screening.json`) | `9a096648063cda57f484f0ecddb802ebf6aa34fb115b26c31e187e75941ef60b` |
| R4 WP-excited-state-kinetics-02 screening (`bounded_audit/r4/excited-02/screening.json`) | `5ceee13be0629cd93b912d68e0a44751e1906c7acfd823cc9297af0a61c94af6` |
| R4 WP-conical-intersection-01 screening (`bounded_audit/r4/conical-01/screening.json`) | `f368b9b1f1ded5800419a5283b541363e83f37c4b8ef54aa641890cb54615487` |
| R5 RAD1 screening (`bounded_audit/r5/radiative-01/screening.json`) | `a5ad482e12223642cdc10db81d36142f9fd8266c7cbb914a8fe243084d31b837` |
| R5 RAD2 screening (`bounded_audit/r5/radiative-02/screening.json`) | `fcb1683765fca39abace7299b09436d39aefa943b96aa515a96f2dab548c83c6` |
| R5 RAD3 screening (`bounded_audit/r5/radiative-03/screening.json`) | `34da3a2651d496885a5981569b64a2dd68738494e333e99dd56636a2d136c55b` |
| R5 XD1 screening (`bounded_audit/r5/cross-domain-01/screening.json`) | `fa096f5932a2871847cb67e0a94a7190516cd94f0bd7c7b57d329a34e24cdfd3` |
| R5 XD2 screening (`bounded_audit/r5/cross-domain-02/screening.json`) | `02456b78ee5852a306652901085e31a2387045faaf30f0b3566f2a6bac22c80f` |

## Non-claims

- 136/136 pair coverage means every pair has a named statement-level screening record, not that every pair has a certified relation.
- An unresolved, notEstablished or outOfScope query is not a failure and is not a refutation.
- The 55 bounded-probe certificates are package-local evidence accepted under the probe policy; they are not additions to the frozen delivered PhotoLean tree.
- The three XD1 candidate declarations are unresolved candidate evidence, not certificates.
- The legacy registry and its 151 records remain historical inputs; the dispositions are additive interpretations and do not edit them.
- The bounded protocol does not exhaust all propositions of the seventeen theories or all relations outside the frozen statement inventory.
- This snapshot is accepted-R8: two independent K3.1 Pro reviews passed and the lead recorded the uniform registry/disposition acceptance flip. Acceptance does not turn unresolved, notEstablished or outOfScope queries into certified ones.

Independent validation is recorded by the fail-closed validator and its report; the acceptance state was set only after two independent K3.1 Pro reviews passed and the lead recorded the acceptance flip. This document is the accepted snapshot's documentation, not additional evidence.
