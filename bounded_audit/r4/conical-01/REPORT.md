# R4 Package CI — conical intersection (`WP-conical-intersection-01`)

Status: **submitted-R4-pending-review**. This report does not self-accept the package;
independent K3 review is required before any acceptance flip.

- Round: R4
- Work package: `WP-conical-intersection-01` (the R4 plan, Package CI)
- Snapshot: `snap-bounded-audit-2026-11-04` (the R1 frozen snapshot id, reused exactly as the
  accepted R3 package reused it; the pinned content hashes are the authority)
- Write directory: `photolean/bounded_audit/r4/conical-01/` only
- Assigned pairs: exactly the sixteen pairs of R1 `WP-conical-intersection-01` (the seventeenth
  node `RACI` against the other sixteen theories)

## 1. Scope and result

| item | count |
|---|---:|
| assigned pairs | 16 |
| screened pairs | 16 |
| named statement-level queries | 16 |
| `certified` | 8 |
| `refuted` | 0 |
| `unresolved` | 6 |
| `notEstablished` | 1 |
| `outOfScope` | 1 |
| `observationalEquivalence` rows | 8 |
| `definitionalIdentity` rows | 1 |
| `implication` rows | 4 |
| `equivalence` rows | 2 |
| `conditionalComposition` rows | 1 |
| legacy certificates reused | 0 |
| new probe certificates | 8 |
| search-log entries | 8 |

Every pair has exactly one named statement-level query. No pair-level anchor is used as chemical
screening. No pair was forced into a relation: the six `unresolved` rows record a remaining
candidate bridge, the `notEstablished` row records a scoped search over the named statement sets,
and the `outOfScope` row records a statement-level jurisdiction boundary. No failed proof is
recorded as `refuted`; this package contains no `refuted` row.

## 2. Pair / query / outcome table

| pair | query | status | expected kind | evidence |
|---|---|---|---|---|
| `P-Marcus-RACI` | `Q-CI-MR-01` | certified | observationalEquivalence | probe `marcusRateBridge` |
| `P-Hammond-RACI` | `Q-CI-HM-01` | unresolved | implication | `SL-CI-HM-01` |
| `P-BEP-RACI` | `Q-CI-BP-01` | unresolved | observationalEquivalence | `SL-CI-BP-01` |
| `P-Kasha-RACI` | `Q-CI-KS-01` | certified | definitionalIdentity | probe `kashaRadiativeBranchPin` |
| `P-Sabatier-RACI` | `Q-CI-SA-01` | unresolved | implication | `SL-CI-SA-01` |
| `P-Goldschmidt-RACI` | `Q-CI-GS-01` | outOfScope | implication | `SL-CI-GS-01` |
| `P-SymmetryFactor-RACI` | `Q-CI-SF-01` | unresolved | equivalence | `SL-CI-SF-01` |
| `P-KashaVavilov-RACI` | `Q-CI-KV-01` | notEstablished | implication | `SL-CI-KV-01` |
| `P-SternVolmer-RACI` | `Q-CI-SV-01` | certified | observationalEquivalence | probe `svQuenchDilutionBridge` |
| `P-QuantumYield-RACI` | `Q-CI-QY-01` | certified | observationalEquivalence | probe `qyTwoChannelBridge` |
| `P-FluorPhos-RACI` | `Q-CI-FP-01` | certified | observationalEquivalence | probe `fluorPhosS1Bridge` |
| `P-EnergyGapLaw-RACI` | `Q-CI-EG-01` | certified | observationalEquivalence | probe `eglRateBridge` |
| `P-StokesShift-RACI` | `Q-CI-SS-01` | unresolved | equivalence | `SL-CI-SS-01` |
| `P-ICvsISC-RACI` | `Q-CI-IC-01` | certified | observationalEquivalence | probe `icRateBridge` |
| `P-Forster-RACI` | `Q-CI-FO-01` | unresolved | conditionalComposition | `SL-CI-FO-01` |
| `P-Einstein-RACI` | `Q-CI-EB-01` | certified | observationalEquivalence | probe `einsteinYieldBridge` |

No assigned pair is missing, no pair outside the sixteen is touched, and the sixteen are disjoint
from the accepted R2 (10) and R3 (11) pairs.

## 3. New Lean evidence

All eight certified rows are backed by **new typed Lean certificates** in
`bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` (namespace
`PhotoLean.RelationAudit.BoundedAudit.CI`), stated in the audit semantic core
`PhotoLean.RelationAudit.Defs` (`Certificate`, `DefinitionalPin`, `ObservationalSetup`,
`Channel`, `DefEq`, `Premise`). The probe imports the delivered theory modules and changes no
delivered statement. It contains no `sorry`, no `admit`, and no custom `axiom`/`constant`.

| probe declaration | kind | underlying delivered statement(s) |
|---|---|---|
| `marcusRateBridge` | observationalEquivalence | `Marcus.rate` (`Marcus/Basic.lean:55`), `Marcus.barrier` (`Marcus/Basic.lean:50`) |
| `kashaRadiativeBranchPin` | definitionalIdentity | `Kasha.radBranch` (`Kasha/Basic.lean:79`), `Kasha.decay` (`Kasha/Basic.lean:76`) |
| `qyTwoChannelBridge` | observationalEquivalence | `QuantumYield.yieldOf` (`QuantumYield/Basic.lean:44`), `QuantumYield.totalRate` (`QuantumYield/Basic.lean:40`) |
| `fluorPhosS1Bridge` | observationalEquivalence | `FluorPhos.phiF` (`FluorPhos/Basic.lean:51`), `FluorPhos.s1Decay` (`FluorPhos/Basic.lean:48`) |
| `svQuenchDilutionBridge` | observationalEquivalence | `SternVolmer.svRatioDyn` (`SternVolmer/Basic.lean:51`), `SternVolmer.dynDecay` (`SternVolmer/Basic.lean:47`), `RACI.quantumYield` (`RACI/Jablonski.lean:17`) |
| `eglRateBridge` | observationalEquivalence | `EnergyGapLaw.nrRate` (`EnergyGapLaw/Basic.lean:74`), `EnergyGapLaw.nrBarrier` (`EnergyGapLaw/Basic.lean:62`) |
| `icRateBridge` | observationalEquivalence | `ICvsISC.icRate` (`ICvsISC/Basic.lean:72`), `ICvsISC.fcBarrier` (`ICvsISC/Basic.lean:63`) |
| `einsteinYieldBridge` | observationalEquivalence | `Einstein.yield_radiative` (`Einstein/Criterion.lean:152`) |

Each certificate has a `_kind` theorem pin, e.g.

```lean
theorem marcusRateBridge_kind :
    certificateKind marcusRateBridge = RelationKind.observationalEquivalence := rfl
```

Chemical reading of the eight rows:

1. **`P-Marcus-RACI`** — the RACI CI channel `A·exp(-β·B)` at `β = 1/(k_B T)` and
   `B = Marcus.barrier lam x = (lam-x)^2/(4 lam)` is the Marcus rate law of the same step. The
   certificate checks the rate-constant channel at every driving force. It is a rate-law
   identification only; it does not identify the Marcus solvent coordinate with the torsion angle,
   and the legacy §17 look-alike row on the different *crossing objects* stays true.
2. **`P-Kasha-RACI`** — the RACI yield `kr/(kr+knr)` at `kr = rad n`, `knr = ic n` is the Kasha
   radiative branching probability `rad n/(rad n + ic n)`. Both definitions unfold to the same
   term, so the row is a `DefEq.refl` definitional identity: the RACI emission yield *is* the
   Kasha radiative branch of the emitting level.
3. **`P-QuantumYield-RACI`** — the RACI yield is the channel-0 yield of the general `n`-channel
   `QuantumYield` calculus on `![kr, knr]`, i.e. the `n = 2` instance of `k i / Σk`. The legacy
   §17 `raci_qy_eq_yieldOf_two_channel` states the same identity; this row re-checks it as a typed
   R4 certificate with a declared quantum-yield channel.
4. **`P-FluorPhos-RACI`** — aggregating the two FluorPhos S₁ nonradiative channels
   (`knr = kISC + kIC`) turns the RACI two-channel yield into the FluorPhos S₁ fluorescence yield.
   The query does *not* claim that the RACI CI/IC channel and the FluorPhos ISC channel are the
   same mechanism; it claims the yield of the summed three-channel decay is the RACI yield at the
   aggregated `knr`, which is the chemical content of the RACI single-sink idealisation.
5. **`P-SternVolmer-RACI`** — an external collisional channel `kq·[Q]` added to the RACI
   nonradiative rate is diluted by exactly the Stern–Volmer intensity ratio
   `(k0 + kq·[Q])/k0`: `Φ(kr, knr + kq·[Q]) = Φ(kr, knr) / SVratio`. The two mechanisms run in
   opposite directions (SV adds an escape channel, RACI removes one), so the row composes them
   instead of identifying them. The premises `0 < kr + knr` and `0 ≤ kq` are load-bearing: they
   are consumed by the division clearing, and the channel domain is `q ≥ 0`.
6. **`P-EnergyGapLaw-RACI`** — the RACI barrier channel at the gap-law crossing barrier
   `nrBarrier lam x` is the EnergyGapLaw nonradiative rate `nrRate`. This is the two-sided rate
   identity; the legacy §17 `log_barrierRate_eq` row is the one-sided affine log shape only.
7. **`P-ICvsISC-RACI`** — the RACI barrier channel at the ICvsISC Franck–Condon barrier
   `fcBarrier lamI xI` is the internal-conversion rate `icRate`, i.e. the RACI CI channel is the
   ICvsISC IC rate at the same barrier. The ISC channel stays outside the comparison because RACI
   has no spin observable.
8. **`P-Einstein-RACI`** — the RACI yield at `kr = A` is the delivered Einstein radiative-yield
   row `A·(1/(A+kNR))`. This is exactly the legacy "radiative conversions enter RACI only as
   `kr`" premise-level entry made statement-level.

**No legacy certificate was reused.** The legacy registry contains only pair-level
`notEstablished` anchors for all sixteen CI pairs (`rec-notestablished-P-...-RACI`); those anchors
are coverage history and cannot serve as named-query evidence. The five delivered §17 machine rows
(`raci_qy_eq_yieldOf_two_channel`, `qy_two_channel_strictAnti_of_nr_lt`, `log_barrierRate_eq`,
`icvsisc_barrier_zero_at_crossing`, `kernel_surfaces_cross_at_tsCoord`) are recorded as
`legacyDisposition` on the relevant rows; none is cited as a certificate.

## 4. Non-certified evidence

The six `unresolved` rows, the `notEstablished` row and the `outOfScope` row each link to exactly
one entry in `search-log.json`. Each entry records the searched inventory statements, searched
kinds, contexts considered, dependencies consulted (with real file locators and findings), actual
commands and results, attempted strategies, candidate evidence, the exact remaining gap or
jurisdiction boundary, recompute commands, and a rationale. All eight entries back-reference their
query and match its status.

- `unresolved`:
  - `Q-CI-HM-01` (Hammond) — no map between the torsion angle `theta` and the two-parabola
    coordinate `q`, and no statement relating `accessGap` to `tsCoord` or to the Hammond barrier.
  - `Q-CI-BP-01` (BEP) — the exponential substitution is immediate through the delivered
    `rate_eq_exp_neg_eact`, but nothing identifies the reactive BEP activation energy with the CI
    accessibility gap; the shared exponential form alone is the "algebraic shape" the R1 boundary
    forbids admitting as a relation. The legacy register records "no shared scalar".
  - `Q-CI-SA-01` (Sabatier) — the catalytic volcano activity and the RACI nonradiative channel
    share only `exp(-barrier/k_B T)`; no adsorption-energy/CI-barrier identification exists.
  - `Q-CI-SF-01` (SymmetryFactor) — the R3 Marcus/SymmetryFactor tie-back routes through the
    kernel barrier, and RACI has no kernel entry point (its conical set is a matrix degeneracy),
    so the crossing-coordinate equality is unbridged.
  - `Q-CI-SS-01` (StokesShift) — the two gaps share a linear shape and a crossing, but no map
    between the displacement coordinate and the torsion angle, and no identification of the
    emission-energy offset with a RACI parameter.
  - `Q-CI-FO-01` (Forster) — the yield composition `Φ(kr, knr + kT) = (1-E)·Φ(kr, knr)` needs the
    donor-lifetime bridge `tauD = 1/(kr+knr)` and the transfer-rate bridge
    `kT = fretRate tauD r6 R`; neither is delivered, so the natural kind
    (`conditionalComposition`) stays a candidate.
- `notEstablished`: `Q-CI-KV-01` (KashaVavilov). The scoped search over the 29 KashaVavilov
  statements and the 71 RACI statements found no statement of the requested kind: the
  KashaVavilov authority has no barrier/conical/torsion statement, and its only yield row is
  Kasha's yield algebra already screened as `Q-CI-KS-01` (reusing it would double-count one
  relation under two pair labels). This is a scoped negative registration, not logical absence.
- `outOfScope`: `Q-CI-GS-01` (Goldschmidt). The jurisdiction reason is statement-level: every
  Goldschmidt declaration is a tolerance-factor/substitution predicate over `(rA, rB, rO)`, and
  every RACI declaration is a two-state Hamiltonian/torsion/rate/yield statement; no statement in
  either authority mentions an object of the other. Recorded as jurisdiction, not as a negative
  existence claim.

## 5. Validation and gates (real outputs)

All commands are run from
`.`.
The full transcript is `evidence/gates.log`.

| gate | command | result |
|---|---|---|
| package validator | `python3 bounded_audit/r4/conical-01/validate.py` | `RESULT: PASS`, 0 failed checks |
| R1 boundary | `python3 audit_boundary/validate_boundary.py` | `RESULT: PASS`, 136 unique pairs |
| R2 package | `python3 bounded_audit/validate_screening.py` | `RESULT: PASS` |
| R3 package | `python3 bounded_audit/validate_r3.py` | `RESULT: PASS` |
| probe compile | `proofs/scripts/lake env lean bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | exit 0 |
| probe axiom audit | `#print axioms` in the probe, parsed from `probes/compile.log` | 8/8 blocks, `[propext, Classical.choice, Quot.sound]` only |
| strict build/scan | `proofs/scripts/check.sh --strict` | `build: OK`, scan `clean`, `verdict: PASS` |
| probe discipline scan | `grep -nE 'sorry|admit|^(private |protected )?(axiom|constant)'` | 0 hits |
| legacy registry | `sha256sum relation_audit/registry.json` | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| frozen Lean tree | `find PhotoLean -name '*.lean' \| wc -l` | 102 |

The package validator re-derives its facts from the frozen R1 inventory, the pair queue, the
cluster plan, the registry, the accepted R2/R3 packages, the package search log, the probe and the
compile log. It checks exact pair coverage, no overlap with the accepted pairs, unique query ids,
endpoint inventory/signature/source-hash resolution **and** the declared source line, the required
semantic fields, the five-status/seven-kind rules, per-status evidence rules, search-log links and
back-references, snapshot hashes, probe hash/declaration/kind-check/axiom-log consistency, counts,
and the coverage fragment. It deliberately **does not pin** `bounded_audit/coverage.json`: it reads
the accepted R2/R3 pair set from the accepted packages and only requires the ledger's accepted
entries to still agree with them, so the later integration append cannot break this validator.

### Mutation tests (`evidence/mutation-tests.log`)

Eleven fail-closed mutations were applied to copies of the artifacts in `/tmp` and validated with
`--screening/--search-log/--fragment` overrides:

| mutation | exit | first failing check |
|---|---:|---|
| M0 unmutated copies | 0 | (pass) |
| M1 drop one assigned pair | 1 | `pairs.coverage` |
| M2 duplicate a query id | 1 | `queries.duplicate` |
| M3 add an accepted R2 pair | 1 | `pairs.coverage`, `pairs.acceptedOverlap` |
| M4 forge a certificate | 1 | `evidence.probeHash`, `evidence.probeDeclMissing`, `probe.declarationCoverage` |
| M5 tamper an endpoint signature hash | 1 | `endpoint.signatureSha256` |
| M6 mislabel a certificate kind | 1 | `evidence.kindMatch` |
| M7 strip an `outOfScope` translation reason | 1 | `translation.reason` |
| M8 swap a certificate for another probe declaration | 1 | `probe.declarationCoverage` |
| M9 delete a search-log entry | 1 | `search.missing` |
| M10 pin the mutable cumulative ledger | 1 | `snapshot.coveragePinned` |
| M11 drift the coverage fragment | 1 | `fragment.counts.delta` |

## 6. Coverage fragment and cumulative state

`coverage-fragment.json` lists the sixteen CI pairs, their per-pair query counts and statuses, and
the package hash. It states `packageState: submitted-R4-pending-review` and
`overlapWithAccepted.intersection: []` (disjoint from the accepted 21 pairs). It is a fragment, not
the cumulative ledger: the integration agent composes it with the accepted 21 pairs into
`bounded_audit/coverage.json` (67/136 screened, 69 remaining). This package does not write, hash-pin
or otherwise modify that ledger.

## 7. Hashes

| artifact | SHA-256 |
|---|---|
| `bounded_audit/r4/conical-01/screening.json` | `f368b9b1f1ded5800419a5283b541363e83f37c4b8ef54aa641890cb54615487` |
| `bounded_audit/r4/conical-01/search-log.json` | `2b349272ad948309909bc8022f488147730104e02b21fa792b9aaa23f29d6b53` |
| `bounded_audit/r4/conical-01/coverage-fragment.json` | `0efa855f60b26452a4daf0c0e6ed48cc31f9f1c826a80c0cab5a17e1605d379b` |
| `bounded_audit/r4/conical-01/validate.py` | `5a258939048a3d8890449712b7c084e003224ecb8dce8ff90920faee8a5876cf` |
| `bounded_audit/r4/conical-01/probes/R4-CI-probe.lean` | `33cf7fe66d3c3cee3431f9ace125259bca3c36ef798d9f5324154b817ce80572` |
| `bounded_audit/r4/conical-01/probes/compile.log` | `f08f7d916488e4089daa105ceae2a33cc3235caace00597226509cb45cc840ea` |
| `bounded_audit/r4/conical-01/probes/scan.log` | `3e5b1aed058e7e3b89fd64caaae9bcf5c72c31a0c1a7df6551b90281564309f7` |
| `bounded_audit/r4/conical-01/evidence/gates.log` | `8f40d33aa0e649364b31f6f19e87797004e412426c8c2a81c9566318a9e268c4` |
| `bounded_audit/r4/conical-01/evidence/mutation-tests.log` | `35e5bbb3bcb7ce891c7d75485459b43daa8744690a757eef187084058ec66c7d` |
| `audit_boundary/statement-inventory.json` (pinned) | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| `audit_boundary/pair-queue.json` (pinned) | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| `audit_boundary/cluster-plan.json` (pinned) | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| `audit_boundary/BOUNDARY.md` (pinned) | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| `relation_audit/registry.json` (pinned) | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |

## 8. Deviations

1. **Snapshot id.** The package reuses the R1 global snapshot id
   (`snap-bounded-audit-2026-11-04`), as the accepted R3 package does, instead of minting an
   R4-specific id. The content hashes above are the authority; no artifact content differs.
2. **BEP left `unresolved`.** A rate-form identity for `P-BEP-RACI` is algebraically immediate
   through the delivered BEP bridge `rate_eq_exp_neg_eact`, and the package deliberately does not
   certify it. The query is named and the candidate is recorded, but the chemical identification
   of a reactive activation energy with a CI accessibility gap has no delivered support; admitting
   it would assert a relation from algebraic shape alone, which §5.3 of the boundary forbids. If
   the review wants that identity certified, the missing item is a statement-level identification
   of the two barriers, not a proof.
3. **`KashaVavilov` is `notEstablished`, not `outOfScope`.** KashaVavilov does contain rate and
   yield statements (Kasha's ladder algebra), so the pair is not outside the jurisdiction; the
   scoped search is what fails to find a CI/barrier/spectral bridge. `outOfScope` is reserved for
   Goldschmidt, where no shared observable exists at all.
4. **Probe outside the frozen source manifest.** Per the R4 plan, the probe is package-local
   (`bounded_audit/r4/conical-01/probes/`) and is compiled with
   `proofs/scripts/lake env lean`; the frozen 102-file `PhotoLean/**` manifest is unchanged. The
   per-declaration axiom audit is the probe's own `#print axioms` block (the accepted R3 pattern),
   because a package-local probe is not a Lake module and cannot be imported by `axioms.sh`.
5. **No builder kept in the package.** The JSON artifacts are content-addressed and the validator
   re-derives every fact from the frozen sources; the throw-away generator used at build time is
   not delivered. The JSON content is authoritative.

## 9. Blockers

None. The package is complete for its sixteen assigned pairs and every required gate passes. The
cumulative ledger and `loop/产出.md` are intentionally untouched: they belong to the integration
agent, and this package must stay `submitted-R4-pending-review` until independent K3 review.

## 10. Reproduction

```bash
cd photolean
python3 bounded_audit/r4/conical-01/validate.py
python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py
python3 bounded_audit/validate_r3.py
proofs/scripts/lake env lean bounded_audit/r4/conical-01/probes/R4-CI-probe.lean
proofs/scripts/check.sh --strict
sha256sum relation_audit/registry.json
find PhotoLean -name '*.lean' | wc -l
```

Expected: four `RESULT: PASS` lines, probe exit 0 with eight
`[propext, Classical.choice, Quot.sound]` blocks, `verdict: PASS`, the pinned registry hash, and
102 Lean files.
