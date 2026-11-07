# R5 Package RAD3 — WP-radiative-energy-transfer-03 screening report

Status: **submitted-R5-pending-review**. Round R5, package `bounded_audit/r5/radiative-03/`.
This package is a bounded submission snapshot; it does not write, hash-pin or otherwise touch the
mutable R5 cumulative ledger (`bounded_audit/coverage.json`) or any accepted R1–R4 artifact.

## 1. Scope

Exactly the thirteen pairs of the frozen R1 work package `WP-radiative-energy-transfer-03`
(`audit_boundary/cluster-plan.json`), with no pair added, dropped or rescreened:

| # | pair | theories | queries | pair outcome |
|---:|---|---|---:|---|
| 1 | `P-FluorPhos-ICvsISC` | FluorPhos / ICvsISC | 2 | certified ×2 |
| 2 | `P-FluorPhos-Forster` | FluorPhos / Forster | 1 | certified |
| 3 | `P-FluorPhos-Einstein` | FluorPhos / Einstein | 1 | certified |
| 4 | `P-EnergyGapLaw-StokesShift` | EnergyGapLaw / StokesShift | 2 | certified ×2 |
| 5 | `P-EnergyGapLaw-ICvsISC` | EnergyGapLaw / ICvsISC | 2 | certified ×2 |
| 6 | `P-EnergyGapLaw-Forster` | EnergyGapLaw / Forster | 1 | outOfScope |
| 7 | `P-EnergyGapLaw-Einstein` | EnergyGapLaw / Einstein | 1 | outOfScope |
| 8 | `P-StokesShift-ICvsISC` | StokesShift / ICvsISC | 1 | certified |
| 9 | `P-StokesShift-Forster` | StokesShift / Forster | 1 | notEstablished |
| 10 | `P-StokesShift-Einstein` | StokesShift / Einstein | 1 | outOfScope |
| 11 | `P-ICvsISC-Forster` | ICvsISC / Forster | 1 | unresolved |
| 12 | `P-ICvsISC-Einstein` | ICvsISC / Einstein | 1 | outOfScope |
| 13 | `P-Forster-Einstein` | Forster / Einstein | 1 | certified |

Totals: **13 pairs, 16 named statement-level queries**. Every pair carries at least one named
query; no pair is represented by a pair-level anchor.

## 2. Outcome counts (queries, not pairs)

| status | count |
|---|---:|
| certified | 10 |
| refuted | 0 |
| unresolved | 1 |
| notEstablished | 1 |
| outOfScope | 4 |
| **total** | **16** |

Expected evidence kinds: `observationalEquivalence` 6, `equivalence` 2,
`definitionalIdentity` 1, `conditionalComposition` 2, `implication` 5. The seven pairs with a
certified query are 1, 2, 3, 4, 5, 8, 13; the six non-certified pairs each carry a statement-level
reason and a scoped, recomputable search record.

Pair coverage is reported separately from query outcomes: seven pairs were resolved by a checked
relation, six were not. No pair was forced into a relation and no edge count is a target.

## 3. Certified evidence

All ten certificates are package-local, typed Lean terms in
`probes/RAD3-probe.lean` (SHA-256 `c693f198…95f09`), statement-first, with no unproved
placeholder and no custom axiomatic declaration. The probe compiles with

```
proofs/scripts/lake env lean bounded_audit/r5/radiative-03/probes/RAD3-probe.lean
```

exit 0; `probes/compile.log` records the ten per-declaration `#print axioms` blocks, each exactly
`[propext, Classical.choice, Quot.sound]`. The compile log is `e3f36828…6d2fa`.

| query | pair | kind | probe declaration | premises |
|---|---|---|---|---|
| `Q-RAD3-FI-01` | FluorPhos/ICvsISC | observationalEquivalence | `Rad3.fiBranchBridge` | none |
| `Q-RAD3-FI-02` | FluorPhos/ICvsISC | equivalence | `Rad3.fiElSayedBridge` | 4 |
| `Q-RAD3-FF-01` | FluorPhos/Forster | observationalEquivalence | `Rad3.ffTransferBridge` | 2 |
| `Q-RAD3-FE-01` | FluorPhos/Einstein | observationalEquivalence | `Rad3.fpEinsBridge` | none |
| `Q-RAD3-ES-01` | EnergyGapLaw/StokesShift | equivalence | `Rad3.esZeroBarrierBridge` | 1 |
| `Q-RAD3-ES-02` | EnergyGapLaw/StokesShift | observationalEquivalence | `Rad3.esBarrierEmissionBridge` | 1 |
| `Q-RAD3-EI-01` | EnergyGapLaw/ICvsISC | definitionalIdentity | `Rad3.eiRateDefinition` | none |
| `Q-RAD3-EI-02` | EnergyGapLaw/ICvsISC | conditionalComposition | `Rad3.eiCrossoverComposition` | 2 |
| `Q-RAD3-SI-01` | StokesShift/ICvsISC | observationalEquivalence | `Rad3.siSurfaceBridge` | none |
| `Q-RAD3-FoE-01` | Forster/Einstein | observationalEquivalence | `Rad3.foEinBridge` | none |

Chemical content of the ten certificates:

1. `Q-RAD3-FI-01` — with the radiative channel shut, the FluorPhos S₁ intersystem-crossing
   branch `kISC/(kISC+kIC)` is the normalized ICvsISC spin-orbit ISC channel
   `iscRate/(iscRate+icRate)` at the two theory-owned channel rates.
2. `Q-RAD3-FI-02` — the El-Sayed boundary of the cascade: at a live triplet radiative channel and
   a live S₁ decay, the FluorPhos phosphorescence yield vanishes exactly when the ICvsISC
   spin-orbit ISC channel vanishes, i.e. exactly when `HSO = 0`. This is the substantive
   cross-theory content of the legacy premise-level `kISC` identification.
3. `Q-RAD3-FF-01` — the Förster transfer efficiency `r6/(r6+R^6)` is the donor fluorescence branch
   at `kF = (1/tauD)(r6/R^6)` and `kIC = 1/tauD`. The two nonzero premises are load-bearing: at
   `tauD = 0` or `R = 0` the two sides differ.
4. `Q-RAD3-FE-01` — the two-channel FluorPhos fluorescence yield is the Einstein radiative yield
   `A*(1/(A+kNR))`; the proof consumes the delivered `Einstein.yield_radiative` row.
5. `Q-RAD3-ES-01` — the gap-law barrier vanishes exactly when the vertical emission window closes,
   at nonzero reorganization energy. The `lam != 0` premise is load-bearing (at `lam = 0` the
   totalized barrier is 0 at every gap while the emission energy is `x`).
6. `Q-RAD3-ES-02` — the quantitative bridge: the gap-law barrier equals
   `emEnergy^2/(4*lam)`, the squared optical emission gap over four times the shared
   reorganization energy.
7. `Q-RAD3-EI-01` — the ICvsISC internal-conversion rate and the EnergyGapLaw nonradiative rate
   are the same function: the two delivered barrier copies have the same body, so the pin is a
   fresh kernel `DefEq.refl`.
8. `Q-RAD3-EI-02` — a typed conditional composition of the rate identification (parent 1) with the
   delivered `ICvsISC.isc_dominates_iff` (parent 2): the IC-vs-ISC crossover read with the gap-law
   rate on the IC side. Both parents are equivalences, so the computed child form is an
   equivalence; the child premise list is exactly `[FCData, 0 < HSO]`, the bridge list is empty,
   and the alignment is `Iff.rfl` on the IC-rate predicate. The probe machine-checks the parent
   IDs, the empty bridge and the child form with `by decide` witnesses.
9. `Q-RAD3-SI-01` — the thermoneutral IC barrier is the Stokes ground surface at the
   equal-curvature crossing coordinate `q = 1/2`; both sides are `lam/4`.
10. `Q-RAD3-FoE-01` — at the Einstein radiative lifetime `tauR A = 1/A`, the Förster rate is
    `aOfB A (r6/R^6)`: the radiative coefficient times the sixth-power geometric factor. Both
    reciprocal maps are totalized, so the identity is unconditional.

Each certified screening row records the endpoint inventory metadata (declaration, kind, source
artifact, source line, version, signature hash, source-file hash), the shared context and explicit
translations, the load-bearing premise predicate and IDs, the scope and snapshot, the
falsification condition, the observation channels where applicable, the probe path/hash, the
build command and log, and the axiom footprint. The probe also contains machine-checked
`example` witnesses pinning each certificate's premise IDs (and the composition's parent IDs,
bridge IDs and form) to the screening manifest, so the validator cross-checks the JSON against the
kernel rather than against prose.

## 4. Non-certified records

Six query outcomes are not certified. Each has a full scoped search log entry in
`search-log.json` (SHA-256 `5c35aa15…a756`), with searched statements and kinds, contexts,
consulted dependencies (artifact, locator, finding), the exact commands and their results,
attempted strategies, candidate evidence, the remaining gap and recompute commands.

| query | pair | status | statement-level reason |
|---|---|---|---|
| `Q-RAD3-EF-01` | EnergyGapLaw/Forster | outOfScope | disjoint descriptor sets: gap-law `(A, lam, kB, T, x)` versus Förster `(tauD, r6, R)`; no declared translation |
| `Q-RAD3-EE-01` | EnergyGapLaw/Einstein | outOfScope | the shared symbol `A` denotes a nonradiative prefactor in one theory and a radiative coefficient in the other; no shared descriptor |
| `Q-RAD3-SF-01` | StokesShift/Forster | notEstablished | no delivered line-shape or overlap declaration; `J` stays a free parameter of `r0six` and the Stokes rows are band maxima only |
| `Q-RAD3-SE-01` | StokesShift/Einstein | outOfScope | band maxima versus a transition frequency / radiation density; identifying the integrated absorption `I` with a band maximum would be a dimensional category error |
| `Q-RAD3-IF-01` | ICvsISC/Forster | unresolved | candidate third-channel composition, but the donor-lifetime and added-channel bridges are not delivered |
| `Q-RAD3-IE-01` | ICvsISC/Einstein | outOfScope | spin-orbit channel strength over a nuclear barrier versus a radiative coefficient over a radiation density |

No failed proof is labelled `refuted`: the package declares `refuted = 0`, the probe contains no
refutation certificate, and the validator enforces both. The `outOfScope` records deny a declared
translation; they do not assert logical non-existence. The `notEstablished` record is a scoped
negative registration for the requested implication, not a claim that no physical relation exists.
The `unresolved` record names the exact missing bridges and makes no negative claim.

## 5. Legacy evidence handling

- `P-EnergyGapLaw-ICvsISC`: the legacy §15 record
  `rec-D-S15-icvscic-icRate-eq-eg-nrRate` is a certified pair row on the same two delivered
  declarations. `Q-RAD3-EI-01` re-certifies the identity statement-first in the package probe; the
  legacy certificate is not cited as evidence.
- `P-EnergyGapLaw-StokesShift`: the legacy §15 record
  `rec-D-S15-egBarrier-zero-iff-emEnergy-zero` used two endpoint aliases
  (`nrBarrier_eq_zero`, `emEnergy_eq_zero`) that are not delivered declarations. The inventory
  registers them as dangling legacy metadata. `Q-RAD3-ES-01` restates the statement-level zero-set
  content on the delivered `EnergyGapLaw.nrBarrier` and `StokesShift.emEnergy` declarations; the
  alias resolution is recorded in `screening.json#aliasResolutions` and the aliases are not cited
  as endpoints anywhere.
- The remaining eleven pairs carry legacy registered-absence or premise-level anchors. Those labels
  are census metadata, not audit verdicts; no query is certified from them.

## 6. Prior coverage and overlap

Prior accepted coverage is derived directly from the five accepted screening packages, not from
the mutable ledger:

```
bounded_audit/wp-surface-01/screening.json   10 pairs
bounded_audit/r3/screening.json              11 pairs
bounded_audit/r4/excited-01/screening.json   16 pairs
bounded_audit/r4/excited-02/screening.json   14 pairs
bounded_audit/r4/conical-01/screening.json   16 pairs
union                                        67 pairs (no duplicate)
```

The RAD3 thirteen pairs are disjoint from that union: `overlapWithAccepted.intersection = []`.
The package validator recomputes the union itself and fails if the count is not 67 or if the
package pair set overlaps it. It never opens `bounded_audit/coverage.json`; a dedicated check
(`ledger.mustNotRead`) fails if that path is ever opened.

## 7. Gates (all run serially; Lake commands are never concurrent)

| gate | command | result |
|---|---|---|
| R1 boundary | `python3 audit_boundary/validate_boundary.py` | exit 0, PASS, 136 unique pairs |
| R2 screening | `python3 bounded_audit/validate_screening.py` | exit 0, PASS |
| R3 historical content | `python3 bounded_audit/r4/validate_r3_content.py` | exit 0, PASS (7 current-ledger freshness checks excluded) |
| R4 historical snapshot | `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json` | exit 0, PASS, 67/136 screened, 69 remaining, 846 checks |
| R4 E1 package | `python3 bounded_audit/r4/excited-01/validate.py` | exit 0, PASS |
| R4 E2 package | `python3 bounded_audit/r4/excited-02/validate.py` | exit 0, PASS |
| R4 CI package | `python3 bounded_audit/r4/conical-01/validate.py` | exit 0, PASS |
| R5 RAD3 package | `python3 bounded_audit/r5/radiative-03/validate.py` | exit 0, PASS |
| strict build/scan | `proofs/scripts/check.sh --strict` | exit 0, PASS, build OK, scan clean |
| probe compile | `proofs/scripts/lake env lean bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | exit 0, 10 axiom blocks |
| probe discipline | forbidden-token scan over the probe and per-declaration axiom audit | 0 hits; all ten blocks exactly `[propext, Classical.choice, Quot.sound]` |
| registry hash | `sha256sum relation_audit/registry.json` | `25d38791…ecbf0` unchanged |
| delivered Lean tree | `find PhotoLean -name '*.lean' \| wc -l` | 102 unchanged |

Full outputs: `evidence/gates.log`, `evidence/probe-scan.log`, `evidence/legacy-registry.log`.

## 8. Mutation tests

Fifteen fail-closed mutations were applied to copies in `/tmp` and validated through the
`--screening/--search-log/--fragment` overrides; the log is `evidence/mutation-tests.log`.

| mutation | exit | first failing check |
|---|---:|---|
| M0 unmutated byte copies | 0 | (pass) |
| M1 drop one assigned pair | 1 | `pairs.coverage` |
| M2 duplicate a query id | 1 | `pair.queryIds` |
| M3 add an accepted prior pair | 1 | `pairs.coverage` |
| M4 forge a certificate declaration | 1 | `evidence.probeDeclMissing` |
| M5 tamper an endpoint signature hash | 1 | `endpoint.signatureSha256` |
| M6 mislabel a certificate kind | 1 | `evidence.kindPin` |
| M7 strip an `outOfScope` translation reason | 1 | `translation.reason` |
| M8 swap a certificate for another probe declaration | 1 | `probe.declarationCoverage` |
| M9 delete a search-log entry | 1 | `search.missing` |
| M10 pin the mutable cumulative ledger | 1 | `snapshot.coveragePinned` |
| M11 drift the coverage fragment | 1 | `fragment.counts.delta` |
| M12 rename a premise id | 1 | `evidence.premiseMatch` |
| M13 change a composition parent id | 1 | `evidence.parentWitness` |
| M14 drift a frozen snapshot hash | 1 | `snapshot.inventorySha256` |
| M15 change an El-Sayed premise id | 1 | `premise.defIds` |

## 9. Hashes

| artifact | SHA-256 |
|---|---|
| `bounded_audit/r5/radiative-03/screening.json` | `34da3a2651d496885a5981569b64a2dd68738494e333e99dd56636a2d136c55b` |
| `bounded_audit/r5/radiative-03/search-log.json` | `5c35aa15b167f156b2e3d3554ea52578b121709b9610bcf3a5f447dc75d3a756` |
| `bounded_audit/r5/radiative-03/coverage-fragment.json` | `a63d14543046f98574b35af199be70d50ea20bf9e41516daa47ad01309fa7a90` |
| `bounded_audit/r5/radiative-03/validate.py` | `5e06e28e5709125dcff8004d08c23aab7c8df3d4d361d63c234252674c594aeb` |
| `bounded_audit/r5/radiative-03/build_package.py` | `63a1040ffef9404262145a048c0de2e32dbe0c97cac2181684bde5b5486ed26d` |
| `bounded_audit/r5/radiative-03/probes/RAD3-probe.lean` | `c693f19830aeb8ce7c01f43f1c2821bc57920f98d0d03f3cdca5dbd1a3f95f09` |
| `bounded_audit/r5/radiative-03/probes/compile.log` | `e3f36828fa40025142f6505feff625947407440efb1eaa407a4ba3e3e6d6d2fa` |
| `bounded_audit/r5/radiative-03/evidence/gates.log` | `3afca026ac6374cc333c3c11890aecfc0a33c7094a848fb90b62a83962c1ed52` |
| `bounded_audit/r5/radiative-03/evidence/mutation-tests.log` | `4efc9514790d860d34320a3afd2a5c8860877ca6e1028e23f0fb5b159cf0dd2f` |
| `bounded_audit/r5/radiative-03/evidence/probe-scan.log` | `ee345016b6938278a68852c7c9bf7929e39923fd3d85f66504df2caa48324119` |
| `bounded_audit/r5/radiative-03/evidence/legacy-registry.log` | `f05d74ba20954fa70448233b5639f28b0c8e2ffecb979b70f19721bbeebd1a50` |
| `bounded_audit/r5/radiative-03/evidence/mutation_tests.py` | `ffff712ee8638d0d19360b82e32e5b54171f094cfb8050635239e8c8b2e50002` |
| `audit_boundary/statement-inventory.json` (pinned) | `3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947` |
| `audit_boundary/pair-queue.json` (pinned) | `8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504` |
| `audit_boundary/cluster-plan.json` (pinned) | `ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24` |
| `audit_boundary/BOUNDARY.md` (pinned) | `ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3` |
| `relation_audit/registry.json` (pinned) | `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0` |
| `bounded_audit/r4/coverage-accepted.json` (frozen) | `d1e44bf7bbb5e81c7b85f610d6ffc1d4d3fed0fcde5cd1ab3202fb23ca6c32fa` |

## 10. Deviations, boundaries and blockers

1. **Snapshot id.** The package reuses the R1 global snapshot id
   (`snap-bounded-audit-2026-11-04`), as the accepted R3/R4 packages do, instead of minting an
   R5-specific id. The content hashes above are the authority.
2. **Extra local artifacts.** Besides the five required deliverables, the package carries
   `build_package.py` (deterministic regeneration of the three JSON artifacts) and `evidence/`
   logs (gates, mutations, probe scan, frozen hashes). These are local evidence; they add no
   theory statement and no registry entry.
3. **Deterministic rebuild.** Re-running `build_package.py` reproduces the three JSON
   artifacts byte for byte (verified by `cmp`); no artifact is hand-edited after generation.
4. **Two queries for `P-FluorPhos-ICvsISC`, `P-EnergyGapLaw-StokesShift` and
   `P-EnergyGapLaw-ICvsISC`.** Each pair's extra query is chemically distinct (the El-Sayed
   boundary versus the branching normalization; the quantitative barrier identity versus the
   zero-set equivalence; the typed crossover composition versus the definitional rate pin). They
   are not duplicate labels on one relation.
5. **The `outOfScope` records deny translations, not physics.** `Q-RAD3-EF-01`, `Q-RAD3-EE-01`,
   `Q-RAD3-SE-01` and `Q-RAD3-IE-01` are statement-level jurisdiction records with their own
   searched statements, commands and findings; none is based on a cluster name or theory-name
   dissimilarity alone.
6. **R5 status.** The package and its fragment are `submitted-R5-pending-review`; the lead, not
   this package, flips acceptance after independent review. No accepted R1–R4 artifact, legacy
   registry, original repository, manuscript or backup was modified.
7. **No blocker.** Every assigned pair has a named query or a statement-level outOfScope record;
   the probe compiles; all applicable gates pass.

## 11. Reproduction

```
cd .
python3 bounded_audit/r5/radiative-03/build_package.py
proofs/scripts/lake env lean bounded_audit/r5/radiative-03/probes/RAD3-probe.lean
python3 bounded_audit/r5/radiative-03/validate.py
python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py
python3 bounded_audit/r4/validate_r3_content.py
python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json
proofs/scripts/check.sh --strict
```

The mutation suite is reproduced by `python3 bounded_audit/r5/radiative-03/evidence/mutation_tests.py`; the log lists the fifteen mutations and their first failing checks.
command (copies under `/tmp`, `--screening/--search-log/--fragment` overrides); the log lists the
fifteen mutations and their first failing checks.

## 12. Non-claims

- This package is not a completeness claim about any pair.
- A certified row is a checked relation under its declared context, premises and snapshot; it is
  not a claim of physical universality.
- A rate or barrier identity is not an identification of the two theories' microscopic
  coordinates, mechanisms or parameters beyond the declared translation.
- An `unresolved` row is not a negative claim and is not a refutation.
- A `notEstablished` or `outOfScope` row is a scoped registration, not logical non-existence.
- No pair was forced into a relation to increase an edge count.
- The legacy registry and the accepted R1–R4 artifacts are read-only in R5; the cumulative R5
  ledger is written by the integration agent, not by this package.
