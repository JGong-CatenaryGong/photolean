# R4 Package E2 — excited-state kinetics, second half (`WP-excited-state-kinetics-02`)

Status: **submitted-R4-pending-review**. This report does not self-accept the package; independent
K3 review is required before any acceptance flip.

- Round: R4
- Work package: `WP-excited-state-kinetics-02` (the R4 plan, Package E2)
- Snapshot: `snap-bounded-audit-2026-11-04-r4e2`
- Write directory: `photolean/bounded_audit/r4/excited-02/` only
- Assigned pairs: exactly the fourteen pairs of R1 `WP-excited-state-kinetics-02`

## 1. Scope and result

| item | count |
|---|---:|
| assigned pairs | 14 |
| screened pairs | 14 |
| named statement-level queries | 14 |
| `certified` | 5 |
| `refuted` | 0 |
| `unresolved` | 4 |
| `notEstablished` | 0 |
| `outOfScope` | 5 |
| `definitionalIdentity` rows | 2 |
| `observationalEquivalence` rows | 3 |
| `implication` rows | 9 |
| legacy certificates reused | 0 |
| new probe certificates | 5 |
| search-log entries | 9 |

Every pair has exactly one named statement-level query. No pair-level anchor is used as chemical
screening. No pair was forced into a relation: the five `outOfScope` rows record jurisdiction and
the four `unresolved` rows record a remaining candidate bridge. A failed proof is not recorded as
`refuted`; no `refuted` row exists in this package.

## 2. Pair / query / outcome table

| pair | query | status | expected kind | evidence |
|---|---|---|---|---|
| `P-BEP-StokesShift` | `Q-E2-BS-01` | certified | observationalEquivalence | probe `bepStokesBridge` |
| `P-BEP-ICvsISC` | `Q-E2-BI-01` | certified | definitionalIdentity | probe `bepICBridge` |
| `P-BEP-Forster` | `Q-E2-BF-01` | outOfScope | implication | `SL-E2-BF-01` |
| `P-BEP-Einstein` | `Q-E2-BE-01` | outOfScope | implication | `SL-E2-BE-01` |
| `P-Kasha-SymmetryFactor` | `Q-E2-KS-01` | unresolved | implication | `SL-E2-KS-01` |
| `P-SymmetryFactor-KashaVavilov` | `Q-E2-SK-01` | outOfScope | implication | `SL-E2-SK-01` |
| `P-SymmetryFactor-SternVolmer` | `Q-E2-SV-01` | unresolved | implication | `SL-E2-SV-01` |
| `P-SymmetryFactor-QuantumYield` | `Q-E2-SQ-01` | unresolved | implication | `SL-E2-SQ-01` |
| `P-SymmetryFactor-FluorPhos` | `Q-E2-SF-01` | unresolved | implication | `SL-E2-SF-01` |
| `P-SymmetryFactor-EnergyGapLaw` | `Q-E2-SE-01` | certified | observationalEquivalence | probe `scEgBridge` |
| `P-SymmetryFactor-StokesShift` | `Q-E2-SS-01` | certified | definitionalIdentity | probe `scStokesBridge` |
| `P-SymmetryFactor-ICvsISC` | `Q-E2-SI-01` | certified | observationalEquivalence | probe `scICBridge` |
| `P-SymmetryFactor-Forster` | `Q-E2-SFo-01` | outOfScope | implication | `SL-E2-SFo-01` |
| `P-SymmetryFactor-Einstein` | `Q-E2-SEIn-01` | outOfScope | implication | `SL-E2-SEIn-01` |

## 3. New Lean evidence

All five certified rows are backed by **new typed Lean certificates** in
`bounded_audit/r4/excited-02/probes/E2-probe.lean` (namespace
`PhotoLean.RelationAudit.BoundedAudit.E2`), built with the audit semantic core
`PhotoLean.RelationAudit.Defs` (`Certificate`, `DefinitionalPin`, `ObservationalSetup`,
`Channel`, `DefEq`). The probe imports the delivered theory modules and changes no delivered
statement. It contains no `sorry`, no `admit`, and no custom `axiom`/`constant`.

| probe declaration | kind | underlying delivered theorem(s) |
|---|---|---|
| `bepStokesBridge` | observationalEquivalence | `BEP.eact_at_zero` (`BEP/Basic.lean:137`), `StokesShift.stokesShift_eq_two_lam` (`StokesShift/Criterion.lean:60`) |
| `bepICBridge` | definitionalIdentity | `Relations.bep_eact_eq_marcus_barrier` (`Relations.lean:245`), `Relations.icvscic_barrier_eq_kernel` (`Relations.lean:693`) |
| `scStokesBridge` | definitionalIdentity | `Relations.ss_s0Surface_eq_kernel` (`Relations.lean:683`), `Relations.ss_s1Surface_eq_kernel` (`Relations.lean:688`) |
| `scEgBridge` | observationalEquivalence | `Relations.eg_barrier_eq_kernel` (`Relations.lean:669`), `SymmetryFactor.betaHalf_holds_in_kernel` (`SymmetryFactor/Sharp.lean:128`) |
| `scICBridge` | observationalEquivalence | `Relations.icvscic_barrier_eq_kernel` (`Relations.lean:693`), `SymmetryFactor.betaHalf_holds_in_kernel` (`SymmetryFactor/Sharp.lean:128`) |

Each certificate has a `_kind` theorem pin:

```lean
theorem bepStokesBridge_kind : certificateKind bepStokesBridge = RelationKind.observationalEquivalence := rfl
theorem bepICBridge_kind : certificateKind bepICBridge = RelationKind.definitionalIdentity := rfl
theorem scStokesBridge_kind : certificateKind scStokesBridge = RelationKind.definitionalIdentity := rfl
theorem scEgBridge_kind : certificateKind scEgBridge = RelationKind.observationalEquivalence := rfl
theorem scICBridge_kind : certificateKind scICBridge = RelationKind.observationalEquivalence := rfl
```

Chemical reading of the five rows:

1. **`P-BEP-StokesShift`** — the BEP thermoneutral barrier `eact lam 0 = lam/4` is one eighth of
   the Stokes shift `2*lam` computed from the same reorganization energy; the equality is stated
   for every `lam` (including the totalized `lam = 0` corner), so no positivity premise is
   load-bearing.
2. **`P-BEP-ICvsISC`** — the ICvsISC Franck–Condon barrier `fcBarrier` is the BEP activation
   barrier `eact` of the same equal-curvature crossing; both theories carry a copy of the kernel
   barrier, and the probe performs the fresh `rfl` check of the two theory-owned terms.
3. **`P-SymmetryFactor-StokesShift`** — the Stokes ground/excited surfaces are the SymmetryFactor
   reactant/product surfaces at equal curvature (`kr = kp = lam`, `dG = e00`); the probe pins both
   surface pairs in one `DefEq`-based definitional identity.
4. **`P-SymmetryFactor-EnergyGapLaw`** — at thermoneutral equal curvature the EGL nonradiative
   barrier is the SymmetryFactor reactant-surface height at the `beta = 1/2` crossing coordinate;
   the barrier-height channel is certified under `0 < lam`.
5. **`P-SymmetryFactor-ICvsISC`** — at thermoneutral equal curvature the IC channel barrier is the
   same SymmetryFactor crossing height; certified under `0 < lam` as a barrier-height
   observational equivalence.

**No legacy certificate was reused.** The legacy registry contains only pair-level
`notEstablished` anchors for all fourteen E2 pairs (`rec-notestablished-P-...`), not named
proposition-level queries or certificates. Those anchors are recorded as coverage history and
are not cited as evidence.

## 4. Non-certified evidence

The four `unresolved` rows and the five `outOfScope` rows each link to exactly one entry in
`search-log.json`. Each entry records the searched inventory statements, searched kinds, contexts
considered, dependencies consulted (with real file locators), actual commands and results,
attempted strategies, candidate evidence, the exact remaining gap or jurisdiction boundary, and
recompute commands. All nine entries back-reference their query and match its status.

- `unresolved`: `Q-E2-KS-01`, `Q-E2-SV-01`, `Q-E2-SQ-01`, `Q-E2-SF-01`. These are candidate
  rate-versus-structure bridges (ladder IC rate, SV quenching rate, QY channel share, FluorPhos
  ISC/IC channels) whose delivered rate law or total translation is missing.
- `outOfScope`: `Q-E2-BF-01`, `Q-E2-BE-01`, `Q-E2-SK-01`, `Q-E2-SFo-01`, `Q-E2-SEIn-01`. These
  pairs have no shared context or declared translation between the relevant statement contexts
  (activated barrier vs. R^-6 transfer rate, radiative coefficients, normalized spectra, or dipole
  orientation). The records explicitly say this is jurisdiction, not logical absence.

## 5. Gates run (real outputs)

### 5.1 Package validator

```text
$ python3 bounded_audit/r4/excited-02/validate.py
R4 E2 bounded screening validation
  root: .
  checks failed: 0
RESULT: PASS (all E2 bounded-screening checks passed)
[exit=0]
```

The validator checks, fail-closed: exact fourteen-pair coverage; no overlap with the accepted
R2/R3 pairs (and with the hardcoded E1/CI lists); unique query IDs; R1 inventory endpoint,
signature-hash and source-hash resolution; required semantic fields; five-status/seven-kind rules;
evidence/search-log links; snapshot hashes; probe hash and declaration/kind/axiom audit; coverage
fragment reconciliation; and forbidden probe tokens. It deliberately **does not pin
`bounded_audit/coverage.json`**.

### 5.2 R1/R2/R3 validators

```text
$ python3 audit_boundary/validate_boundary.py
RESULT: PASS (all boundary checks passed)              [exit=0]
$ python3 bounded_audit/validate_screening.py
RESULT: PASS (all bounded-screening checks passed)     [exit=0]
$ python3 bounded_audit/validate_r3.py
RESULT: PASS (all R3 bounded-screening checks passed)  [exit=0]
```

The full outputs are in `evidence/gates.log`.

### 5.3 Probe compilation and axiom audit

```text
$ proofs/scripts/lake env lean bounded_audit/r4/excited-02/probes/E2-probe.lean
'...bepStokesBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'...bepICBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'...scStokesBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'...scEgBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'...scICBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit=0]
```

`probes/compile.log` is the real compiler output; `probes/axioms.log` records the five
per-declaration axiom print-outs; `probes/scan.log` records a clean forbidden-token scan.

### 5.4 Strict build / scan

```text
$ proofs/scripts/check.sh --strict
Build completed successfully.
==> sorry / custom axiom scan (PhotoLean/**/*.lean)
clean
==> summary
build: OK
allowed axioms: propext Classical.choice Quot.sound
verdict: PASS
[exit=0]
```

Full output: `evidence/strict-build-scan.log`. No concurrent Lake build lock was observed; the
build completed on the first attempt.

## 6. Fail-closed mutation tests (in `/tmp`)

Ten mutations were applied to in-memory/temporary copies (never to the package files) and the
validator was invoked on the mutated artifact. All ten exited 1 with the expected diagnostic code.

```text
duplicate-pair         exit=1 target=pairs.duplicate              present=True
delete-query           exit=1 target=pair.noQuery                 present=True
bad-endpoint-hash      exit=1 target=endpoint.sourceArtifactSha256 present=True
bad-status             exit=1 target=outcome.status               present=True
kind-refuted           exit=1 target=query.kindRefuted            present=True
bad-probe-hash         exit=1 target=evidence.probeHash           present=True
delete-pair            exit=1 target=pairs.count                  present=True
bad-fragment-count     exit=1 target=fragment.pairCount           present=True
bad-search-status      exit=1 target=search.status                present=True
missing-rationale      exit=1 target=query.chemicalRationale      present=True
SCREENING_MUTATIONS PASS
```

Full output: `evidence/mutation-tests.log`.

## 7. Hashes (SHA-256)

Package artifacts:

```text
5ceee13be0629cd93b912d68e0a44751e1906c7acfd823cc9297af0a61c94af6  bounded_audit/r4/excited-02/screening.json
cf3928dd98dbe0d5c9da6ba274e8bbc9234b1fa7b08b5248c30d165b66721922  bounded_audit/r4/excited-02/search-log.json
810ad34065ad0ddf7774b2810c401a94cfa6b5eb514a890026fdb4a6245e646d  bounded_audit/r4/excited-02/coverage-fragment.json
33c6e63342c762fd03d0aed68d17edf4c10b60a186b4438705ae5d2e1eb593d3  bounded_audit/r4/excited-02/validate.py
0e6e3cf50cb9d21e9f88db11cedd12ccc584b8c5b4c46a943665616a013a16a8  bounded_audit/r4/excited-02/build_screening.py
69a7889f458558c78701883774c22fe4868fdca48626c3e846d1427457524c11  bounded_audit/r4/excited-02/probes/E2-probe.lean
484f181d88db2d646f3763520bb72fc67f8fd320d27f2fdd4cec0112bde2928e  bounded_audit/r4/excited-02/probes/compile.log
7036e28e4f603fb0204dce47604e019a307f850c63a23c353062a3a3b29e49be  bounded_audit/r4/excited-02/probes/axioms.log
d26c446aeef68e17763f73ba5462d04dda8cb91b96f0f99fa2e64808499c783f  bounded_audit/r4/excited-02/probes/scan.log
```

Frozen / accepted references read by this package:

```text
3debf588b081b7a572487bffb78bccacd2e8c5ed327a6d6bfb655663fe1fa947  audit_boundary/statement-inventory.json
8357f61cfb54e056b72fb73a5fb08d450d29adb9a0e9c7956e04ebff8cb25504  audit_boundary/pair-queue.json
ded71097c3b7c336b290483272c5f49ec7e80fd7a9a7ec0223352a2186d04a24  audit_boundary/cluster-plan.json
ad4d88a0e1d91232ee4b8969dd0a67ef53210b937b2554fec58dfa5b862a95c3  audit_boundary/BOUNDARY.md
25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0  relation_audit/registry.json
2a98dac9d75d76782a307bd6903dd6adec6dcc946f09e186c07895e3bee1b49c  bounded_audit/wp-surface-01/screening.json
452d213c5a142b4910f7adcf1e4efd433d02be83f538510992a2dfe758ed262c  bounded_audit/r3/screening.json
c72fbc4cb134e57cde379f2a10011c9a27f0f7a3497af50fd6c4c404bdf2745a  ../backup/photolean-source-2026-11-04.tar.gz
```

## 8. Deviations, baseline observations, blockers

1. **No legacy certificate was reusable.** All fourteen legacy records are pair-level
   `notEstablished` absence anchors, so the five certified rows are new probe certificates. This
   is not a relabelling of an absence anchor.
2. **The legacy register records "no edge" for several newly certified pairs.** In particular
   `Relations.lean` §16 registers no-edge rows for StokesShift/EnergyGapLaw/ICvsISC vs
   SymmetryFactor, and for BEP vs Forster/Einstein. The R4 contract treats the legacy register as
   coverage history, not an audit verdict (`BOUNDARY.md` §1.3); the five new rows are fresh
   statement-level checks, not edits of the legacy register. The outOfScope rows agree with the
   legacy no-edge reason where that reason is a genuine disjointness of contexts.
3. **Two certified rows are definitional kernel-copy pins** (`Q-E2-BI-01`, `Q-E2-SS-01`). They are
   genuine `DefEq`/`rfl` checks of theory-owned terms, not wrappers: each pair needs its own
   statement-level answer and the two terms are distinct declarations in distinct theory
   namespaces. They were not created to raise a count; the two observational rows
   (`Q-E2-SE-01`, `Q-E2-SI-01`) and the thermodynamic identity (`Q-E2-BS-01`) carry independent
   content.
4. **Baseline drift observed (outside E2 write scope).** The current
   `bounded_audit/r3/screening.json` hashes to `452d213c…`, while the R3 report section 8 records
   `587b867f…`; the current `bounded_audit/coverage.json` hashes to `a584d38e…`, while the same
   section records `1c526971…`. The R3 search log, R3 probe and R3 validator still match their
   recorded hashes, and `validate_r3.py` passes on the current R3 screening. This package pins
   the **current** R3 screening hash and deliberately does not pin `coverage.json`. Reconciling
   the recorded-versus-current R3 hashes is outside E2's write scope and is left to the lead /
   integration / K3 review.
5. **No concurrent Lake build lock was encountered.** If one occurs, the prescribed response is to
   wait and retry without deleting lock files.
6. **Blockers:** none for E2. The package is complete and validated; it remains
   `submitted-R4-pending-review` until independent K3 review.

## 9. Reproduction

From `bounded-relation-audit-2026-11-04/photolean`:

```bash
python3 bounded_audit/r4/excited-02/validate.py
python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py
python3 bounded_audit/validate_r3.py
proofs/scripts/lake env lean bounded_audit/r4/excited-02/probes/E2-probe.lean
proofs/scripts/check.sh --strict
python3 bounded_audit/r4/excited-02/build_screening.py   # regenerates screening/search-log/fragment
```

The builder is deterministic given the frozen inventory, the probe and the search-log data; it
must be re-run after any package-local text change because `screening.json` pins the
`search-log.json` and probe hashes, and `coverage-fragment.json` pins the `screening.json` hash.

## 10. Non-claims

- This package is not a completeness claim about any pair.
- A `certified` row is a checked relation under its declared context, premises and snapshot; it is
  not a claim of physical universality.
- An `unresolved` row is not a negative claim and is not a refutation.
- An `outOfScope` row records jurisdiction, not logical absence.
- The fourteen-pair count is a bounded-audit coverage count; the package does not edit or claim
  the cumulative R4 ledger.
- The legacy registry and the accepted R1/R2/R3 artifacts were read only.
