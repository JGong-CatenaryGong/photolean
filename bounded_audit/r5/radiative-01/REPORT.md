# R5 Package RAD1 — `WP-radiative-energy-transfer-01` screening report

- **Round / package**: R5, Package RAD1, `bounded_audit/r5/radiative-01/`
- **Work package**: `WP-radiative-energy-transfer-01` (R1 cluster `radiative-energy-transfer`), exactly 16 pairs
- **Status**: `submitted-R5-pending-review` — this package claims no acceptance
- **Repair round**: R6 — corrected the `Q-RAD1-MSS-01` regime prose, the `Q-RAD1-KKV-01` kind rationale and the `mkvCmp` left StatementRef. R7 — corrected the probe §4 emission-energy comment (positive exactly in the inverted region `lam < e00`, negative in the normal region `e00 < lam`, zero at `e00 = lam`) and added a fail-closed comment pin; no theorem, proof, relation kind or outcome changed
- **Snapshot**: `snap-bounded-audit-2026-11-04-r5rad1`
- **Toolchain**: `leanprover/lean4:v4.17.0`, mathlib `v4.17.0`
- **Language**: all repository artifacts are English

## 1. Summary

| quantity | value |
|---|---|
| assigned pairs screened | **16 / 16** |
| named statement-level queries | **17** (one per pair; `P-Marcus-EnergyGapLaw` carries two chemically distinct queries) |
| certified | **11** |
| unresolved | **2** |
| outOfScope | **4** |
| refuted | **0** |
| notEstablished | **0** |
| new Lean probe certificates | **11** (all typed `Certificate`s, statement-first, no `sorry`, no custom axiom) |
| per-declaration axiom footprint | `[propext, Classical.choice, Quot.sound]` on 11/11 |
| scoped search-log entries | **6** (one for each non-certified query) |
| prior coverage derivation | **67** accepted pairs from the five accepted `screening.json` packages (R2 10 + R3 11 + R4 E1 16 + E2 14 + CI 16); the mutable R5 ledger is neither read nor pinned |

Screened is **not** the same as certified. Pair coverage is reported separately from outcome
counts below. The package does not claim that one query per pair exhausts all conceivable
relations between these theories outside the frozen bounded query protocol.

## 2. Deliverables and SHA-256

| artifact | SHA-256 |
|---|---|
| `screening.json` | `a5ad482e12223642cdc10db81d36142f9fd8266c7cbb914a8fe243084d31b837` |
| `search-log.json` | `1b711c1dbda4bbdc77e4da53025192e17b0b79011b394f859763f796d74dbf3a` |
| `coverage-fragment.json` | `38ab39d7ecef2a28b08e90724cf0eb22f5958daa8dcc9c92a1012f5669f680ad` |
| `validate.py` | `98c82e25399a57b1db13c6c64f04457e3debf824fffc319848c529984f861cfd` |
| `build_screening.py` | `bc5da8acd1971c49b4fd62031aa9763bad89d7f2110e626accfa109f2dd35854` |
| `probes/RAD1-probe.lean` | `38cc6056139db6890175441cf029bf9e5c01ad6e1b63c88e2d2f9ad5b388cfeb` |
| `probes/compile.log` | `858becc880884f1dba11cb7a28e3066a1e01c63767b762e306ef6aa7d6d6db45` |
| `evidence/gates.log` | `3557576c9e90b7c3d93bf72decc18be1251afc68768ee81e0834d8b687b5f8b5` |
| `evidence/mutation-tests.log` | `9a950fc09145be544347715ff646b98f0168b0da61ada4de5cd98f0041d7c486` |
| `evidence/mutation_tests.py` | `f225b2cd207afd9bb2fbacf4f9a3f75566110a598503b26507c59979c1ff7d39` |
| `evidence/search-commands.log` | `114cadad70b78995bcba3e9f03131268fb24033cb790d0d983ba955820b6b99c` |

Pinned input hashes (recorded in `screening.json#snapshot`): statement inventory
`3debf588…fa947`, pair queue `8357f61c…25504`, cluster plan `ded71097…04a24`, boundary
`ad4d88a0…a95c3`, legacy registry `25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0`,
accepted R2 `2a98dac9…1b49c`, accepted R3 `452d213c…d262c`, accepted R4 E1 `9a096648…1f60b`,
E2 `5ceee13b…94af6`, CI `f368b9b1…15487`.

## 3. Pair coverage and queries

| pair | query | kind | outcome | certificate |
|---|---|---|---|---|
| `P-Marcus-KashaVavilov` | `Q-RAD1-MKVV-01` | implication | certified | `mkvBridge` |
| `P-Marcus-EnergyGapLaw` | `Q-RAD1-MEG-01` | definitionalIdentity | certified | `marcusEglRateBridge` |
| `P-Marcus-EnergyGapLaw` | `Q-RAD1-MEG-02` | equivalence | certified | `marcusEglZoneBridge` |
| `P-Marcus-StokesShift` | `Q-RAD1-MSS-01` | equivalence | certified | `marcusSSBridge` |
| `P-Marcus-ICvsISC` | `Q-RAD1-MIC-01` | definitionalIdentity | certified | `marcusICRateBridge` |
| `P-Marcus-Forster` | `Q-RAD1-MFO-01` | implication | outOfScope | — (jurisdiction record) |
| `P-Marcus-Einstein` | `Q-RAD1-MEB-01` | implication | outOfScope | — (jurisdiction record) |
| `P-Kasha-KashaVavilov` | `Q-RAD1-KKV-01` | implication | certified | `kashaVavBridge` |
| `P-Kasha-EnergyGapLaw` | `Q-RAD1-KEG-01` | definitionalIdentity | certified | `kashaEglRateBridge` |
| `P-Kasha-StokesShift` | `Q-RAD1-KSS-01` | implication | outOfScope | — (jurisdiction record) |
| `P-Kasha-ICvsISC` | `Q-RAD1-KIC-01` | conditionalComposition | unresolved | — (scoped search) |
| `P-Kasha-Forster` | `Q-RAD1-KFO-01` | implication | outOfScope | — (jurisdiction record) |
| `P-Kasha-Einstein` | `Q-RAD1-KEB-01` | observationalEquivalence | certified | `kashaEinsteinBridge` |
| `P-KashaVavilov-SternVolmer` | `Q-RAD1-VSV-01` | observationalEquivalence | certified | `kvSvBridge` |
| `P-KashaVavilov-QuantumYield` | `Q-RAD1-VQY-01` | observationalEquivalence | certified | `kvQyBridge` |
| `P-KashaVavilov-FluorPhos` | `Q-RAD1-VFP-01` | observationalEquivalence | certified | `kvFpBridge` |
| `P-KashaVavilov-EnergyGapLaw` | `Q-RAD1-VEG-01` | conditionalComposition | unresolved | — (scoped search) |

Outcome counts: certified 11, unresolved 2, outOfScope 4, refuted 0, notEstablished 0.
Kind counts: definitionalIdentity 3, implication 6, equivalence 2, conditionalComposition 2,
observationalEquivalence 4.

### 3.1 Chemical content of the certified rows

All eleven are typed `Certificate`s in the `PhotoLean.RelationAudit` semantic core
(`PhotoLean/RelationAudit/Defs.lean`); none is a wrapper around a legacy record, and none is a
shape-only match of two notations.

1. `Q-RAD1-MKVV-01` (Marcus → KashaVavilov, implication). A Marcus-controlled IC step at
   reorganization energy `lam` and gap `x` whose squared gap leaves the Kasha tolerance window
   forces `0 < upperYield`, hence (D2 boundary) an observable failure of Kasha's rule instead of
   Vavilov spectral invariance. Consumes `Kasha.not_kashaWithin_of_gap_far` and
   `KashaVavilov.antiKasha_observable_iff`.
2. `Q-RAD1-MEG-01` (Marcus ↔ EnergyGapLaw, definitionalIdentity). `Marcus.rate = EnergyGapLaw.nrRate`
   as a fresh `rfl` pin: the gap law's nonradiative rate *is* the Marcus activated rate.
3. `Q-RAD1-MEG-02` (Marcus ↔ EnergyGapLaw, equivalence). `Marcus.InvertedRegion lam x ↔
   EnergyGapLaw.InvertedGap lam x` — the same region boundary `x = lam`.
4. `Q-RAD1-MSS-01` (Marcus ↔ StokesShift, equivalence). The Stokes emission energy is positive
   (band maximum above the 0-0 energy) **iff** the step is in the Marcus inverted region
   (`lam < e00`); it is negative or zero outside that region (normal region `e00 < lam`, and
   the zero-photon corner `e00 = lam`). The emission window closes exactly at the region
   boundary. Delivered row SS-C9 (`StokesShift.emEnergy_pos_iff_inverted`).
5. `Q-RAD1-MIC-01` (Marcus ↔ ICvsISC, definitionalIdentity). `Marcus.rate = ICvsISC.icRate`: the
   spin-conserving internal-conversion channel rate is the Marcus activated rate.
6. `Q-RAD1-KKV-01` (Kasha → KashaVavilov, implication). Under the ladder's standing premises and
   positive yields, the exact Kasha rule entails equality of the normalized spectral shapes
   (`KashaVavilov.SpecSame`) — Vavilov's spectral law, delivered as KV-B7. This is the one-way
   implication `KashaRule → SpecSame`; the converse is not claimed. `SpecSame` is a
   spectral-shape statement only and does not assert that the fluorescence yield is constant
   across excitation levels; no `VavilovAt`/`VavilovUpTo` yield-independence claim is attached
   to it.
7. `Q-RAD1-KEG-01` (Kasha ↔ EnergyGapLaw, definitionalIdentity). `Kasha.marcusIC =
   EnergyGapLaw.nrRate`: the ladder's declared IC channel rate is the energy-gap-law
   nonradiative rate.
8. `Q-RAD1-KEB-01` (Kasha ↔ Einstein, observationalEquivalence). The lowest level's radiative
   branch `A/(A + kNR)` is `A·τ` with the observed lifetime `τ = 1/(A + kNR)`; one real-valued
   channel, total in `(A, kNR)`.
9. `Q-RAD1-VSV-01` (KashaVavilov ↔ SternVolmer, observationalEquivalence). A collisional quench
   added to the level-0 decay dilutes the ladder's bottom-emission channel by exactly the
   Stern–Volmer ratio of the unquenched level-0 decay and leaves the upper-block leak invariant —
   i.e. the Vavilov-relevant leak is quench-covariant, the bottom channel is not.
10. `Q-RAD1-VQY-01` (KashaVavilov ↔ QuantumYield, observationalEquivalence). The ladder's
    fluorescence yield is the level-0 two-channel quantum yield transported by the funnel
    transmission plus the upper-block leak.
11. `Q-RAD1-VFP-01` (KashaVavilov ↔ FluorPhos, observationalEquivalence). Under the explicit
    channel-lumping translation (`rad 0 = kF`, `ic 0 = kISC + kIC`) the ladder's bottom-level
    yield equals the three-channel FluorPhos fluorescence yield.

Each certified query carries: explicit shared context with fields and physical reading;
left/right translations with their requirements; premise predicate, premise IDs and per-premise
load-bearing notes; statement IDs, declarations, source lines, versions and recomputed signature /
source-artifact hashes of both endpoints; scope and snapshot; expected kind with rationale;
falsification condition; outcome with the probe declaration, the kind-check theorem, the build
command, the axiom print-out match, and at least one underlying delivered theorem at a verified
source line.

### 3.2 Non-certified rows

- `Q-RAD1-MFO-01` (**outOfScope**, Marcus/Forster): `Marcus.rate` takes `(A, lam, kB, T, x)`;
  `Forster.fretRate` takes `(tauD, r6, R)`. No inventory statement accepts both; `Relations.lean`
  §16 (line 964) registers no edge; a separation is not a driving force, and an Arrhenius shape
  alone must not identify a barrier with a transfer geometry.
- `Q-RAD1-MEB-01` (**outOfScope**, Marcus/Einstein): `Marcus.rate` vs `Einstein.aOfB` (radiation
  density factor `8πhν³/c³`); §16 line 969 registers no edge; the only Einstein rate-level contact
  is the QuantumYield anchor, i.e. a different pair.
- `Q-RAD1-KSS-01` (**outOfScope**, Kasha/StokesShift): `Kasha.radBranch` (rate arrays) vs
  `StokesShift.emEnergy` (energy offsets); §16 line 956 registers no edge.
- `Q-RAD1-KFO-01` (**outOfScope**, Kasha/Forster): `Kasha.emitYield` vs `Forster.fretRate`; a
  single-molecule ladder has no donor–acceptor pair; §16 line 964 registers no edge.
- `Q-RAD1-KIC-01` (**unresolved**, Kasha/ICvsISC): the candidate composition is
  `ic 1 = ICvsISC.icRate` followed by the delivered Kasha window row; the missing parent is the
  ladder channel assignment, which no delivered statement states (the ladder stores `ic` as a free
  rate array).
- `Q-RAD1-VEG-01` (**unresolved**, KashaVavilov/EnergyGapLaw): the candidate composition is
  gap-law rate → ladder channel → Kasha window → anti-Kasha; the missing parent is the same ladder
  channel assignment (the window row is stated with the Kasha-side `marcusIC`).

Every non-certified row links to a search-log entry containing the searched statements, searched
kinds, considered contexts, consulted dependencies (with locators), the real commands and their
results, the attempted strategies and why each failed, the candidate evidence, the exact remaining
gap or jurisdiction reason, recompute commands, and a rationale.

## 4. Evidence reuse and legacy disposition

- Legacy certified records for `P-Marcus-EnergyGapLaw` (rate identity, region equivalence),
  `P-Marcus-ICvsISC` (IC rate identity) and `P-Kasha-KashaVavilov` (D2 verdict) are **re-derived**
  at statement level from the delivered declarations (`cert_nrRate`, `cert_invertedGap`,
  `cert_icRate`, `specSame_of_kashaRule`); the legacy certificate objects are not cited as
  evidence. Each query's `provenance.legacyDisposition` states this.
- Legacy pair-level anchors (`notEstablished` / `unresolved` / undelivered-candidate) are recorded
  as coverage history in `legacyDisposition`, never used as an audit verdict and never used to
  veto a new certificate.

## 5. Gates actually run (real outputs in `evidence/gates.log`)

| # | command | result |
|---|---|---|
| 1 | `python3 audit_boundary/validate_boundary.py` | `RESULT: PASS` (17 theories, 136 pairs, 1154 statement rows, registry `25d38791…ecbf0`) |
| 2 | `python3 bounded_audit/validate_screening.py` | `RESULT: PASS` (0 checks failed) |
| 3 | `python3 bounded_audit/r4/validate_r3_content.py` | `RESULT: PASS` (0 failed; exactly the 7 enumerated current-ledger freshness checks excluded) |
| 4 | `python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json --skip-package-validators` | `RESULT: PASS` (840 checks passed; cumulative 67/136) |
| 5 | `python3 bounded_audit/r5/radiative-01/validate.py` | `RESULT: PASS` (0 checks failed) |
| 6 | `proofs/scripts/lake env lean bounded_audit/r5/radiative-01/probes/RAD1-probe.lean` | exit 0; 11/11 axiom print-outs `[propext, Classical.choice, Quot.sound]` |
| 7 | `proofs/scripts/check.sh --strict` | `build: OK`, scan `clean`, `verdict: PASS` |
| 8 | `python3 bounded_audit/r5/radiative-01/evidence/mutation_tests.py` | 15/15: control passes, 14 mutations fail closed with the expected code (including the six semantic-pin mutations M9–M14; M13 reinstates the old reversed §4 comment and M14 drops the normal-region sentence) |
| 9 | `python3 bounded_audit/r5/radiative-01/build_screening.py` (second run) | byte-identical artifacts (all three hashes unchanged) |
| 10 | ledger-independence test (`evidence/ledger-independence.log`): copy the tree to `/tmp`, delete `bounded_audit/coverage.json` **from the copy only**, run the copied validator | `RESULT: PASS` — the validator provably does not read the mutable ledger |

The validator checks, fail-closed: exact assigned sixteen pairs (and agreement with the R1 cluster
plan's work-package list); no overlap with the 67 accepted pairs derived *directly from the five
accepted packages*; the full 136-pair universe and the 69-pair remaining set; unique query IDs;
endpoint existence, inventory-field agreement, source-artifact hash, source-line match, signature
hash recomputation, non-dangling status and cross-theory pair membership; context/translation/
premise/scope/snapshot semantics; observation channels exactly where the kind requires them;
exactly one five-status outcome per query; certified evidence linked to a probe declaration, its
kind-check theorem, its axiom print-out and its underlying theorems; unresolved/notEstablished
evidence linked to a scoped search; outOfScope evidence with a statement-level jurisdiction
rationale; a search-log back-reference for every non-certified query and none for certified ones;
counts; fragment consistency; the mutable-ledger abstention; a forbidden-token scan of the
probe; and the repaired semantic pins: `Q-RAD1-MSS-01`'s question and falsification condition
must equal the pinned inverted-region reading and agree with the delivered
`emEnergy_pos_iff_inverted` direction, `Q-RAD1-KKV-01`'s kind rationale must state the one-way
`KashaRule → SpecSame` implication with no `VavilovAt`/`VavilovUpTo` yield-independence claim
attached, and `mkvCmp`'s left StatementRef must name `PhotoLean.Marcus.barrier` at the delivered
barrier source. It also pins the probe's §4 block comment to the corrected three-regime reading
(`emEnergy = e00 - lam`, positive exactly in `lam < e00`, negative in `e00 < lam`, zero at
`e00 = lam`), rejects three reversed phrases anywhere in the probe, and checks the comment against
the delivered `emEnergy_eq`, `inverted_corner` and `emission_window_closes` rows. Any internal
exception exits 1.

## 6. Deviations from the plan

1. **Two queries for one pair.** `P-Marcus-EnergyGapLaw` carries two chemically distinct queries
   (rate-level definitional identity and region-level equivalence), which the common package
   requirement explicitly permits. All other pairs carry one.
2. **`refuted` and `notEstablished` are zero.** No countermodel was found or manufactured; failed
   proof search was never recorded as refutation. The two missing-row cases are recorded as
   `unresolved` with the precise missing parent, which is the honest status: they are neither
   negative existence claims (`notEstablished`) nor statements outside the jurisdiction.
3. **Observation channels.** Exact `observationalEquivalence` rows carry one real-valued channel
   each (4 channels). Definitional identities, equivalences and implications carry none, because
   the audit contract requires channels only for observational/distinguishability certificates.
4. **Three certified rows re-derive legacy certified content** (Marcus/EnergyGapLaw,
   Marcus/ICvsISC, Kasha/KashaVavilov). They are delivered at statement level from the theory
   declarations, not copied from the legacy registry objects; the legacy records remain coverage
   history only.
5. **Probe location vs the strict scan range.** `proofs/ENGINE.yml` sets `SOURCE_DIRS="PhotoLean"`,
   so `check.sh --strict` does not scan `bounded_audit/r5/radiative-01/probes/RAD1-probe.lean`.
   The probe is instead covered by (a) the validator's forbidden-token scan of the probe source,
   (b) the per-declaration `#print axioms` audit parsed by the validator, and (c) the real compile
   gate. This limitation is inherited from the accepted R4 packages and is stated here rather than
   papered over.
6. **Prior coverage is derived, not pinned.** The package pins the five accepted package hashes and
   derives 67 accepted pairs from them; it never reads or pins `bounded_audit/coverage.json`. The
   validator enforces the abstention on the structured snapshot and reference objects, and the
   ledger-independence test in `evidence/ledger-independence.log` proves it operationally: the
   copied tree passes with the ledger deleted.

## 7. Blockers, risks and non-claims

- **No blocker.** All sixteen pairs are screened, all gates are green, and the probe compiles with
  a clean axiom footprint.
- **Risk (recorded honestly).** The two definitional rate identities (`Kasha.marcusIC =
  EnergyGapLaw.nrRate`, `Marcus.rate = ICvsISC.icRate`) are model-level identifications of one
  nonradiative channel expressed in two theory copies. They are *not* claims that the two theories
  are the same theory, and they do not identify a reaction barrier with an optical or geometric
  parameter. A reviewer who rejects the channel identification can reject the translation without
  disputing the algebra; the rationale says so explicitly.
- **Risk (recorded honestly).** Three certified rows are definitional rate identities
  (`Marcus.rate = EnergyGapLaw.nrRate`, `Kasha.marcusIC = EnergyGapLaw.nrRate`,
  `Marcus.rate = ICvsISC.icRate`). They are not three copies of one finding: each is the rate-level
  statement of a different pair, and the package deliberately keeps `P-Kasha-ICvsISC` (the pair
  that would follow by transitivity through the ladder's `ic`) **unresolved**, because the ladder
  stores its conversion channel as a free rate array and no delivered statement assigns the
  ICvsISC law to it. The asymmetry is the point: ICvsISC's `icRate` is a delivered channel law,
  the ladder's `ic` is not.
- **Risk (recorded honestly).** `Q-RAD1-VSV-01` treats dynamic quenching as an addition to the
  ladder's level-0 decay. That is the declared physical premise of the row (and of the
  SternVolmer/QuantumYield dilution row it is compared with); the row's two premises make the
  premise explicit.
- **Non-claims.** Screened ≠ certified; one query per pair does not exhaust the conceivable
  relations outside the frozen protocol; the outOfScope rows are jurisdiction records about
  statement-level vocabulary, not claims that the physical processes are unrelated; no acceptance
  is claimed and no other package, the ledger, the legacy registry, `PhotoLean/**`, the original
  repositories, the manuscript or the backup were modified.

## 8. Reproduction

```bash
cd bounded-relation-audit-2026-11-04/photolean
python3 bounded_audit/r5/radiative-01/build_screening.py        # regenerate the three JSON artifacts
python3 bounded_audit/r5/radiative-01/validate.py               # package gate (fail-closed)
proofs/scripts/lake env lean bounded_audit/r5/radiative-01/probes/RAD1-probe.lean
python3 bounded_audit/r5/radiative-01/evidence/mutation_tests.py
python3 audit_boundary/validate_boundary.py
python3 bounded_audit/validate_screening.py
python3 bounded_audit/r4/validate_r3_content.py
python3 bounded_audit/r4/validate_coverage.py --coverage bounded_audit/r4/coverage-accepted.json --skip-package-validators
proofs/scripts/check.sh --strict
```
