# theories/EnergyGapLaw/TASKS.md — PhotoLean task board: EnergyGapLaw (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/EnergyGapLaw/plan.md`.
- Status of this theory: **Phase 2 (proof layer) delivered** — all 26 Sprint-0 declarations proved,
  every row moved `stmt` -> `review` (verifier adjudication pending, so no box is ticked);
  batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.

### Sprint-0/Phase-2 delivery record (prover_a)

- Delivered modules (owner prover_a; one commit per module, the batch-registered deviation from
  one-commit-per-lemma):
  `PhotoLean/EnergyGapLaw/{Basic,Criterion,Sharp,RatModel,Instances}.lean`.
- Build evidence (exit 0 each): `proofs/scripts/lake build PhotoLean.EnergyGapLaw.<Module>` for
  all five modules; `proofs/scripts/check.sh --strict` with the five modules as targets = PASS
  (scan `clean`), and the whole-tree `proofs/scripts/check.sh --strict` = PASS.
- Axiom evidence: `proofs/scripts/axioms.sh <Module> <qualified name>` = PASS for all **17**
  authority theorems plus the one auxiliary row `lnRate_second_difference` (18/18); every one
  depends on at most `propext, Classical.choice, Quot.sound`.
- Fidelity: `python3 theories/BEP/probes/bep-fidelity.py --theory EnergyGapLaw` reports
  `skeleton declarations 26`, `delivered, word-for-word 26`, `not delivered yet 0`,
  `signature differences 0`; the single "not in authority" entry is the auxiliary row.
- Statement discipline: all 26 signatures are transcribed verbatim from the authority, including
  the three §3.1 corrections (EG-I3 defect magnitude `-5`, EG-S4 without the unconsumable
  `0 < A`, EG-C4 corollary as the iff). No statement was changed and no statement incident arose;
  the `Rat.nrBarrier_cast` row was checked against the SV-R1 shadowing pitfall with a scratch
  `#print` and is a real (non-vacuous) bridge.
- Premise note for the verifier (CORRECTED 2026-09-23, verifier run 2 finding M1): EG-C4's
  `secant_slope_neg_iff` carries the authority's premise `x₁ ≠ x₂`. The first note called it
  decorative — that was arithmetically wrong: at `x₁ = x₂ = 2, lam = 1` the left side is `0/0 < 0`
  (false) while the right side is true, so `¬ (LHS ↔ RHS)`. The premise is load-bearing and IS
  consumed by the proof; the local unused-variable disable was a no-op and has been removed.

## Sprint 0 — environment, statements, plan

- [x] Statement skeleton `theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` compiles at 0 errors
      (`proofs/scripts/lake env lean`) — placeholder theorem bodies on purpose
- [x] Plan landed: `theories/EnergyGapLaw/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates)
- [x] Literature leaf: `theories/EnergyGapLaw/LITERATURE.md` (sources with formalizable implications)

### Sprint-0 declaration board (26 declarations: 9 definitions incl. 1 inductive, 17 theorems)

- Skeleton: `theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean`,
  sha256 `2294c38f6040337ba9ef172b00ce6ffa7a78f1f36547234778690871b1480a64`
  (measured after the last edit; every row below is a declaration of this exact file).
- Compile command (gate: exit 0, exactly 17 `declaration uses 'sorry'` warnings, no other output):
  `proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean`
- API probe: `theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean` (exit 0, no `sorry`),
  sha256 `52e843a4eaa61ef128c4d69fd8553e5b6094bbd428d31f0f2167bec9cf2d1b90`;
  compile: `proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean`

| # | Plan row | Declaration | Kind | Status |
|---|----------|-------------|------|--------|
| 1 | EG-B1 | `nrBarrier` | def | `done` |
| 2 | EG-B1 | `cert_nrBarrier` | theorem | `done` |
| 3 | EG-B2 | `nrRate` | def | `done` |
| 4 | EG-B2 | `cert_nrRate` | theorem | `done` |
| 5 | EG-B3 | `InvertedGap` | def | `done` |
| 6 | EG-B3 | `cert_invertedGap` | theorem | `done` |
| 7 | EG-B4 | `lnRate` | def | `done` |
| 8 | EG-C1 | `lnRate_eq` | theorem | `done` |
| 9 | EG-C2 | `lnRate_strictAnti_on_inverted` | theorem | `done` |
| 10 | EG-C3 | `lnRate_strictMono_on_normal` | theorem | `done` |
| 11 | EG-C4 | `secant_slope_exact` | theorem | `done` |
| 12 | EG-C4 (corollary) | `secant_slope_neg_iff` | theorem | `done` |
| 13 | EG-S1 | `eglTangent` | def | `done` |
| 14 | EG-S2 | `eglTangent_overestimates` | theorem | `done` |
| 15 | EG-S2a | `eglTangent_defect` | theorem | `done` |
| 16 | EG-S3 | `not_affine_on_window` | theorem | `done` |
| 17 | EG-S4 | `eglTangent_slope_strictAnti` | theorem | `done` |
| 18 | EG-R1 | `Rat.nrBarrier` | def | `done` |
| 19 | EG-R1 (cast row; name assigned in Sprint 0) | `Rat.nrBarrier_cast` | theorem | `done` |
| 20 | EG-R2 | `EGZone` | inductive | `done` |
| 21 | EG-R2 | `egZoneQ` | def | `done` |
| 22 | EG-R2 (correctness row) | `egZoneQ_eq_inverted_iff` | theorem | `done` |
| 23 | EG-R3 | `nrRate_decidable_order` | def | `done` |
| 24 | EG-I1 | `aromaticSeries` | theorem | `done` |
| 25 | EG-I2 | `normalRegionCounter` | theorem | `done` |
| 26 | EG-I3 | `tangentWitness` | theorem | `done` |

---

## Verifier run 2 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence: nine modules (this theory's five) rebuilt from source with
zero diagnostics; whole-tree `check.sh --strict` PASS with scan `clean` (the five EnergyGapLaw
targets are in `defaultTargets` since `ec74c92`); `#print axioms` 18/18 PASS (only
`propext Classical.choice Quot.sound`); fidelity 26/26 with 0 differences; `Rat.nrBarrier_cast`
`#print`-checked as a real bridge; instance arithmetic independently recomputed (barrier chain
`1/8, 1/2, 9/8`, normal-region counter `9/32 < 1/8`, defect `5`); adversarial attacks against every
premise-removed form broke as expected while **no delivered form broke** (edge inputs `x = lam`,
`x = x*`, far inputs, midpoint at `lam` all discharged); `not_affine_on_window` instantiated on the
concrete window `[0,1]` with second difference `-1/8 ≠ 0`.

Findings and their resolution:
* **M1 (fixed 2026-09-23 by the lead)** — the delivery comment called `h : x₁ ≠ x₂` of
  `secant_slope_neg_iff` decorative and disabled the unused-variable linter locally. Wrong: at
  `x₁ = x₂ = 2, lam = 1` the left side is `0/0 < 0` (false) while the right side is true, so the
  premise is load-bearing; the disable suppressed nothing (the stripped file emits no warning).
  The comment is corrected and the no-op `set_option` removed.
* **M2 (documented 2026-09-23)** — the instance rows are barrier-side; their rate-side readings are
  prose justified by EG-C2/EG-C3 (plan §4 note added; the verifier confirmed the rate-level chains
  compile through the delivered rows).
* L4 (plan §4 EG-I3 body printed the draft `-20`) — fixed by the lead 2026-09-23.
* L6 premise residue (EG-C1's `lam ≠ 0` / `0 < kB*T` are proof-consumed but not statement-necessary)
  — carried to the Phase-3 premise audit.

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entry 5): `lnRate_eq` dropped `lam ≠ 0` and `0 < kB*T` (degenerate inputs totalize consistently); ten call sites adapted. All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).
