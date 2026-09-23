# theories/FluorPhos/TASKS.md — PhotoLean task board: FluorPhos (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/FluorPhos/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) delivered in part** — 28 of the 29
  authority declarations are proved in `PhotoLean/FluorPhos/{Basic,Criterion,RatModel,Instances}.lean`
  (all except `phiP_strictMono_isc`, reported NEEDS-LARGE-MODEL); the statement authority compiles
  at 0 errors; batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.
- **Phase 2 (prover_c, 2026-09-23)**: gate evidence — per-module `proofs/scripts/lake build` exit 0
  for `Basic` / `Criterion` / `RatModel` / `Instances`; `proofs/scripts/check.sh --strict` (whole
  tree) verdict PASS (scan clean); `proofs/scripts/axioms.sh` PASS for all 15 delivered theorems
  (each `depends on axioms: [propext, Classical.choice, Quot.sound]`); fidelity
  `python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos` = 28/29 word-for-word,
  0 signature differences, 1 not delivered (`phiP_strictMono_isc`).
  The `Rat.*` cast rows were `#print`-checked against the SV-R1 vacuous-identity class: the printed
  right-hand sides are the `PhotoLean.FluorPhos`-level definitions, so the rows are real bridges
  (no STATEMENT-INCIDENT).

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/FluorPhos/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` — **29 declarations**
      (16 theorems + 13 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `b116adddea484896f7068c00141989d70871db4f51fe36749a2dbc44e24f4480`
- [x] API calibration probe: `theories/FluorPhos/probes/FluorPhos-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/FluorPhos/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `s1Decay` — Basic.lean — review — proved (Phase 2)
- [ ] `phiF` — Basic.lean — review — proved (Phase 2)
- [ ] `iscBranch` — Basic.lean — review — proved (Phase 2)
- [ ] `t1BranchP` — Basic.lean — review — proved (Phase 2)
- [ ] `phiP` — Basic.lean / RatModel.lean — review — proved (Phase 2)
- [ ] `FPData` — Basic.lean — review — proved (Phase 2)
- [ ] `phiP_eq` — Criterion.lean — review — proved (Phase 2)
- [ ] `phiP_div_phiF` — Criterion.lean — review — proved (Phase 2)
- [ ] `phiF_add_phiP_le_one` — Criterion.lean — review — proved (Phase 2)
- [ ] `phiF_add_phiP_eq_one_iff` — Criterion.lean — review — proved (Phase 2)
- [ ] `phiF_strictAnti_isc` — Criterion.lean — review — proved (Phase 2)
- [ ] `phiP_strictMono_isc` — NOT DELIVERED — NEEDS-LARGE-MODEL — the residual arithmetic step `0 < kF + kIC` from `0 < kF + kISC + kIC` and `0 ≤ kISC` is not closed by the tactics tried (five routes; see EXPERIENCE.md 2026-09-23 prover_c entry)
- [ ] `crossover_isc` — Criterion.lean — review — proved (Phase 2)
- [ ] `crossover_isc_threshold` — Criterion.lean — review — proved (Phase 2)
- [ ] `hso_zero_no_phosphorescence` — Criterion.lean — review — proved (Phase 2)
- [ ] `nonvacuous_competition` — Criterion.lean — review — proved (Phase 2)
- [ ] `s1Decay` — Basic.lean — review — proved (Phase 2)
- [ ] `phiF` — Basic.lean — review — proved (Phase 2)
- [ ] `phiP` — Basic.lean / RatModel.lean — review — proved (Phase 2)
- [ ] `Rat.phiF_cast` — RatModel.lean — review — proved (Phase 2); `#print`-checked non-vacuous (real bridge)
- [ ] `Rat.phiP_cast` — RatModel.lean — review — proved (Phase 2); `#print`-checked non-vacuous (real bridge)
- [ ] `FPZone` — RatModel.lean — review — Phase 2
- [ ] `fpZoneQ` — RatModel.lean — review — Phase 2
- [ ] `fpZoneQ_phosphorDominant_iff` — RatModel.lean — review — proved (Phase 2)
- [ ] `naphthaleneLike` — Instances.lean — review — Phase 2
- [ ] `naphthaleneLike_verdict` — Instances.lean — review — proved (Phase 2)
- [ ] `eosinLike` — Instances.lean — review — Phase 2
- [ ] `eosinLike_verdict` — Instances.lean — review — proved (Phase 2)
- [ ] `crossoverWitness_verdict` — Instances.lean — review — proved (Phase 2)

## Sprint 1+ — proof formalization (Phase 2, delivered 2026-09-23 by prover_c)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed. All rows are at **review** (ticking is lead-only
after a verifier PASS). One row is deliberately absent from the delivered sources:
`phiP_strictMono_isc` (FP-C5 second half), reported NEEDS-LARGE-MODEL with the exact residual
arithmetic step in the task-board row above and in `proofs/EXPERIENCE.md`.

## Authority re-freeze — 2026-09-23 (FP-C5 second half, plan §3.1 entry 2)

`phiP_strictMono_isc` was re-frozen with the load-bearing premise `0 < kF + kIC`: the first frozen
form is FALSE at `kF = kIC = 0` (kernel-checked counterexample at `kISC = 1 → 2`, both sides `1/2`;
probe `.lake/tmp/lead_fp_c5_probe.lean`, exit 0). New authority sha256 `b116adddea484896f7068c00141989d70871db4f51fe36749a2dbc44e24f4480`.
