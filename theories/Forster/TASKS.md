# theories/Forster/TASKS.md — PhotoLean task board: Forster (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Forster/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) complete — all rows at `review`**;
  the statement authority is unchanged (still the Sprint-0 frozen sha256 recorded below) and every
  authority declaration is delivered verbatim (bep-fidelity: 32/32 word-for-word, 0 differences,
  0 undelivered). The rows below are moved `stmt` → `review` by prover_d; ticking (`[x]`) is
  lead-only after verifier PASS. Batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.
- Evidence (prover_d, 2026-09-23): per-module `lake build` exit 0 for all four modules;
  `proofs/scripts/check.sh --strict <module>` PASS on each (scan: clean); `proofs/scripts/axioms.sh`
  PASS on all 22 theorems (only propext / Classical.choice / Quot.sound); `bep-fidelity.py
  --theory Forster` → signature differences 0.
- Route note (FO-C2, the batch's highest-risk row): delivered by the plan's two-step route
  (triangle inequality + ℝ² Cauchy–Schwarz via `nlinarith` + `Real.sin_sq_add_cos_sq`), with the
  final comparison taken through the square-root form (`Real.sqrt_le_sqrt`,
  `Real.sqrt_sq_eq_abs`) — the plan's registered fallback `kappaSq_le_eight` was **not** needed
  and the statement is unchanged. See `proofs/API-NOTES.md` §photobatch/Forster.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/Forster/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/Forster/probes/Forster-statement-skeleton.lean` — **32 declarations**
      (22 theorems + 10 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `b3f3c3b18966545032e231a8a99ed17aeb949072c309d6afbfaed28c6cc0e661`
- [x] API calibration probe: `theories/Forster/probes/Forster-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/Forster/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `kappaSq` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretRate` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff6` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `r0six` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `kappaConvention` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `kappaSq_nonneg` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `kappaSq_le_four` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `kappaSq_eq_zero_witness` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `kappaSq_eq_four_witness` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff_eq` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff_self` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff6_strictMono_r6` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `r0six_ratio` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `r0six_ratio_mem` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fret_blind_spot` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff6_mono_kappa` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff_via_lifetime` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff_via_lifetime'` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff_at_twoR0` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff6` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `r0six` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretRate` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `fretEff6_cast` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `frameKappa` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `frame_sum_eq_six` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `iso_frame_avg` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `rat_blind_spot` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `rat_max_bias` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `cy3cy5Like_verdict` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `blindSpotGeometry_verdict` — skeleton — Phase 2 — review — proved (prover_d)
- [ ] `maxGeometry_verdict` — skeleton — Phase 2 — review — proved (prover_d)

## Sprint 1+ — proof formalization (Phase 2, delivered by prover_d 2026-09-23)

Sprint FO1 `Basic` → FO2 `Criterion` → FO3 `RatModel` → FO4 `Instances`; each closed with
`lake build` green before the next was claimed. All 32 declaration rows are at `review`
(writer = prover_d); the lead ticks after verifier PASS.

Module map and row counts:

| Module | Rows | Content |
|---|---|---|
| `PhotoLean/Forster/Basic.lean` | FO-B1..FO-B6 | `kappaSq`, `fretRate`, `fretEff6`, `fretEff`, `r0six`, `kappaConvention` |
| `PhotoLean/Forster/Criterion.lean` | FO-C1..FO-C11 (14 theorems) | the `κ² ≤ 4` bound, the two witnesses, the efficiency certificate and monotonicity, the convention-bias pair, the blind spot, the lifetime readings |
| `PhotoLean/Forster/RatModel.lean` | FO-R1..FO-R3 | the ℚ twins + cast coherence, `frameKappa`/`frame_sum_eq_six`/`iso_frame_avg`, the decision-layer rows |
| `PhotoLean/Forster/Instances.lean` | FO-I1..FO-I3 | `cy3cy5Like_verdict` (64/793), the blind-spot and maximal-κ² geometries |

Open coordination item for the lead: the four `PhotoLean.Forster.*` targets are **not yet in
`lakefile.toml`'s `defaultTargets`**, so a bare `check.sh --strict` builds the other theories but
not these modules while its scan still covers them (the acceptance hole ENGINE.md §1.1 warns
about). Per-module builds and `check.sh --strict <module>` are green.

Known whole-tree strict-gate failure outside Forster (not this theory's rows):
`PhotoLean/FluorPhos/Scratch.lean` carries unproved placeholders at lines 25/26/28/29.
