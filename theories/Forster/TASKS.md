# theories/Forster/TASKS.md — PhotoLean task board: Forster (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Forster/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

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

- [ ] `kappaSq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff6` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `r0six` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kappaConvention` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kappaSq_nonneg` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kappaSq_le_four` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kappaSq_eq_zero_witness` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kappaSq_eq_four_witness` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff_self` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff6_strictMono_r6` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `r0six_ratio` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `r0six_ratio_mem` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fret_blind_spot` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff6_mono_kappa` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff_via_lifetime` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff_via_lifetime'` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff_at_twoR0` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff6` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `r0six` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fretEff6_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `frameKappa` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `frame_sum_eq_six` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `iso_frame_avg` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `rat_blind_spot` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `rat_max_bias` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cy3cy5Like_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `blindSpotGeometry_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `maxGeometry_verdict` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
