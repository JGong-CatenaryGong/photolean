# theories/SternVolmer/TASKS.md — PhotoLean task board: SternVolmer (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/SternVolmer/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/SternVolmer/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` — **46 declarations**
      (27 theorems + 19 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `811e34c0bf02d2b2a0479f613a73eb0db601a57cf331537750ca48706085cfa5`
- [x] API calibration probe: `theories/SternVolmer/probes/SternVolmer-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/SternVolmer/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `dynDecay` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioDyn` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauRatioDyn` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioStat` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauRatioStat` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `KSV` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioBoth` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Mech` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauRatioOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `LifetimeTracks` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `dyn_lifetime_tracks_intensity` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stat_lifetime_flat` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stat_lifetime_separates` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioDyn_linear` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioStat_linear` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioDyn_at_zero` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioStat_at_zero` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioDyn_strictMono_q` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioStat_strictMono_q` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `intensity_curve_coincidence` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `lifetimeTracks_iff_dyn` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioBoth_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioBoth_secondDifference` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioDyn_secondDifference` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svRatioStat_secondDifference` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `curvature_witnesses_coexistence` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `d1_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.svRatioDyn` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.tauRatioDyn` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.svRatioStat` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.tauRatioStat` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.svRatioDyn_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.tauRatioDyn_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.svRatioStat_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `Rat.tauRatioStat_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `SVZone` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svZoneQ` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svZoneQ_dynLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svZoneQ_statLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svZoneQ_mixedLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `svZoneQ_inconsistent` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `oxygenDynamic` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `complexStatic` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `conflation_witness` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `mixed_witness` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
