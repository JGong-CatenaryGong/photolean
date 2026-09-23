# theories/FluorPhos/TASKS.md — PhotoLean task board: FluorPhos (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/FluorPhos/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/FluorPhos/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` — **29 declarations**
      (16 theorems + 13 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `2aa08f1c153b6494c09fd9848c76644ab0b7a59c2a3f46d32a25db7a8d3223bb`
- [x] API calibration probe: `theories/FluorPhos/probes/FluorPhos-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/FluorPhos/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `s1Decay` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `iscBranch` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `t1BranchP` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `FPData` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP_div_phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF_add_phiP_le_one` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF_add_phiP_eq_one_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF_strictAnti_isc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP_strictMono_isc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `crossover_isc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `crossover_isc_threshold` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `hso_zero_no_phosphorescence` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `nonvacuous_competition` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s1Decay` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiF_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `phiP_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `FPZone` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fpZoneQ` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fpZoneQ_phosphorDominant_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `naphthaleneLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `naphthaleneLike_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `eosinLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `eosinLike_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `crossoverWitness_verdict` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
