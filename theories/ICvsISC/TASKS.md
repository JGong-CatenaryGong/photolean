# theories/ICvsISC/TASKS.md — PhotoLean task board: ICvsISC (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/ICvsISC/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/ICvsISC/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` — **20 declarations**
      (14 theorems + 6 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `07d1201c31dfd81ba373706b441ecbd7cafaa193b1404ce05c7029944475977e`
- [x] API calibration probe: `theories/ICvsISC/probes/ICvsISC-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/ICvsISC/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `fcBarrier` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cert_fcBarrier` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `icRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cert_icRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `iscRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `FCData` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `rate_ratio_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `log_rate_ratio` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `isc_dominates_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `spin_discount` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `hso_zero_isc_absent` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `barrier_diff_closed_form` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `equal_prefactors_decision` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fcBarrier` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fcBarrier_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `barrierOrderQ` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `barrierOrderQ_correct` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aromaticCarbonylLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `elSayedFavoredLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `hsoZeroWitness` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
