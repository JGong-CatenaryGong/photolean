# theories/QuantumYield/TASKS.md — PhotoLean task board: QuantumYield (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/QuantumYield/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/QuantumYield/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` — **29 declarations**
      (19 theorems + 10 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `967a11a1c788096d8fef39c90e62fd7e4cb5a2747efd3eb7e6621d2ca7b46a90`
- [x] API calibration probe: **missing** (to be supplied in Phase 2)
- [ ] Literature leaf populated: `theories/QuantumYield/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `totalRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `QYData` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `sum_yieldOf_eq_one` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_eq_mul_tauOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_nonneg` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_le_one` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_pos_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_div_yieldOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `totalRate_cons` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_cons_zero` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_cons_succ` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_cons_succ_factor` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_cons_lt` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `totalRate_zero_counterexample` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `nonvacuous_all_channels_live` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `totalRate` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `QYData` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `totalRate_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yieldOf_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fluoresceinS1` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `quinineLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `quenchDilution` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `inst_fluoresceinS1_phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `inst_quinineLike_phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `inst_quenchDilution_phiF` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `inst_quenchDilution_sternVolmer` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
