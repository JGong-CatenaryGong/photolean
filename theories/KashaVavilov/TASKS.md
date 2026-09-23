# theories/KashaVavilov/TASKS.md — PhotoLean task board: KashaVavilov (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/KashaVavilov/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/KashaVavilov/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` — **29 declarations**
      (20 theorems + 9 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `5a51614d80d8340d76b605657802152f6574ad40c31aa6eb9e8d373d65dfdb15`
- [x] API calibration probe: `theories/KashaVavilov/probes/KashaVavilov-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/KashaVavilov/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `SpecSame` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fluoYield_eq_emitYield_zero_add_upperYield` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `rateData_mono` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `specFrac_zero_of_kashaRule` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `specFrac_succ_of_kashaRule` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kashaRule_mono` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `specSame_of_kashaRule` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kashaRule_not_implies_vavilovAt` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `vavilovAt_not_implies_kashaRule` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `lossless_separates_kasha_vavilov` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `d2_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cascade_pos_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emitYield_pos_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `antiKasha_observable_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `upperYield_pos_of_rad_pos` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `exists_maximal_emitter` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kashaPureLadderRad` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kashaPureLadderIc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `kashaPureLadder_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `antiVavilovLadderRad` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `antiVavilovLadderIc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `antiVavilovLadder_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `vavilovOnlyLadderRad` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `vavilovOnlyLadderIc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `vavilovOnlyLadder_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `losslessLadderRad` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `losslessLadderIc` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `losslessLadder_verdict` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `instances_distinct` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
