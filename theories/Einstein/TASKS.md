# theories/Einstein/TASKS.md — PhotoLean task board: Einstein (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Einstein/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/Einstein/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/Einstein/probes/Einstein-statement-skeleton.lean` — **33 declarations**
      (22 theorems + 11 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `de13f5b3850513efdc7fa5f46de1371386a07c574364c425a5967ed619be286d`
- [x] API calibration probe: `theories/Einstein/probes/Einstein-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/Einstein/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `radFactor` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfB` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `b12OfB21` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fOfA` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfInt` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauR` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `radFactor_pos` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `bOfA_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfb_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `detailed_balance` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `degeneracy_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `af_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fa_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `int_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfInt_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `full_chain_roundtrip` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `f_pos_iff_a_pos` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `yield_radiative` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `lifetime_pos` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfB` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `b12OfB21` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fOfA` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfInt` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauR` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfB_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `b12OfB21_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `fOfA_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `aOfInt_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `tauR_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `rat_roundtrip_verdicts` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `radFactor_not_rational` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `twoLevelDyeLike` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `degeneracySwap` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
