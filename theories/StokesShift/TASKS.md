# theories/StokesShift/TASKS.md — PhotoLean task board: StokesShift (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/StokesShift/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/StokesShift/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` — **35 declarations**
      (23 theorems + 12 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `d5b88990db19a20b36c0e638ea9deb83366e2a9fbf81281e0d969f9aa0ba3c0a`
- [x] API calibration probe: **missing** (to be supplied in Phase 2)
- [ ] Literature leaf populated: `theories/StokesShift/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [ ] `s0Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cert_s0Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s1Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `cert_s1Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `absEnergy` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stokesShift` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `absEnergy_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy_eq` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stokesShift_eq_two_lam` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stokesShift_pos_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy_pos_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `mirror_midpoint` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `abs_sub_e00_eq_e00_sub_em` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emission_window_closes` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `inverted_corner` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy_pos_iff_inverted` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s0Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s1Surface` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `absEnergy` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stokesShift` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s0Surface_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `s1Surface_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `absEnergy_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `emEnergy_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `stokesShift_cast` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `SSZone` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `ssZoneQ` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `ssZoneQ_eq_normalEmission_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `ssZoneQ_eq_zeroPhoton_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `ssZoneQ_eq_invertedEmission_iff` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `mirrorDye` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `largeRelaxation` — skeleton — Phase 1 — stmt — placeholder body registered
- [ ] `invertedCorner` — skeleton — Phase 1 — stmt — placeholder body registered

## Sprint 1+ — proof formalization (Phase 2, not started)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed.
