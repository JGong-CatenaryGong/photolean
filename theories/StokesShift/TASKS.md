# theories/StokesShift/TASKS.md — PhotoLean task board: StokesShift (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/StokesShift/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete** — the statement
  authority compiles at 0 errors with placeholder theorem bodies; batch: photophysics subgraph
  (groups A–D), dispatched 2026-09-22.
- Status of Phase 2: **delivered, in `review`** — all 35 declarations are proved in
  `PhotoLean/StokesShift/{Basic,Criterion,RatModel,Instances}.lean` by prover_a (2026-09-22);
  independent verification is pending and ticking stays lead-only (iron rule 7). The corrected
  SS-C9 row (`emEnergy_pos_iff_inverted`) is delivered exactly as carried by the statement
  authority (plan §3.1 entry 1).

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

### Declaration board (all `review`; ticking is lead-only after verifier PASS)

- [ ] `s0Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B1)
- [ ] `cert_s0Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B1)
- [ ] `s1Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B2)
- [ ] `cert_s1Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B2)
- [ ] `absEnergy` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B3)
- [ ] `emEnergy` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B4)
- [ ] `stokesShift` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Basic.lean` (SS-B5)
- [ ] `absEnergy_eq` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C1)
- [ ] `emEnergy_eq` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C2)
- [ ] `stokesShift_eq_two_lam` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C3)
- [ ] `stokesShift_pos_iff` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C4)
- [ ] `emEnergy_pos_iff` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C5)
- [ ] `mirror_midpoint` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C6)
- [ ] `abs_sub_e00_eq_e00_sub_em` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C7)
- [ ] `emission_window_closes` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C8)
- [ ] `inverted_corner` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C8)
- [ ] `emEnergy_pos_iff_inverted` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Criterion.lean` (SS-C9, corrected form)
- [ ] `s0Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [ ] `s1Surface` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [ ] `absEnergy` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [ ] `emEnergy` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [ ] `stokesShift` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [ ] `s0Surface_cast` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [ ] `s1Surface_cast` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [ ] `absEnergy_cast` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [ ] `emEnergy_cast` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [ ] `stokesShift_cast` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [ ] `SSZone` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [ ] `ssZoneQ` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [ ] `ssZoneQ_eq_normalEmission_iff` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [ ] `ssZoneQ_eq_zeroPhoton_iff` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [ ] `ssZoneQ_eq_invertedEmission_iff` — delivered — Phase 2 — review — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [ ] `mirrorDye` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Instances.lean` (SS-I1)
- [ ] `largeRelaxation` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Instances.lean` (SS-I2)
- [ ] `invertedCorner` — delivered — Phase 2 — review — `PhotoLean/StokesShift/Instances.lean` (SS-I3)

## Sprint 1+ — proof formalization (Phase 2, delivered; awaiting independent verification)

Sprints SS1–SS4 were delivered in order (Basic → Criterion → RatModel → Instances), each closing
with `proofs/scripts/lake build PhotoLean.StokesShift.<Module>` green before the next was
claimed. Author-measured gate evidence (not an independent verdict):
`proofs/scripts/lake build` exit 0 for each of the four modules; `proofs/scripts/axioms.sh` run
on all 23 delivered theorems prints only `propext, Classical.choice, Quot.sound`;
`proofs/scripts/check.sh --strict` verdict PASS (`clean` scan); and
`python3 theories/BEP/probes/bep-fidelity.py --theory StokesShift` reports 35/35 word-for-word,
0 not delivered, 0 signature differences.

No statement was changed in Phase 2; the delivered declarations are the authority's rows
verbatim. No row needed a large-model escalation and no statement incident occurred.
