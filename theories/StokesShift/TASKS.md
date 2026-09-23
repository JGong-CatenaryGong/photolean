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
  independent verification is pending and ticking stays lead-only (iron rule 7). **Verifier run 1 (2026-09-23): PASS** — see the record at the end of this board. The corrected
  SS-C9 row (`emEnergy_pos_iff_inverted`) is delivered exactly as carried by the statement
  authority (plan §3.1 entry 1).

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/StokesShift/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` — **35 declarations**
      (23 theorems + 12 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `d5b88990db19a20b36c0e638ea9deb83366e2a9fbf81281e0d969f9aa0ba3c0a`
- [x] API calibration probe: `theories/StokesShift/probes/StokesShift-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/StokesShift/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `review`; ticking is lead-only after verifier PASS)

- [x] `s0Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B1)
- [x] `cert_s0Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B1)
- [x] `s1Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B2)
- [x] `cert_s1Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B2)
- [x] `absEnergy` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B3)
- [x] `emEnergy` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B4)
- [x] `stokesShift` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Basic.lean` (SS-B5)
- [x] `absEnergy_eq` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C1)
- [x] `emEnergy_eq` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C2)
- [x] `stokesShift_eq_two_lam` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C3)
- [x] `stokesShift_pos_iff` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C4)
- [x] `emEnergy_pos_iff` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C5)
- [x] `mirror_midpoint` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C6)
- [x] `abs_sub_e00_eq_e00_sub_em` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C7)
- [x] `emission_window_closes` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C8)
- [x] `inverted_corner` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C8)
- [x] `emEnergy_pos_iff_inverted` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Criterion.lean` (SS-C9, corrected form)
- [x] `s0Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [x] `s1Surface` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [x] `absEnergy` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [x] `emEnergy` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [x] `stokesShift` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1, ℚ shadow)
- [x] `s0Surface_cast` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [x] `s1Surface_cast` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [x] `absEnergy_cast` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [x] `emEnergy_cast` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [x] `stokesShift_cast` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R1)
- [x] `SSZone` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [x] `ssZoneQ` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [x] `ssZoneQ_eq_normalEmission_iff` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [x] `ssZoneQ_eq_zeroPhoton_iff` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [x] `ssZoneQ_eq_invertedEmission_iff` — delivered — Phase 2 — done — `PhotoLean/StokesShift/RatModel.lean` (SS-R2)
- [x] `mirrorDye` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Instances.lean` (SS-I1)
- [x] `largeRelaxation` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Instances.lean` (SS-I2)
- [x] `invertedCorner` — delivered — Phase 2 — done — `PhotoLean/StokesShift/Instances.lean` (SS-I3)

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

---

## Verifier run 1 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence (raw outputs in the verifier's report):
build all delivered modules exit 0; whole-tree `check.sh --strict` PASS with scan `clean`;
`#print axioms` over every delivered theorem (102 for the four wave-1 theories) — all within
`[propext, Classical.choice, Quot.sound]` (five classifier rows depend on `propext` only);
fidelity `--theory StokesShift` — 0 signature differences against the authority; authority sha256 on this
board matches the file byte-for-byte; headline rows `#print`-checked as non-trivial; independent
recomputation of the named-instance verdicts matched; adversarial counterexample attempts against
the headline rows and the boundary predicates only broke *premise-removed* forms, confirming the
delivered premises are load-bearing (or registering them for the premise audit below).

Findings carried to the Phase-3 audit and to the lead (recorded here as the single source of truth):
* M1 statement-change index missing in `proofs/API-NOTES.md` (fixed by the lead 2026-09-23).
* M2 `theories/StokesShift/plan.md` §4/§5 printed the refuted SS-C9 form (fixed by the lead 2026-09-23).
* M3 `SternVolmer.mixed_witness` third conjunct is a tautology (Phase-3 authority re-freeze list).
* M4 `Einstein.radFactor_not_rational` does not mention `radFactor` (Phase-3 re-freeze list; the
  intended `Irrational (radFactor 1 1 1)` is provable — verifier's probe).
* M5 stale SternVolmer evidence block (fixed by the lead 2026-09-23).
* M6 weakest-premise standard not yet executed on the wave-1 theories (Phase-3 premise audit;
  the concrete non-load-bearing premises are listed in `proofs/EXPERIENCE.md`).
* L1–L7 low findings: record hygiene, commit granularity (registered deviation), suppressions
  hiding one real unused premise, an empty commit whose correction never landed (relaunched by the
  lead 2026-09-23), and the naming-bridge caveat on `emEnergy_pos_iff_inverted`.
