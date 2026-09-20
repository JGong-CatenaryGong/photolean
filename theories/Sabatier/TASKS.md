# theories/Sabatier/TASKS.md — PhotoLean task board: the Sabatier principle (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [x] <theorem> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Sabatier/plan.md`.
- **Statement authority** (target): `theories/Sabatier/probes/sabatier-statement-skeleton.lean`.
- Theory direction: **the Sabatier principle / volcano plot**, human request of 2026-09-21
  (three parts: formal description / proof and exact conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Sabatier`; sources under `PhotoLean/Sabatier/`
  (`SOURCE_DIRS` is global and covers them).

---

## Sprint 0 — environment, statements, plan

- [x] Theory directory `theories/Sabatier/` created with the five required items; contract
      `proofs/ENGINE.yml` extended with the multi-theory data plane (`THEORIES` + `PLAN_Sabatier` /
      `TASKS_Sabatier` / `LITERATURE_Sabatier` / `PROBES_Sabatier` / `RESULT_Sabatier`)
- [ ] Statement skeleton compiles (`theories/Sabatier/probes/sabatier-statement-skeleton.lean`)
- [ ] Lead risk probe (`theories/Sabatier/probes/sabatier-risk-probe.lean`): the critical-path
      statements proved *before* planning
- [ ] API calibration (`api_researcher`) → `proofs/API-NOTES.md` §Sabatier +
      `theories/Sabatier/probes/sabatier-api-*.lean`
- [ ] Literature survey (`literature_researcher`) → `theories/Sabatier/LITERATURE.md`
- [ ] Full plan landed (`theories/Sabatier/plan.md` §1–§14)
- [ ] `lakefile.toml` `defaultTargets` extended with the delivered modules
