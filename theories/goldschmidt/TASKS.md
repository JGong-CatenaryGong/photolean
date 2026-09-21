# theories/goldschmidt/TASKS.md — PhotoLean task board: the Goldschmidt tolerance factor and rules (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [x] <theorem> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`, `lead`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/goldschmidt/plan.md`.
- **Statement authority**: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean`
  (fidelity check `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt [--milestone G<k>]`).
- **Sprint-0 kernel evidence**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` (0 error).
- Theory direction: **the Goldschmidt tolerance factor and Goldschmidt's rules of ionic
  substitution**, human request of 2026-09-21 (three parts: formal description / proof and exact
  conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Goldschmidt`; sources under `PhotoLean/Goldschmidt/`
  (`SOURCE_DIRS` is global and covers them).

---

## Sprint 0 — environment, statements, plan (in progress)

- [x] Theory directory `theories/goldschmidt/` created with the five required items; contract
      `proofs/ENGINE.yml` extended (`THEORIES="… goldschmidt"` + `PLAN_goldschmidt` /
      `TASKS_goldschmidt` / `LITERATURE_goldschmidt` / `PROBES_goldschmidt` / `RESULT_goldschmidt`)
- [x] **Statement skeleton compiles**: `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean`
      (**138 declarations**, 0 error, placeholder-only bodies; fidelity checker wired:
      `python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt` → 138 not delivered, 0 signature
      differences). Three rows corrected at Sprint 0 before dispatch — plan §3.1
- [ ] **Lead risk probe**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` — proves the
      critical-path statement forms *before* planning (window equivalence, squared form, symmetric
      band, `rO` trichotomy, irrationality row, radius-rule bridge, charge-compensation existence,
      `ℚ` classifier transfer, instance spot checks)
- [ ] API calibration (`api_researcher`) → `proofs/API-NOTES.md` § "Goldschmidt theory (2026-09-21)"
      + `theories/goldschmidt/probes/goldschmidt-api-*.lean`
- [ ] Literature survey (`literature_researcher`) → `theories/goldschmidt/LITERATURE.md` +
      `theories/goldschmidt/literature/INSTANCE-DATA.md`
- [x] Plan landed: `theories/goldschmidt/plan.md` §1–§14
- [x] **Off-kernel exact-rational instance cross-check**:
      `theories/goldschmidt/probes/goldschmidt-instance-check.py` → exit 0, 0 mismatches; exact `t²`
      values and verdicts recorded in plan §9
- [ ] `lakefile.toml` `defaultTargets` extended with `PhotoLean.Goldschmidt.Basic` (one line per
      module, in the same commit as the module)
- [x] Human confirmation of the design (2026-09-21: directory `theories/goldschmidt/`, full scope
      ①+②+③, module layout G1–G6)

## G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`; owner lead)

- [ ] definitions `tolFac` / `latticeOf` / `idealAO` / `idealA` / `rAMin` / `rAMax` / `InBand` /
      `GoldschmidtConforms` / `GoldschmidtZone` / `goldschmidtZone` / band constants / `gapA`
      — Basic.lean — lead — todo — plan §4
- [ ] `tolFac_pos`, `tolFac_eq_distRatio`, `contact_iff_tolFac_one`, `idealA_eq`, `idealA_tolFac`,
      `gapA_pos_iff`, the three `goldschmidtZone_eq_*_iff` rows, `rAMin_one` / `rAMax_one`
      — Basic.lean — lead — todo — plan §4

## G2 — rules layer (`PhotoLean/Goldschmidt/Rules.lean`; owner prover_a)

- [ ] all rows of plan §5 — Rules.lean — prover_a — todo

## G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`; owner prover_b)

- [ ] all rows of plan §6 — Criterion.lean — prover_b — todo

## G4 — sharp conditions (`PhotoLean/Goldschmidt/Sharp.lean`; owner prover_d)

- [ ] all rows of plan §7 — Sharp.lean — prover_d — todo

## G5 — rational decision layer (`PhotoLean/Goldschmidt/RatModel.lean`; owner prover_c)

- [ ] all rows of plan §8 — RatModel.lean — prover_c — todo

## G6 — instance verdicts (`PhotoLean/Goldschmidt/Instances.lean`; owner prover_c)

- [ ] all rows of plan §9 (families I1–I8) — Instances.lean — prover_c — todo

## G7 — closeout (owner lead)

- [ ] relations node / no-edge registry for the Goldschmidt theory (`PhotoLean/Relations.lean`,
      `theories/RELATIONS.md`), README + AGENTS status, bilingual `RESULTS.md`, final verifier run
      — lead — todo
