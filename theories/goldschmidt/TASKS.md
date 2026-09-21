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
- [~] **Lead risk probe**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` — **owner
      prover_a, IN FLIGHT, and it does NOT compile yet** (67 errors measured by `prover_d`, 53 by the
      lead). Honest status: the probe did **not** gate the milestone dispatches (the authority
      compiling plus the provers' own kernel work did), and **no row of it may be cited as kernel
      evidence until it reports exit 0 / 0 errors** — plan §1.2. Four FALSE authority rows were caught
      instead by the milestone provers (`chiTol_anti` in G2; the two `r_O` monotonicity rows and
      `tolFac_rO_const_iff` in G3 — plan §3.1 items 6–9); the probe is being brought to 0 error
      against the corrected signatures
- [~] API calibration (`api_researcher`) → `proofs/API-NOTES.md` § "Goldschmidt theory (2026-09-21)"
      + `theories/goldschmidt/probes/goldschmidt-api-*.lean` (5 probes; the lead independently
      re-ran all five: exit 0 / 0 error each)
- [~] Literature survey (`literature_researcher`) → `theories/goldschmidt/LITERATURE.md` +
      `theories/goldschmidt/literature/INSTANCE-DATA.md`
- [x] Plan landed: `theories/goldschmidt/plan.md` §1–§14
- [x] **Off-kernel exact-rational instance cross-check**:
      `theories/goldschmidt/probes/goldschmidt-instance-check.py` → exit 0, 0 mismatches; exact `t²`
      values and verdicts recorded in plan §9
- [x] `lakefile.toml` `defaultTargets` extended with `PhotoLean.Goldschmidt.Basic` (commit `bdfd681`;
      the remaining five modules are registered one line per module as they land)
- [x] Human confirmation of the design (2026-09-21: directory `theories/goldschmidt/`, full scope
      ①+②+③, module layout G1–G6)

## G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`; owner prover_b; delivered)

> Delivered commit `65cdd32` (213 lines, 29 declarations = 15 definitions + 14 theorems), all
> word-for-word against the corrected authority. Gates reported by the owner and independently
> re-run by the lead: `lake build` OK (0 warning) / `check.sh --strict` `verdict: PASS` /
> `axioms.sh` **14/14** `PASS (only mathlib infrastructure axioms)` / fidelity **29/29**,
> `signature differences: 0`. Owner side-effect: the authority's `goldschmidtZone_eq_tooLarge_iff`
> draft was FALSE on an inverted band and was corrected before delivery (plan §3.1 item 4).

- [ ] definitions `tolFac` / `latticeOf` / `idealAO` / `idealA` / `rAMin` / `rAMax` / `InBand` /
      `GoldschmidtConforms` / `GoldschmidtZone` / `goldschmidtZone` / band constants / `gapA`
      — Basic.lean — prover_b — review — plan §4
- [ ] `tolFac_pos`, `two_div_sqrtTwo`, `latticeOf_div_sqrtTwo`, `tolFac_eq_distRatio`,
      `contact_iff_tolFac_one`, `idealA_eq`, `idealA_tolFac`, `gapA_pos_iff`,
      `goldschmidtZone_eq_tooSmall_iff`, `goldschmidtZone_eq_ideal_iff`,
      `goldschmidtZone_eq_tooLarge_iff` (exact form), `goldschmidtZone_eq_tooLarge_iff_of_band`,
      `rAMin_one`, `rAMax_one` — Basic.lean — prover_b — review — plan §4
      (verifier run 1: batch 1 = G1 + Sprint-0 artifacts)

## G2 — rules layer (`PhotoLean/Goldschmidt/Rules.lean`; owner prover_c; proving)

- [ ] all rows of plan §5 — Rules.lean — prover_c — proving — (dispatched in parallel with G1: the
      rules layer does not import the description layer, so it needed no Basic.lean)
      — author reports **17/18 delivered and all four gates green** (build OK / `check.sh --strict`
      PASS / 12 of 12 `axioms.sh` PASS / fidelity `signature differences: 0`, `not delivered yet: 1`);
      the missing row is `chiTol_anti`, FALSE in the authority and corrected in commit `d6821c4`
      (plan §3.1 item 8; the owner is delivering it in a second commit)

## G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`; owner prover_d; proving)

- [ ] all rows of plan §6 — Criterion.lean — prover_d — proving — (the two headline equivalences
      `conforms_iff_radius_window` and `conforms_iff_sq` are the critical path for G4/G5/G6)
      — **three of its rows were FALSE in the authority and were corrected before delivery**
      (`tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt`: the `rO ↦ t` pole at `rO = -rB` means
      `0 < rO` is not enough — the rows now take `(hB : 0 < rB + rO)`; `tolFac_rO_const_iff`: now takes
      `(hrB : 0 ≤ rB) (hrO : 0 < rO)`. Kernel counterexamples in plan §3.1 items 6–8)

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
