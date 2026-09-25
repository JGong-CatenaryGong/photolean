# theories/FluorPhos/TASKS.md — PhotoLean task board: FluorPhos (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/FluorPhos/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) complete and independently verified
  (verifier run 5, 2026-09-23 PASS), plus the Phase-3 negative-result addition** — **30 of the 30**
  authority declarations are proved in `PhotoLean/FluorPhos/{Basic,Criterion,RatModel,Instances}.lean`
  (`phiP_strictMono_isc`, absent at Phase 2, was delivered and verified by run 5; the Phase-3 row
  `fpC5_firstForm_refuted` was ticked after the final audit); the statement authority compiles
  at 0 errors; batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.
- **Count history (2026-09-24, audit fix F4)**: the Sprint-0 / Phase-2 / verifier-run-5 records
  *below* read "29 of 29" — that was the authority as frozen at Sprint 0 and re-frozen for FP-C5b
  (16 theorems + 13 definitions/structures/inductives). The Phase-3 negative-result row
  `fpC5_firstForm_refuted` (FP-I4, the 30th declaration, 17th theorem) was added afterwards, so the
  current totals are **30 of 30** (fidelity probe 2026-09-24: `skeleton declarations 30`,
  `word-for-word 30`, `not delivered 0`, `signature differences 0`). The historical lines are kept
  as written rather than rewritten.
- **Phase 2 (prover_c, 2026-09-23)**: gate evidence — per-module `proofs/scripts/lake build` exit 0
  for `Basic` / `Criterion` / `RatModel` / `Instances`; `proofs/scripts/check.sh --strict` (whole
  tree) verdict PASS (scan clean); `proofs/scripts/axioms.sh` PASS for all 15 delivered theorems
  (each `depends on axioms: [propext, Classical.choice, Quot.sound]`); fidelity
  `python3 theories/BEP/probes/bep-fidelity.py --theory FluorPhos` = 29/29 word-for-word,
  0 signature differences, 1 not delivered (`phiP_strictMono_isc`).
  The `Rat.*` cast rows were `#print`-checked against the SV-R1 vacuous-identity class: the printed
  right-hand sides are the `PhotoLean.FluorPhos`-level definitions, so the rows are real bridges
  (no STATEMENT-INCIDENT).

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/FluorPhos/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` — **29 declarations**
      (16 theorems + 13 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `2a717f1f51fd0f263513675945694b55a9034bb1e6b1299489d630ac7f96e7f4`
- [x] API calibration probe: `theories/FluorPhos/probes/FluorPhos-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/FluorPhos/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [x] `s1Decay` — Basic.lean — done — proved (Phase 2)
- [x] `phiF` — Basic.lean — done — proved (Phase 2)
- [x] `iscBranch` — Basic.lean — done — proved (Phase 2)
- [x] `t1BranchP` — Basic.lean — done — proved (Phase 2)
- [x] `phiP` — Basic.lean / RatModel.lean — done — proved (Phase 2)
- [x] `FPData` — Basic.lean — done — proved (Phase 2)
- [x] `phiP_eq` — Criterion.lean — done — proved (Phase 2)
- [x] `phiP_div_phiF` — Criterion.lean — done — proved (Phase 2)
- [x] `phiF_add_phiP_le_one` — Criterion.lean — done — proved (Phase 2)
- [x] `phiF_add_phiP_eq_one_iff` — Criterion.lean — done — proved (Phase 2)
- [x] `phiF_strictAnti_isc` — Criterion.lean — done — proved (Phase 2)
- [x] `phiP_strictMono_isc` — delivered 2026-09-23 by the lead on the re-frozen statement (premise `0 < kF + kIC`; route `div_lt_div_iff₀` + `unfold s1Decay` + one `nlinarith`); the prover's five failed routes are in EXPERIENCE.md
- [x] `crossover_isc` — Criterion.lean — done — proved (Phase 2)
- [x] `crossover_isc_threshold` — Criterion.lean — done — proved (Phase 2)
- [x] `hso_zero_no_phosphorescence` — Criterion.lean — done — proved (Phase 2)
- [x] `nonvacuous_competition` — Criterion.lean — done — proved (Phase 2)
- [x] `s1Decay` — Basic.lean — done — proved (Phase 2)
- [x] `phiF` — Basic.lean — done — proved (Phase 2)
- [x] `phiP` — Basic.lean / RatModel.lean — done — proved (Phase 2)
- [x] `Rat.phiF_cast` — RatModel.lean — done — proved (Phase 2); `#print`-checked non-vacuous (real bridge)
- [x] `Rat.phiP_cast` — RatModel.lean — done — proved (Phase 2); `#print`-checked non-vacuous (real bridge)
- [x] `FPZone` — RatModel.lean — done — Phase 2
- [x] `fpZoneQ` — RatModel.lean — done — Phase 2
- [x] `fpZoneQ_phosphorDominant_iff` — RatModel.lean — done — proved (Phase 2)
- [x] `naphthaleneLike` — Instances.lean — done — Phase 2
- [x] `naphthaleneLike_verdict` — Instances.lean — done — proved (Phase 2)
- [x] `eosinLike` — Instances.lean — done — Phase 2
- [x] `eosinLike_verdict` — Instances.lean — done — proved (Phase 2)
- [x] `crossoverWitness_verdict` — Instances.lean — done — proved (Phase 2)

## Sprint 1+ — proof formalization (Phase 2, delivered 2026-09-23 by prover_c)

Rows are claimed one at a time per the plan's sprint order; each claim closes with
`lake build` green before the next is claimed. All rows are at **review** (ticking is lead-only
after a verifier PASS). The one row that was absent (see the history above) is now delivered and
independently verified (verifier run 5, 2026-09-23): the whole theory is 29/29 with 0 signature
differences, 16/16 theorems proved, `#print axioms` 16/16 clean, and the whole-tree strict gate PASS
with the four targets in `defaultTargets`.

## Authority re-freeze — 2026-09-23 (FP-C5 second half, plan §3.1 entry 2)

`phiP_strictMono_isc` was re-frozen with the load-bearing premise `0 < kF + kIC`: the first frozen
form is FALSE at `kF = kIC = 0` (kernel-checked counterexample at `kISC = 1 → 2`, both sides `1/2`;
probe `.lake/tmp/lead_fp_c5_probe.lean`, exit 0). New authority sha256 `2a717f1f51fd0f263513675945694b55a9034bb1e6b1299489d630ac7f96e7f4`.

---

## Verifier run 5 — 2026-09-23 (independent, read-only)

**Verdict: PASS** on the machine gates (build 4/4 re-elaborated from source with no error
diagnostics; whole-tree strict PASS with scan `clean`; `#print axioms` 16/16; fidelity 29/29 with 0
differences, confirmed by the verifier's own extractor that also compares definition BODIES;
definition transcriptions `rfl`-equal to the authority; independent recomputation of the instance
values; a 58 240-point nonnegativity grid with zero violations; adversarial attacks broke only
premise-removed variants).

**The verifier's independent judgement on the FP-C5b re-freeze**: the added premise
`0 < kF + kIC` is *exactly* load-bearing — necessary (strictness cannot be relaxed to `0 ≤`: at
`kF = kIC = 0` both sides equal `kP/(kP+kNR)`) and sufficient (the numerator difference is
`(kF + kIC)·(kISC' − kISC) > 0`). It also proved the prime-side bundle `h'` is derivable, so that
premise is conservative rather than load-bearing.

Findings and resolution:
* **F1 (fixed)** — the plan's §3.1 section was missing and §4 still printed the pre-re-freeze
  premise set; both synced (entries 0–3 + the corrected FP-C5 row).
* **F2 (fixed)** — the board still said "28 of 29" / "NOT DELIVERED" / "one row deliberately
  absent"; all synced and the rows ticked on this PASS.
* **F3 (fixed)** — the Criterion module header claimed `h` + `h'` supply `0 < kF + kIC` (refuted by
  the kernel) and said no premise had changed; the prose and the row docstring are corrected.
* **F4 (fixed)** — the delivered modules cited only the Phase-1 authority hash; they now cite the
  re-frozen hash with the Phase-1 prefix as history, and this board keeps both.
* **F5 (fixed)** — `RESULTS.md` status synced.
* **F6 (registered)** — the batch headline count: the authorities carry **279 declarations**, of
  which **182 are theorem rows** (the "180 registered placeholder theorems" of Phase 1 grew by the
  two rows added during the batch: `Forster.kappaSq_le_four`'s companion witness rows are counted
  inside, and the auxiliary rows are extra); the Fidelity sweep reports 279/279 word-for-word.
  The accurate statement for the final report: **every registered theorem row is delivered**.
* **F7 (fixed)** — the API-NOTES statement-change index rows 5/6 were malformed by an earlier
  edit; repaired.
* Premise residue (F3 of the verifier's own list): `crossover_isc`'s `hkF`/`hkP`,
  `crossover_isc_threshold`'s and `fpZoneQ_*`'s `hkF`, `hso_zero_no_phosphorescence`'s `h`, and
  FP-C5b's `h'` — queued for the Phase-3 premise audit with the verifier's stripped-form proofs.

## Phase-3 additions (2026-09-23)

- `fpC5_firstForm_refuted` (FP-I4, negative-result finalization): the first frozen FP-C5 second
  half refuted at `kF = kIC = 0, kISC = 1 → 2` (both yields `1/2`). Authority sha256 `2a717f1f51fd0f263513675945694b55a9034bb1e6b1299489d630ac7f96e7f4`.
- Five premise trims (crossover_isc, crossover_isc_threshold, hso_zero_no_phosphorescence,
  fpZoneQ_phosphorDominant_iff, phiP_strictMono_isc) — plan §3.1 entry 3.

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entries 3–4): five premise trims + the `fpC5_firstForm_refuted` negative-result row (FP-I4). All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).

### Phase-3 additions

- [x] `fpC5_firstForm_refuted` — delivered — Phase 3 — done — `PhotoLean/FluorPhos/Instances.lean` (FP-I4, the negative-result finalization; verifier final audit PASS 2026-09-23)

Rows FP-I1..I3 and this addition: Phase-3 additions (FP-I4) ticked after the final audit.

## Linter residue (registered 2026-09-24, audit fix F6c)

- `PhotoLean/FluorPhos/RatModel.lean:89`'s `fpZoneQ (kF kISC kIC kP kNR : ℚ)` keeps the binder
  `kIC` although the classifier body never uses it: the verdict compares `kISC * kP` with
  `kF * (kP + kNR)`, and `kIC` cancels in the φ_P/φ_F ratio, so the binder is part of the uniform
  five-rate interface rather than a premise. The build therefore prints `unused variable 'kIC'`
  by design, and no `set_option linter.unusedVariables false` is added (a code edit to a delivered
  module would void its recorded verification; the warning itself reaches no gate — the strict scan
  looks for placeholder/axiom keywords, and no delivered row consumes the binder). The other two
  residue sites (SternVolmer's ℝ and ℚ `tauRatioStat`) are registered on
  `theories/SternVolmer/TASKS.md`.

## Authority hash record (2026-09-24, audit fix F5)

`sha256sum theories/FluorPhos/probes/FluorPhos-statement-skeleton.lean` recomputed 2026-09-24; the
blob at each revision is recoverable from git (`git show <rev>:<path> | sha256sum`). The delivered
modules' docstrings cite the value of the FP-C5b re-freeze, which is one revision behind the
current file — recorded here so the citation is traceable rather than stale-looking:

- `5158987` (Phase-1 freeze): `2aa08f1c153b6494…` (never recorded on this board)
- `488f51d` (FP-C5b re-freeze, 2026-09-22): `b116adddea484896f7068c00141989d70871db4f51fe36749a2dbc44e24f4480` — **the value cited in `PhotoLean/FluorPhos/*` docstrings**
- `ba1dfa4` (Phase-3 premise trims): `38f5bc0a906a727e…`
- `45f60b5` (FP-I4 negative-result row, 2026-09-23): `2a717f1f51fd0f263513675945694b55a9034bb1e6b1299489d630ac7f96e7f4` — **current** (recorded at the Sprint-0 block, the re-freeze section and the Phase-3 section above)
