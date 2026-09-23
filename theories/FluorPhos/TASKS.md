# theories/FluorPhos/TASKS.md — PhotoLean task board: FluorPhos (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/FluorPhos/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) complete and independently verified
  (verifier run 5, 2026-09-23 PASS)** — 29 of the 29
  authority declarations are proved in `PhotoLean/FluorPhos/{Basic,Criterion,RatModel,Instances}.lean`
  (all except `phiP_strictMono_isc`, reported closed by the lead 2026-09-23 (route: div_lt_div_iff₀ + nlinarith)); the statement authority compiles
  at 0 errors; batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.
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
