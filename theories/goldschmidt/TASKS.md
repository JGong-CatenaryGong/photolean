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
- **Sprint-0 kernel evidence**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` — **not yet
  evidence**: it does not compile yet (see the Sprint-0 row below and plan §1.2/§11). No row of it may
  be cited as kernel evidence until it reports exit 0 / 0 errors.
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
- [~] **Sprint-0 risk probe**: `theories/goldschmidt/probes/goldschmidt-risk-probe.lean` — **owner
      prover_a; it COMPILES: measured raw at the lead's run `proofs/scripts/lake env lean <file>` →
      exit 0, 0 errors, 35 placeholder warnings, 0 other diagnostics, 819 lines (commits `d96a626` →
      `3d39dde`), with 105 of the 139 authority rows closed by real proofs and 34 placeholders.** It is
      **not** an acceptance artifact and never was: `proofs/ENGINE.yml` sets `SOURCE_DIRS="PhotoLean"`,
      so the file lives outside the gate's scan range by design and no `check.sh --strict` covers it —
      its status is an artifact claim, and the earlier claim that it was 0-error evidence was wrong
      (recorded in `proofs/EXPERIENCE.md`). Honest status: the probe did **not** gate the milestone dispatches (the authority
      compiling plus the provers' own kernel work did), and **no row of it may be cited as kernel
      evidence until it reports exit 0 / 0 errors** — plan §1.2. Four FALSE authority rows were caught
      instead by the milestone provers (`chiTol_anti` in G2; the two `r_O` monotonicity rows and
      `tolFac_rO_const_iff` in G3 — plan §3.1 items 6–8); the probe is being brought to 0 error
      against the corrected signatures
- [~] API calibration (`api_researcher`) → `proofs/API-NOTES.md` § "Goldschmidt theory (2026-09-21)"
      + `theories/goldschmidt/probes/goldschmidt-api-*.lean` (7 probes; the lead and the verifier independently
      re-ran all seven: exit 0 / 0 error each; the probes themselves are committed with the
      API-NOTES entry)
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

## G1 — description layer (`PhotoLean/Goldschmidt/Basic.lean`; owner prover_b; **VERIFIED — verifier run 1 PASS**)

> **Verifier run 1 (independent, batch 1 = G1 + the Sprint-0 artifacts): PASS — 0 HIGH / 6 MEDIUM / 9
> LOW.** All 15 findings are in the record layer (plan/board/API-NOTES wording, the probe's status, and
> the fidelity checker's milestone-scope blind spot); no delivered declaration was invalidated. The
> verifier re-ran all four gates itself (14/14 `axioms.sh`, bare `check.sh --strict` PASS, and the
> clean-tree `git archive` re-runs at `65cdd32`/`bdfd681`), re-derived the six instance `t²` values
> independently (identical to plan §9), and tried to break the four classifier rows with a
> **1000-point exact-rational search including 450 inverted bands and 100 degenerate bands: 0
> violations**. The lead has disposed of M1–M6 and L1–L9 in the record (M1/M2/M3 with api_researcher).

> Delivered commit `65cdd32` (213 lines, 29 declarations = 15 definitions + 14 theorems), all
> word-for-word against the corrected authority. Gates reported by the owner and independently
> re-run by the lead: `lake build` OK (0 warning) / `check.sh --strict` `verdict: PASS` /
> `axioms.sh` **14/14** `PASS (only mathlib infrastructure axioms)` / fidelity **29/29**,
> `signature differences: 0`. Owner side-effect: the authority's `goldschmidtZone_eq_tooLarge_iff`
> draft was FALSE on an inverted band and was corrected before delivery (plan §3.1 item 4).

- [x] definitions `tolFac` / `latticeOf` / `idealAO` / `idealA` / `rAMin` / `rAMax` / `InBand` /
      `GoldschmidtConforms` / `GoldschmidtZone` / `goldschmidtZone` / band constants / `gapA`
      — Basic.lean — prover_b — done — (verifier run 1 PASS) — plan §4
- [x] `tolFac_pos`, `two_div_sqrtTwo`, `latticeOf_div_sqrtTwo`, `tolFac_eq_distRatio`,
      `contact_iff_tolFac_one`, `idealA_eq`, `idealA_tolFac`, `gapA_pos_iff`,
      `goldschmidtZone_eq_tooSmall_iff`, `goldschmidtZone_eq_ideal_iff`,
      `goldschmidtZone_eq_tooLarge_iff` (exact form), `goldschmidtZone_eq_tooLarge_iff_of_band`,
      `rAMin_one`, `rAMax_one` — Basic.lean — prover_b — done — (verifier run 1 PASS) — plan §4

## G2 — rules layer (`PhotoLean/Goldschmidt/Rules.lean`; owner prover_c; **VERIFIED — verifier run 2 PASS**)

- [x] all rows of plan §5 — Rules.lean — prover_c — done — (verifier run 2 PASS) — commits
      `52e204e`/`931e350`/`40d8d09` (the third drops the two non-load-bearing premises of
      `radiusMatch_comp_ratchet`, plan §3.1 item 11, and re-proves it by the triangle route),
      **18/18**, gates green (build / `check.sh --strict` / 13 of 13 `axioms.sh` both by the owner and
      by the lead / fidelity 18/18 `0 differences`). Milestone delivered — (dispatched in parallel with G1: the
      rules layer does not import the description layer, so it needed no Basic.lean)
      — author reports **17/18 delivered and all four gates green** (build OK / `check.sh --strict`
      PASS / 12 of 12 `axioms.sh` PASS / fidelity `signature differences: 0`, `not delivered yet: 1`);
      the missing row is `chiTol_anti`, FALSE in the authority and corrected in commit `d6821c4`
      (plan §3.1 item 8; the owner is delivering it in a second commit)

## G3 — law layer (`PhotoLean/Goldschmidt/Criterion.lean`; owner prover_d; **VERIFIED — verifier run 2 PASS**)

- [x] all rows of plan §6 — Criterion.lean — prover_d — done — (verifier run 2 PASS; its one HIGH was
      the record-layer docstring sentence corrected in `82e2089`) — commit `2ca5f2c`, **24/24**
      plus 8 `private` helpers, gates green (lead re-ran all 24 `axioms.sh` independently: 24/24) — (the two headline equivalences
      `conforms_iff_radius_window` and `conforms_iff_sq` are the critical path for G4/G5/G6)
      — **three of its rows were FALSE in the authority and were corrected before delivery**
      (`tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt`: the `rO ↦ t` pole at `rO = -rB` means
      `0 < rO` is not enough — the rows now take `(hB : 0 < rB + rO)`; `tolFac_rO_const_iff`: now takes
      `(hrB : 0 ≤ rB) (hrO : 0 < rO)`. Kernel counterexamples in plan §3.1 items 6–8)

## G4 — sharp conditions (`PhotoLean/Goldschmidt/Sharp.lean`; owner prover_b; **VERIFIED — mechanical re-run + batch-3 follow-up + bounded acceptance run, all PASS, zero HIGH**)

- [x] all rows of plan §7 (12 theorems: the two edge-failure rows, the point-band row, the
      substitution transfer, the 15 %-rule → Δt bridge, `tolFac_irrational`, and the five witnesses)
      — Sharp.lean — prover_b — **done** — verifier run 3 measured its gate battery green (build,
      bare gate PASS, fidelity 12/12, `axioms.sh` PASS) with no HIGH but declined a verdict; the
      batch-3 follow-up then completed exactly the three unchecked items and returned **PASS**, and
      the mechanical re-run and the bounded acceptance run (whose `axioms.sh` sweep covers 98/98
      public theorems) returned **PASS** as well — see the acceptance records — commits `cd09ef1` +
      `af9429a` (the point-band row re-delivered after the authority dropped its unconsumed premise,
      plan §3.1 item 9); owner-reported gates: build OK /
      `check.sh --strict` PASS / 12 of 12 `axioms.sh` PASS / fidelity 12/12 `0 differences`.
      Owner finding: `conforms_point_band_iff`'s `0 < rB + rO` premise is never consumed → the
      authority dropped it (plan §3.1 item 9) and the row was re-delivered in `af9429a`.

## G5 — rational decision layer (`PhotoLean/Goldschmidt/RatModel.lean`; owner prover_c; **VERIFIED — mechanical re-run + batch-3 follow-up + bounded acceptance run, all PASS, zero HIGH**)

- [x] all rows of plan §8 — RatModel.lean — prover_c — **done** — same history as G4 (run 3 green
      but declined; superseded by the batch-3 follow-up, the mechanical re-run and the bounded
      acceptance run, all **PASS** — see the acceptance records) — commits `65985fe` + `67a58a4`,
      **22/22**, gates green (lead re-ran all 12 `axioms.sh`: 12/12); the second commit drops the two
      unconsumed premises of `inBandQ_ideal_iff` (plan §3.1 item 10)

## G6 — instance verdicts (`PhotoLean/Goldschmidt/Instances.lean`; owner prover_d; **VERIFIED — mechanical re-run + batch-3 follow-up + bounded acceptance run, all PASS, zero HIGH**)

- [x] all rows of plan §9 (families I1–I8) — Instances.lean — prover_d — **done** — same history as
      G4/G5 (run 3 green but declined; superseded by three **PASS** verdicts — see the acceptance
      records); its 23 verdicts are additionally
      covered by the off-kernel exact-rational script with 0 mismatches and by run 1's independent
      recomputation of the same numbers — commit
      `427609b`, **34/34**, gates green (owner-reported build / `check.sh --strict` / 23 of 23
      `axioms.sh` / fidelity 34/34; the lead re-ran the 23-row `axioms.sh` sweep: 23/23); the
      off-kernel exact-rational cross-check exits 0 with 0 mismatches. Owner finding: the strict scan
      caught one comment line beginning with `constant` (the keyword-allow-list is matched by a
      line-wise grep over comments too) — reworded, recorded in the experience bank

## G7 — closeout (owner lead)

- [x] relations node / no-edge registry for the Goldschmidt theory (`PhotoLean/Relations.lean` §10,
      `theories/RELATIONS.md` §1/§2.5/§3 N4), with the measured import facts and the N4 shape look-alike
      against Sabatier — commit `c045fe5`; `Relations.lean` rebuilt and gate-clean — lead — done
- [x] README sixth-theory status entry (modules, 139 declarations, fidelity 139/139) and the
      six-theory relation-graph bullet — commit `b5e28d8` — lead — done
- [x] bilingual `RESULTS.md` (the single human-facing deliverable, English original + Chinese
      rendering per section) — commits `b3e2e69`/`f95a704`/`671b082` — lead — done
- [x] literature round 1 incorporated into `plan.md` §1.1/§2/§9/§12 and `RESULTS.md` §6 (the primary
      source retrieved: the factor and the `0.8–1.0` band are Goldschmidt's own, the `[1, 11/10]` band
      is declared with no printed support, the 15 % reference is the *smaller* ion, the charge rule is a
      later systematization) — commits `671b082`/`f95a704` — lead — done
- [x] instance docstrings aligned with the literature record (the `SrTiO₃` printed-vs-derived flip, the
      `LaMnO₃` spin state and the unverified `Mn³⁺` radius, the documented coupled-substitution
      citations replacing the undocumented `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺`) — lead — done (comment-only,
      commit `e1ce442`)
- [x] final verifier runs recorded in the acceptance table below (runs 1/2/3, the mechanical run, the bounded acceptance run and the batch-3 follow-up) — lead — done

---

## Verification boundary at closeout (what is verifier-issued and what is lead-measured)

- **Verifier-issued (independent role, read-only, own probes):** run 1 — G1 + the Sprint-0 artifacts,
  **PASS**, 0 HIGH; run 2 — G2 + G3, **PASS**, one record-layer HIGH and one real defect (both fixed
  in the same round), plus an independent re-proof of the 8 `private` helpers of `Criterion.lean`.
  Those are the ticks above.
- **Verifier-measured but verdict-declined:** run 3 — the gate battery of G4/G5/G6 (three modules
  build, bare `check.sh --strict` PASS, fidelity 12/22/34 with 0 differences, `axioms.sh` **47/47**)
  came back green with **no HIGH**; the run declined PASS/FAIL because three items were unfinished.
- **Lead-measured (recorded as such, not as independent verification):** the documentation audit
  (counts 139 public declarations / 98 public theorems recomputed from the sources; all 7 signatures
  quoted in `RESULTS.md` §3 verified word-for-word); the post-commit re-runs at `40d8d09`/`ed4f580`
  for the G2 follow-up and the tree-drift finding; the evaluator-route measurement
  (`proofs/EXPERIENCE.md`).
- **All five verification lines have since returned:** run 1 **PASS**, run 2 **PASS**, the mechanical
  re-run **PASS**, run 3's follow-up **PASS**, the bounded acceptance run **PASS** — **zero HIGH findings
  anywhere**, and the two verifier-issued MID/LOW classes that touched an artifact (the false docstring,
  the over-strong hypothesis) plus every record-layer finding are disposed. The G4/G5/G6 rows are
  therefore ticked on verifier verdicts, and the only items left open are documentation-level and
  registered: the literature round-2 tasks (`LITERATURE.md` §OUT: two citation defects, the OCR page
  check of Skrifter VII p. 79–83, and pp. 112–117 unread).

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| batch | scope | verdict | key evidence |
|---|---|---|---|
| Run 1 (independent verifier; batch 1 = G1 + the Sprint-0 artifacts) | `PhotoLean/Goldschmidt/Basic.lean` (29 declarations) + authority skeleton, 5 API probes, the off-kernel instance script, contract/lakefile registration, plan/board/experience | **PASS** — 0 HIGH / 6 MEDIUM / 9 LOW | verifier re-ran all four gates (14/14 `axioms.sh`, bare `check.sh --strict` PASS, clean-tree `git archive` re-runs at `65cdd32`/`bdfd681`); 1000-point exact-rational search over the four classifier rows (450 inverted + 100 degenerate bands) with **0 violations**; independent recomputation of all six instance `t²` values, identical to plan §9; all 15 findings were record-layer only and were disposed in `fdb9899` (M1–M3 with `api_researcher`) |
| Run 2 (independent verifier; batch 2 = G2 + G3) | `Rules.lean` (18) + `Criterion.lean` (24 + 8 `private` helpers), the corrected `r_O` rows and `chiTol_anti` | **PASS** (one HIGH, record layer) | verifier re-ran build / `check.sh --strict` / **37/37** `axioms.sh` / fidelity (G2 18/18, G3 24/24, 0 differences) and repeated the fidelity+build+gate runs on clean `git archive` copies of `931e350` and `2ca5f2c` (file md5s identical to the commits); it re-proved all **8 `private` helpers** of `Criterion.lean` independently (8/8 consumed, no dead helper) and adversarially re-derived every corrected row, finding each remaining hypothesis load-bearing with kernel counterexamples (`hB` for the `r_O` rows, `hrB` for the constant row, the direction of `chiTol_anti`, all four premises of `conforms_iff_sq`, `hc ≠ 0`, `rO ≠ 0`). Findings: **H1** — the delivered `Criterion.lean` docstrings repeated the FALSE sentence "at `δ > 1` the band is empty" (record layer; the theorem is unaffected) → fixed in the same round; **M1** — `radiusMatch_comp_ratchet`'s `hr1`/`htau1` are **non-load-bearing** → removed from the authority (plan §3.1 item 11) and re-delivery asked of the owner; M2/M3/M4 + L1–L4 — plan/TASKS table sync, a phantom §5 row, stale board rows and two ownership mismatches → all fixed. |
| Lead-measured audit (recorded as *not* an independent verifier verdict) | the documentation-plane items batch 3 did not reach: (b) the counts and (c) the quoted signatures | **all verified, raw evidence** | (b) mechanical recount from the six sources: `Basic.lean` 14 defs + 1 inductive + 14 theorems = 29, `Rules.lean` 5 + 13 = 18, `Criterion.lean` 24 theorems (+ **8** `private` helpers), `Sharp.lean` 12, `RatModel.lean` 10 + 12 = 22, `Instances.lean` 11 + 23 = 34 → **139 public declarations, 98 public theorems**, exactly as plan §4–§9 and `RESULTS.md` §8 claim; (c) all **7** signatures quoted in `RESULTS.md` §3 match the delivered files word-for-word. Also recorded from the same audit: an evaluator-based second route (`#eval decide`) covers the three `zoneQ` classifier rows but **cannot** cover `inBandQ`/`ChargeBalanced` (Decidable synthesis fails) or `tolFacSq` (`noncomputable`) — `proofs/EXPERIENCE.md`. |
| G2 follow-up (verifier finding M1) | the `radiusMatch_comp_ratchet` premise drop | **fixed and verified** | the owner re-delivered the row in `40d8d09` (triangle route, only `0 ≤ tau`, shorter by 7 lines, no unused-hypothesis lint); the lead re-ran at that commit: build OK, `check.sh --strict` PASS, **13/13** `axioms.sh`, fidelity G2 18/18 `0 differences`; whole-theory fidelity is back to **139/139, 0 differences** |
| Run 3 (independent verifier; batch 3 = G4 + G5 + G6 + documentation plane + the frozen tree) | `Sharp.lean` (12) + `RatModel.lean` (22) + `Instances.lean` (34), the risk probe, plan/TASKS/LITERATURE/RESULTS/API-NOTES/README/Relations/lakefile | **INCOMPLETE** (code face green, no HIGH) | measured at tree `b3e2e69`: the three modules build, the bare `check.sh --strict` prints `verdict: PASS` with all six theory directories at 5/5, fidelity is 139/139 (G4 12/12, G5 22/22, G6 34/34, 0 differences) and `axioms.sh` is **47/47 PASS** (45 × `[propext, Classical.choice, Quot.sound]`, 2 × `[Quot.sound]` for the charge rows; `sorryAx` 0). It did **not** reach the instance recomputation, the adversarial attempts or the documentation audit (a)–(f), so it declined to give PASS/FAIL. Its two MEDIUM findings are disposed: the acceptance-tree drift (the gates were re-run at `ed4f58066b288deda34027339fb5a434e8343580` by the lead — `build: OK`, `verdict: PASS`) and the risk probe's evidence status (the probe is **outside `SOURCE_DIRS` by design**, so no gate covers it; its raw compile state is now recorded in the Sprint-0 board row). Its LOW (the `SrTiO₃` docstring's "below 1" possibly contradicting the delivered `t > 1`) is fixed by naming the radius compilation in the docstring. A bounded follow-up run for the three un-checked items was dispatched; it returned **PASS** (0 HIGH / 0 MEDIUM / 2 LOW) — recorded in the three rows below. |
| Mechanical re-run (independent verifier; the five modules' gate battery + an independent recomputation) | `Rules`/`Criterion`/`Sharp`/`RatModel`/`Instances` + the instance layer | **PASS** (2 LOW, record layer) | five modules build; bare `check.sh --strict` PASS with all six theory directories at 5/5; fidelity 139/139 and 12/22/34 per milestone, `0 differences`; `axioms.sh` **47/47** (plus `RatModel` 12/12), no `sorryAx`; **its own recomputation of all 23 instance rows: 23/23 confirmed, 0 contradictions**; source hashes frozen across two measurements; LOW-1 (the statement change was missing from `API-NOTES`) and LOW-2 (duplicate acceptance rows) were both fixed in the follow-up doc round |
| Batch-3 follow-up (independent verifier; the three items run 3 left unchecked) | G4–G6 gates + the instance recomputation + the adversarial round + the documentation audit | **PASS** (0 HIGH / 0 MEDIUM / 2 LOW) | at `HEAD = 7097e5b`: build, bare gate PASS, fidelity 139/139, `axioms.sh` 47/47; **its own 23-row recomputation: 0 contradictions** (BaNiO₃ margin 0.03212 reproduced); **adversarial round done**: kernel counterexamples proving the named hypotheses load-bearing (`zoneQ_eq_zone` without `0 ≤ rA + rO`, `tolFac_rO_const_iff` without `0 ≤ rB`, `conforms_iff_radius_window` without `0 < rB + rO`), negative-assertion probes that fail to typecheck, and a **248 832-tuple** degenerate-input search (0 violations inside the hypothesis domain, non-vacuity witnesses inside it); counts 139/98 and the 7 RESULTS-quoted signatures verified; LOW-1 (`Relations.lean`'s grep wording) and LOW-2 (the charge-pair phrasing) fixed in the follow-up doc round |
| Bounded acceptance run (independent verifier; the wrap-up acceptance) | G2–G6 + the documentation plane | **PASS** (0 HIGH / 2 MEDIUM / 8 LOW) | six modules build; bare gate PASS; `axioms.sh` **98/98 public theorems** (so `Sharp`'s 12 and `RatModel`'s 12 are now covered too); fidelity 139/139; the Sprint-0 probe independently re-run (exit 0, 0 errors, 35 placeholders — matching the board); its own recomputation 23/23 with 0 divergence; counts 139/98 verified; `defaultTargets` complete. MEDIUM-1: the "`Instances` ← all five" import fact was **wrong** (it imports four, not `Sharp`) → fixed in plan/Relations/RELATIONS. MEDIUM-2 (with the mechanical run's LOW-1): the statement changes were missing from `API-NOTES` → an index section is appended. LOW-1…LOW-8: the BaNiO₃ margin direction, the instance-script's float label, two plan cross-references, the duplicate acceptance rows, the `Relations.lean` grep wording, the `RELATIONS.md` Chinese count, and the I1/I3 family label → all fixed |
