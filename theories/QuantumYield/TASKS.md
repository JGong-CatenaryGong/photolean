# theories/QuantumYield/TASKS.md — PhotoLean task board: QuantumYield (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/QuantumYield/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) delivered by prover_b, awaiting independent
  verifier judgement** — all 29 authority declarations transcribed verbatim into
  `PhotoLean/QuantumYield/{Basic,Criterion,RatModel,Instances}.lean`, 19/19 theorems proved, no
  unproved placeholder and no custom axiomatic declaration anywhere in the delivered tree. Batch:
  photophysics subgraph (groups A–D), dispatched 2026-09-22; Phase-2 run 2026-09-23.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/QuantumYield/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` — **29 declarations**
      (19 theorems + 10 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `967a11a1c788096d8fef39c90e62fd7e4cb5a2747efd3eb7e6621d2ca7b46a90`
- [x] API calibration probe: `theories/QuantumYield/probes/QuantumYield-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/QuantumYield/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `review`; ticking is lead-only after verifier PASS)

- [x] `totalRate` — `PhotoLean/QuantumYield/Basic.lean` — Phase 2 — done — QY-B1, build exit 0
- [x] `yieldOf` — `PhotoLean/QuantumYield/Basic.lean` — Phase 2 — done — QY-B2, build exit 0
- [x] `tauOf` — `PhotoLean/QuantumYield/Basic.lean` — Phase 2 — done — QY-B3, build exit 0
- [x] `QYData` — `PhotoLean/QuantumYield/Basic.lean` — Phase 2 — done — QY-B4, build exit 0
- [x] `sum_yieldOf_eq_one` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [ ] `yieldOf_eq_mul_tauOf` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 3 re-freeze
      (plan §3.1 entry 1) — **review** — `QYData` premise dropped (verifier run 2: non-load-bearing;
      stripped form re-proved by prover_b 2026-09-23; build + axioms + fidelity PASS on the changed
      row); awaits verifier re-check of the re-frozen row
- [x] `yieldOf_nonneg` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_le_one` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_pos_iff` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_div_yieldOf` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `totalRate_cons` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_cons_zero` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_cons_succ` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `yieldOf_cons_succ_factor` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done —
      proved, axioms PASS
- [x] `yieldOf_cons_lt` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done — proved,
      axioms PASS
- [x] `totalRate_zero_counterexample` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done —
      proved, axioms PASS
- [x] `nonvacuous_all_channels_live` — `PhotoLean/QuantumYield/Criterion.lean` — Phase 2 — done —
      proved, axioms PASS
- [x] `Rat.totalRate` — `PhotoLean/QuantumYield/RatModel.lean` — Phase 2 — done — QY-R1, build
      exit 0
- [x] `Rat.yieldOf` — `PhotoLean/QuantumYield/RatModel.lean` — Phase 2 — done — QY-R1, build
      exit 0
- [x] `Rat.QYData` — `PhotoLean/QuantumYield/RatModel.lean` — Phase 2 — done — QY-R1 incl. the
      `Decidable` instance, build exit 0
- [x] `Rat.totalRate_cast` — `PhotoLean/QuantumYield/RatModel.lean` — Phase 2 — done — proved,
      axioms PASS, `#print`-inspected (real bridge, not the shadow identity)
- [x] `Rat.yieldOf_cast` — `PhotoLean/QuantumYield/RatModel.lean` — Phase 2 — done — proved,
      axioms PASS, `#print`-inspected (real bridge, not the shadow identity)
- [x] `fluoresceinS1` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done — QY-I1, build
      exit 0
- [x] `quinineLike` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done — QY-I2, build
      exit 0
- [x] `quenchDilution` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done — QY-I3, build
      exit 0
- [x] `inst_fluoresceinS1_phiF` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done —
      proved (`φF = 9/10`), axioms PASS
- [x] `inst_quinineLike_phiF` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done — proved
      (`φF = 11/20`), axioms PASS
- [x] `inst_quenchDilution_phiF` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 — done —
      proved (`φF = 18/29`), axioms PASS
- [x] `inst_quenchDilution_sternVolmer` — `PhotoLean/QuantumYield/Instances.lean` — Phase 2 —
      review — proved (ratio `29/20`), axioms PASS

## Sprint 1 — proof formalization (Phase 2): delivery record (prover_b, 2026-09-23)

Area ownership for this run: `PhotoLean/QuantumYield/*.lean` and this board (the lead dispatched
the QuantumYield proofs to prover_b; plan §6 names prover_c — the dispatch supersedes the plan's
sprint-order line, recorded here for traceability).

Gates re-runnable as-is (raw results of the delivery run):

| gate | command | result |
|---|---|---|
| build | `proofs/scripts/lake build PhotoLean.QuantumYield.{Basic,Criterion,RatModel,Instances}` | exit 0 each, zero warnings |
| axioms | `proofs/scripts/axioms.sh <module> <namespace-qualified theorem>` | PASS on all 19 theorems; only `propext Classical.choice Quot.sound` |
| strict gate | `proofs/scripts/check.sh --strict` (whole tree) | exit 0, scan clean, 16/16 leaf planes |
| fidelity | `python3 theories/BEP/probes/bep-fidelity.py --theory QuantumYield` | 29/29 word-for-word, 0 signature differences, 0 declarations outside the authority |
| commits | — | `5daa642` (QY1 Basic), `5865874` (QY2 Criterion), `08c3bbf` (QY3 RatModel), `4dff991` (QY4 Instances) |

Statement-incident check (the batch's namespace-shadowing pitfall, SV-R1): a `Rat.`-prefixed
declaration elaborates its own *type* inside the `Rat` namespace, so an unqualified right-hand side
would silently collapse the cast row to `↑x = ↑x`. Both `Rat` cast rows were `#print`-inspected in a
scratch probe after proving: the printed types carry the fully-qualified
`PhotoLean.QuantumYield.totalRate` / `.yieldOf` on the right, i.e. the intended bridges. **No
statement incident for this theory** — the authority's right-hand sides are already fully qualified.

Recorded premise notes (statement layer untouched, signatures verbatim):
* QY-C2 (`yieldOf_eq_mul_tauOf`) and QY-C6 third form (`yieldOf_cons_succ`) carry the frozen premise
  `h : QYData k` that their proofs do not consume — both identities are definitional in the
  totalized-division model. The premise stays (signature fidelity; frozen Phase-1 statement) and the
  `unusedVariables` linter is disabled locally on exactly those two rows, in the repository's
  established style, so the build stays warning-free without hiding any other warning.

Lead action outside this area (not written by prover_b — file not owned): `lakefile.toml`
`defaultTargets` does not list the four `PhotoLean.QuantumYield.*` modules (ENGINE.md §1.1: the scan
covers the whole directory while a bare `check.sh --strict` build does not). Add the four lines
before this theory is closed; the per-module builds above are green meanwhile.

## Sprint 1+ — verifier judgement (pending)

Rows above move `review → done` only on an independent verifier PASS, by the lead. A verifier is
asked to re-run the four gates of the table, plus the `#print` inspection of the two `Rat` cast rows
and the load-bearing-premise row QY-C8 (`totalRate_zero_counterexample`).

---

## Verifier run 2 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence: four modules rebuilt from source, zero diagnostics;
whole-tree `check.sh --strict` PASS with scan `clean` (targets in `defaultTargets` since `d4d34e9`);
`#print axioms` 19/19 PASS; fidelity 29/29, 0 differences; the two `Rat.*_cast` rows `#print`-checked
as real bridges; instance verdicts recomputed independently (φ = 9/10, 11/20, 18/29; SV ratio 29/20);
attacks: removing `total_pos`/`QYData` broke exactly the rows the plan says need them
(`sum_yieldOf_eq_one`, `yieldOf_cons_succ_factor`, `yieldOf_cons_lt`), while `yieldOf_cons_succ`
survives without the bundle (definitional under totalized division) — matching the authority's
premise notes; **no delivered form broke**.

Findings: L2 board staleness (fixed 2026-09-23: `defaultTargets` and the literature row);
L3 `RESULTS.md` still Phase-1 text (fixed); L6 premise residue on QY-C2 / QY-C6-third-form
(carried to the Phase-3 premise audit).

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entries 1–2): `yieldOf_eq_mul_tauOf` and the third cons row dropped their `QYData` premises (definition-level identities); the two linter suppressions were removed with them. All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).
