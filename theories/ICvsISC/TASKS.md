# theories/ICvsISC/TASKS.md — PhotoLean task board: ICvsISC (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/ICvsISC/plan.md`.
- Status of this theory: **Phase 1 (statement formalization) complete**; **Phase 2 (proof layer)
  delivered 2026-09-23 by prover_a** — all four modules (`Basic`, `Criterion`, `RatModel`,
  `Instances`) build, the board rows below are at `review`, and the batch awaits an independent
  verifier run. The Phase-1 statement layer is unchanged (no statement edit was needed).
  Batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/ICvsISC/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` — **20 declarations**
      (14 theorems + 6 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `07d1201c31dfd81ba373706b441ecbd7cafaa193b1404ce05c7029944475977e`
- [x] API calibration probe: `theories/ICvsISC/probes/ICvsISC-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/ICvsISC/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all rows at `review` after the Phase-2 delivery; ticking is lead-only after
### verifier PASS)

- [x] `fcBarrier` — `Basic.lean` — Phase 2 — done — FC-B1; body verbatim from the authority
- [x] `cert_fcBarrier` — `Basic.lean` — Phase 2 — done — FC-B1; `rfl`; build + strict + axioms PASS
- [x] `icRate` — `Basic.lean` — Phase 2 — done — FC-B2; body verbatim from the authority
- [x] `cert_icRate` — `Basic.lean` — Phase 2 — done — FC-B2; `unfold` + `rfl`; gates PASS
- [x] `iscRate` — `Basic.lean` — Phase 2 — done — FC-B3; explicit `HSO ^ 2` prefactor
- [x] `FCData` — `Basic.lean` — Phase 2 — done — FC-B4; five positivity fields, transcribed
- [x] `rate_ratio_eq` — `Criterion.lean` — Phase 2 — done — FC-C1; `div_mul_div_comm` +
      `Real.exp_sub`; gates PASS. **Decorative-premise note:** the `FCData` hypothesis is not
      consumed (the factorization holds for totalized division unconditionally); kept verbatim,
      local linter option, registered for the Phase-3 premise audit
- [x] `log_rate_ratio` — `Criterion.lean` — Phase 2 — done — FC-C2; `Real.log_mul` +
      `mul_div_assoc` + `Real.log_pow` + `Real.log_exp`; gates PASS
- [x] `isc_dominates_iff` — `Criterion.lean` — Phase 2 — done — FC-C3; `Real.log_lt_log_iff` +
      FC-C2 + `div_pos_iff_of_pos_right`; gates PASS
- [x] `spin_discount` — `Criterion.lean` — Phase 2 — done — FC-C4; FC-C3 + `Real.log_neg`;
      gates PASS
- [x] `hso_zero_isc_absent` — `Criterion.lean` — Phase 2 — done — FC-C5; gates PASS.
      **Decorative-premise note:** `h0 : HSO = 0` does not occur in the frozen conclusion (the row
      writes the literal `0` in the `HSO` slot); kept verbatim, local linter option, registered for
      the Phase-3 premise audit
- [x] `barrier_diff_closed_form` — `Criterion.lean` — Phase 2 — done — FC-C6; `field_simp` +
      `ring` on the two nonzero-curvature premises; gates PASS
- [x] `equal_prefactors_decision` — `Criterion.lean` — Phase 2 — done — FC-C7; unit coupling
      consumed by rewriting the literal `1` back to `HSO`, then `mul_lt_mul_iff_of_pos_left` +
      `Real.exp_lt_exp` + `div_lt_div_iff_of_pos_right`; gates PASS
- [x] `fcBarrier` — `RatModel.lean` (`Rat.fcBarrier`) — Phase 2 — done — FC-R1; ℚ shadow,
      verbatim
- [x] `fcBarrier_cast` — `RatModel.lean` — Phase 2 — done — FC-R1; `push_cast` + `ring`;
      gates PASS; **`#print`-verified non-vacuous** (the printed type is
      `PhotoLean.ICvsISC.fcBarrier ↑lam ↑x = ↑(PhotoLean.ICvsISC.Rat.fcBarrier lam x)` and the proof
      term carries `Rat.cast_div` / `Rat.cast_pow` / `Rat.cast_sub` — the SV-R1 namespace-shadowing
      pitfall was checked before delivery, not closed by `rfl`)
- [x] `barrierOrderQ` — `RatModel.lean` (`Rat.barrierOrderQ`) — Phase 2 — done — FC-R2;
      `decide` on the ℚ barrier order, verbatim
- [x] `barrierOrderQ_correct` — `RatModel.lean` — Phase 2 — done — FC-R2;
      `decide_eq_true_eq` + two `fcBarrier_cast` rewrites + `Rat.cast_lt`; gates PASS
- [x] `aromaticCarbonylLike` — `Instances.lean` — Phase 2 — done — FC-I1; barriers `1/16` vs
      `1/8`, verdict `false`; `norm_num` / `decide_eq_false_iff_not`; gates PASS
- [x] `elSayedFavoredLike` — `Instances.lean` — Phase 2 — done — FC-I2; barriers `1/16` vs
      **`1/32`** (the probe-recomputed value, plan §3.1 / API-NOTES statement-change index row 4),
      verdict `true`; gates PASS
- [x] `hsoZeroWitness` — `Instances.lean` — Phase 2 — done — FC-I3; `simp` at ℚ; gates PASS

## Sprint 1 — proof formalization (Phase 2, delivered by prover_a 2026-09-23)

Delivered modules (all under `PhotoLean/ICvsISC/`, none of them touching the statement layer):

| module | rows | commit |
|---|---|---|
| `Basic.lean` | FC-B1..FC-B4 (6 declarations) | `4af2c74` |
| `Criterion.lean` | FC-C1..FC-C7 (7 theorems) | `b84844e` |
| `RatModel.lean` | FC-R1..FC-R2 (4 declarations) | `0a84dea` |
| `Instances.lean` | FC-I1..FC-I3 (3 theorems) | `2d3578f` |

Raw gate evidence (prover_a run, 2026-09-23):

- `proofs/scripts/lake build PhotoLean.ICvsISC.{Basic,Criterion,RatModel,Instances}` — exit 0
  (four separate builds).
- `proofs/scripts/check.sh --strict <module>` — exit 0, scan `clean`, `verdict: PASS` for each of
  the four modules.
- `proofs/scripts/axioms.sh` on all **14** authority theorems
  (`cert_fcBarrier`, `cert_icRate`, `rate_ratio_eq`, `log_rate_ratio`, `isc_dominates_iff`,
  `spin_discount`, `hso_zero_isc_absent`, `barrier_diff_closed_form`, `equal_prefactors_decision`,
  `Rat.fcBarrier_cast`, `Rat.barrierOrderQ_correct`, `aromaticCarbonylLike`, `elSayedFavoredLike`,
  `hsoZeroWitness`) — every row `depends on axioms: [propext, Classical.choice, Quot.sound]`,
  `verdict: PASS (only mathlib infrastructure axioms)`.
- `python3 theories/BEP/probes/bep-fidelity.py --theory ICvsISC` — skeleton declarations 20,
  delivered word-for-word **20**, delivered-not-in-authority 0, not delivered yet 0, signature
  differences **0**; exit 0.
- Whole-tree `proofs/scripts/check.sh --strict` at the time of delivery — `verdict: FAIL (strict)`
  with a **single** scan hit: `PhotoLean/FluorPhos/Criterion.lean:224` (an uncommitted
  work-in-progress edit by another prover, outside this theory's ownership). The whole-tree *build*
  was OK; every `PhotoLean/ICvsISC/*.lean` file scanned clean. The gate must be re-run after the
  FluorPhos edit lands.
- **Delivery gap for the lead**: the four new modules are not in `lakefile.toml` `defaultTargets`
  (this task's ownership excludes `lakefile.toml`), so the whole-tree `check.sh --strict` PASS does
  not *build* them. The lead must append
  `"PhotoLean.ICvsISC.Basic" … "PhotoLean.ICvsISC.Instances"` before the verifier's whole-tree
  build counts as evidence for this theory.

Statement layer: **unchanged** — no API drift, no statement edit, no re-freeze. The one arithmetic
correction of this theory (FC-I2's ISC barrier `1/16` → `1/32`) was made in Phase 1 and is already
carried by the frozen authority; it is re-recorded in `proofs/API-NOTES.md` §photobatch
statement-change index row 4.

Premise observations registered for the Phase-3 audit (statements untouched): FC-C1's `FCData`
bundle and FC-C5's `h0 : HSO = 0` are decorative — the frozen conclusions do not mention the
parameter they constrain. Both rows keep the authority's signature verbatim with a local
`linter.unusedVariables` option (the precedent of `PhotoLean/BEP/Sharp.lean` and
`PhotoLean/EnergyGapLaw/Criterion.lean`) rather than a silent repair.

---

## Verifier run 4 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence: four modules re-elaborated from source with zero
diagnostics; whole-tree `check.sh --strict` PASS twice (HEAD `ec8b55e`/`488f51d`) with scan `clean`
and the four targets in `defaultTargets`; `#print axioms` 14/14 PASS; fidelity 20/20 with 0
differences plus an independent transcript grid (5832 configurations, 0 mismatches); kernel
certificates printed as `Eq.refl` (real definitional pins on `Kernel.barrier` / `Marcus.rate`);
`Rat.fcBarrier_cast` `#print`-checked as a real bridge (`rfl` fails, the cast chain does not);
instance barriers independently recomputed (`1/16` vs `1/8`; `1/32` — the plan draft's `1/16` is
wrong); the log-form competition law matched an independent 40-digit numerical computation; and
every premise-removed attack broke as expected while **no delivered form broke**.

Findings and their resolution:
* **F1 (fixed 2026-09-23 by the lead)** — the plan had no §3.1 section although §3 promised one and
  API-NOTES pointed at it; §4 still printed the draft FC-I2 `1/16`. §3.1 added, §4 synced.
* **F2 (Phase-3 premise audit, extended list)** — field-level non-load-bearing premises verified by
  the verifier: `FCData.posLamI`/`posLamS` (neither consumed nor needed by any Criterion statement),
  `posAS` decorative on FC-C4/FC-C7, `hH : HSO = 1` decorative at the statement level (consumed in
  the proof); while `posAI`/`posAS`/`poskBT` ARE load-bearing on FC-C3 (kernel counterexamples).
  Recorded here and in EXPERIENCE for the Phase-3 authority revision.
* **F3 (Phase-3 re-freeze candidate)** — `hsoZeroWitness (AS : ℚ) : (0:ℚ)^2 * AS = 0` is
  `zero_mul` and mentions no model object (no `iscRate`, no barrier, no `HSO` premise); the plan's
  FC-I3 description is wider than the row. Same class as SternVolmer's `mixed_witness`; queued.
* **F5 (fixed 2026-09-23)** — `RESULTS.md` still carried the Phase-1 status text; synced at ticking.
* **F4/F6 (registered)** — module-granular commits (batch practice) and the tree-state caveat for
  whole-tree gate claims (already in EXPERIENCE).

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entries 2–3): `hso_zero_isc_absent` and `equal_prefactors_decision` dropped their decorative `HSO` hypotheses; `hsoZeroWitness` re-frozen to the spin-discount witness. All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).
