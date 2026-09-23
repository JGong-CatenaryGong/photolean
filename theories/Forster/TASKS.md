# theories/Forster/TASKS.md — PhotoLean task board: Forster (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/Forster/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) complete — all rows at `review`**;
  the statement authority is unchanged (still the Sprint-0 frozen sha256 recorded below) and every
  authority declaration is delivered verbatim (bep-fidelity: 32/32 word-for-word, 0 differences,
  0 undelivered). The rows below are moved `stmt` → `review` by prover_d; ticking (`[x]`) is
  lead-only after verifier PASS. Batch: photophysics subgraph (groups A–D), dispatched 2026-09-22.
- Evidence (prover_d, 2026-09-23): per-module `lake build` exit 0 for all four modules;
  `proofs/scripts/check.sh --strict <module>` PASS on each (scan: clean); `proofs/scripts/axioms.sh`
  PASS on all 22 theorems (only propext / Classical.choice / Quot.sound); `bep-fidelity.py
  --theory Forster` → signature differences 0.
- Route note (FO-C2, the batch's highest-risk row): delivered by the plan's two-step route
  (triangle inequality + ℝ² Cauchy–Schwarz via `nlinarith` + `Real.sin_sq_add_cos_sq`), with the
  final comparison taken through the square-root form (`Real.sqrt_le_sqrt`,
  `Real.sqrt_sq_eq_abs`) — the plan's registered fallback `kappaSq_le_eight` was **not** needed
  and the statement is unchanged. See `proofs/API-NOTES.md` §photobatch/Forster.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/Forster/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/Forster/probes/Forster-statement-skeleton.lean` — **32 declarations**
      (22 theorems + 10 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `b3f3c3b18966545032e231a8a99ed17aeb949072c309d6afbfaed28c6cc0e661`
- [x] API calibration probe: `theories/Forster/probes/Forster-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/Forster/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all `stmt`; ticking is lead-only after verifier PASS)

- [x] `kappaSq` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretRate` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff6` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `r0six` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `kappaConvention` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `kappaSq_nonneg` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `kappaSq_le_four` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `kappaSq_eq_zero_witness` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `kappaSq_eq_four_witness` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff_eq` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff_self` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff6_strictMono_r6` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `r0six_ratio` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `r0six_ratio_mem` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fret_blind_spot` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff6_mono_kappa` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff_via_lifetime` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff_via_lifetime'` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff_at_twoR0` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff6` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `r0six` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretRate` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `fretEff6_cast` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `frameKappa` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `frame_sum_eq_six` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `iso_frame_avg` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `rat_blind_spot` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `rat_max_bias` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `cy3cy5Like_verdict` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `blindSpotGeometry_verdict` — skeleton — Phase 2 — done — proved (prover_d)
- [x] `maxGeometry_verdict` — skeleton — Phase 2 — done — proved (prover_d)

## Sprint 1+ — proof formalization (Phase 2, delivered by prover_d 2026-09-23)

Sprint FO1 `Basic` → FO2 `Criterion` → FO3 `RatModel` → FO4 `Instances`; each closed with
`lake build` green before the next was claimed. All 32 declaration rows are at `review`
(writer = prover_d); the lead ticks after verifier PASS.

Module map and row counts:

| Module | Rows | Content |
|---|---|---|
| `PhotoLean/Forster/Basic.lean` | FO-B1..FO-B6 | `kappaSq`, `fretRate`, `fretEff6`, `fretEff`, `r0six`, `kappaConvention` |
| `PhotoLean/Forster/Criterion.lean` | FO-C1..FO-C11 (14 theorems) | the `κ² ≤ 4` bound, the two witnesses, the efficiency certificate and monotonicity, the convention-bias pair, the blind spot, the lifetime readings |
| `PhotoLean/Forster/RatModel.lean` | FO-R1..FO-R3 | the ℚ twins + cast coherence, `frameKappa`/`frame_sum_eq_six`/`iso_frame_avg`, the decision-layer rows |
| `PhotoLean/Forster/Instances.lean` | FO-I1..FO-I3 | `cy3cy5Like_verdict` (64/793), the blind-spot and maximal-κ² geometries |

Coordination items, both resolved by the lead on 2026-09-23 (commit `d343833`):
* the four `PhotoLean.Forster.*` targets were **not** in `lakefile.toml`'s `defaultTargets`
  (so a bare `check.sh --strict` built the other theories but not these modules while its scan
  already covered them — the acceptance hole ENGINE.md §1.1 warns about). The four targets are
  now appended; a bare `proofs/scripts/check.sh --strict` builds them.
* the whole-tree strict gate had been failing on another prover's
  `PhotoLean/FluorPhos/Scratch.lean` (unproved placeholders); that scratch file has been
  relocated out of the scanned tree.

Whole-tree evidence after that commit (prover_d, 2026-09-23):
`proofs/scripts/check.sh --strict` → build OK, scan `clean`, verdict **PASS**.

---

## Verifier run 3 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence: four modules rebuilt and re-elaborated from source with zero
diagnostics; whole-tree `check.sh --strict` PASS with scan `clean` (the four Forster targets appear in
the bare `lake build` plan since `d343833`); `#print axioms` 22/22 PASS; fidelity 32/32 with 0
differences, confirmed by an independent comparator script; `Rat.fretEff6_cast` `#print`-checked as a
real bridge.

**`kappaSq_le_four` — the batch's highest-risk row — independently confirmed as TRUE, NON-VACUOUS and
with the SHARP bound 4**: the verifier searched 721³ angle grid points, 4·10⁶ random unit-vector
triples and 1764 exact-rational configurations (max value exactly 4, none above), produced its own
kernel certificate that no smaller uniform bound exists (`¬ ∃ b < 4, ∀ …`), and checked the delivered
statement is word-for-word the authority's `≤ 4` (`kappaSq_le_eight` does not exist in the sources).

Findings and their resolution:
* **F2 (fixed 2026-09-23 by the lead)** — plan §4 still printed superseded forms (`frameKappa : ℚ`,
  `FO-I1 = 64/729`, the `fretEff6_eq` name, FO-C10's spare binder) and the plan had no §3.1 section
  although §3 promised one; the API-NOTES statement-change index had no Forster row. All synced.
* **F3 (corrected 2026-09-23)** — the delivery note claimed the plan's Phase-1 closing step was
  invalid. The verifier showed the PLAN ROUTE ITSELF compiles (`sq_le_sq` closing, its own probe
  `verifier_Forster_planroute.lean`, exit 0); the delivered proof simply chose a different (also
  sound) square-root closing. The overstated claim is corrected in `proofs/API-NOTES.md` and
  `proofs/EXPERIENCE.md`.
* **F1 (registered deviation)** — FO3/FO4's proof sources landed inside the lead's `docs(phase2)`
  commit (no `feat(FO3)`/`feat(FO4)` commits exist); history cannot be rewritten, so the delivery
  locus is recorded here instead of in `git log`.
* **F4 (Phase-3 premise audit)** — `fret_blind_spot`'s `0 < R` and `fretEff6_mono_kappa`'s
  `0 < κ₁` are proof-consumed but the statements are provable without them (verifier probes).
* F5 `RESULTS.md` Phase-1 text — synced 2026-09-23; F6 the LITERATURE false-positive flag —
  corrected 2026-09-23; F7/F8 informational (all-tree warnings come from other theories;
  `fretRate` is a representation-layer definition with no law row, by design).

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entry 4): `fret_blind_spot` dropped `hR`; `fretEff6_mono_kappa` weakened to `0 ≤ κ₁`. All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).
