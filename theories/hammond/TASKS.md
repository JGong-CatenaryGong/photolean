# theories/hammond/TASKS.md — PhotoLean task board: the Hammond postulate (single source of truth for status)

- Status vocabulary: `todo` (not started) → `stmt` (statements calibrated and compiling) →
  `proving` (proof in progress) → `review` (handed to the verifier) → `done` (verifier PASS,
  recorded on this board).
- Row format: `- [ ] <theorem> — <file> — <owner> — <status> — <note>`.
- **Ticking (`[x]`) happens only after a verifier PASS and is done by the lead**; workers never
  tick their own rows.
- The owner column holds engine role names (`prover_a`…`prover_d`); one file has at most one
  concurrent owner.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/hammond/plan.md`.
- **Statement authority**: `theories/hammond/probes/hammond-statement-skeleton.lean`
  (compiled: 0 error; **102 declarations** = 17 definitions + 85 theorems).
- Theory direction: **Hammond's postulate in the two-parabola (Marcus-type) model**, human
  request of 2026-09-20 (three parts: formal description / proof and conditions / instance verdicts).
- Deliverable module prefix: `PhotoLean.Hammond`; sources under `PhotoLean/Hammond/`
  (`SOURCE_DIRS` is global and covers them).

---

## Sprint 0 — environment, statements, plan (closed)

- [x] Theory directory `theories/hammond/` created; contract extended with the multi-theory data
      plane (`THEORIES="Marcus hammond"` + `PLAN_hammond` / `TASKS_hammond` / `LITERATURE_hammond`
      / `PROBES_hammond` / `RESULT_hammond`); `proofs/scripts/check.sh` gained a generic
      per-theory leaf check (additive; skipped when `THEORIES` is unset)
- [x] **Statement skeleton compiles**: `theories/hammond/probes/hammond-statement-skeleton.lean`
      (85 declarations, 0 error)
- [x] **Lead risk probe**: `theories/hammond/probes/hammond-risk-probe.lean` — 0 error / 0 warning;
      proves the core statement forms *before* planning (crossing uniqueness, both barrier
      identities, monotonicity, both sharpness branches, regime equivalence, the Leffler secant
      identity, the ℚ classifier computations, the cast transfer)
- [x] API calibration dispatched (`api_researcher`) → `proofs/API-NOTES.md` (Hammond section) +
      `theories/hammond/probes/hammond-api-*.lean`
- [x] Literature survey dispatched (`literature_researcher`) → `theories/hammond/LITERATURE.md`
      (Hammond 1955 verbatim wording, Leffler 1953, the `α = 1/2 + ΔG°/(2λ)` loci, the
      inverted-region/`α < 0` question, exceptions, instance-parameter provenance)
- [x] Plan landed: `theories/hammond/plan.md` (H1–H5, statement authority, sprint order, honesty table)
- [ ] Human confirmation of the plan

---

## H1 — description layer (`PhotoLean/Hammond/Basic.lean`; owner prover_a; Sprint 1)

- [ ] definitions `reactantSurface` / `productSurface` / `tsCoord` / `gapReactant` / `gapProduct`
      / `lefflerSecant` / `ReactionRegion` / `ReactantLike` / `ProductLike` / `HammondConforms`
      / `HammondDescriptor` / `HZone` / `hammondZone` — Basic.lean — prover_a — review — plan §2.2
- [ ] `crossing_iff` — Basic.lean — prover_a — review — plan §4.2
- [ ] `gapReactant_eq_crossing_energy` — Basic.lean — prover_a — review — plan §4.2
- [ ] `gapProduct_eq_crossing_energy` — Basic.lean — prover_a — review — plan §4.2 (corrected: well-referenced form `... - dG`)
- [ ] `gapProduct_sub_gapReactant` — Basic.lean — prover_a — review — plan §4.2
- [ ] `gapProduct_eq_gapReactant_neg` — Basic.lean — prover_a — review — plan §4.2
- [ ] `tsCoord_neg` — Basic.lean — prover_a — review — plan §4.2
- [ ] `tsCoord_zero` — Basic.lean — prover_a — review — plan §4.2
- [ ] `tsCoord_zero_lam` — Basic.lean — prover_a — review — plan §4.2
- [ ] `tsCoord_at_lam` — Basic.lean — prover_a — review — plan §4.2
- [ ] `tsCoord_mem_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `reactionRegion_pos` — Basic.lean — prover_a — review — plan §4.3
- [ ] `not_reactionRegion_of_nonpos` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_early_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_half_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_late_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_atReactant_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_atProduct_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_beyondReactant_iff` — Basic.lean — prover_a — review — plan §4.3
- [ ] `hammondZone_eq_beyondProduct_iff` — Basic.lean — prover_a — review — plan §4.3

## H2 — Hammond criterion (`PhotoLean/Hammond/Criterion.lean`; owner prover_a; Sprint 2)

- [ ] `tsCoord_antitone` — Criterion.lean — prover_a — review — plan §5
- [ ] `hammond_descriptor_holds` — Criterion.lean — prover_a — review — plan §5
- [ ] `reactantLike_iff` — Criterion.lean — prover_a — review — plan §5
- [ ] `productLike_iff` — Criterion.lean — prover_a — review — plan §5
- [ ] `gap_compare_iff` — Criterion.lean — prover_a — review — plan §5
- [ ] `lefflerSecant_eq_midpoint` — Criterion.lean — prover_a — review — plan §5
- [ ] `lefflerSecant_symm` — Criterion.lean — prover_a — review — plan §5
- [ ] `lefflerSecant_mem_iff` — Criterion.lean — prover_a — review — plan §5
- [ ] `tsCoord_lt_zero_iff_inverted` — Criterion.lean — prover_a — review — plan §5
- [ ] `lefflerSecant_neg_iff_inverted` — Criterion.lean — prover_a — review — plan §5
- [ ] `conforms_iff_zone` — Criterion.lean — prover_a — review — plan §5 (corrected: the three-predicate disjunction was a trichotomy tautology)
- [ ] `exists_reactantLike` — Criterion.lean — prover_a — review — plan §5
- [ ] `exists_productLike` — Criterion.lean — prover_a — review — plan §5
- [ ] `exists_reactionRegion` — Criterion.lean — prover_a — review — plan §5
- [ ] `barrier_eq_gapReactant` — Criterion.lean — prover_a — review — plan §5

## H3 — sharp conditions (`PhotoLean/Hammond/Sharp.lean`; owner prover_d; Sprint 3)

- [ ] `hammond_lam_pos_of_descriptor` — Sharp.lean — prover_d — review — plan §6
- [ ] `hammond_sharp` — Sharp.lean — prover_d — review — plan §6 (critical path)
- [ ] `hammond_fails_of_nonpos` — Sharp.lean — prover_d — review — plan §6
- [ ] `exists_direction_reversal_of_neg` — Sharp.lean — prover_d — review — plan §6
- [ ] `exists_direction_reversal_of_eq` — Sharp.lean — prover_d — review — plan §6
- [ ] `conforms_requires_pos` — Sharp.lean — prover_d — review — plan §6

## H4 — microscopic conditions (`PhotoLean/Hammond/Compose.lean`; owner prover_b; Sprint 4)

- [ ] `hammond_descriptor_of_inner` — Compose.lean — prover_b — review — plan §7
- [ ] `hammond_descriptor_of_microscopic` — Compose.lean — prover_b — review — plan §7
- [ ] `hammond_descriptor_of_nonoverlap` — Compose.lean — prover_b — review — plan §7 (stretch)
- [ ] `exists_reactionRegion_of_microscopic` — Compose.lean — prover_b — review — plan §7

## H5a — rational decision layer (`PhotoLean/Hammond/RatModel.lean`; owner prover_c; Sprint 2)

- [ ] `tsCoordQ` / `gapReactantQ` / `lefflerSecantQ` / `hammondZoneQ` definitions —
      RatModel.lean — prover_c — review — plan §8.1
- [ ] `tsCoordQ_cast` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `gapReactantQ_cast` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `lefflerSecantQ_cast` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_hammondZone` (7-branch transfer; highest-risk item) — RatModel.lean —
      prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_early_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_half_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_late_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_atReactant_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_atProduct_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_beyondReactant_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_eq_beyondProduct_iff` — RatModel.lean — prover_c — review — plan §8.1
- [ ] `hammondZoneQ_beyondReactant_iff_inverted` — RatModel.lean — prover_c — review — plan §8.1

## H5b — instance verdicts (`PhotoLean/Hammond/Instances.lean`; owner prover_c; Sprint 3)

- [ ] I1 `inst_I1_thermoneutral_zone` / `_conforms` / `_coord` — Instances.lean — prover_c — review — plan §8.2
- [ ] I2 `inst_I2_exergonic_zone` / `_reactantLike` / `_conforms` — Instances.lean — prover_c — review — plan §8.2
- [ ] I3 `inst_I3_endergonic_zone` / `_productLike` / `_conforms` — Instances.lean — prover_c — review — plan §8.2
- [ ] I4 `inst_I4_barrierless_zone` / `_coord` / `_notConforms` / `_family_descriptor` —
      Instances.lean — prover_c — review — plan §8.2
- [ ] I5 `inst_I5_mcc_normal_zone` / `_coord` / `_conforms` — Instances.lean — prover_c — review — plan §8.2
- [ ] I6 `inst_I6_mcc_inverted_zone` / `_coord` / `_notConforms` / `_region` / `_leffler_negative` —
      Instances.lean — prover_c — review — plan §8.2
- [ ] I7 `inst_I7_rc_inverted_zone` / `_coord` / `_notConforms` — Instances.lean — prover_c — review — plan §8.2
- [ ] I8 `inst_I8_nonphysical_fails_neg` / `_fails_zero` / `_no_region` — Instances.lean — prover_c — review — plan §8.2
- [ ] I9 `inst_I9_mcc_structural_monotone` — Instances.lean — prover_c — review — plan §8.2
- [ ] I10 `inst_I10_nonvacuous` — Instances.lean — prover_c — review — plan §8.2

---

## Acceptance records (independent verifier runs; the lead ticks from these)

| Batch | Scope | Verdict | Key evidence | Notes |
|---|---|---|---|---|
| — | — | — | — | pending |

## Notes and conflict log

- **Contract/gate change (lead, Sprint 0)**: `proofs/ENGINE.yml` gained a multi-theory data plane
  and `proofs/scripts/check.sh` a generic per-theory leaf check. Both are additive: the canonical
  Marcus leaves and the scan/build behaviour are unchanged. Verified by running the gate on
  `PhotoLean.Marcus.Basic` after the patch.
- **Layout decision (must be reported to the human)**: theory artifacts live under
  `theories/hammond/` as requested; the Lean sources live under `PhotoLean/Hammond/` because the
  contract's `SOURCE_DIRS` (the acceptance gate's scan/build range) is global. The plan's §3
  records this; changing it would require a contract + `lakefile.toml` redesign.
- **Known-weak lemma warning (inherited lesson)**: a zone "trichotomy"-style lemma carries little
  information; the semantic content of the classifier is carried by the seven `..._iff` lemmas.
  Do not overstate the classifier lemmas in `RESULTS.md`.
