# theories/SternVolmer/TASKS.md — PhotoLean task board: SternVolmer (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/SternVolmer/plan.md`.
- Status of this theory: **Phase 2 (proof formalization) delivered by `prover_c` (SV1–SV4),
  awaiting independent verification** — every one of the 27 theorem rows of the statement
  authority carries a real proof body in `PhotoLean/SternVolmer/`, and every declaration row of the
  authority is delivered with its signature transcribed verbatim.
  Board status of all 46 authority declarations, plus the 4 auxiliary rows of the SV-R1 incident:
  `review`. Ticking is lead-only, after verifier PASS.

## Sprint 0 — environment, statements, plan (Phase 1 deliverable)

- [x] Plan landed: `theories/SternVolmer/plan.md` (statement inventory, sprint order, honesty table,
      edge candidates) — lead-authored 2026-09-22
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` — **46 declarations**
      (27 theorems + 19 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `811e34c0bf02d2b2a0479f613a73eb0db601a57cf331537750ca48706085cfa5`
- [x] API calibration probe: `theories/SternVolmer/probes/SternVolmer-api-probe.lean` (exit 0)
- [ ] Literature leaf populated: `theories/SternVolmer/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all 46 authority declarations now `review`; ticking is lead-only after verifier PASS)

- [ ] `dynDecay` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioDyn` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `tauRatioDyn` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioStat` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `tauRatioStat` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `KSV` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioBoth` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Mech` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioOf` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `tauRatioOf` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `LifetimeTracks` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `dyn_lifetime_tracks_intensity` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `stat_lifetime_flat` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `stat_lifetime_separates` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioDyn_linear` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioStat_linear` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioDyn_at_zero` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioStat_at_zero` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioDyn_strictMono_q` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioStat_strictMono_q` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `intensity_curve_coincidence` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `lifetimeTracks_iff_dyn` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioBoth_eq` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioBoth_secondDifference` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioDyn_secondDifference` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svRatioStat_secondDifference` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `curvature_witnesses_coexistence` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `d1_verdict` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.svRatioDyn` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.tauRatioDyn` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.svRatioStat` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.tauRatioStat` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.svRatioDyn_cast` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.tauRatioDyn_cast` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.svRatioStat_cast` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `Rat.tauRatioStat_cast` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `SVZone` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svZoneQ` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svZoneQ_dynLike` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svZoneQ_statLike` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svZoneQ_mixedLike` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `svZoneQ_inconsistent` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `oxygenDynamic` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `complexStatic` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `conflation_witness` — delivered — review — signature verbatim, real body delivered (Sprint 1+)
- [ ] `mixed_witness` — delivered — review — signature verbatim, real body delivered (Sprint 1+)

## Sprint 1+ — proof formalization (Phase 2, delivered by `prover_c`, status `review`)

Owner: `prover_c` (exclusive ownership of `PhotoLean/SternVolmer/*.lean` and this board).
Milestones in the plan's sprint order: SV1 `Basic` → SV2 `Criterion` (the D1 core) →
SV3 `RatModel` → SV4 `Instances`.

### Modules delivered

- `PhotoLean/SternVolmer/Basic.lean` — SV-B1..SV-B9 (11 declarations: `dynDecay`, `svRatioDyn`,
  `tauRatioDyn`, `svRatioStat`, `tauRatioStat`, `KSV`, `svRatioBoth`, `Mech`, `svRatioOf`,
  `tauRatioOf`, `LifetimeTracks`), `import Mathlib` only.
- `PhotoLean/SternVolmer/Criterion.lean` — SV-C1..SV-C10 (17 theorems, including the D1 core
  `intensity_curve_coincidence`, `lifetimeTracks_iff_dyn`, `curvature_witnesses_coexistence` and
  the headline `d1_verdict`).
- `PhotoLean/SternVolmer/RatModel.lean` — SV-R1..SV-R3 (4 ℚ shadows + 4 cast rows + `SVZone` +
  `svZoneQ` + 4 zone-correctness rows), plus 4 auxiliary rows (see the incident below).
- `PhotoLean/SternVolmer/Instances.lean` — SV-I1..SV-I4 (`oxygenDynamic`, `complexStatic`,
  `conflation_witness`, `mixed_witness`).

### Gate evidence (2026-09-22, `prover_c`)

- `proofs/scripts/lake build PhotoLean.SternVolmer.{Basic,Criterion,RatModel,Instances}` — exit 0
  each (linter warnings only: the authority itself leaves `Ka`/`q` of `tauRatioStat` and the
  `hk0`/`hkq` premises of SV-C8/SV-C10 unused — weakest-premise shape, statements frozen).
- `proofs/scripts/axioms.sh` on all 17 Criterion rows, both Instances rows and all 12 RatModel
  rows — `verdict: PASS (only mathlib infrastructure axioms)`, `propext`, `Classical.choice`,
  `Quot.sound`.
- `proofs/scripts/check.sh --strict` (whole tree) — `verdict: PASS`, scan `clean`.
- `python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer` — 39 word-for-word of 39
  authority keys, `signature differences: 0`, 4 auxiliary declarations reported separately.

### Statement incident — SV-R1 cast-coherence rows (found in SV3; lead decision needed)

The four SV-R1 rows `Rat.svRatioDyn_cast`, `Rat.tauRatioDyn_cast`, `Rat.svRatioStat_cast`,
`Rat.tauRatioStat_cast` are **degenerate as written in the frozen authority**: a declaration named
`Rat.foo` has its type elaborated inside the `Rat` namespace, so the unqualified right-hand
identifiers (`svRatioDyn`, `tauRatioDyn`, `svRatioStat`, `tauRatioStat`) resolve to the ℚ shadows
instead of the `ℝ` ratios. The elaborated type is the vacuous identity `↑x = ↑x`, e.g.
`#print PhotoLean.SternVolmer.Rat.svRatioDyn_cast` shows
`@Rat.cast (PhotoLean.SternVolmer.Rat.svRatioDyn a b q)` on both sides; the row closes by `rfl`.
This contradicts the authority's own docstring ("the ℚ shadow computes the real dynamic intensity
ratio"), plan §4 (SV-R1) and the API probe's measured shape (the probe used an unnamed `example`,
hence the outer namespace, hence the intended reading — which is why Phase 1 did not catch it).

Handling in SV3 (no statement may be changed by the prover):
- the four rows are kept **verbatim** (statement authority; textual fidelity), with the incident
  documented in their docstrings, and are proved by `rfl`;
- the intended content is delivered as 4 auxiliary declarations with disambiguated right-hand
  sides: `rat_svRatioDyn_cast_real`, `rat_tauRatioDyn_cast_real`, `rat_svRatioStat_cast_real`,
  `rat_tauRatioStat_cast_real` (not `Rat.`-prefixed, so the file's `Rat`-keyed signature stays
  identical to the authority for the fidelity checker).
- Recommended re-freeze (lead, plan §3.1 + statement-authority sha256): qualify the right-hand
  side as `PhotoLean.SternVolmer.svRatioDyn a b q` (etc.), or drop the `Rat.` prefix from the four
  theorem names; then the auxiliary rows become the delivered rows and the `rfl` proofs are
  replaced by the `norm_cast` proofs already present in the file.

### Board change proposed to the lead (not done: `lakefile.toml` is not owned by `prover_c`)

`lakefile.toml` `defaultTargets` must gain the four modules, otherwise the bare
`proofs/scripts/check.sh --strict` builds everything except this theory (the scan still covers the
files, the build does not — the acceptance hole the file's own comment warns about):
`PhotoLean.SternVolmer.Basic`, `.Criterion`, `.RatModel`, `.Instances`.
