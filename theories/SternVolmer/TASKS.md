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
- [x] **Statement authority re-frozen 2026-09-22** (plan §3.1 entry 1): the four SV-R1
      cast-coherence rows carried a vacuous right-hand side (the unqualified identifier resolved to
      the ℚ shadow); the authority now carries fully-qualified right-hand sides, the delivered rows
      are the real bridges (`#print` evidence), fidelity 46/46 with 0 differences.
- [x] **Statement skeleton compiles** (the Sprint-0 gate):
      `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` — **46 declarations**
      (27 theorems + 19 definitions/structures/inductives),
      `proofs/scripts/lake env lean` exit 0 (placeholder-body warnings only), sha256 `d4b129c125254d8e9a9c26243a3d6596183942086136fae97a6fc98735aa0baf`
- [x] API calibration probe: `theories/SternVolmer/probes/SternVolmer-api-probe.lean` (exit 0)
- [x] Literature leaf populated: `theories/SternVolmer/LITERATURE.md` (literature_researcher, batch
      round 2026-09-22) — statement-impact summary: none against the frozen inventory

### Declaration board (all 46 authority declarations now `review`; ticking is lead-only after verifier PASS)

- [x] `dynDecay` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioDyn` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `tauRatioDyn` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioStat` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `tauRatioStat` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `KSV` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioBoth` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Mech` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioOf` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `tauRatioOf` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `LifetimeTracks` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `dyn_lifetime_tracks_intensity` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `stat_lifetime_flat` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `stat_lifetime_separates` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioDyn_linear` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioStat_linear` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioDyn_at_zero` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioStat_at_zero` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioDyn_strictMono_q` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioStat_strictMono_q` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `intensity_curve_coincidence` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `lifetimeTracks_iff_dyn` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioBoth_eq` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioBoth_secondDifference` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioDyn_secondDifference` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svRatioStat_secondDifference` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `curvature_witnesses_coexistence` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `d1_verdict` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.svRatioDyn` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.tauRatioDyn` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.svRatioStat` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.tauRatioStat` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.svRatioDyn_cast` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.tauRatioDyn_cast` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.svRatioStat_cast` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `Rat.tauRatioStat_cast` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `SVZone` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svZoneQ` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svZoneQ_dynLike` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svZoneQ_statLike` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svZoneQ_mixedLike` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `svZoneQ_inconsistent` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `oxygenDynamic` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `complexStatic` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `conflation_witness` — delivered — done — signature verbatim, real body delivered (Sprint 1+)
- [x] `mixed_witness` — delivered — done — signature verbatim, real body delivered (Sprint 1+)

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
- `python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer` — **46 word-for-word of 46**
  authority keys, `signature differences: 0`, 0 declarations outside the authority (post-re-freeze,
  after the checker's dotted-name fix of 2026-09-23; the pre-fix run reported 39 keys because
  every `Rat.*` row collapsed into one key — an artefact of the checker, not of the delivery).

### Statement incident SV-R1 — RESOLVED by re-freeze (lead, 2026-09-22; plan §3.1 entry 1)

The four SV-R1 rows `Rat.svRatioDyn_cast`, `Rat.tauRatioDyn_cast`, `Rat.svRatioStat_cast`,
`Rat.tauRatioStat_cast` were **degenerate as first frozen**: a declaration named `Rat.foo`
elaborates its type inside the `Rat` namespace, so the unqualified right-hand identifiers resolved
to the ℚ shadows and the rows were the vacuous identity `↑x = ↑x` (closable by `rfl`). Found while
proving by prover_c, who kept the frozen rows verbatim, delivered the intended content as four
transitional `rat_*_cast_real` rows and escalated.

**Resolution (lead, 2026-09-22, commit `edccefc` + `b1cb8a1`)**: the authority was re-frozen with
fully-qualified right-hand sides (`PhotoLean.SternVolmer.svRatioDyn (a : ℝ) (b : ℝ) (q : ℝ)` etc.),
the delivered rows now carry the real bridges (proofs by fully-qualified `unfold` + `norm_cast`),
and the transitional rows were removed. `#print` evidence after the fix:
`∀ (a b q : ℚ), ↑(Rat.svRatioDyn a b q) = PhotoLean.SternVolmer.svRatioDyn ↑a ↑b ↑q` — a real
bridge, not a tautology. Authority sha256 updated on this board; fidelity 46/46, 0 differences;
axioms on the four rows clean. **Independently re-verified in verifier run 1 (2026-09-23)** via
`#print` and by numerical instantiation.

### Board change proposed to the lead (not done: `lakefile.toml` is not owned by `prover_c`)

`lakefile.toml` `defaultTargets` must gain the four modules, otherwise the bare
`proofs/scripts/check.sh --strict` builds everything except this theory (the scan still covers the
files, the build does not — the acceptance hole the file's own comment warns about):
`PhotoLean.SternVolmer.Basic`, `.Criterion`, `.RatModel`, `.Instances`.
**DONE (lead, 2026-09-23, `937f636`)**: the four targets are in `defaultTargets` and the whole-tree
gate builds them.

---

## Verifier run 1 — 2026-09-23 (independent, read-only)

**Verdict: PASS, 0 blocking.** Evidence (raw outputs in the verifier's report):
build all delivered modules exit 0; whole-tree `check.sh --strict` PASS with scan `clean`;
`#print axioms` over every delivered theorem (102 for the four wave-1 theories) — all within
`[propext, Classical.choice, Quot.sound]` (five classifier rows depend on `propext` only);
fidelity `--theory SternVolmer` — 0 signature differences against the authority; authority sha256 on this
board matches the file byte-for-byte; headline rows `#print`-checked as non-trivial; independent
recomputation of the named-instance verdicts matched; adversarial counterexample attempts against
the headline rows and the boundary predicates only broke *premise-removed* forms, confirming the
delivered premises are load-bearing (or registering them for the premise audit below).

Findings carried to the Phase-3 audit and to the lead (recorded here as the single source of truth):
* M1 statement-change index missing in `proofs/API-NOTES.md` (fixed by the lead 2026-09-23).
* M2 `theories/StokesShift/plan.md` §4/§5 printed the refuted SS-C9 form (fixed by the lead 2026-09-23).
* M3 `SternVolmer.mixed_witness` third conjunct is a tautology (Phase-3 authority re-freeze list).
* M4 `Einstein.radFactor_not_rational` does not mention `radFactor` (Phase-3 re-freeze list; the
  intended `Irrational (radFactor 1 1 1)` is provable — verifier's probe).
* M5 stale SternVolmer evidence block (fixed by the lead 2026-09-23).
* M6 weakest-premise standard not yet executed on the wave-1 theories (Phase-3 premise audit;
  the concrete non-load-bearing premises are listed in `proofs/EXPERIENCE.md`).
* L1–L7 low findings: record hygiene, commit granularity (registered deviation), suppressions
  hiding one real unused premise, an empty commit whose correction never landed (relaunched by the
  lead 2026-09-23), and the naming-bridge caveat on `emEnergy_pos_iff_inverted`.

### Phase-3 authority revision (2026-09-23)

Phase-3 revision (plan §3.1 entries 2–4): `lifetimeTracks_iff_dyn` dropped `hk0`; `d1_verdict` dropped `hkq` and weakened `hk0` to `k0 ≠ 0`; `mixed_witness` re-frozen to the model-tied second difference. All rows re-verified after the revision: build green, `#print axioms` clean, fidelity 0
differences (see the final verifier run's record).

## Authority hash record (2026-09-24, audit fix F5)

`sha256sum theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` recomputed 2026-09-24;
every superseded value is recoverable from git (`git show <rev>:<path> | sha256sum`):

- `5158987` (Phase-1 freeze): `811e34c0bf02d2b2a0479f613a73eb0db601a57cf331537750ca48706085cfa5` — never recorded on this board
- `edccefc` (cast-coherence re-freeze, 2026-09-22): `d4b129c125254d8e9a9c26243a3d6596183942086136fae97a6fc98735aa0baf` — the value quoted earlier in this file; correct for that revision, so the "authority sha256 updated on this board" note of the cast-coherence entry was true when written
- `fdbef08` (Phase-3 authority revision, 2026-09-23): `4c44e22a415e62e0e82411f0017b51bc4545642f05955554f8ea71697a29294d` — **current**

The stale gap was created by the Phase-3 revision, after which the quoted value was not refreshed.
