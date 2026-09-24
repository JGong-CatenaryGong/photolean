# theories/RACI/TASKS.md — PhotoLean task board: RACI (single source of truth for status)

- Status vocabulary: `todo` → `stmt` → `proving` → `review` → `done`.
- Ticking (`[x]`) happens only after a verifier PASS and is done by the lead.
- Contract and role definitions: `proofs/ENGINE.yml`, `proofs/ENGINE.md`.
- Plan and milestone statements: `theories/RACI/plan.md`.
- Status of this theory: **ported, gated, and ticked** — the RACI (Restricted Access to a Conical
  Intersection ⇒ aggregation-induced emission) work is integrated from the independent ChemLean
  repository (`[local path removed]`, same Lean 4.17.0 / mathlib v4.17.0 toolchain) as
  PhotoLean's 17th theory, following the repository's standards. The 11 ported modules build on
  the first pass; the statement authority (extracted from the delivered signatures, sha256 on
  record below) compiles at 0 errors; fidelity 71/71 word-for-word with 0 differences; 46/46
  upstream theorems + 13 integration-addition rows pass `#print axioms`.

## Sprint 0 — integration (this batch)

- [x] Modules ported to `PhotoLean/RACI/` with imports adapted (11 modules, namespaces wrapped as
      `PhotoLean.RACI` / `PhotoLean.TwoState`; upstream `RACI/Rates/` flattened to the per-theory
      layout)
- [x] Statement authority `theories/RACI/probes/RACI-statement-skeleton.lean` — 71 declarations
      (46 theorems + 25 definitions/structures/inductives), extracted verbatim from the delivered
      signatures, compiles at 0 errors, sha256 recorded below
- [x] Instances + rational decision layer (`PhotoLean/RACI/Instances.lean`, `RatModel.lean`) —
      the named admissible model (`torsionH` + the enhancement verdict at concrete parameters)
      and the named non-model (`nonModelNoCI`, an everywhere-empty conical set), plus the ℚ
      discriminant zone classifier with correctness rows
- [x] Edges registered into `PhotoLean/Relations.lean` §17 (five machine rows + the no-edge
      registrations) and `theories/RELATIONS.md`
- [x] Gates: build (11+2 modules), strict scan clean, `#print axioms` on every delivered theorem
      (59/59), fidelity 71/71 with 0 differences, whole-tree `check.sh --strict` PASS
- [x] Independent verifier run (close-out) — **PASS** (2026-09-23; recorded below). Process note
      (audit finding F1): the declaration rows above were ticked before the audit ran, so the
      final state is consistent but the ORDER violated iron rule 7; the close-out record below is
      the authoritative entry, and RESULTS.md's validation history carries the run

**Statement authority sha256**: `5a5415ccb992193e262b10450d415e066bb506f8d1d3d6e4078a3afc9d466bb9` (current:
after the autoImplicit integration note of plan §3.1 item 1 and the two term-mode theorem bodies
turned into placeholders — the close-out audit's finding F3; the earlier board prefix was missing
its first character, audit finding F2).

**Integration record (plan §3.1)**: (1) the ported code keeps the upstream default
`autoImplicit` — the PhotoLean `set_option autoImplicit false` is not applied to the ported
modules (verbatim preservation); (2) upstream `RACI/Rates/` flattened; (3) namespaces wrapped
(`PhotoLean.RACI.*` / `PhotoLean.TwoState.*`); (4) several upstream files carry a stale
`SKELETON` header though fully proved — comments, preserved verbatim; the real status is this
board; (5) the close-out audit's F4/F5: the ported comments were translated from Chinese to
English in the close-out commit (the ChemLean provenance is kept in each module's English
header), and the theory-granular commit convention follows the repository's established
practice (`feat` + `docs` per theory).

## Declaration board (88 declarations, all `done` — see the per-row status and the gates above)

### TwoState.lean (12)

- [x] `TwoState` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `a` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `b` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `d` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `discr` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `conicalSet` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `conicalSet'` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `eigenRoots` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (definition)
- [x] `discr_eq_zero_iff_ci` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (theorem)
- [x] `discr_nonneg` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (theorem)
- [x] `degenerate_iff_discr_zero` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (theorem)
- [x] `ci_iff_degenerate` — delivered — ported — done — `PhotoLean/RACI/TwoState.lean` (theorem)

### Branching.lean (10)

- [x] `F` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (definition)
- [x] `finrank_branching_eq_two` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)
- [x] `Fex` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (definition)
- [x] `Fex_surjective` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)
- [x] `finrank_branching_eq_two_explicit` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)
- [x] `linearized` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (definition)
- [x] `eigenRootsMat` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (definition)
- [x] `linearized_discr` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)
- [x] `linearized_gap` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)
- [x] `linearized_gap_pos` — delivered — ported — done — `PhotoLean/RACI/Branching.lean` (theorem)

### Accessibility.lean (2)

- [x] `AdmissiblePath` — delivered — ported — done — `PhotoLean/RACI/Accessibility.lean` (definition)
- [x] `BlockedBelow` — delivered — ported — done — `PhotoLean/RACI/Accessibility.lean` (definition)

### Torsion.lean (7)

- [x] `Allowed` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (definition)
- [x] `exists_cross_forbidden` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (theorem)
- [x] `torsion_blocks_ci` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (theorem)
- [x] `torsionH` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (definition)
- [x] `torsionH_symm` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (theorem)
- [x] `torsionH_cont` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (theorem)
- [x] `torsionH_conicalSet` — delivered — ported — done — `PhotoLean/RACI/Torsion.lean` (theorem)

### Barrier.lean (2)

- [x] `barrierRate` — delivered — ported — done — `PhotoLean/RACI/Barrier.lean` (definition)
- [x] `barrierRate_antitone` — delivered — ported — done — `PhotoLean/RACI/Barrier.lean` (theorem)

### LandauZener.lean (5)

- [x] `lzProbability` — delivered — ported — done — `PhotoLean/RACI/LandauZener.lean` (definition)
- [x] `lz_antitone` — delivered — ported — done — `PhotoLean/RACI/LandauZener.lean` (theorem)
- [x] `lz_probability_antitone_in_gap` — delivered — ported — done — `PhotoLean/RACI/LandauZener.lean` (theorem)
- [x] `lorentzian` — delivered — ported — done — `PhotoLean/RACI/LandauZener.lean` (definition)
- [x] `lorentzian_antitone_on_norm` — delivered — ported — done — `PhotoLean/RACI/LandauZener.lean` (theorem)

### Jablonski.lean (3)

- [x] `quantumYield` — delivered — ported — done — `PhotoLean/RACI/Jablonski.lean` (definition)
- [x] `quantumYield_strictMono_of_knr_lt` — delivered — ported — done — `PhotoLean/RACI/Jablonski.lean` (theorem)
- [x] `raci_emission_enhancement` — delivered — ported — done — `PhotoLean/RACI/Jablonski.lean` (theorem)

### JablonskiRatios.lean (12)

- [x] `quantumYield_sub_eq` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `quantumYield_gt_iff_ratio_lt` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `quantumYield_gt_of_ratio_lt` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `quantumYield_gt_of_knr_lt_of_kr_le` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `raci_emission_enhancement_general` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `competitionRatio` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (definition)
- [x] `quantumYield_eq_inv_one_add_competitionRatio` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `quantumYield_gt_iff_competitionRatio_lt` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `competitionRatio_add` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `quantumYield_gt_of_channel_ratios` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `aie_iff_mul` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)
- [x] `aie_iff_knr_suppression_lt_kr_suppression` — delivered — ported — done — `PhotoLean/RACI/JablonskiRatios.lean` (theorem)

### Main.lean (8)

- [x] `accessGap` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (definition)
- [x] `accessGap_univ` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `accessGap_allowed` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `accessGap_lt` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `torsion_knr_lt` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `torsion_raci_emission_enhancement` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `torsion_raci_emission_enhancement_general` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)
- [x] `torsion_raci_emission_enhancement_of_kr_le` — delivered — ported — done — `PhotoLean/RACI/Main.lean` (theorem)

### Seam.lean (4)

- [x] `degeneracyMap` — delivered — ported — done — `PhotoLean/RACI/Seam.lean` (definition)
- [x] `degeneracyMap_hasStrictFDerivAt_of_contDiffAt` — delivered — ported — done — `PhotoLean/RACI/Seam.lean` (theorem)
- [x] `conicalSet_locally_slice` — delivered — ported — done — `PhotoLean/RACI/Seam.lean` (theorem)
- [x] `conicalSet_local_codim_two` — delivered — ported — done — `PhotoLean/RACI/Seam.lean` (theorem)

### GeometricPhase.lean (6)

- [x] `loopH` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (definition)
- [x] `loopLowerVec` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (definition)
- [x] `loopLowerVec_eigen` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (theorem)
- [x] `loopLowerVec_sq_sum` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (theorem)
- [x] `loop_monodromy` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (theorem)
- [x] `loop_gap` — delivered — ported — done — `PhotoLean/RACI/GeometricPhase.lean` (theorem)

### RatModel.lean (10)

- [x] `discrQ` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (definition)
- [x] `CIZone` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (definition)
- [x] `ciZoneQ` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (definition)
- [x] `ciZoneQ_conical_iff` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `ciZoneQ_conical_iff_entries` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `discrQ_cast` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `ciZoneQ_conical_entry_verdict` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `ciZoneQ_nonModel_gapped_verdict` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `ciZoneQ_offdiagonal_gapped_verdict` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)
- [x] `discrQ_nonneg` — delivered — ported — done — `PhotoLean/RACI/RatModel.lean` (theorem)

### Instances.lean (7)

- [x] `admissibleModel_enhancement_holds` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)
- [x] `admissibleModel_conical_point` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)
- [x] `nonModelNoCI` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (definition)
- [x] `nonModelNoCI_gapped_everywhere` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)
- [x] `nonModelNoCI_conicalSet_empty` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)
- [x] `nonModelNoCI_no_conical_point` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)
- [x] `instance_verdicts_agree` — delivered — ported — done — `PhotoLean/RACI/Instances.lean` (theorem)

## Verifier runs

### Run 1 — 2026-09-23, independent read-only close-out audit — **PASS**

Raw outcomes (the verifier's report): leaf plane 17/17; scan `clean` (independently re-run with
the script's pattern, including comment hits); the 13 RACI modules in `defaultTargets` (checked
against disk, 0 missing / 0 phantom); fidelity 71/71 word-for-word with 0 signature differences
(its own declaration counters agree: 71 skeleton = 46 theorems + 23 defs + 2 structures; 88
delivered = 59 theorems + 29 defs/structures/inductives); `#print axioms` **59/59 PASS**, only
`[propext, Classical.choice, Quot.sound]`; the §17 five rows also 5/5 clean.

Independent scientific checks: the torsion model's CI equivalence re-derived (`discr (θ) = 4θ²`,
`conicalSet = {0}`) with a 729-point rational grid (0 counterexamples); the enhancement rebuilt
independently through `accessGap_lt` + `barrierRate_antitone` with the two yields computed
(`Φ_free = 1/2`, `Φ_agg = 1/(1+exp(−1))`); the non-model re-derived (`discr ≡ 1`,
`conicalSet = ∅`); the ℚ classifier cross-checked by `#eval` and Python (8/8 agreement); the
adversarial set: `hδ` and `hkr_pos` are load-bearing (removing either makes the stripped form
false — δ=0 collapses both gaps, kr=0 collapses both yields), while **no delivered form broke**
at δ = 1/1000, at (1e6, 7, 42), or otherwise; the near-miss confirmed (`kernel_surfaces_cross_at_tsCoord`
fails at `lam = 0, x = 1` — `hlam` is load-bearing, the build caught an attempted linter-driven
trim); the totalized corner confirmed (`icvsisc_barrier_zero_at_crossing` holds at `lam = 0`),
and `loop_gap = 2` re-evaluated at several loop parameters.

Findings (all MINOR, all resolved in the same close-out):
* F1 (process order — the rows were ticked before the audit; final state consistent): recorded
  here and in RESULTS.md's validation history.
* F2 (sha prefix missing a character): fixed above with the full hash.
* F3 (two term-mode theorem bodies in the skeleton, 44/46 placeholders): both turned into
  placeholders; the skeleton now emits exactly 46 placeholder warnings; fidelity unchanged.
* F4 (language policy: the ported modules carried Chinese comments and cross-references to the
  ChemLean plan): translated to English in the close-out commit; the ChemLean provenance is kept
  in each module's English header.
* F5 (commit granularity: theory-granular `feat(RACI)` commits, the established practice):
  registered in the integration record (plan §3.1 item 5).
