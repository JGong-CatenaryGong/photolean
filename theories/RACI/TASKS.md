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
- [ ] Independent verifier run (close-out) — pending; ticking below is by the gates above and the
      final audit's verdict

**Statement authority sha256**: `de0af9457ecd204…` (current; recorded after the autoImplicit
integration note of plan §3.1 item 1).

**Integration record (plan §3.1)**: (1) the ported code keeps the upstream default
`autoImplicit` — the PhotoLean `set_option autoImplicit false` is not applied to the ported
modules (verbatim preservation); (2) upstream `RACI/Rates/` flattened; (3) namespaces wrapped
(`PhotoLean.RACI.*` / `PhotoLean.TwoState.*`); (4) several upstream files carry a stale
`SKELETON` header though fully proved — comments, preserved verbatim; the real status is this
board.

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

- Pending: the independent close-out audit (Phase-3-style: gates, axioms, adversarial
  instantiations of the enhancement theorem, the negative-model verdicts, the §17 edge rows).
