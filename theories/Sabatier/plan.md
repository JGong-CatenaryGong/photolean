# theories/Sabatier/plan.md — PhotoLean formalization plan: the Sabatier principle and the volcano plot (S1–S5)

> Project: turn the **Sabatier principle** — "the optimal catalyst binds the key intermediate neither
> too strongly nor too weakly", in its quantitative form the **volcano plot** — into a
> *machine-checked* theory inside a two-branch Brønsted–Evans–Polanyi (BEP) model of a two-step
> catalytic cycle.
> Target system: Lean 4.17.0 + mathlib (`MODULE_PREFIX=PhotoLean`, contract `proofs/ENGINE.yml`).
> Status: **all six modules delivered and verified** (2026-09-21). Sprint 0 closed (contract entry,
> statement authority, risk probe, API calibration, literature round 1, plan); S1 30/30, S2 19/19,
> S3 11/11, S4 13/13, S5a 21/21, S5b 38/38 word-for-word against the authority, 107/107 theorems
> kernel-complete, whole-tree gate PASS. Verifier runs: run 1 (S1) PASS, run 2 (S2/S3/S4/S5a) PASS,
> run 3 (S5b + frozen tree + documentation plane) mathematics PASS with documentation findings
> V1–V14, all disposed and re-checked in run 4. Milestone status is tracked on the board
> `theories/Sabatier/TASKS.md` — that file is the single source of truth, this file is the plan of
> record.
> Authority: contract `proofs/ENGINE.yml`; board `theories/Sabatier/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/Sabatier/LITERATURE.md` with the long tables in
> `theories/Sabatier/literature/INSTANCE-DATA.md`.
> **Statement authority**: `theories/Sabatier/probes/sabatier-statement-skeleton.lean` — delivered
> signatures must match it word for word (check: `python3 theories/BEP/probes/bep-fidelity.py
> --theory Sabatier [--milestone S<k>]`).
> **Sprint-0 kernel evidence**: `theories/Sabatier/probes/sabatier-risk-probe.lean` (0 error) proves
> the critical-path statement forms BEFORE the milestones were dispatched.

---

## 1. Overall goal and boundaries

### 1.1 The physical claim being formalized

Sabatier's rule of heterogeneous catalysis is a statement about a **catalyst series**: plotting the
catalytic activity against one descriptor of the catalyst — the binding energy `dE` of the key
reaction intermediate, in the convention "more negative = stronger binding" — the activity is
**maximal at an intermediate binding strength** and falls off on both sides. The plot looks like a
volcano, hence "volcano plot": too-weak binding leaves the activation step too expensive, too-strong
binding leaves the desorption/removal step too expensive. The three parts of the human request map
onto:

> **Part ① — the formal description.** The effective barrier `Ea(dE)` of the two-step cycle is the
> **maximum of two BEP branches**, `branchUp dE = alphaA*dE + betaA` (the step penalized by weak
> binding) and `branchDown dE = betaB - alphaB*dE` (the step penalized by strong binding); the apex
> `dE* = (betaB - betaA)/(alphaA + alphaB)` is their crossing point, a *derived* quantity; the
> activity is `exp(-Ea/(kB*T))` and the volcano plot is its graph against `dE`. "The Sabatier
> description holds" is made a Lean predicate, `VolcanoDescriptor f de0`: `de0` is the **unique
> global minimizer** of the barrier profile `f`.

> **Part ② — proof and exact conditions.** The **sharp condition** is
> `volcano_descriptor_iff`: the two-branch profile is a volcano at its apex **iff
> `0 < alphaA * alphaB`** — the two branches penalize opposite ends of the descriptor axis (their
> slopes have the same nonzero sign, i.e. one branch grows, the other falls). In the physical
> orientation (`SabatierConforms alphaA alphaB := 0 < alphaA ∧ 0 < alphaB`) the description holds
> unconditionally (`volcano_descriptor_of_physical`); `alphaA = 0` degenerates the apex into a
> half-line plateau, opposite-slope signs destroy the interior optimum altogether — both with
> kernel-checked witnesses, and the general condition is *label invariant*
> (`volcano_descriptor_iff_labels`, `volcano_descriptor_of_neg`). The activity layer is the volcano
> plot proper: `volcanoActivity_peak_iff`.

> **Part ③ — instances and verdicts.** A finite catalogue of instances — model-constructed ones and
> the literature's own descriptor values (HER `ΔG_H*` per metal, the OER apex, one two-parabola
> cross-check) — each decided by the kernel: does the series conform to the Sabatier description
> (`SabatierConforms`, `VolcanoDescriptor`), and does the catalyst satisfy the principle
> (its descriptor lies at the apex, or within a tolerance `tol`: `Optimal`, `NearOptimal`,
> `SZone`), with the quantitative penalty bound `volcanoBarrier_le_apex_add`.

### 1.2 The model (chosen, not derived)

| ingredient | formalization | status |
|---|---|---|
| descriptor | one real scalar `dE` (binding energy of the key intermediate; more negative = stronger) | modelling choice (§13) |
| two steps of the cycle | two BEP branches `branchUp`, `branchDown` in `dE` | empirical linear free-energy relation |
| effective barrier | `volcanoBarrier .. dE = max (branchUp .. dE) (branchDown .. dE)` | **declared modelling premise** (§12) |
| apex | `apex alphaA betaA alphaB betaB = (betaB - betaA)/(alphaA + alphaB)` (crossing, derived) | theorem (`apex_crossing`, `apex_unique_crossing`) |
| activity | `activity f kB T dE = exp (-(f dE)/(kB*T))` (Arrhenius / transition-state form) | modelling choice |
| Sabatier description | `VolcanoDescriptor f de0` = unique global minimizer | definition |
| physical orientation | `SabatierConforms alphaA alphaB = 0 < alphaA ∧ 0 < alphaB` | series-level verdict |
| rational layer | `…Q` mirrors on ℚ + cast-transfer lemmas | decision layer for instances |

The literature (`theories/Sabatier/LITERATURE.md`) supports the *premise* — one branch penalizes each
end of the descriptor axis, with the rate-determining step switching at the descriptor zero
(Nørskov et al. 2005, *J. Electrochem. Soc.* **152** J23, p. J25 — "ΔG_H* = 0 separates the two legs
of the volcano"; Yang et al. 2021, *Catal. Sci. Technol.* **11** 6832, verbatim: "for the metals with
ΔG_H < 0 (ΔG_H > 0), the activation barrier of the rate-limiting Heyrovsky (Volmer) reaction
decreases with increasing (decreasing) ΔG_H"; Azcona-Aliende et al. 2026, *ACS Catal.* **16** 5805:
"two lines, one with a negative slope and another with a positive slope, the hinge point being the
ideal catalyst"; Man et al. 2011, *ChemCatChem* **3** 1159, Eq. 4.16–4.18 for the `max`-form on
step free energies) — and it does **NOT** contain the sharp condition `0 < alphaA*alphaB`, which is
this theory's own exactification (§3.1, §12). The `Ea = max(branches)` identification is a *declared*
premise: the literature's own kinetic treatments (energetic-span, Kozuch & Shaik; Langmuir coverage
factors on the strong-binding leg; Man's `max` acting on free energies with barriers explicitly
excluded) do not state it as a kinetic law (§12).

### 1.3 Human request → milestones

| Human request | Milestone | Deliverable |
|---|---|---|
| ① turn the Sabatier principle into a formal description | **S1** (description layer) | `PhotoLean/Sabatier/Basic.lean`: branches, effective barrier, apex, pass height, `VolcanoDescriptor`, `AntiVolcanoDescriptor`, `activity`, `SabatierConforms`, `TooStrong`/`Optimal`/`TooWeak`/`NearOptimal`, `SZone`/`sabatierZone`, crossing geometry and the classifier lemmas |
| ②a prove the description | **S2** (law layer) | `PhotoLean/Sabatier/Criterion.lean`: the apex is the unique global minimizer, both leg monotonicities, the tolerance penalty bound, the apex-centred form, the leg slopes = BEP coefficients, the activity layer, non-vacuity |
| ②b find the exact conditions | **S3** (sharp conditions) | `PhotoLean/Sabatier/Sharp.lean`: `⟺ 0 < alphaA * alphaB`, the label-invariant form, the volcano plot itself, and explicit failure witnesses (flat, plateau, anti-volcano) |
| ②c microscopic / cross-theory form | **S4** | `PhotoLean/Sabatier/Compose.lean`: the two-parabola volcano built from the repository's own `PhotoLean.BEP` model, its apex `√(λ₁λ₂)(√λ₂-√λ₁)/(√λ₁+√λ₂)`, and the BEP-linear volcano as the max of the two tangent lines (a pointwise lower bound; exact at a symmetric cycle's apex) |
| ③ plug in instances and decide | **S5** (instances & verdicts) | `PhotoLean/Sabatier/RatModel.lean` (computable ℚ verdict layer + cast transfers) and `PhotoLean/Sabatier/Instances.lean` (kernel-checked verdicts for model rows and literature rows) |

### 1.4 Explicit non-goals (scope control)

- **Not deriving the model.** That a catalytic cycle is captured by one scalar descriptor, that each
  step's barrier is affine in it (BEP), and that the effective barrier is the max of the two branch
  barriers are modelling assumptions, not theorems; the formalized content is conditional on them
  (§12).
- **No claim that the Sabatier principle is a theorem of quantum mechanics or of kinetics.** One
  quantitative realization inside one model is made exact.
- **No coverage/site/kinetic detail**: no Langmuir coverages, no microkinetics, no TOF equations
  beyond the Arrhenius proxy `exp(-Ea/(kB*T))`, no prefactor dependence, no scaling relations
  between several descriptors, no d-band model.
- **No claim about measured rates.** Literature descriptors enter as *printed numbers with
  provenance*, transcribed as rationals; the instances decide statements about those numbers, not
  about the experiments (§8.2, §12).
- **No `sorry`, no custom `axiom`** in delivered files (enforced by `proofs/scripts/check.sh
  --strict` and `axioms.sh`).

---

## 2. Conventions and symbol table

Axis convention (the literature's `ΔG_H* = ΔE_H + 0.24 eV`, Nørskov 2005 Eq. [8]): the descriptor is
the **free** binding energy `ΔG_H*`, so that the ideal HER catalyst sits at `dE = 0` in the
literature's own reading (LITERATURE.md §R2.1, and §R1.2.3 for the axis note: on the raw `ΔE_H` axis the apex would be at
`dE = -0.24`; §R4 carries the delegated-parcel state, not the axis note). Sign convention: more negative `dE` = stronger binding.

| symbol | Lean | meaning |
|---|---|---|
| `dE` | `dE : ℝ` | descriptor (binding energy of the key intermediate) |
| `alphaA`, `betaA` | `branchUp alphaA betaA dE = alphaA*dE + betaA` | BEP branch of the weak-binding-penalized step |
| `alphaB`, `betaB` | `branchDown alphaB betaB dE = betaB - alphaB*dE` | BEP branch of the strong-binding-penalized step |
| `Ea` | `volcanoBarrier alphaA betaA alphaB betaB dE` | effective (rate-limiting) barrier `= max` of the two |
| `dE*` | `apex alphaA betaA alphaB betaB` | crossing point of the two branches |
| `B*` | `apexBarrier alphaA betaA alphaB betaB` | pass height of the volcano |
| `kB`, `T` | `kB T : ℝ` | Boltzmann constant, temperature (only `0 < kB*T`, `kB*T ≠ 0` are ever used) |
| `a` | `activity f kB T dE = exp (-(f dE)/(kB*T))` | activity (volcano-plot ordinate) |
| — | `VolcanoDescriptor f de0` | `de0` is the unique global minimizer of `f` |
| — | `AntiVolcanoDescriptor f de0` | `de0` is the unique global maximizer of `f` (the activity form) |
| — | `SabatierConforms alphaA alphaB := 0 < alphaA ∧ 0 < alphaB` | series-level conformance verdict |
| — | `TooStrong`/`Optimal`/`TooWeak apexD dE` | point verdicts against the apex |
| — | `NearOptimal tol apexD dE := |dE - apexD| ≤ tol` | tolerance form of "not too strong, not too weak" |
| — | `SZone`/`sabatierZone apexD dE` | decidable three-way classifier (`tooStrong`/`optimal`/`tooWeak`) |
| `λ` | `lam1`, `lam2` (`BEP.eact lam x = (lam - x)^2/(4*lam)`) | reorganization energies of the two steps (S4) |
| `dE*` (parabolic) | `apexPar lam1 lam2` | crossing point of the two Marcus-type parabolas |

House conventions: ASCII identifiers only; parameter order "model parameters first, the varying
descriptor last"; physical premises are explicit hypotheses of every statement; the classifier
lemmas are `…_iff` characterizations (a trichotomy-"characterization" would be a tautology and is
not delivered — the S1 lesson from the Hammond run).

---

## 3. Statement authority and inventory

`theories/Sabatier/probes/sabatier-statement-skeleton.lean` (0 error, placeholder-only bodies) is
the authority: it declares **132 declarations — 105 theorems + 26 definitions + 1 inductive**. Sections: `## S1`
(description layer, 30 declarations — delivered), `## S2` (law layer), `## S3` (sharp conditions),
`## S4` (cross-theory form), `## S5a` (rational layer), `## S5b` (instances). Milestone-scoped
fidelity is checked with the theory-generic checker:

```
python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier [--milestone S1|S2|S3|S4|S5a|S5b]
```

Auxiliary declarations in the delivered files are allowed and reported separately; a **signature
difference is a defect**.

### 3.1 Statement-correction log (the authority changes only through this log)

Two statements of the first skeleton draft were **false** and were replaced after the Sprint-0 risk
probe produced kernel counterexamples — the same defect class the Kasha run recorded ("every
skeleton statement must be spot-checked, not only the ones that look risky"):

1. **`apex_comm` / `volcanoBarrier_comm` (deleted).** Stated as: swapping the two branch labels
   (`(alphaA,betaA,alphaB,betaB) ↦ (alphaB,betaB,alphaA,betaA)`) leaves the apex and the profile
   unchanged. Both are FALSE: the second pair is read through `branchDown`, whose slope is `-alphaB`,
   so the naive swap *negates* the apex (`apex 1 0 1 2 = 1` versus `apex 1 2 1 0 = -1`). The correct
   identity (`apex_relabel`, `volcanoBarrier_relabel`, now in S1) passes the parameters through the
   relabelling `(alphaA,betaA,alphaB,betaB) ↦ (-alphaB,betaB,-alphaA,betaA)`, which really is the
   same two branches with the two ends of the descriptor axis interchanged. Kernel witnesses:
   `apex_naive_swap_values` / `apex_naive_swap_ne` in
   `theories/Sabatier/probes/sabatier-risk-probe.lean` (appended after verifier run 1 pointed out
   that the Sprint-0 probe had carried only the *corrected* forms, not the witnesses).
2. **`activity_descriptor_iff` (replaced).** Stated as: the barrier profile is a volcano iff the
   activity is a volcano (same `VolcanoDescriptor`). FALSE: `activity = exp(-barrier/(kB*T))` is
   strictly *decreasing* in the barrier, so the barrier's unique *minimum* is the activity's unique
   *maximum*; the correct statement (`antiDescriptor_activity_iff`, S2) uses the dual predicate
   `AntiVolcanoDescriptor`, and the volcano-plot headline is `volcanoActivity_peak_iff` (S3).
   Auxiliary renames in the same pass: `activity_apex_le → activity_le_apex` (the inequality's
   direction is now in the name), `volcanoActivity_descriptor_iff → volcanoActivity_peak_iff`.
   The S1 file was delivered after the corrections; the S2–S5a dispatches cite the corrected
   signatures. Kernel witness for the scope of the corrected row: `activity_zero_kT_witness` in the
   same probe shows that at `kB*T = 0` the activity is the constant `1`, so the `0 < kB*T` premise is
   necessary and the docstring that asserted the equivalence unconditionally was corrected.

3. **Instance-row label inversion in S5b (corrected after the append).** The first S5b draft
   classified the catalyst at `dE = 0` of the asymmetric series `(1/2, 0, 1, 1)` (apex `2/3`) as
   *too weak*; the axis convention (more negative `dE` = stronger binding) makes `dE = 0 < 2/3` the
   **too-strong** side, and the barrier there is dominated by the branch penalized by strong binding
   (`volcanoBarrier … 0 = 1`). Caught by `theories/Sabatier/probes/sabatier-instance-check.py`, the
   kernel-independent exact-rational cross-check, *before* the kernel met the row. Fix: the I2 rows
   are now `inst_I2_zone_tooStrong` / `inst_I2_barrier_tooStrong` at `dE = 0` **and**
   `inst_I2_zone_tooWeak` / `inst_I2_barrier_tooWeak` at `dE = 1` (above the apex; barrier `1/2`).
   Class of the defect (third occurrence in this repository): *a label whose meaning depends on a
   sign convention*. Every zone-flavoured row must state which side of the apex it is on, in the
   convention of the theory, and a cross-check must recompute it rather than restate it.

**Authority append (S5b, after the literature round landed).** The literature rows I9–I12 were
appended to the `## S5b` section of the authority once `theories/Sabatier/LITERATURE.md` round 1
fixed the printed numbers and their provenance (the kasha precedent: literature rows enter the
authority after the literature exists). The append adds 12 theorems and changes no existing row; the
S5a section that `prover_c` was implementing at that moment is untouched. The numbers and their axes:
I9–I11 are HER rows on the `ΔG_H*` axis with the symmetric reference volcano (Pt `-0.09`, Au `+0.45`,
W `-0.43` eV; Nørskov et al. 2005 Table I with Eq. [8], `[arith]`), I12 is the *derivable* OER row
(`max (ΔG_O - ΔG_OH, 3.20 - (ΔG_O - ΔG_OH))`, Man et al. 2011 Eq. 4.16–4.18 → apex `16/10 = 8/5` eV,
overpotential `37/100` V).

Two statements were also *added* to S1 as delivered auxiliaries during the same pass
(`branchDown_le_branchUp_of_apex_le`, `branchUp_le_branchDown_of_le_apex`), because the branch
identification lemmas need the non-strict comparison; they are auxiliary declarations, not authority
rows (the fidelity checker reports them as such).

---

## 4. S1 — description layer (`PhotoLean/Sabatier/Basic.lean`; DELIVERED)

Definitions: `branchUp`, `branchDown`, `volcanoBarrier`, `apex`, `apexBarrier`,
`VolcanoDescriptor`, `AntiVolcanoDescriptor`, `activity`, `SabatierConforms`, `TooStrong`,
`Optimal`, `TooWeak`, `NearOptimal`, `SZone` (+`deriving DecidableEq, Repr`), `sabatierZone`.

Theorems: `branch_gap`, `apex_crossing`, `apex_unique_crossing`, `apex_eq_zero_iff` (apex at the
thermoneutral descriptor value exactly when the two offsets balance — the plan's honest form of the
literature's "apex at ΔG = 0 is an idealization"), `apex_relabel`, `volcanoBarrier_relabel`,
`volcanoBarrier_at_apex`, `branchUp_lt_branchDown_of_lt_apex`, `branchDown_lt_branchUp_of_apex_lt`,
`volcanoBarrier_eq_branchUp_of_apex_le`, `volcanoBarrier_eq_branchDown_of_le_apex`,
`sabatierZone_eq_optimal_iff`, `sabatierZone_eq_tooStrong_iff`, `sabatierZone_eq_tooWeak_iff`,
`nearOptimal_iff_band`.

Evidence at freeze: build OK, `check.sh --strict` PASS, 30/30 word-for-word against the authority
(2 auxiliary declarations), `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## 5. S2 — law layer (`PhotoLean/Sabatier/Criterion.lean`; owner prover_b)

`volcanoBarrier_apex_le` (apex is a global minimizer), `volcanoBarrier_eq_apex_iff` (unique
minimizer — the pointed pass), `volcanoBarrier_strictMono_of_apex_le` and
`volcanoBarrier_strictAnti_of_le_apex` (the two legs), `volcanoBarrier_le_apex_add` (the quantitative
tolerance bound: within `tol` of the apex the barrier excess is at most `max alphaA alphaB * tol` —
"not too strong, not too weak" made a number), `volcanoBarrier_apex_form` (excess over the pass =
max of two one-sided penalties), `volcanoBarrier_secSlope_of_apex_le` /
`volcanoBarrier_secSlope_of_le_apex` (the observable leg slopes are `alphaA` and `-alphaB`; the
literature's "volcano legs have slopes ±α"), `apexBarrier_eq`, `volcano_descriptor_of_physical`
(the physical orientation implies the description), the activity layer (`activity_pos`,
`activity_le_apex`, `activity_eq_apex_iff`, `antiDescriptor_activity_iff`, `activity_ratio`) and the
non-vacuity witnesses (`exists_optimal`, `exists_tooWeak`, `exists_tooStrong`,
`exists_nearOptimal` with its `0 ≤ tol` premise — without it the statement is FALSE, a sign premise
that the risk probe caught before dispatch).

## 6. S3 — sharp conditions (`PhotoLean/Sabatier/Sharp.lean`; owner prover_d)

The headline `volcano_descriptor_iff : VolcanoDescriptor … ↔ 0 < alphaA * alphaB`; the contrapositive
`descriptor_fails_of_nonpos_product`; the instance-layer form `volcano_descriptor_iff_labels`;
label invariance `volcano_descriptor_of_neg`; the volcano plot `volcanoActivity_peak_iff`; and the
three failure modes with explicit witnesses — `flat_witness`/`not_descriptor_flat` (both slopes zero:
a constant profile), `plateau_witness`/`not_descriptor_plateau` (one slope zero: the barrier is
minimal on a half-line, so there is no pointed apex), `antiVolcano_monotone`/
`not_descriptor_mixedSign` (opposite-slope signs: the barrier is strictly monotone, the activity has
no interior maximum). The general condition is *label invariant* — a series whose two branches both
"descend" is the same volcano read with the branches interchanged — which is why the sharp statement
is the product form and the physical orientation `0 < alphaA ∧ 0 < alphaB` is the catalysis reading
of it (S1's `SabatierConforms`).

## 7. S4 — microscopic / cross-theory form (`PhotoLean/Sabatier/Compose.lean`; owner prover_a)

Builds the volcano out of the repository's own two-parabola model (`PhotoLean.BEP.eact`):
`parabolaUp`, `parabolaDown`, `parabolicBarrier`, `apexPar`. Theorems:
`linearVolcano_eq_bepTangent` (the BEP-linear volcano with slopes `1/2` is exactly the max of the two
**tangent lines** of the parabolas — the literature's linear volcano as the linear-response form of
this repository's model), `bepLine_le_eact` (a parabola lies above its tangent),
`linearVolcano_le_parabolic` (hence the linear volcano is a pointwise **lower bound**: the
linearization systematically underestimates the barrier away from the apex),
`parabolicBarrier_crossing` / `parabolicBarrier_apex_le` / `parabolicBarrier_eq_apex_iff` /
`parabolic_descriptor` (the two-parabola model is itself a volcano, with the closed-form apex
`√(λ₁λ₂)(√λ₂-√λ₁)/(√λ₁+√λ₂)`; no BEP linearization is needed for the Sabatier description),
`apexPar_self` (a symmetric cycle's apex sits at the thermoneutral descriptor value) and
`linearVolcano_apex_exact` (at that apex the linear and parabolic volcanoes agree exactly).

## 8. S5 — instances and verdicts

### 8.1 S5a — computable rational layer (`PhotoLean/Sabatier/RatModel.lean`; owner prover_c)

ℚ mirrors `branchUpQ`, `branchDownQ`, `volcanoBarrierQ`, `apexQ`, `apexBarrierQ`, `sabatierZoneQ`,
`SabatierConformsQ`, `NearOptimalQ` (the `SZone` inductive is shared with S1), the cast-transfer
lemmas (`branchUpQ_cast`, `branchDownQ_cast`, `volcanoBarrierQ_cast`, `apexQ_cast`,
`apexBarrierQ_cast`, `sabatierZoneQ_eq_sabatierZone`, `sabatierConformsQ_iff`, `nearOptimalQ_iff`),
the ℚ classifier characterizations (`sabatierZoneQ_eq_optimal_iff` / `…_tooStrong_iff` /
`…_tooWeak_iff`) and the ℚ law rows `volcanoBarrierQ_apex_le` / `volcanoBarrierQ_eq_apex_iff`, so
that instance verdicts are discharged by exact rational arithmetic rather than by real-number
analysis.

### 8.2 S5b — instance rows (`PhotoLean/Sabatier/Instances.lean`; owner prover_c, second dispatch)

Two kinds of rows, kept apart on purpose (§12):

- **derivable rows** — the numbers are *theories' own* (rational arithmetic on stated premises), e.g.
  the OER apex `1.60 eV = 3.20/2` (three printed loci, LITERATURE.md §R4), the two-parabola
  cross-check `apexPar 1 4 = 2/3`, the symmetric-cycle rows, the tolerance verdict on the asymmetric
  series (`NearOptimal`, plus the penalty bound instance);
- **literature rows** — numbers transcribed from a printed source with provenance (HER `ΔG_H*` per
  metal on the `ΔG_H* = ΔE_H + 0.24 eV` axis: Pt `-0.09`, Ir `+0.03`, Pd `-0.14`, Rh `-0.10`,
  Ni/Co `-0.27`, Mo `-0.37`, W `-0.43`, Cu `+0.19`, Ag `+0.51`, Au `+0.45`, Nb `-0.56` eV; Nørskov
  et al. 2005 Table I with Eq. [8], arithmetic marked `[arith]` in the literature record). These are
  rows where the *number* is a premise and the *verdict* is kernel-checked.
- **non-conforming rows** — series that fail conformance (`0 < alphaA` fails; mixed signs), decided
  by the kernel with the S3 witnesses, showing that the verdict layer is not vacuous in either
  direction.

## 9. Sprint order, ownership, dispatch

| Sprint | Content | Owner (file ownership is exclusive) |
|---|---|---|
| 0 | contract entry, statement authority, risk probe, API calibration, literature round 1, plan, S1 | lead |
| 1 | S2 / S3 / S4 / S5a in parallel (all depend only on S1) | prover_b (`Criterion.lean`), prover_d (`Sharp.lean`), prover_a (`Compose.lean`), prover_c (`RatModel.lean`) |
| 2 | S5b instance rows (needs S5a + S3) | prover_c (`Instances.lean`) |
| 3 | independent verification (three-layer gate + own probes), RESULTS.md, experience-bank write-back | verifier (read-only) → lead |

Order rule: the riskiest / most upstream claim first — the sharp condition (S3) and the crossing
geometry (S1) were proved at probe level before any dispatch; the S4 parabola/sqrt algebra is the
main open risk (§10). `lakefile.toml` `defaultTargets` gains one line per delivered module, in the
same commit as the module (a module that is not in the default targets is an acceptance hole —
`check.sh` scans the whole source directory while the build covers only the listed targets).

## 10. Risks and mitigations

| risk | state | mitigation |
|---|---|---|
| a skeleton statement is false | **materialized twice** (§3.1) and fixed with kernel counterexamples | the risk probe is the standing instrument; provers are instructed to STOP and report rather than weaken |
| `Real.sqrt` algebra in `apexPar` (S4) | open | risk sketch in the dispatch (substitute `λ = s²`, both parabolas equal `((s1²+s2²)/(2(s1+s2)))²`); `√` API calibrated (`sqrt_pos_of_pos`, `sq_sqrt`, `sqrt_mul`) |
| the ℚ→ℝ transfers do not commute with `max`/`/` | closed by calibration | `Rat.cast_max`, `Rat.cast_lt`, `unfold …Q …; push_cast; ring`, `unfold zoneQ zone; norm_cast` — kernel-verified recipes in `proofs/API-NOTES.md` |
| the tolerance bound silently assumes `0 ≤ tol` | controlled | `NearOptimal` is a closed band; the bound is proven with the sign of `tol` derived from the hypothesis, not assumed; `exists_nearOptimal` carries `0 ≤ tol` explicitly |
| literature numbers transcribed as theorems | guarded | the two-tier instance design (§8.2, §12); each number carries its printed locus in the docstring |
| concurrent writers on one file | n/a | one owner per file (§9); commits touch exactly one source path |

## 11. Acceptance criteria and gate commands

For each module (commands from the contract; `lake` only through `proofs/scripts/lake`):

```
proofs/scripts/lake build PhotoLean.Sabatier.<Module>
proofs/scripts/check.sh --strict PhotoLean.Sabatier.<Module>          # build + placeholder/axiom scan
proofs/scripts/axioms.sh PhotoLean.Sabatier.<Module> PhotoLean.Sabatier.<thm>   # namespace-qualified
python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier --milestone S<k>
git log -1 --oneline                                                  # feat(S<k>): <lemma>
```

Deliverable acceptance = the frozen-tree gate: `proofs/scripts/check.sh --strict` (bare, all default
targets) PASS, every delivered theorem `#print axioms` clean
(`[propext, Classical.choice, Quot.sound]`), fidelity `signature differences: 0` per milestone, and
an independent `verifier` PASS recorded on the board. A worker's report is not acceptance.

## 12. Honesty table — what is assumed, what is proved

| claim | status |
|---|---|
| `Ea(dE) = max (branchUp, branchDown)` | **ASSUMED** (modelling premise; §1.2). The literature's support is a rate-determining-step / energetic-span argument and a Langmuir-coverage treatment on the strong-binding leg, neither of which is the max-form; sources that print a `max` use step free energies, not barriers. Declared in every docstring, never hidden in a definition. |
| both steps are affine (BEP) in the descriptor | **ASSUMED** (empirical linear free-energy relation; the repository's own BEP theory quantifies its error elsewhere) |
| activity `= exp(-Ea/(kB*T))` with a descriptor-independent prefactor | **ASSUMED** |
| apex = crossing point of the branches | **PROVED** (`apex_crossing`, `apex_unique_crossing`) |
| apex is the unique global minimizer iff `0 < alphaA * alphaB` | **PROVED** (`volcano_descriptor_iff`); the condition itself is this theory's exactification — see the negative result in LITERATURE.md (no source states it; sources cite opposite-sign branches and a hinge point) |
| physical orientation `0 < alphaA ∧ 0 < alphaB` ⇒ description | **PROVED** (`volcano_descriptor_of_physical`) |
| label invariance of the sharp condition | **PROVED** (`volcano_descriptor_iff_labels`, `volcano_descriptor_of_neg`) |
| activity has its unique maximum at the apex iff same-sign slopes | **PROVED** (`volcanoActivity_peak_iff`) |
| within `tol` of the apex ⇒ barrier excess ≤ `max(alphaA,alphaB)*tol` | **PROVED** (`volcanoBarrier_le_apex_add`) |
| legs' finite differences are `alphaA` / `-alphaB` | **PROVED** (`volcanoBarrier_secSlope_*`) |
| apex at the thermoneutral descriptor value `dE = 0` | **PROVED, conditionally**: `apex_eq_zero_iff` shows it is *equivalent* to `betaA = betaB` (balanced offsets); the literature reports apex shifts away from the ideal value, so this is a symmetry statement, not a law |
| two-parabola model is a volcano with the closed-form apex | **PROVED** (`parabolic_descriptor`, `apexPar`) |
| the linear BEP volcano is a lower bound on the parabolic one | **PROVED** (`linearVolcano_le_parabolic`) |
| the literature's `α ∈ (0,1)` / `ΔG_H*` values | **DERIVED, not transcribed**: every `ΔG_H*` row is the source's printed `ΔE_H` plus `0.24 eV` by the source's own Eq. [8] (the literature record's `[arith]` column, `LITERATURE.md` §R2.1 note "No source prints a `ΔG_H*` column at all"); the arithmetic is on a source, not a theorem, and the instance rows state which kind of row they are |
| the OER apex `1.60 eV = 3.20/2` | **DERIVABLE** from the stated premises (two separate printed loci, LITERATURE.md §R4) — discharged by the kernel in the instance layer |
| the `*CO ≈ -0.5 eV` value of the CO₂RR family | **ASSUMED NUMBER** (secondary source, fitted value) — if used, it enters as an explicit numerical premise, never as a theorem |
| measured activity, coverages, microkinetics, multiple descriptors, scaling relations | **OUT OF SCOPE** (§1.4) |

## 13. Scope limits (registered, not hidden)

1. One scalar descriptor and one pair of branches: multi-descriptor systems, scaling-relation
   constraints between descriptors, and site/coverage corrections are outside the model.
2. `max` is a *steady-state-free* idealization of the rate-determining step; recrossing, multiple
   parallel paths and non-Arrhenius behaviour are out of scope.
3. The descriptor axis is the free binding energy; the raw `ΔE` axis shifts the apex by the entropy
   term (`ΔG_H* = ΔE_H + 0.24 eV` at HER conditions, Nørskov 2005 Eq. [8]) — instance rows must state
   which axis they use.
4. `alphaA = 0` is treated as a degenerate branch (a plateau) rather than as an unphysical series; the
   theory reports the failure instead of excluding it by fiat.
5. Zero-temperature/zero-`kB*T` limits: all activity statements carry `0 < kB*T` explicitly.
6. The two-parabola composition (S4) identifies the two steps' reaction energies with the descriptor
   and its negative; a general two-step cycle with a non-zero overall driving force is not treated.
7. No claim is made about any *measured* rate or any *specific* real catalyst beyond the transcribed
   numbers and the model's verdict on them.

## 14. Leaves

```
PhotoLean/Sabatier/{Basic,Criterion,Sharp,Compose,RatModel,Instances}.lean
theories/Sabatier/{plan.md,TASKS.md,LITERATURE.md,RESULTS.md}
theories/Sabatier/probes/        statement authority, risk probe, API probes, fidelity cross-checks
theories/Sabatier/literature/    long literature tables (INSTANCE-DATA.md)
proofs/API-NOTES.md              § "Sabatier theory (2026-09-21)" — mathlib calibration
proofs/EXPERIENCE.md             Sprint-0 round record (including the two false statements)
proofs/ENGINE.yml                THEORIES + the five PLAN_/TASKS_/LITERATURE_/PROBES_/RESULT_ entries
```
