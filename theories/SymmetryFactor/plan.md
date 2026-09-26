# theories/SymmetryFactor/plan.md — PhotoLean formalization plan: the symmetry-factor adjudication (F1–F4)

> Status: **delivered and independently verified (2026-09-21, same-day; verifier run 1 PASS on the
> board)** — F1–F4, five
> modules, 35 declarations, author-gated (build / strict scan / `#print axioms` / fidelity 35/35).
> The statement authority
> `theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean` (sha256 recorded on the
> board) is the state every delivered signature matches word for word; §3.1 records the two
> Sprint-0 statement corrections. Adopted from the H1-crossing plan (its planning notes are held
> outside the repository) under direct human instruction; the H1 goal and the pre-registered
> literature decision rule are inherited verbatim from that plan.
> Authority: contract `proofs/ENGINE.yml`; board `theories/SymmetryFactor/TASKS.md`; experience
> bank `proofs/EXPERIENCE.md`; literature `theories/SymmetryFactor/LITERATURE.md`.
> Human request (2026-09-21): execute the H1-crossing plan — deliver the first **adjudicated
> conflation** (a reading the literature takes as a universal working value, decided by the kernel
> with an exact validity boundary), then integrate it into the relation graph.

---

## 1. Overall goal and boundaries

### 1.1 The claim being adjudicated

Electrochemical kinetics works with a **symmetry factor** β (Butler–Volmer) and an observable
**transfer coefficient** α (Tafel slope). The modelling literature *usually takes both to be 0.5*
(LITERATURE S1, verbatim: "α the so-called anodic (cathodic) charge transfer coefficient, usually
both taken to be equal to 0.5"); IUPAC's own Technical Report warns that the value "can by no means
be assumed" and predicts "large deviations of β from 0.5" when the two force constants differ
(LITERATURE S2, printed pp. 255–257). This theory turns that warning into a **machine-checked
equivalence boundary** inside the two-parabola model generalized to unequal curvatures:

* the thermoneutral crossing coordinate of `V_r(q) = kr·q²` against `V_p(q) = kp·(q−1)² + ΔG°` is
  `tsCoordZero kr kp = √kp / (√kr + √kp)` (existence, uniqueness on `[0,1]`, calculus-free);
* **the verdict**: `BetaHalfReading kr kp ↔ kr = kp` (`betaHalf_iff_equalForceConstants`) — the
  β = 1/2 reading coincides with the structural transfer coefficient **exactly** in the
  equal-curvature regime;
* kernel-checked witnesses: `(1,4) ↦ 2/3 ≠ 1/2` (refutation), `(4,1) ↦ 1/3` (direction
  asymmetry), `(λ,λ) ↦ 1/2` (the whole equal-curvature family, tied back to `Kernel.tsCoord` and
  `BEP.transfer` by certificates);
* the chemical reading of the asymmetry: the crossing sits on the side of the **softer** well — a
  stiffer product well gives a *late* transition state at **zero** driving force
  (`tsCoordZero_gt_half_iff_stiffProduct`), a Hammond-style verdict with no driving force at all.

**Why this is the H1 crossing** (existence form): a pair of readings the literature treats as
interchangeable (S1 performs the identification unqualified; S2/S3 document that it needs
conditions) is **decided** by the kernel, with the exact boundary (`kr = kp`) and rational
witnesses — and the decision *explains the persistence of the conflation*: the equal-curvature
Marcus picture, the diagram every textbook draws, is precisely the regime where the identification
holds (`betaHalf_holds_in_kernel`).

### 1.2 The model (chosen, not derived)

Two classical harmonic surfaces with **independent** curvature parameters `kr`, `kp` (the kernel's
equal-curvature model is the `kr = kp` diagonal); reaction coordinate `q ∈ [0,1]`; transition state
= classical crossing point; driving-force convention `x = −ΔG°` with this milestone fixed at
thermoneutrality `x = 0`. Totalized division and totalized `Real.sqrt` (negative inputs ↦ 0) are
Lean conventions, registered here and in every docstring that relies on them.

### 1.3 Explicit non-goals (registered, not hidden)

1. The **kinetic** reading α = −∂Ea/∂x at general driving force for unequal curvatures (needs the
   general-`x` crossing profile and a derivative/secant-limit argument — analysis substrate,
   METHOD.md §7 boundary). The thermoneutral structural reading suffices for the verdict; the
   IUPAC warning sentence is about the same comparison.
2. The Leffler α = q‡ identification **under asymmetry** (its breakdown is the stretch goal of the
   H1 plan §6; registered as future work, not attempted here).
3. Temperature/solvent dependence, tunnelling corrections, the `αc + αa = n/ν` complementarity
   law beyond the delivered BEP single-electron row.
4. No measured electrode kinetics: instance rows are kernel facts about **declared numbers**.

## 2. Conventions and symbols

| symbol | meaning |
|---|---|
| `kr`, `kp` | reactant / product curvature parameters (`ℝ`; physical regime `0 < ·`) |
| `tsCoordZero kr kp` | thermoneutral crossing coordinate `√kp/(√kr+√kp)` |
| `BetaHalfReading kr kp` | the claim `tsCoordZero kr kp = 1/2` |
| `a`, `b` | ℚ square-roots of the curvatures in the decision layer (`kr = a²`, `kp = b²`) |
| `tsCoordZeroQ a b` | the ℚ shadow `b/(a+b)` |

## 3. Statement authority and inventory

The authority is `probes/SymmetryFactor-statement-skeleton.lean` (compiles at 0 error with
placeholders; calibrated before any proof work per iron rule 2, with the API probe
`probes/SymmetryFactor-api-probe.lean` settling every mathlib name first per iron rule 4).

### 3.1 Statement-correction log (the authority changes only through this log)

| date | row | what was wrong | correction | evidence |
|---|---|---|---|---|
| 2026-09-21 | F1 `tsCoordZero_nonneg` | first draft carried `(hkr : 0 ≤ kr) (hkp : 0 ≤ kp)`; **neither is load-bearing** — totalized `Real.sqrt` is nonnegative on every input and totalized division gives `0/0 = 0`, so the row is true unconditionally | both premises dropped (weakest-premise standard, iron rule 3 — the Goldschmidt item-2/5 discipline applied *during* Sprint 0 rather than after a verifier round) | the delivered proof consumes no premise; the linter reports none unused |
| 2026-09-21 | F1 `tsCoordZero_le_one` | same defect class, same two premises | both premises dropped | same |
| 2026-09-21 | F0 API round (no authority row) | four guessed names **do not exist** in this toolchain: `Real.sqrt_four`, `sq_eq_sq_iff_eq_or_eq`, `BEP.transfer_thermoneutral`@Basic (it lives in `BEP.Criterion`), and bare `norm_num` does **not** evaluate `Real.sqrt` of perfect-square numerals | the `Real.sqrt_sq` route (`show (4:ℝ) = 2^2; rw [Real.sqrt_sq]`), `sq_eq_sq_iff_abs_eq_abs`, import `BEP.Criterion`; recorded in `proofs/API-NOTES.md` §symmetryFactor | probe runs (exit codes) in the round's shell history; corrected names re-probed |

### 3.2 Inventory

| milestone | module | content (declarations) |
|---|---|---|
| F1 | `PhotoLean/SymmetryFactor/Basic.lean` | 5 definitions + 1 theorem = **6** |
| F1 | `PhotoLean/SymmetryFactor/Criterion.lean` | 9 theorems = **9** |
| F2 | `PhotoLean/SymmetryFactor/Sharp.lean` | 10 theorems = **10** |
| F3 | `PhotoLean/SymmetryFactor/RatModel.lean` | 2 definitions + 3 theorems = **5** |
| F4 | `PhotoLean/SymmetryFactor/Instances.lean` | 5 theorems = **5** |
| **total** | | **35 declarations** (28 theorems + 7 definitions) |

## 4. Proof routes (calibrated by the API probe before dispatch)

* Crossing uniqueness is **calculus-free**: at a crossing inside `[0,1]`, the quantities `√kr·q` and
  `√kp·(1−q)` are nonnegative with equal squares (`sq_eq_sq_iff_abs_eq_abs` + `abs_of_nonneg`),
  hence equal; a linear solve gives the closed form (`eq_div_iff` + `ring`).
* The interval restriction is load-bearing and its necessity is a **delivered witness**
  (`crossing_witness_outside_interval`: at `(1,4)` the second real root `q = 2` satisfies the
  crossing equation outside `[0,1]`).
* The verdict iff reduces to `√kp = √kr ↔ kp = kr` (`div_eq_iff`, `Real.sq_sqrt`).
* Monotonicity: `div_lt_div_iff₀` (LEFT denominator first — measured), `Real.sqrt_lt_sqrt`,
  `mul_lt_mul_of_pos_right/left`, `linarith`.
* ℚ layer: perfect-square curvatures make the shadow exact (`Real.sqrt_mul_self` + `Rat.cast_div`);
  the reading-bridge uses `Rat.cast_inj` and an explicit `((1/2:ℚ):ℝ) = 1/2` numeral lemma —
  `norm_cast`/`exact_mod_cast` were **tried and rejected** (the `(1/2:ℝ)` numeral does not present
  as a `Rat.cast`, so mod_cast reports a type mismatch; measured).
* `field_simp` alone does **not** close `√lam/(√lam+√lam) = 1/2` (measured: unsolved goals); the
  deterministic route is `div_eq_iff` + `ring`.

## 5. Sprint order, ownership, dispatch

Single-sprint delivery under direct human instruction (the review-fix session acts as lead+prover;
independent verification is dispatched afterwards, per iron rule 6 — the writer does not
adjudicate). Order: F0 (literature L1/L2 + API probe + skeleton) → F1 → F2 → F3 → F4 → relation
graph integration (Relations.lean §11 + RELATIONS.md + README closeout, iron rule 8).

## 6. Acceptance criteria and gate commands

```bash
proofs/scripts/lake build                                                    # all targets incl. the five new modules
proofs/scripts/check.sh --strict                                             # leaf plane 7/7 + build + scan → verdict: PASS
proofs/scripts/lake env lean theories/SymmetryFactor/probes/SymmetryFactor-statement-skeleton.lean   # authority compiles (placeholders)
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor          # 35/35 word-for-word, 0 differences
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor --milestone F1   # 15/15 scoped
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Sharp PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Instances PhotoLean.SymmetryFactor.inst_conflation_falsified
```

Independent verification (to be dispatched): re-run all gates; adversarial rounds — (i) the
**vacuity pass** of the review-fix round (attempt `∀`-forms of every `∃`-row and of
`BetaHalfReading`/`not_betaHalf_universal`; a compile is a finding), (ii) premise-consumption audit
(weakest-premise standard), (iii) documentation plane.

## 7. Risks and mitigations

| risk | mitigation | status |
|---|---|---|
| L1 conflation locus not found first-hand | pre-registered decision rule (H1 plan §3): deliver as "machine-checked boundary of an IUPAC-warned identification", H1∃ stays open — **not needed**: S1 found and read first-hand (arXiv 2104.05424 §2.1) | closed |
| √-algebra friction | Goldschmidt squared-pattern + API probe before dispatch; four guessed names caught at probe stage | closed |
| `norm_num` on `Real.sqrt` | measured boundary; `Real.sqrt_sq` route | closed |
| cast numerals `(1/2:ℝ)` vs `↑(1/2:ℚ)` | explicit `hone` + `Rat.cast_inj` (norm_cast rejected, measured) | closed |

## 8. Honesty table — what is assumed, what is proved

| claim | status |
|---|---|
| two harmonic surfaces, classical crossing = TS, thermoneutral scope | **modelling assumption** (§1.2) |
| `tsCoordZero` closed form, existence + uniqueness on `[0,1]` | **theorem** (F1) |
| interval restriction load-bearing | **theorem** (witness `q = 2` at `(1,4)`) |
| `BetaHalfReading kr kp ↔ kr = kp` | **theorem** (F2 headline) |
| refutation witnesses `(1,4) ↦ 2/3`, `(4,1) ↦ 1/3` | **theorem** + ℚ-layer kernel decisions |
| equal-curvature tie-backs to `Kernel.tsCoord` / `BEP.transfer` | **theorem** (certificates) |
| kinetic reading (derivative), general driving force, Leffler-under-asymmetry | **not formalized** (§1.3) — registered |
| instance rows | kernel facts about **declared numbers**, not measurements |
| "the literature usually takes 0.5" | **literature record** (S1, first-hand read; a modelling-practice locus, not a theorem about chemistry) |

## 9. Position in the repository

Seventh node of the relation graph. Edges: specialization certificates to `PhotoLean.Kernel` and
`PhotoLean.BEP` (equal-curvature diagonal), registered as the graph's first **adjudicated
conflation** (class A1, `PhotoLean/Relations.lean` §11); expected no-edges to Kasha / Sabatier /
Goldschmidt (no shared scalar; import facts recorded in the registry). Imports: `Basic` ←
`Mathlib`; `Criterion` ← `Basic`; `Sharp` ← `Criterion` + `Kernel` + `BEP.Criterion`; `RatModel` ←
`Basic`; `Instances` ← `RatModel` + `Sharp`.
