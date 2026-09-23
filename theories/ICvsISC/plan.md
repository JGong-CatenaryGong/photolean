# theories/ICvsISC/plan.md — PhotoLean formalization plan: internal conversion vs intersystem crossing — the Franck–Condon competition (FC1–FC4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/ICvsISC-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/ICvsISC/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group B (two-parabola basis),
> third theory of the group.

---

## 1. Overall goal and boundaries

### 1.1 The claim

Internal conversion (IC) and intersystem crossing (ISC) are both nonradiative transitions whose
Franck–Condon-weighted rates, in the classical two-parabola picture, are Marcus rates over their
own gaps and reorganization energies — except that ISC carries the spin-orbit coupling prefactor
`H_SO²`. The competition law: `log(k_ISC/k_IC) = 2·log H_SO + log(A_S/A_I) +
(b_IC − b_ISC)/(k_BT)` — the race is read off the **barrier difference** against a spin
discount; with equal prefactors and `0 < H_SO < 1`, ISC wins only when its FC barrier is
*strictly lower* (the spin discount); with `H_SO = 0` the ISC channel is shut regardless of
gaps (the El-Sayed boundary as a model row).

### 1.2 The model (chosen, not derived)

Two independent two-parabola barrier computations (IC channel: `lamI, xI`; ISC channel:
`lamS, xS`), Arrhenius rates with prefactors `AI`, `HSO²·AS`. The theory carries **its own
copies** of the kernel barrier pinned by `rfl` certificates (hard constraint 1). El-Sayed's rule
(the orbital dependence of `H_SO`) is a parameter premise — registered, never derived.

### 1.3 Explicit non-goals

* No spin-orbit coupling theory (H_SO is a parameter).
* No hot ISC from upper vibrational levels (the gaps are the 0-0/vertical data as given).
* No reverse channels.

## 2. Conventions and symbols

`lamI, xI` / `lamS, xS` — reorganization energy and gap of the IC / ISC channel; `AI, AS > 0`
prefactors; `HSO ≥ 0` the spin-orbit coupling amplitude (enters as `HSO²`); `kB·T > 0`.
Namespace `PhotoLean.ICvsISC`; rational layer `PhotoLean.ICvsISC.Rat`.

## 3. Statement authority and inventory

The authority is `probes/ICvsISC-statement-skeleton.lean` (Phase-1 placeholder bodies; sha256 on
the board once compiling).

### 3.1 Statement-correction log

* **Entry 2 (FC-C5/FC-C7, 2026-09-23, Phase-3 premise audit)** — the hypothesis
  `h0 : HSO = 0` of `hso_zero_isc_absent` and `hH : HSO = 1` of `equal_prefactors_decision` were
  dropped together with their now-unused `HSO` binders: both conclusions bake the literal
  (`iscRate 0 …`, `iscRate 1 …`), so the hypotheses were decorative at the statement level
  (verifier run 4, F2); the primed proof of FC-C7 now works on the literal directly.
* **Entry 3 (FC-I3, 2026-09-23, Phase-3 vacuity audit, verifier run 4 finding F3)** —
  `hsoZeroWitness` was re-frozen from the tautology `(0 : ℚ) ^ 2 * AS = 0` (`zero_mul`, no model
  object) to the spin-discount witness: `Rat.barrierOrderQ 1 (3/2) 2 (3/2) = true ∧
  iscRate (0 : ℝ) 1 2 1 1 (3/2) = 0` — the pure barrier race is won by ISC (`1/32 < 1/16`) yet
  with the coupling shut the ISC rate vanishes.

* **Entry 1 (FC-I2 instance barrier, 2026-09-22, probe recompute; plan-text sync 2026-09-23 after
  verifier run 4 finding F1)** — the §4 draft questioned `1/16`; the probe recomputed the ISC
  barrier as `1/32` (`fcBarrier 2 (3/2) = (2 − 3/2)²/(4·2) = 1/32`), so the pure-FC race is
  `1/32 < 1/16` and ISC wins. The authority and the delivered row carry `1/32`; this entry records
  the plan-text sync.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (FC-B), `Criterion.lean` (FC-C), `RatModel.lean` (FC-R),
`Instances.lean` (FC-I).

**FC-B (copies + certificates + definitions):**

* FC-B1 `fcBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)`;
  `cert_fcBarrier : fcBarrier lam x = PhotoLean.Kernel.barrier lam x` (`rfl`).
* FC-B2 `icRate (AI lamI kB T xI : ℝ) : ℝ := AI * Real.exp (-(fcBarrier lamI xI) / (kB * T))`;
  `cert_icRate : icRate AI lamI kB T xI = PhotoLean.Marcus.rate AI lamI kB T xI`
  (`unfold` + `rfl`).
* FC-B3 `iscRate (HSO AS lamS kB T xS : ℝ) : ℝ :=
  HSO ^ 2 * AS * Real.exp (-(fcBarrier lamS xS) / (kB * T))` — the spin-orbit prefactor is
  explicit (physical premise visibility).
* FC-B4 `structure FCData (AI AS lamI lamS kB T : ℝ) : Prop` with fields `0 < AI`, `0 < AS`,
  `0 < lamI`, `0 < lamS`, `0 < kB * T` — the premise bundle (no `HSO` sign premise: the
  amplitude enters squared).

**FC-C (the competition laws):**

* FC-C1 `rate_ratio_eq (h : FCData ...) (xI xS HSO : ℝ) :
  iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI
    = (HSO ^ 2 * AS / AI) * Real.exp ((fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T))` —
  the ratio factors into spin/prefactor × the FC factor.
* FC-C2 `log_rate_ratio (h : FCData ...) (hH : 0 < HSO) :
  Real.log (iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI)
    = 2 * Real.log HSO + Real.log (AS / AI)
      + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)` — the log-form competition law.
* FC-C3 `isc_dominates_iff (h : FCData ...) (hH : 0 < HSO) :
  (icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS ↔
    fcBarrier lamS xS - fcBarrier lamI xI
      < (kB * T) * (2 * Real.log HSO + Real.log (AS / AI)))` — the crossover, exactly.
* FC-C4 `spin_discount (h : FCData ...) (hH0 : 0 < HSO) (hH1 : HSO < 1)
  (hA : AI = AS) (hd : icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS) :
  fcBarrier lamS xS < fcBarrier lamI xI` — with equal prefactors and a sub-unit spin-orbit
  coupling, an ISC win forces a strictly lower ISC barrier.
* FC-C5 `hso_zero_isc_absent (h : FCData ...) (h0 : HSO = 0) :
  iscRate 0 AS lamS kB T xS = 0 ∧ ¬ (icRate AI lamI kB T xI < iscRate 0 AS lamS kB T xS)` —
  the El-Sayed boundary: no spin-orbit coupling, no ISC, whatever the gaps. (The second conjunct
  needs `0 ≤ icRate` — discharge from `0 < AI` and `Real.exp_pos` via `mul_nonneg`.)
* FC-C6 `barrier_diff_closed_form (hlamI : lamI ≠ 0) (hlamS : lamS ≠ 0) :
  fcBarrier lamI xI - fcBarrier lamS xS
    = ((lamI - xI) ^ 2 * lamS - (lamS - xS) ^ 2 * lamI) / (4 * lamI * lamS)` — the competition
  read directly off gaps and curvatures.
* FC-C7 `equal_prefactors_decision (h : FCData ...) (hA : AI = AS) (hH : HSO = 1) :
  (icRate AI lamI kB T xI < iscRate 1 AS lamS kB T xS ↔
    fcBarrier lamS xS < fcBarrier lamI xI)` — the pure-FC layer: with unit coupling and equal
  prefactors the race is the barrier ordering (the rational decision layer decides **this**
  comparison; no `exp` evaluation enters any instance).

**FC-R (rational decision layer):**

* FC-R1 `Rat.fcBarrier (lam x : ℚ) : ℚ` + cast coherence.
* FC-R2 the FC-C7 specialization decided at ℚ: `Rat.barrierOrderQ (lamI xI lamS xS : ℚ) : Bool`
  with the correctness row `(barrierOrderQ ... = true) ↔ (fcBarrier cast ...) < ...` on ℝ.

**FC-I (named instances, representative rational models):**

* FC-I1 `aromaticCarbonylLike` (lamI = 1, xI = 3/2, lamS = 1/2, xS = 1, HSO = 1/10, AI = AS):
  barriers `1/16` vs `1/8` — the ISC barrier is *higher*, the spin discount makes the win
  harder; verdict computed at the barrier level (`decide`) + the FC-C4 direction registered.
* FC-I2 `elSayedFavoredLike` (HSO = 1, AI = AS, lamI = 1, xI = 3/2, lamS = 2, xS = 3/2): pure
  barrier race, ISC barrier `1/32` < IC barrier `1/16` (probe-recomputed — §3.1 entry 1); the row states
  the exact rational comparison and the FC-C7 verdict.
* FC-I3 `hsoZeroWitness` (HSO = 0, arbitrary gaps): ISC absent (FC-C5), decided at ℚ on the
  prefactor side.

## 5. Proof routes

FC-C1: `Real.exp_sub`, `exp_neg`, field normal forms. FC-C2: `Real.log_mul` chains
(`Real.log_rpow`? no — `HSO^2` gives `Real.log (HSO^2) = 2 * Real.log HSO` via
`Real.log_pow` or `log_mul` + `sq`; calibrate). FC-C3: `Real.log_lt_log_iff` / the ratio `> 1`
form via `lt_div_iff` + `Real.one_lt_exp_iff`. FC-C4: FC-C3 with `Real.log_one` and
`2·log HSO < 0` (`Real.log_neg`). FC-C7: `Real.exp_lt_exp` cancellation + the unit prefactors.
All risk sits in the `Real.log/exp` API surface — shared with EnergyGapLaw's probe (reuse its
API rows; add only `Real.log_pow`).

## 6. Sprint order, ownership, dispatch

Sprint FC0 (Phase 1) → FC1 `Basic` → FC2 `Criterion` → FC3 `RatModel` → FC4 `Instances`.
Owner: prover_a (group B block, after EnergyGapLaw).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.ICvsISC.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.ICvsISC.Criterion
    proofs/scripts/axioms.sh PhotoLean.ICvsISC.Criterion PhotoLean.ICvsISC.isc_dominates_iff
    python3 theories/BEP/probes/bep-fidelity.py --theory ICvsISC

## 8. Risks and mitigations

* The `log` of a product of three factors (spin² × prefactor ratio × exp) is the API-heaviest
  row; the probe must confirm `Real.log_pow` / `Real.log_mul` associativity patterns first.
* FC-I2's numbers must be recomputed by the probe before the row is written (the skeleton carries
  the probe-checked values).

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Classical two-parabola FC factors for both channels | FC-C rows |
| 2 | El-Sayed's rule enters only as the parameter `HSO` (LITERATURE) | — |
| 3 | `FCData` positivity bundle explicit on every row | — |
| 4 | Named instances are representative rational models | their barrier verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **EnergyGapLaw — composition (machine target)**: both FC rates are EG rates; FC-C3 inherits
  the EG monotonicity (one row: at fixed curvature the ISC window is a gap window).
* **FluorPhos — composition (machine target)**: `kISC` of FluorPhos is `iscRate` here; the
  crossover (FP-C6) moves with the gaps (one conditional row carrying the identification as an
  explicit hypothesis, the Kasha §7 pattern).
* **Marcus — certificates**: FC-B1/B2.
* **Kasha — composition candidate**: the ladder's `ic n` rates are the IC channel of this
  theory (extends Relations §7; one row).
* **StokesShift — certificate**: shared surfaces; no independent content (one row at most).
* **SternVolmer / QuantumYield / KashaVavilov / Forster / Einstein / Sabatier / Goldschmidt /
  SymmetryFactor / Hammond / BEP**: no edge — absence drafts registered.

## 11. Position in the repository

Seventh theory of the batch, third of group B; imports `PhotoLean.Kernel` and
`PhotoLean.Marcus.Basic` for the certificates; nothing delivered is modified.
