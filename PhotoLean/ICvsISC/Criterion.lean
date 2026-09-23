/-
PhotoLean.ICvsISC.Criterion — FC2, the competition laws of IC vs ISC.

`PhotoLean.ICvsISC.Basic` delivers the description layer (the kernel copies, their certificates,
the explicit `HSO²` prefactor, the `FCData` positivity bundle). This module states and proves the
exact laws of the competition:

* FC-C1 `rate_ratio_eq` — **the factorization**: the rate ratio splits into the spin/prefactor
  factor `HSO²·AS/AI` times the Franck–Condon Boltzmann factor of the barrier difference. The
  factoring step is `div_mul_div_comm` and the two exponentials merge through `Real.exp_sub`, so
  the row is an unconditional identity of totalized division (no positivity enters it — see the
  premise note below).
* FC-C2 `log_rate_ratio` — **the log-form competition law**, the row the whole theory is about:
  `log(k_ISC/k_IC) = 2·log HSO + log(AS/AI) + (b_IC − b_ISC)/(kB·T)`. The route is the
  api-probe-calibrated one: `Real.log_mul` (with `HSO²·AS/AI ≠ 0` and `Real.exp_ne_zero`),
  `Real.log (HSO²) = 2·log HSO` through `mul_div_assoc` + `Real.log_pow`, then `Real.log_exp`.
* FC-C3 `isc_dominates_iff` — **the crossover, exactly**: ISC dominates iff its barrier deficit
  beats the spin/prefactor threshold. Both rates are strictly positive under `FCData`, so
  `Real.log_lt_log_iff` transfers the race to the log side; the log difference is FC-C2; the
  remaining arithmetic clears the **positive** thermal energy from the quotient
  (`div_pos_iff_of_pos_right`) and is closed by `linarith`.
* FC-C4 `spin_discount` — **the spin discount**: with equal prefactors (`log(AS/AI) = log 1 = 0`)
  and a sub-unit coupling, FC-C3 plus `Real.log_neg hH0 hH1` gives
  `(kB·T)·(2·log HSO) < 0`, so an ISC win forces a strictly *lower* ISC barrier.
* FC-C5 `hso_zero_isc_absent` — **the El-Sayed boundary as a model row**: at zero spin-orbit
  coupling the ISC rate vanishes, hence the IC channel cannot lose to it, whatever the gaps. The
  second conjunct needs `0 < icRate`; it is discharged from `0 < AI` and `Real.exp_pos` by
  `mul_pos` (row FC-C5 note).
* FC-C6 `barrier_diff_closed_form` — the barrier difference in closed form, read directly off gaps
  and curvatures: `field_simp` + `ring` (api-probe dry-run), with `lamI ≠ 0`, `lamS ≠ 0` the exact
  premises the algebra consumes.
* FC-C7 `equal_prefactors_decision` — **the pure-FC layer**: with unit coupling and equal
  prefactors the race *is* the barrier ordering. `Real.exp_lt_exp` cancels the exponentials, the
  unit prefactor is consumed by `mul_lt_mul_iff_of_pos_left`, and the remaining comparison is the
  barrier order FC-C6/FC-R2 speak about. No `exp` evaluation enters any instance row.

Premise notes (registered for the Phase-3 premise audit, statements unchanged — the authority is
frozen). Two hypotheses of the authority are **decorative** in the sense that the frozen conclusion
does not mention the parameter they constrain: FC-C1's `FCData` bundle (the factoring identity
holds for totalized division with no positivity at all) and FC-C5's `h0 : HSO = 0` (the conclusion
writes the literal `0` in the `HSO` slot, so the equation is not consumed). Both rows are kept
verbatim for signature fidelity with a local `linter.unusedVariables` option, exactly as
`PhotoLean/BEP/Sharp.lean` and `PhotoLean/EnergyGapLaw/Criterion.lean` do for their decorative
premises; the observation is reported on the board rather than silently repaired. FC-C7's
`hH : HSO = 1` is decorative in the same sense, but it *is* consumed: the proof rewrites the
literal `1` of the conclusion back to the parameter `HSO`, proves the general form and
specializes, so no option is needed there.

Every other physical premise is explicit and load-bearing: `0 < HSO` (FC-C2/C3/C4), `0 < AI`
(FC-C4/C7), `0 < kB * T` (FC-C3/C7), `0 < AS` and the reorganization energies via `FCData`;
nothing is hidden in a definition.

Plan locus: `theories/ICvsISC/plan.md` §4 (FC-C rows), §5 (routes), §8 (risks); sprint FC2; board
`theories/ICvsISC/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.ICvsISC.Criterion
    proofs/scripts/check.sh --strict PhotoLean.ICvsISC.Criterion
    proofs/scripts/axioms.sh PhotoLean.ICvsISC.Criterion PhotoLean.ICvsISC.<theorem>

Statement authority: every declaration below matches
`theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean` word for word. The delivered file
contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of
every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately:
the keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out
anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import PhotoLean.ICvsISC.Basic

set_option autoImplicit false

namespace PhotoLean

namespace ICvsISC

/-! ## FC-C — the competition laws -/

set_option linter.unusedVariables false in
/-- The rate ratio factors into spin/prefactor × the Franck–Condon factor.
Plan section 4, row FC-C1. Proof route: `Real.exp_sub`, `Real.exp_neg`, field normal forms. -/
theorem rate_ratio_eq {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) :
    iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI
      = (HSO ^ 2 * AS / AI) * Real.exp ((fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)) := by
  have hmerge : Real.exp (-(fcBarrier lamS xS) / (kB * T)) / Real.exp (-(fcBarrier lamI xI) / (kB * T))
      = Real.exp ((fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hfac :
      HSO ^ 2 * AS * Real.exp (-(fcBarrier lamS xS) / (kB * T))
          / (AI * Real.exp (-(fcBarrier lamI xI) / (kB * T)))
        = (HSO ^ 2 * AS / AI)
          * (Real.exp (-(fcBarrier lamS xS) / (kB * T))
            / Real.exp (-(fcBarrier lamI xI) / (kB * T))) := by
    rw [div_mul_div_comm]
  unfold iscRate icRate
  rw [hfac, hmerge]

/-- The log-form competition law: `log(k_ISC/k_IC)` reads off the barrier difference against the
spin discount `2·log HSO`. Plan section 4, row FC-C2.
Proof route: `Real.log_mul` chains; `Real.log (HSO^2) = 2 * Real.log HSO` via `Real.log_pow`
(plan §5 calibration flag — dry-run in the API probe). -/
theorem log_rate_ratio {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH : 0 < HSO) :
    Real.log (iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI)
      = 2 * Real.log HSO + Real.log (AS / AI)
        + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T) := by
  have hf1 : HSO ^ 2 * AS / AI ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hH)) (ne_of_gt h.posAS))
      (ne_of_gt h.posAI)
  have hf2 : Real.exp ((fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)) ≠ 0 :=
    Real.exp_ne_zero _
  have hlog1 : Real.log (HSO ^ 2 * AS / AI) = 2 * Real.log HSO + Real.log (AS / AI) := by
    rw [mul_div_assoc]
    rw [Real.log_mul (pow_ne_zero 2 (ne_of_gt hH))
        (div_ne_zero (ne_of_gt h.posAS) (ne_of_gt h.posAI)), Real.log_pow]
    norm_num
  rw [rate_ratio_eq h xI xS HSO, Real.log_mul hf1 hf2, hlog1, Real.log_exp]

/-- The crossover, exactly: ISC dominates iff its barrier deficit beats the spin/prefactor
threshold. Plan section 4, row FC-C3.
Proof route: `Real.log_lt_log_iff`, or the ratio-`> 1` form via `lt_div_iff₀` +
`Real.one_lt_exp_iff`. -/
theorem isc_dominates_iff {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH : 0 < HSO) :
    (icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS ↔
      fcBarrier lamS xS - fcBarrier lamI xI
        < (kB * T) * (2 * Real.log HSO + Real.log (AS / AI))) := by
  have hIC : 0 < icRate AI lamI kB T xI := by
    unfold icRate
    exact mul_pos h.posAI (Real.exp_pos _)
  have hISC : 0 < iscRate HSO AS lamS kB T xS := by
    unfold iscRate
    exact mul_pos (mul_pos (pow_pos hH 2) h.posAS) (Real.exp_pos _)
  have hsub : Real.log (icRate AI lamI kB T xI) < Real.log (iscRate HSO AS lamS kB T xS)
      ↔ 0 < Real.log (iscRate HSO AS lamS kB T xS) - Real.log (icRate AI lamI kB T xI) :=
    sub_pos.symm
  have hdiff : Real.log (iscRate HSO AS lamS kB T xS) - Real.log (icRate AI lamI kB T xI)
      = 2 * Real.log HSO + Real.log (AS / AI)
        + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T) := by
    rw [← Real.log_div (ne_of_gt hISC) (ne_of_gt hIC), log_rate_ratio h xI xS HSO hH]
  have h2 : (0 < Real.log (iscRate HSO AS lamS kB T xS) - Real.log (icRate AI lamI kB T xI))
      ↔ 0 < 2 * Real.log HSO + Real.log (AS / AI)
        + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T) := by
    rw [hdiff]
  have h3 : (0 < 2 * Real.log HSO + Real.log (AS / AI)
        + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T))
      ↔ fcBarrier lamS xS - fcBarrier lamI xI
        < (kB * T) * (2 * Real.log HSO + Real.log (AS / AI)) := by
    have hnum : 2 * Real.log HSO + Real.log (AS / AI)
          + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)
        = ((kB * T) * (2 * Real.log HSO + Real.log (AS / AI))
            + (fcBarrier lamI xI - fcBarrier lamS xS)) / (kB * T) := by
      have hd : kB * T ≠ 0 := ne_of_gt h.poskBT
      field_simp
      ring
    rw [hnum, div_pos_iff_of_pos_right h.poskBT]
    constructor <;> intro hh <;> linarith
  exact (Real.log_lt_log_iff hIC hISC).symm.trans (hsub.trans (h2.trans h3))

/-- The spin discount: with equal prefactors and a sub-unit spin-orbit coupling, an ISC win
forces a strictly lower ISC barrier. Plan section 4, row FC-C4.
Proof route: FC-C3 with `Real.log_one` and `2 * Real.log HSO < 0` from `Real.log_neg`. -/
theorem spin_discount {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH0 : 0 < HSO) (hH1 : HSO < 1) (hA : AI = AS)
    (hd : icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS) :
    fcBarrier lamS xS < fcBarrier lamI xI := by
  have hc := (isc_dominates_iff h xI xS HSO hH0).mp hd
  have hlog1 : Real.log (AS / AI) = 0 := by
    rw [← hA, div_self (ne_of_gt h.posAI), Real.log_one]
  have hL : 2 * Real.log HSO + Real.log (AS / AI) < 0 := by
    rw [hlog1, add_zero]
    linarith [Real.log_neg hH0 hH1]
  have hdL : (kB * T) * (2 * Real.log HSO + Real.log (AS / AI)) < 0 :=
    mul_neg_of_pos_of_neg h.poskBT hL
  exact sub_neg.mp (lt_trans hc hdL)

set_option linter.unusedVariables false in
/-- The El-Sayed boundary as a model row: no spin-orbit coupling, no ISC, whatever the gaps.
Plan section 4, row FC-C5.
Proof route: the first conjunct by the zero prefactor; the second from `0 ≤ icRate`, discharged
from `0 < AI` and `Real.exp_pos` via `mul_nonneg` (row FC-C5 note). -/
theorem hso_zero_isc_absent {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS : ℝ) :
    iscRate 0 AS lamS kB T xS = 0 ∧ ¬ (icRate AI lamI kB T xI < iscRate 0 AS lamS kB T xS) := by
  have hzero : iscRate 0 AS lamS kB T xS = 0 := by
    unfold iscRate
    ring
  constructor
  · exact hzero
  · rw [hzero]
    intro hlt
    have hpos : 0 < icRate AI lamI kB T xI := by
      unfold icRate
      exact mul_pos h.posAI (Real.exp_pos _)
    linarith

/-- The barrier difference in closed form: the competition read directly off gaps and
curvatures. Plan section 4, row FC-C6.
Proof route: `field_simp` + `ring` (dry-run in the API probe). -/
theorem barrier_diff_closed_form {lamI lamS xI xS : ℝ} (hlamI : lamI ≠ 0) (hlamS : lamS ≠ 0) :
    fcBarrier lamI xI - fcBarrier lamS xS
      = ((lamI - xI) ^ 2 * lamS - (lamS - xS) ^ 2 * lamI) / (4 * lamI * lamS) := by
  unfold fcBarrier
  field_simp
  ring

/-- The pure-FC layer: with unit coupling and equal prefactors the race IS the barrier
ordering — the comparison the rational decision layer decides (no `exp` evaluation enters any
instance). Plan section 4, row FC-C7.
Proof route: `Real.exp_lt_exp` cancellation + the unit prefactors. -/
theorem equal_prefactors_decision {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS : ℝ) (hA : AI = AS) :
    (icRate AI lamI kB T xI < iscRate 1 AS lamS kB T xS ↔
      fcBarrier lamS xS < fcBarrier lamI xI) := by
  have hisc : iscRate 1 AS lamS kB T xS = AS * Real.exp (-(fcBarrier lamS xS) / (kB * T)) := by
    unfold iscRate
    ring
  have hic : icRate AI lamI kB T xI = AI * Real.exp (-(fcBarrier lamI xI) / (kB * T)) := by
    unfold icRate
    ring
  rw [hisc, hic, ← hA, mul_lt_mul_iff_of_pos_left h.posAI, Real.exp_lt_exp]
  rw [neg_div, neg_div, neg_lt_neg_iff, div_lt_div_iff_of_pos_right h.poskBT]

end ICvsISC

end PhotoLean
