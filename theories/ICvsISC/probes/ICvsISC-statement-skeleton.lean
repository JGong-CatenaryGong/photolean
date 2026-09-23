/-
ICvsISC-statement-skeleton.lean — the STATEMENT AUTHORITY of the ICvsISC theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the
theorem bodies are placeholders on purpose (definitions and the structure carry their real
bodies). This file must compile at 0 error
(`proofs/scripts/lake env lean theories/ICvsISC/probes/ICvsISC-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the placeholder bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory ICvsISC` compares the delivered
signatures to this file word for word.

Plan: `theories/ICvsISC/plan.md` (photophysics batch 2026-09-22, group B, third theory).
Milestones: FC1 (Basic), FC2 (Criterion), FC3 (RatModel), FC4 (Instances).

The theory: internal conversion (IC) vs intersystem crossing (ISC) — two independent
two-parabola Franck–Condon barrier computations whose rates are Marcus rates over their own gaps
and reorganization energies, with ISC carrying the explicit spin-orbit prefactor `HSO²`. The
competition law factors the rate ratio into spin/prefactor × the FC factor; with equal prefactors
and `0 < HSO < 1` an ISC win forces a strictly lower ISC barrier (the spin discount); at
`HSO = 0` the ISC channel is shut whatever the gaps (the El-Sayed boundary as a model row). The
theory carries its own copies of the kernel barrier / Marcus rate, pinned by `rfl` certificates
(plan §1.2, hard constraint 1). El-Sayed's rule enters only as the parameter `HSO` — registered,
never derived (plan §9). Literature anchors: `theories/ICvsISC/LITERATURE.md` (S1 the rule's
origin, S3 the competition picture).
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace ICvsISC

/-! ## FC-B — copies, certificates, definitions (Phase-2 module `PhotoLean/ICvsISC/Basic.lean`) -/

/-- The Franck–Condon barrier of one channel: reorganization energy `lam`, gap `x`. The theory's
own copy of the kernel barrier (plan §1.2, hard constraint 1), pinned by `cert_fcBarrier`.
Plan section 4, row FC-B1. -/
noncomputable def fcBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Certificate: the theory's barrier copy IS the delivered kernel barrier.
Plan section 4, row FC-B1. Proof route: `rfl`. -/
theorem cert_fcBarrier {lam x : ℝ} : fcBarrier lam x = PhotoLean.Kernel.barrier lam x := by
  sorry

/-- The IC rate: Arrhenius over the channel's own barrier with prefactor `AI`.
Plan section 4, row FC-B2. -/
noncomputable def icRate (AI lamI kB T xI : ℝ) : ℝ :=
  AI * Real.exp (-(fcBarrier lamI xI) / (kB * T))

/-- Certificate: the IC rate IS the delivered Marcus rate.
Plan section 4, row FC-B2. Proof route: `unfold` + `rfl`. -/
theorem cert_icRate {AI lamI kB T xI : ℝ} :
    icRate AI lamI kB T xI = PhotoLean.Marcus.rate AI lamI kB T xI := by
  sorry

/-- The ISC rate: Arrhenius over the channel's own barrier with the explicit spin-orbit
prefactor `HSO² · AS` (physical premise visibility: the coupling enters squared, so no sign
premise on `HSO`). Plan section 4, row FC-B3. -/
noncomputable def iscRate (HSO AS lamS kB T xS : ℝ) : ℝ :=
  HSO ^ 2 * AS * Real.exp (-(fcBarrier lamS xS) / (kB * T))

/-- The premise bundle: positivity of both prefactors, both reorganization energies, and the
thermal energy `kB · T`. No `HSO` sign premise — the amplitude enters squared.
Plan section 4, row FC-B4. -/
structure FCData (AI AS lamI lamS kB T : ℝ) : Prop where
  /-- Positive IC prefactor. -/
  posAI : 0 < AI
  /-- Positive ISC base prefactor. -/
  posAS : 0 < AS
  /-- Positive IC reorganization energy. -/
  posLamI : 0 < lamI
  /-- Positive ISC reorganization energy. -/
  posLamS : 0 < lamS
  /-- Positive thermal energy. -/
  poskBT : 0 < kB * T

/-! ## FC-C — the competition laws (Phase-2 module `PhotoLean/ICvsISC/Criterion.lean`) -/

/-- The rate ratio factors into spin/prefactor × the Franck–Condon factor.
Plan section 4, row FC-C1. Proof route: `Real.exp_sub`, `Real.exp_neg`, field normal forms. -/
theorem rate_ratio_eq {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) :
    iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI
      = (HSO ^ 2 * AS / AI) * Real.exp ((fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T)) := by
  sorry

/-- The log-form competition law: `log(k_ISC/k_IC)` reads off the barrier difference against the
spin discount `2·log HSO`. Plan section 4, row FC-C2.
Proof route: `Real.log_mul` chains; `Real.log (HSO^2) = 2 * Real.log HSO` via `Real.log_pow`
(plan §5 calibration flag — dry-run in the API probe). -/
theorem log_rate_ratio {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH : 0 < HSO) :
    Real.log (iscRate HSO AS lamS kB T xS / icRate AI lamI kB T xI)
      = 2 * Real.log HSO + Real.log (AS / AI)
        + (fcBarrier lamI xI - fcBarrier lamS xS) / (kB * T) := by
  sorry

/-- The crossover, exactly: ISC dominates iff its barrier deficit beats the spin/prefactor
threshold. Plan section 4, row FC-C3.
Proof route: `Real.log_lt_log_iff`, or the ratio-`> 1` form via `lt_div_iff₀` +
`Real.one_lt_exp_iff`. -/
theorem isc_dominates_iff {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH : 0 < HSO) :
    (icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS ↔
      fcBarrier lamS xS - fcBarrier lamI xI
        < (kB * T) * (2 * Real.log HSO + Real.log (AS / AI))) := by
  sorry

/-- The spin discount: with equal prefactors and a sub-unit spin-orbit coupling, an ISC win
forces a strictly lower ISC barrier. Plan section 4, row FC-C4.
Proof route: FC-C3 with `Real.log_one` and `2 * Real.log HSO < 0` from `Real.log_neg`. -/
theorem spin_discount {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hH0 : 0 < HSO) (hH1 : HSO < 1) (hA : AI = AS)
    (hd : icRate AI lamI kB T xI < iscRate HSO AS lamS kB T xS) :
    fcBarrier lamS xS < fcBarrier lamI xI := by
  sorry

/-- The El-Sayed boundary as a model row: no spin-orbit coupling, no ISC, whatever the gaps.
Plan section 4, row FC-C5.
Proof route: the first conjunct by the zero prefactor; the second from `0 ≤ icRate`, discharged
from `0 < AI` and `Real.exp_pos` via `mul_nonneg` (row FC-C5 note). -/
theorem hso_zero_isc_absent {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (h0 : HSO = 0) :
    iscRate 0 AS lamS kB T xS = 0 ∧ ¬ (icRate AI lamI kB T xI < iscRate 0 AS lamS kB T xS) := by
  sorry

/-- The barrier difference in closed form: the competition read directly off gaps and
curvatures. Plan section 4, row FC-C6.
Proof route: `field_simp` + `ring` (dry-run in the API probe). -/
theorem barrier_diff_closed_form {lamI lamS xI xS : ℝ} (hlamI : lamI ≠ 0) (hlamS : lamS ≠ 0) :
    fcBarrier lamI xI - fcBarrier lamS xS
      = ((lamI - xI) ^ 2 * lamS - (lamS - xS) ^ 2 * lamI) / (4 * lamI * lamS) := by
  sorry

/-- The pure-FC layer: with unit coupling and equal prefactors the race IS the barrier
ordering — the comparison the rational decision layer decides (no `exp` evaluation enters any
instance). Plan section 4, row FC-C7.
Proof route: `Real.exp_lt_exp` cancellation + the unit prefactors. -/
theorem equal_prefactors_decision {AI AS lamI lamS kB T : ℝ} (h : FCData AI AS lamI lamS kB T)
    (xI xS HSO : ℝ) (hA : AI = AS) (hH : HSO = 1) :
    (icRate AI lamI kB T xI < iscRate 1 AS lamS kB T xS ↔
      fcBarrier lamS xS < fcBarrier lamI xI) := by
  sorry

/-! ## FC-R — the rational decision layer (Phase-2 module `PhotoLean/ICvsISC/RatModel.lean`) -/

namespace Rat

/-- The ℚ shadow of the Franck–Condon barrier. Plan section 4, row FC-R1. -/
def fcBarrier (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Cast coherence: the ℚ shadow computes the real barrier.
Plan section 4, row FC-R1. Proof route: `push_cast` + `ring` (dry-run in the API probe). -/
theorem fcBarrier_cast {lam x : ℚ} :
    _root_.PhotoLean.ICvsISC.fcBarrier (lam : ℝ) (x : ℝ) = (fcBarrier lam x : ℝ) := by
  sorry

/-- The barrier-order decision at ℚ: `true` iff the ISC barrier is strictly lower than the IC
barrier — the FC-C7 comparison, computed. Plan section 4, row FC-R2. -/
def barrierOrderQ (lamI xI lamS xS : ℚ) : Bool :=
  decide (fcBarrier lamS xS < fcBarrier lamI xI)

/-- Correctness of the decision: the Bool computes the real barrier order.
Plan section 4, row FC-R2.
Proof route: unfold `barrierOrderQ`, `of_decide_eq_true` / `decide_eq_true_eq`, then
`fcBarrier_cast` + `Rat.cast_lt`. -/
theorem barrierOrderQ_correct {lamI xI lamS xS : ℚ} :
    barrierOrderQ lamI xI lamS xS = true ↔
      _root_.PhotoLean.ICvsISC.fcBarrier (lamS : ℝ) (xS : ℝ) <
        _root_.PhotoLean.ICvsISC.fcBarrier (lamI : ℝ) (xI : ℝ) := by
  sorry

end Rat

/-! ## FC-I — named instances: representative rational models
(Phase-2 module `PhotoLean/ICvsISC/Instances.lean`) -/

/-- The aromatic-carbonyl-like instance (`lamI = 1, xI = 3/2, lamS = 1/2, xS = 1`, `HSO = 1/10`,
`AI = AS`): the barriers are `1/16` (IC) vs `1/8` (ISC) — the ISC barrier is *higher*, so with
equal prefactors and `HSO < 1` the spin discount makes the win harder. The verdict is computed at
the barrier level (`decide`), and the FC-C4 direction is registered contrapositively: the ISC
barrier is not lower, so FC-C4 gives no ISC win. Plan section 4, row FC-I1.
Proof route: `norm_num` at ℚ for the barrier values; the verdict via `decide_eq_false_iff_not`
+ `norm_num` (bare `by decide` does not reduce ℚ-literal Bools in the kernel — probe-calibrated;
values pre-computed in the API probe). -/
theorem aromaticCarbonylLike :
    Rat.fcBarrier 1 (3 / 2) = 1 / 16 ∧ Rat.fcBarrier (1 / 2) 1 = 1 / 8 ∧
      ¬ (Rat.fcBarrier (1 / 2) 1 < Rat.fcBarrier 1 (3 / 2)) ∧
        Rat.barrierOrderQ 1 (3 / 2) (1 / 2) 1 = false := by
  sorry

/-- The El-Sayed-favored-like instance (`HSO = 1`, `AI = AS`, `lamI = 1, xI = 3/2, lamS = 2,
xS = 3/2`): a pure barrier race. The probe-recomputed barriers (plan §8: recomputed before the
row was written) are `1/16` (IC) vs `1/32` (ISC), so the ISC barrier is strictly lower and the
FC-C7 verdict is `true`. Plan section 4, row FC-I2.
Proof route: `norm_num` at ℚ for the barrier values; the verdict via `decide_eq_true_eq` +
`norm_num` (probe-calibrated). -/
theorem elSayedFavoredLike :
    Rat.fcBarrier 1 (3 / 2) = 1 / 16 ∧ Rat.fcBarrier 2 (3 / 2) = 1 / 32 ∧
      Rat.fcBarrier 2 (3 / 2) < Rat.fcBarrier 1 (3 / 2) ∧
        Rat.barrierOrderQ 1 (3 / 2) 2 (3 / 2) = true := by
  sorry

/-- The zero-coupling witness (`HSO = 0`, arbitrary gaps): the ISC prefactor vanishes at ℚ for
any base prefactor `AS` — the FC-C5 boundary decided on the prefactor side (no gap data enters).
Plan section 4, row FC-I3. Proof route: `simp` / `mul_zero` at ℚ. -/
theorem hsoZeroWitness (AS : ℚ) : (0 : ℚ) ^ 2 * AS = 0 := by
  sorry

end ICvsISC

end PhotoLean
