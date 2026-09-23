/-
ICvsISC API-calibration probe (Sprint 0, iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/ICvsISC/probes/ICvsISC-api-probe.lean
Expected: exit 0. Every `#check` output is recorded in proofs/API-NOTES.md §ICvsISC.

The probe (a) confirms every mathlib / delivered-PhotoLean name the statement skeleton and the
plan §5 proof routes use, and (b) pre-computes the FC-I instance witnesses the plan flags for
probe-checking (plan §4 FC-I2, §8: the numbers are recomputed HERE before the row is written).
Probe-local mirrors carry the same definitions because the skeleton file is not an importable
module. Probe examples MAY be proved (probes are calibration tools, the exemplar probe does
this).
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

-- delivered-PhotoLean tie-back targets (plan §11; FC-B1/B2 certificates)
#check @PhotoLean.Kernel.barrier
#check @PhotoLean.Marcus.barrier
#check @PhotoLean.Marcus.rate

-- mathlib exp/log API (skeleton statements + plan §5/§8 proof routes)
#check @Real.exp
#check @Real.log
#check @Real.exp_add
#check @Real.exp_sub
#check @Real.exp_neg
#check @Real.exp_pos
#check @Real.exp_nonneg
#check @Real.exp_ne_zero
#check @Real.exp_lt_exp
#check @Real.one_lt_exp_iff
#check @Real.exp_log
#check @Real.log_exp
#check @Real.log_mul
#check @Real.log_div
#check @Real.log_inv
#check @Real.log_pow
#check @Real.log_one
#check @Real.log_neg
#check @Real.log_lt_log_iff

-- order / field API
#check @lt_div_iff₀
#check @div_lt_iff₀
#check @mul_nonneg
#check @div_pos

-- Bool / decide API (the rational decision layer)
#check @of_decide_eq_true
#check @decide_eq_true_eq
#check @decide_eq_false_iff_not

-- cast API (ℚ → ℝ coherence)
#check @Rat.cast_inj
#check @Rat.cast_lt

namespace ICvsISCProbe

/-- Probe-local mirror of the skeleton's `fcBarrier` (row FC-B1). -/
noncomputable def fcBarrierR (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Probe-local mirror of the skeleton's `icRate` (row FC-B2). -/
noncomputable def icRateR (AI lamI kB T xI : ℝ) : ℝ :=
  AI * Real.exp (-(fcBarrierR lamI xI) / (kB * T))

/-- Probe-local mirror of the skeleton's `Rat.fcBarrier` (row FC-R1). -/
def fcBarrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Probe-local mirror of the skeleton's `Rat.barrierOrderQ` (row FC-R2). -/
def barrierOrderQ (lamI xI lamS xS : ℚ) : Bool :=
  decide (fcBarrierQ lamS xS < fcBarrierQ lamI xI)

-- FC-B1 certificate route (plan: `rfl`).
example (lam x : ℝ) : fcBarrierR lam x = PhotoLean.Kernel.barrier lam x := rfl

-- FC-B2 certificate route (plan: `unfold` + `rfl`; plain `rfl` already closes it).
example (AI lamI kB T xI : ℝ) :
    icRateR AI lamI kB T xI = PhotoLean.Marcus.rate AI lamI kB T xI := rfl

-- FC-R1 cast-coherence route.
example (lam x : ℚ) :
    (fcBarrierQ lam x : ℝ) = ((lam : ℝ) - (x : ℝ)) ^ 2 / (4 * (lam : ℝ)) := by
  unfold fcBarrierQ
  push_cast
  ring

-- FC-I1 pre-computation (aromaticCarbonylLike): barriers 1/16 (IC) vs 1/8 (ISC) — the ISC
-- barrier is higher, the barrier-race verdict is `false`.
example : fcBarrierQ 1 (3 / 2) = 1 / 16 := by norm_num [fcBarrierQ]
example : fcBarrierQ (1 / 2) 1 = 1 / 8 := by norm_num [fcBarrierQ]
example : ¬ (fcBarrierQ (1 / 2) 1 < fcBarrierQ 1 (3 / 2)) := by norm_num [fcBarrierQ]
-- NOTE (calibrated): bare `by decide` does NOT reduce the ℚ-literal Bool in the kernel
-- (`Int.decNonneg` gets stuck); the working verdict route is the decide-iff lemma + `norm_num`.
example : barrierOrderQ 1 (3 / 2) (1 / 2) 1 = false := by
  unfold barrierOrderQ
  rw [decide_eq_false_iff_not]
  norm_num [fcBarrierQ]

-- FC-I2 pre-computation (elSayedFavoredLike) — plan §8: recomputed HERE before the row is
-- written. Result: IC barrier 1/16, ISC barrier 1/32 (NOT 1/16): the ISC barrier is strictly
-- lower, the FC-C7 verdict is `true`.
example : fcBarrierQ 1 (3 / 2) = 1 / 16 := by norm_num [fcBarrierQ]
example : fcBarrierQ 2 (3 / 2) = 1 / 32 := by norm_num [fcBarrierQ]
example : fcBarrierQ 2 (3 / 2) < fcBarrierQ 1 (3 / 2) := by norm_num [fcBarrierQ]
example : barrierOrderQ 1 (3 / 2) 2 (3 / 2) = true := by
  rw [barrierOrderQ, decide_eq_true_eq]
  norm_num [fcBarrierQ]

-- FC-I3 (hsoZeroWitness): the ISC prefactor at `HSO = 0`, arbitrary base prefactor.
example (AS : ℚ) : (0 : ℚ) ^ 2 * AS = 0 := by simp

-- FC-C6 algebra route, dry-run on the mirror.
example (lamI lamS xI xS : ℝ) (hlamI : lamI ≠ 0) (hlamS : lamS ≠ 0) :
    fcBarrierR lamI xI - fcBarrierR lamS xS
      = ((lamI - xI) ^ 2 * lamS - (lamS - xS) ^ 2 * lamI) / (4 * lamI * lamS) := by
  unfold fcBarrierR
  field_simp
  ring

-- FC-C2 key step (plan §5 calibration flag): `Real.log (HSO^2) = 2 * Real.log HSO`.
example {HSO : ℝ} (_hH : 0 < HSO) : Real.log (HSO ^ 2) = 2 * Real.log HSO := by
  rw [Real.log_pow]
  norm_num

-- FC-C1 core step, dry-run: the exp factors merge into the barrier difference.
example (bI bS kBT : ℝ) :
    Real.exp (-bS / kBT) / Real.exp (-bI / kBT) = Real.exp ((bI - bS) / kBT) := by
  rw [← Real.exp_sub]
  congr 1
  ring

end ICvsISCProbe
