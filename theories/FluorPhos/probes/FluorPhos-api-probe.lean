/-
fluorPhos API-calibration probe (FP0-b, iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/FluorPhos/probes/FluorPhos-api-probe.lean
Expected: exit 0. Calibration results are reported back to the lead with the Phase-1 dispatch;
registration in proofs/API-NOTES.md is the api_researcher's leaf (this worker does not touch
proofs/).

Coverage:
* the division/order API for the FP-C proof routes (plan §5),
* the ℚ→ℝ cast API for the FP-R1 cast-coherence rows,
* decidability/norm_num at ℚ for the FP-R2 zone verdicts and the FP-I instances,
* the plan's pre-computed witnesses (FP-C8, FP-I1, FP-I2, FP-I3) as proved examples
  (probes are calibration tools; examples here MAY be proved, as in the symmetryFactor probe),
* the kernel-checked counterexample behind the FP-C5 premise correction (plan §3.1 entry 1)
  and a dry-run of the corrected monotonicity route.
-/
import Mathlib

-- ── division / order API (FP-C1..C6 routes, plan §5) ─────────────────────────
#check @div_self
#check @div_eq_iff
#check @eq_div_iff
#check @div_le_iff₀
#check @div_lt_iff₀
#check @lt_div_iff₀
#check @le_div_iff₀
#check @div_lt_div_iff₀
#check @div_lt_div_iff_of_pos_left
#check @div_lt_div_iff_of_pos_right
#check @div_nonneg
#check @div_pos
#check @mul_pos
#check @mul_nonneg
#check @mul_lt_mul_of_pos_right
#check @add_pos
#check @add_nonneg
#check @add_eq_zero_iff_of_nonneg
#check @mul_eq_zero

-- ── ℚ→ℝ cast API (FP-R1 cast coherence, FP-R2 correctness rows) ─────────────
#check @Rat.cast_zero
#check @Rat.cast_one
#check @Rat.cast_add
#check @Rat.cast_mul
#check @Rat.cast_div
#check @Rat.cast_lt
#check @Rat.cast_le
#check @Rat.cast_pos
#check @Rat.cast_nonneg
#check @Rat.cast_inj

-- ── tactic availability for the FP-C routes (field_simp / ring / nlinarith / norm_num) ──
example {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b / (a * b) = 1 := by
  field_simp

-- ── FP-C8 witness pre-computation (plan: kF = kISC = kIC = kP = kNR = 1 gives
--    phiF = 1/3, phiP = 1/6, both channels live) ──────────────────────────────
example : (1 : ℝ) / (1 + 1 + 1) = 1 / 3 := by norm_num
example : ((1 : ℝ) / (1 + 1 + 1)) * (1 / (1 + 1)) = 1 / 6 := by norm_num
example : (1 : ℝ) / (1 + 1 + 1) = 1 / 3 ∧ ((1 : ℝ) / (1 + 1 + 1)) * (1 / (1 + 1)) = 1 / 6 := by
  constructor <;> norm_num

-- ── FP-I1 pre-computation (naphthaleneLike: kF = 1, kISC = 1, kIC = 1/2, kP = 1/10,
--    kNR = 1; phiF = 2/5, phiP = 2/55) and the fluorDominant comparison ───────
example : (1 : ℚ) / (1 + 1 + 1 / 2) = 2 / 5 := by norm_num
example : ((1 : ℚ) / (1 + 1 + 1 / 2)) * ((1 / 10) / (1 / 10 + 1)) = 2 / 55 := by norm_num
-- NOTE (calibration finding): bare `decide` FAILS on ℚ comparisons of literal arithmetic in
-- v4.17.0 — the kernel reduction of `Rat.instDecidableLt` gets stuck on `Rat.blt` applied to
-- unevaluated `OfNat`/mul/add expressions (measured 2026-09-22 on the three zone comparisons
-- below). The calibrated route for the FP-R2/FP-I verdicts is `norm_num` (the plan's FP-I3
-- "decide at ℚ" note is superseded; statements are unaffected).
example : (1 : ℚ) * (1 / 10 + 1) > 1 * (1 / 10) := by norm_num

-- ── FP-I2 pre-computation (eosinLike: kF = 1, kISC = 10, kIC = 1/2, kP = 1, kNR = 1):
--    the phosphorDominant comparison and the FP-C6 premise arithmetic ─────────
example : (1 : ℚ) * (1 + 1) < 10 * 1 := by norm_num
example : (0 : ℚ) < 1 + 10 + 1 / 2 ∧ (0 : ℚ) < 1 + 1 := by constructor <;> norm_num

-- ── FP-I3 pre-computation (crossoverWitness): the threshold kF·(kP+kNR)/kP = 2 at
--    kF = kP = kNR = 1, straddled by kISC = 1 (fluorDominant) and kISC = 3 (phosphorDominant) ──
example : (1 : ℚ) * (1 + 1) / 1 = 2 := by norm_num
example : (1 : ℚ) * (1 + 1) > 1 * 1 := by norm_num
example : (1 : ℚ) * (1 + 1) < 3 * 1 := by norm_num

-- ── cast numeral bridge (symmetryFactor lesson: use explicit numeral lemmas, not mod_cast) ──
example : ((2 / 5 : ℚ) : ℝ) = 2 / 5 := by norm_num
example : ((2 / 55 : ℚ) : ℝ) = 2 / 55 := by norm_num

-- ── plan §3.1 entry 1 evidence: at kF = kIC = 0 the ISC branch is pinned at 1, so phiP is
--    constant in kISC — the strict-monotonicity half of FP-C5 as first drafted (premises
--    `FPData`, `0 < kP`, `kISC < kISC'` only) is FALSE; the premise `0 < kF + kIC` is
--    load-bearing and has been added to the skeleton row. ─────────────────────
example {kISC kISC' : ℝ} (h0 : 0 < kISC) (hlt : kISC < kISC') :
    (kISC / (0 + kISC + 0)) * (1 / (1 + 1)) = (kISC' / (0 + kISC' + 0)) * (1 / (1 + 1 : ℝ)) := by
  have h1 : kISC / ((0 : ℝ) + kISC + 0) = 1 := by
    rw [show (0 : ℝ) + kISC + 0 = kISC by ring, div_self (ne_of_gt h0)]
  have h2 : kISC' / ((0 : ℝ) + kISC' + 0) = 1 := by
    rw [show (0 : ℝ) + kISC' + 0 = kISC' by ring, div_self (ne_of_gt (lt_trans h0 hlt))]
  rw [h1, h2]

-- ── corrected FP-C5 route dry-run: the ISC branch kISC ↦ kISC/(kISC + c) is strictly
--    monotone exactly when c = kF + kIC > 0 (the added premise). ──────────────
example {kISC kISC' c : ℝ} (hc : 0 < c) (h0 : 0 ≤ kISC) (hlt : kISC < kISC') :
    kISC / (kISC + c) < kISC' / (kISC' + c) := by
  have hs : 0 < kISC + c := by linarith
  have hs' : 0 < kISC' + c := by linarith
  rw [div_lt_div_iff₀ hs hs']
  nlinarith [mul_lt_mul_of_pos_right hlt hc]
