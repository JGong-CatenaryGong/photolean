/-
EnergyGapLaw API-calibration probe (Sprint 0, iron rule 4: no guessed names).
Run: proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean
Expected: exit 0, no `sorry`. Every `#check` confirms a name that the statement skeleton
(`EnergyGapLaw-statement-skeleton.lean`) or its plan-§5 proof routes use; the proved `example`s
pre-compute the EG-I instance witnesses the plan flags for probe-checking (plan §4 EG-I3, §8:
the numbers are recomputed HERE before the row is written). Probe-local mirrors carry the same
definitions because the skeleton file is not an importable module. Probe examples MAY be proved
(probes are calibration tools, the exemplar probe does this).

Calibration headline (LITERATURE.md, statement-impact summary, item 1): the EG-I3 defect
magnitude at `lam = 1/2`, `kB * T = 1/40`, `x* = 3/2`, `x = 2` is **5**, not the plan draft's
parenthetical `−20` — verified below by `norm_num` before the row is written.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic
import PhotoLean.BEP.Sharp

set_option autoImplicit false

-- delivered-PhotoLean tie-back targets (plan §11; EG-B1..B3 certificates)
#check @PhotoLean.Kernel.barrier
#check @PhotoLean.Marcus.barrier
#check @PhotoLean.Marcus.rate
#check @PhotoLean.Marcus.InvertedRegion

-- the second-difference engine EG-S3 mirrors (plan §4 row EG-S3: "calibrate the pattern there")
#check @PhotoLean.BEP.not_epLinearOn_of_ne_zero

-- mathlib exp/log API (skeleton statements + plan §5/§8 proof routes)
#check @Real.exp
#check @Real.log
#check @Real.exp_pos
#check @Real.exp_ne_zero
#check @Real.exp_lt_exp
#check @Real.exp_strictMono
#check @Real.exp_log
#check @Real.log_exp
#check @Real.log_mul

-- order / field API (the division normal forms of plan §5, and the order consumers)
#check @div_div
#check @neg_div
#check @div_pos
#check @div_nonneg
#check @mul_pos
#check @sq_nonneg
#check @sq_eq_zero_iff
#check @sub_pos

-- Set / interval API (the EG-S3 window)
#check @Set.Icc
#check @Set.mem_Icc

-- Bool / decide API (the rational decision layer)
#check @decide_eq_true_eq
#check @decide_eq_false_iff_not

-- cast API (ℚ → ℝ coherence)
#check @Rat.cast_lt
#check @Rat.cast_inj

namespace EnergyGapLawProbe

/-- Probe-local mirror of the skeleton's `nrBarrier` (row EG-B1). -/
noncomputable def nrBarrierR (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Probe-local mirror of the skeleton's `nrRate` (row EG-B2). -/
noncomputable def nrRateR (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(nrBarrierR lam x) / (kB * T))

/-- Probe-local mirror of the skeleton's `eglTangent` (row EG-S1). -/
noncomputable def eglTangentM (A lam kB T xStar x : ℝ) : ℝ :=
  Real.log (nrRateR A lam kB T xStar) + (lam - xStar) / (2 * lam * (kB * T)) * (x - xStar)

/-- Probe-local mirror of the skeleton's `InvertedGap` (row EG-B3). -/
def InvertedGapM (lam x : ℝ) : Prop := lam < x

/-- Probe-local mirror of the skeleton's `Rat.nrBarrier` (row EG-R1). -/
def nrBarrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Probe-local mirror of the skeleton's `EGZone` (row EG-R2). -/
inductive EGZoneM | normal | barrierless | inverted
  deriving DecidableEq

/-- Probe-local mirror of the skeleton's `egZoneQ` (row EG-R2). -/
def egZoneQM (lam x : ℚ) : EGZoneM :=
  if x < lam then EGZoneM.normal
  else if lam < x then EGZoneM.inverted
  else EGZoneM.barrierless

/-- Probe-local mirror of the skeleton's `nrRate_decidable_order` (row EG-R3): decides the
strict rate increase from gap `x₁` to gap `x₂` on the barrier side. -/
def nrRateOrderM (lam x₁ x₂ : ℚ) : Bool :=
  decide (nrBarrierQ lam x₂ < nrBarrierQ lam x₁)

-- EG-B1 certificate route (plan: `rfl`, definitional copy).
example (lam x : ℝ) : nrBarrierR lam x = PhotoLean.Kernel.barrier lam x := rfl

-- EG-B2 certificate route (plan: `unfold` + `rfl`; plain `rfl` already closes it).
example (A lam kB T x : ℝ) :
    nrRateR A lam kB T x = PhotoLean.Marcus.rate A lam kB T x := rfl

-- EG-B3 certificate route (plan: `Iff.rfl`).
example (lam x : ℝ) : InvertedGapM lam x ↔ PhotoLean.Marcus.InvertedRegion lam x := Iff.rfl

-- EG-C1 route dry-run (plan §5: `Real.log_mul` + `Real.log_exp`, then field normal forms) —
-- the risk surface of the batch, calibrated before the skeleton's docstrings cite it.
example {A lam kB T x : ℝ} (hA : 0 < A) (hlam : lam ≠ 0) (hkT : 0 < kB * T) :
    Real.log (nrRateR A lam kB T x)
      = Real.log A - (lam - x) ^ 2 / (4 * lam * (kB * T)) := by
  have hkT0 : kB * T ≠ 0 := ne_of_gt hkT
  unfold nrRateR nrBarrierR
  rw [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

-- EG-R1 cast-coherence route (the ℚ shadow computes the real barrier at cast parameters).
example (lam x : ℚ) :
    (nrBarrierQ lam x : ℝ) = ((lam : ℝ) - (x : ℝ)) ^ 2 / (4 * (lam : ℝ)) := by
  unfold nrBarrierQ
  push_cast
  ring

-- EG-R2 zone-verdict route: instance zone verdicts are closed by `norm_num [egZoneQM]`.
example : egZoneQM (1 / 2) 1 = .inverted := by norm_num [egZoneQM]
example : egZoneQM (1 / 2) (3 / 2) = .inverted := by norm_num [egZoneQM]
example : egZoneQM (1 / 2) 2 = .inverted := by norm_num [egZoneQM]
example : egZoneQM 2 (1 / 2) = .normal := by norm_num [egZoneQM]
example : egZoneQM 2 1 = .normal := by norm_num [egZoneQM]
example : egZoneQM 2 2 = .barrierless := by norm_num [egZoneQM]

-- EG-R2 correctness-row route (the plan's cast row): unfold the classifier, trichotomy by
-- `by_cases`, then `Rat.cast_lt`.
example {lam x : ℚ} : (egZoneQM lam x = .inverted) ↔ (lam : ℝ) < (x : ℝ) := by
  rw [Rat.cast_lt]
  unfold egZoneQM
  by_cases h1 : x < lam
  · rw [if_pos h1]
    exact ⟨fun h => EGZoneM.noConfusion h, fun h => absurd h (not_lt_of_gt h1)⟩
  · rw [if_neg h1]
    by_cases h2 : lam < x
    · rw [if_pos h2]
      exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg h2]
      exact ⟨fun h => EGZoneM.noConfusion h,
             fun h => absurd (le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)) (ne_of_lt h)⟩

-- EG-R3 decide route (calibrated ICvsISC note: bare `by decide` does NOT reduce ℚ-literal
-- Bools in the kernel; the working route is the decide-iff lemma + `norm_num`).
example : nrRateOrderM (1 / 2) (3 / 2) 1 = true := by
  unfold nrRateOrderM
  rw [decide_eq_true_eq]
  norm_num [nrBarrierQ]
example : nrRateOrderM (1 / 2) 2 (3 / 2) = true := by
  unfold nrRateOrderM
  rw [decide_eq_true_eq]
  norm_num [nrBarrierQ]
example : nrRateOrderM 2 (1 / 2) 1 = true := by
  unfold nrRateOrderM
  rw [decide_eq_true_eq]
  norm_num [nrBarrierQ]

-- EG-I1 pre-computation (aromaticSeries, plan §8: recomputed HERE before the row is written) —
-- ℝ side, the dispatch's three barrier values.
example : (1 / 2 - 1 : ℝ) ^ 2 / (4 * (1 / 2)) = 1 / 8 := by norm_num
example : (1 / 2 - 3 / 2 : ℝ) ^ 2 / (4 * (1 / 2)) = 1 / 2 := by norm_num
example : (1 / 2 - 2 : ℝ) ^ 2 / (4 * (1 / 2)) = 9 / 8 := by norm_num
-- ℚ side, the instance row itself: the barrier chain `1/8 < 1/2 < 9/8` (all gaps inverted).
example : nrBarrierQ (1 / 2) 1 = 1 / 8 := by norm_num [nrBarrierQ]
example : nrBarrierQ (1 / 2) (3 / 2) = 1 / 2 := by norm_num [nrBarrierQ]
example : nrBarrierQ (1 / 2) 2 = 9 / 8 := by norm_num [nrBarrierQ]
example : nrBarrierQ (1 / 2) 1 < nrBarrierQ (1 / 2) (3 / 2) ∧
    nrBarrierQ (1 / 2) (3 / 2) < nrBarrierQ (1 / 2) 2 := by
  norm_num [nrBarrierQ]

-- EG-I2 pre-computation (normalRegionCounter): at `lam = 2` the barriers DECREASE in the gap
-- (`9/32` at `x = 1/2`, `1/8` at `x = 1`), so the rate increases with the gap.
example : nrBarrierQ 2 (1 / 2) = 9 / 32 := by norm_num [nrBarrierQ]
example : nrBarrierQ 2 1 = 1 / 8 := by norm_num [nrBarrierQ]
example : nrBarrierQ 2 1 < nrBarrierQ 2 (1 / 2) := by norm_num [nrBarrierQ]

-- EG-I3 pre-computation (tangentWitness, plan §8: recomputed HERE before the row is written).
-- The exact defect magnitude is 5 — the plan draft's parenthetical `−20` is wrong
-- (LITERATURE.md, statement-impact summary, item 1).
example : ((2 : ℝ) - 3 / 2) ^ 2 / (4 * (1 / 2) * (1 / 40)) = 5 := by norm_num

-- EG-I3 full-equation route dry-run on the mirrors: after the EG-C1 rewrite both `log A` terms
-- cancel and `norm_num` closes the defect equation `lnRate 2 = eglTangent (3/2) 2 − 5`.
example {A : ℝ} (hA : 0 < A) :
    Real.log (nrRateR A (1 / 2) 1 (1 / 40) 2)
      = eglTangentM A (1 / 2) 1 (1 / 40) (3 / 2) 2 - 5 := by
  have key : ∀ x : ℝ,
      Real.log (nrRateR A (1 / 2) 1 (1 / 40) x)
        = Real.log A - (1 / 2 - x) ^ 2 / (4 * (1 / 2) * (1 * (1 / 40))) := by
    intro x
    unfold nrRateR nrBarrierR
    rw [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _), Real.log_exp]
    field_simp
    ring
  unfold eglTangentM
  rw [key 2, key (3 / 2)]
  -- calibrated: after the rewrite the goal is the atom-carrying identity
  -- `Real.log A - 45 = Real.log A - 20 + -20 - 5`; bare `norm_num` leaves it, `ring` closes it.
  ring

-- EG-C2/C3 sign factor (plan §5): the quadratic comparison factors as
-- `(x₂ − x₁) * (x₁ + x₂ − 2 * lam)`; the region premises fix the sign. Dry-run both regimes.
example {lam x₁ x₂ : ℝ} (hx1 : lam < x₁) (h : x₁ < x₂) :
    (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr h) (by linarith : x₁ + x₂ - 2 * lam > 0)]
example {lam x₁ x₂ : ℝ} (hx2 : x₂ < lam) (h : x₁ < x₂) :
    (lam - x₂) ^ 2 < (lam - x₁) ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr h) (by linarith : 2 * lam - x₁ - x₂ > 0)]

end EnergyGapLawProbe
