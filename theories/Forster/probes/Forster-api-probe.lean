/-
Forster-api-probe.lean — API-calibration probe for the Forster theory (FO0; iron rule 4: no
guessed names). Run:

  proofs/scripts/lake env lean theories/Forster/probes/Forster-api-probe.lean

Expected: exit 0. The `#check` block calibrates every mathlib name the statement authority
(`Forster-statement-skeleton.lean`) and the plan-§5 proof routes use. The proved `example`s are
the plan-mandated witness pre-computations (plan §4 FO-I1 "recompute in the probe"), the FO-R2
`decide` route dry-run, and dry-runs of the risky FO-C proof routes (plan §5). Probes are
calibration tools: examples MAY be proved (the SymmetryFactor exemplar probe does the same).

Findings are reported to the lead for `proofs/API-NOTES.md` (that file is api_researcher-owned;
this probe is the evidence).
-/
import Mathlib

set_option autoImplicit false

-- ── the skeleton's own external names (signatures and definition bodies) ──────────────
#check @Real.sin
#check @Real.cos
#check @Real.pi
#check @StrictMonoOn
#check @Set.Ioi
#check @Set.Icc
#check @Finset.sum
#check @Finset.univ
#check (2 : Fin 3)

-- ── FO-C1 / FO-C2 routes (plan §5): squares, abs, trigonometric bounds ───────────────
#check @sq_nonneg
#check @sq_le_sq
#check @sq_abs
#check @abs_le
#check @abs_add
#check @abs_sub
#check @abs_mul
#check @abs_nonneg
#check @Real.sin_sq_add_cos_sq
#check @Real.cos_sq_add_sin_sq
#check @Real.sin_sq_le_one
#check @Real.cos_sq_le_one
#check @Real.abs_sin_le_one
#check @Real.abs_cos_le_one
#check @Real.sin_pi_div_two
#check @Real.cos_pi_div_two
#check @Real.sin_zero
#check @Real.cos_zero

-- ── FO-C4 / FO-C7 / FO-C8 / FO-C10 / FO-C11 routes (plan §5): field algebra ──────────
#check @div_pow
#check @div_pos
#check @div_nonneg
#check @zero_div
#check @div_zero
#check @lt_div_iff₀
#check @div_lt_iff₀
#check @div_lt_div_iff₀
#check @mul_div_cancel_left₀
#check @mul_div_cancel_right₀
#check @ne_of_gt
#check @pow_ne_zero
#check @mul_le_mul_of_nonneg_left
#check @mul_lt_mul_of_pos_right
#check @one_ne_zero
#check @sub_zero

-- ── FO-R1 cast bridges (the SymmetryFactor lesson: the name is `Rat.cast_inj`) ───────
#check @Rat.cast_inj
#check @Rat.cast_div
#check @Rat.cast_add
#check @Rat.cast_mul
#check @Rat.cast_pow
#check @Rat.cast_one
#check @Rat.cast_zero

-- ══ proved examples (calibration witnesses) ═════════════════════════════════════════

-- FO-I1 recompute (plan §4: "recompute in the probe; the row states the exact rational
-- efficiency"). The probe value is 64/793 — the plan's printed `64/729` does NOT survive
-- recomputation: (3/2)^6 = 729/64, so 1/(1 + (3/2)^6) = 64/(64 + 729) = 64/793.
example : (1 : ℚ) / (1 + (3 / 2) ^ 6) = 64 / 793 := by norm_num
example : (1 : ℝ) / (1 + (3 / 2) ^ 6) = 64 / 793 := by norm_num
-- … and 64/729 is the value of the *reciprocal-shaped* expression 1/(3/2)^6 = (2/3)^6,
-- which is what the plan's ellipsis apparently printed:
example : (1 : ℚ) / ((3 / 2) ^ 6) = 64 / 729 := by norm_num

-- FO-R2 dry run, corrected at probe time: `decide` does not reduce ℚ division/multiplication
-- (measured boundary, cf. `PhotoLean.Marcus.RatModel` lines 15-16), and `norm_num` with
-- `Fin.ext_iff` overflows the recursion depth. The working kernel route is: the frame factor is
-- INTEGER-valued (every axis-aligned pair gives 0, 1 or 4), so decide the sum over ℤ and finish
-- the average over ℚ by norm_num. The skeleton's FO-R2 carries this two-step shape.
def frameKappaProbe (i j k : Fin 3) : ℤ :=
  ((if i = j then 1 else 0) - 3 * (if i = k then 1 else 0) * (if j = k then 1 else 0)) ^ 2

example : (∑ i : Fin 3, ∑ j : Fin 3, frameKappaProbe i j 2) = 6 := by decide
example : ((∑ i : Fin 3, ∑ j : Fin 3, frameKappaProbe i j 2 : ℤ) : ℚ) / 9 = 2 / 3 := by
  norm_num [show (∑ i : Fin 3, ∑ j : Fin 3, frameKappaProbe i j 2) = 6 from by decide]

-- FO-R3 dry runs (ℚ decision-layer shadows of the named instances).
def fretEff6Q (r6 R : ℚ) : ℚ := r6 / (r6 + R ^ 6)
def r0sixQ (C κsq Φ J n : ℚ) : ℚ := C * κsq * Φ * J / n ^ 4

example : fretEff6Q 1 (3 / 2) = 64 / 793 := by norm_num [fretEff6Q]
example : fretEff6Q (r0sixQ 1 0 1 1 1) 1 = 0 ∧ 0 < fretEff6Q (r0sixQ 1 (2 / 3) 1 1 1) 1 := by
  norm_num [fretEff6Q, r0sixQ]
example : r0sixQ 1 4 1 1 1 / r0sixQ 1 (2 / 3) 1 1 1 = 6 := by norm_num [r0sixQ]

-- FO-R1 cast-bridge shape (ℚ shadow computes the ℝ efficiency).
example (r6 R : ℚ) :
    ((r6 / (r6 + R ^ 6) : ℚ) : ℝ) = (r6 : ℝ) / ((r6 : ℝ) + (R : ℝ) ^ 6) := by
  norm_cast

-- FO-C3 witnesses at closed values (plan §4: `Real.sin_pi_div_two`, `Real.sin_zero`,
-- `Real.cos_zero`). The zero witness holds for EVERY azimuth φ (donor perpendicular,
-- acceptor parallel to the separation).
example (φ : ℝ) :
    (Real.sin (Real.pi / 2) * Real.sin 0 * Real.cos φ - 2 * Real.cos (Real.pi / 2) * Real.cos 0) ^ 2
      = 0 := by
  rw [Real.sin_pi_div_two, Real.sin_zero, Real.cos_zero, Real.cos_pi_div_two]
  ring
example :
    (Real.sin 0 * Real.sin 0 * Real.cos 0 - 2 * Real.cos 0 * Real.cos 0) ^ 2 = 4 := by
  rw [Real.sin_zero, Real.cos_zero]
  norm_num

-- FO-C2 route pieces (plan §5).
-- The triangle step: |a·cosφ − b| ≤ |a| + |b|.
example (a b φ : ℝ) : |a * Real.cos φ - b| ≤ |a| + |b| := by
  have h1 : |a * Real.cos φ - b| ≤ |a * Real.cos φ| + |b| := abs_sub _ _
  have h2 : |a * Real.cos φ| ≤ |a| * |Real.cos φ| := le_of_eq (abs_mul _ _)
  have h3 : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
  have h4 : |a| * |Real.cos φ| ≤ |a| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg a)
  rw [mul_one] at h4
  linarith
-- The ℝ² Cauchy–Schwarz certificate shape: `nlinarith` with the witness (x₁y₂ − x₂y₁)² ≥ 0.
example (x₁ x₂ y₁ y₂ : ℝ) :
    (x₁ * y₁ + x₂ * y₂) ^ 2 ≤ (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
  nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]
-- The closing count: sin²θD + 4·cos²θD ≤ 4 (the plan's "`Real.cos_sq_le_one`-adjacent" step).
example (θ : ℝ) : Real.sin θ ^ 2 + 4 * Real.cos θ ^ 2 ≤ 4 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h2 := Real.cos_sq_le_one θ
  nlinarith

-- FO-C4 route dry run (field algebra; `div_pow` + `field_simp` + `ring`).
example {R0 R : ℝ} (hR0 : 0 < R0) :
    (1 : ℝ) / (1 + (R / R0) ^ 6) = R0 ^ 6 / (R0 ^ 6 + R ^ 6) := by
  have hR0' : R0 ≠ 0 := ne_of_gt hR0
  have hR06' : R0 ^ 6 ≠ 0 := pow_ne_zero 6 hR0'
  have hsum' : R0 ^ 6 + R ^ 6 ≠ 0 := by
    have h1 : (0 : ℝ) < R0 ^ 6 := pow_pos hR0 6
    have h2 : (0 : ℝ) ≤ R ^ 6 := by positivity
    exact ne_of_gt (by linarith)
  rw [div_pow]
  field_simp

-- FO-C6 route dry run: a ↦ a/(a+c) is strictly monotone on (0,∞) for c > 0.
example {c : ℝ} (hc : 0 < c) : StrictMonoOn (fun a : ℝ => a / (a + c)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have h1 : (0 : ℝ) < a + c := by linarith
  have h2 : (0 : ℝ) < b + c := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_lt_mul_of_pos_right hab hc]

-- FO-C7 route dry run: the misestimate ratio is κ²/(2/3) verbatim.
example {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n) (κsq : ℝ) :
    (C * κsq * Φ * J / n ^ 4) / (C * (2 / 3) * Φ * J / n ^ 4) = κsq / (2 / 3) := by
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hn)
  have hden : (0 : ℝ) < C * (2 / 3) * Φ * J / n ^ 4 := by positivity
  have hden' : C * (2 / 3) * Φ * J / n ^ 4 ≠ 0 := ne_of_gt hden
  field_simp
  ring

-- FO-C8 route dry run: the blind spot pair.
example {R : ℝ} (hR : 0 < R) :
    (0 : ℝ) / (0 + R ^ 6) = 0 ∧ 0 < (2 / 3 : ℝ) / (2 / 3 + R ^ 6) := by
  constructor
  · exact zero_div _
  · exact div_pos (by norm_num) (by positivity)

-- FO-C10 first variant route dry run (verbatim shape; the plan's spare binder `R` omitted here).
example {kD kF : ℝ} (hkD : 0 < kD) (hkF : 0 ≤ kF) :
    1 - (1 / (kD + kF)) / (1 / kD) = (kF / kD) / (kF / kD + 1) := by
  have hkD' : kD ≠ 0 := ne_of_gt hkD
  have hsum' : kD + kF ≠ 0 := ne_of_gt (by linarith)
  have hkF' : kF / kD + 1 ≠ 0 := by
    have h1 : (0 : ℝ) ≤ kF / kD := div_nonneg hkF (le_of_lt hkD)
    exact ne_of_gt (by linarith)
  field_simp
  ring_nf
  -- field_simp's denominator-clearance side condition (kF = 0 corner) is trivially inhabited
  exact Or.inl trivial

-- FO-C10 second variant: the VERBATIM statement (no premise on `r6`) is FALSE at `r6 = −R⁶`
-- under totalized division — probe-proved counterexample (deviation evidence; the skeleton's
-- FO-C10b therefore carries the load-bearing premise `0 ≤ r6`).
example :
    ¬ ∀ r6 : ℝ, (1 : ℝ) - (1 / (1 + 1 * (r6 / (1 : ℝ) ^ 6))) / (1 / 1)
      = r6 / (r6 + (1 : ℝ) ^ 6) := by
  intro h
  have hthis := h (-1)
  have e1 : (1 : ℝ) + 1 * ((-1) / (1 : ℝ) ^ 6) = 0 := by norm_num
  have e2 : (-1 : ℝ) + (1 : ℝ) ^ 6 = 0 := by norm_num
  simp only [e1, e2, div_zero, zero_div, sub_zero] at hthis
  exact one_ne_zero hthis

-- FO-C10 second variant, FIXED route (with `0 ≤ r6`): `field_simp` + `ring` closes it.
example {kD r6 R : ℝ} (hkD : 0 < kD) (hR : 0 < R) (hr6 : 0 ≤ r6) :
    1 - (1 / (kD + kD * (r6 / R ^ 6))) / (1 / kD) = r6 / (r6 + R ^ 6) := by
  have hkD' : kD ≠ 0 := ne_of_gt hkD
  have hR6 : (0 : ℝ) < R ^ 6 := by positivity
  have hr6' : (0 : ℝ) ≤ r6 / R ^ 6 := div_nonneg hr6 (le_of_lt hR6)
  have hden' : kD + kD * (r6 / R ^ 6) ≠ 0 :=
    ne_of_gt (by have := mul_nonneg (le_of_lt hkD) hr6'; linarith)
  have hsum' : r6 + R ^ 6 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

-- FO-C11 route dry run (plan §5: `norm_num` after the `div_pow`/cancel normal forms).
example {R0 : ℝ} (hR0 : 0 < R0) : (1 : ℝ) / (1 + (2 * R0 / R0) ^ 6) = 1 / 65 := by
  have hR0' : R0 ≠ 0 := ne_of_gt hR0
  have h : 2 * R0 / R0 = (2 : ℝ) := by field_simp
  rw [h]
  norm_num
