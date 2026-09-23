/-
PhotoLean.Forster.Criterion — milestone FO2, the law layer.

The theory: Förster resonance energy transfer and the **κ² convention dependency analysis**
(plan `theories/Forster/plan.md`, §1.1 and §4).

The headline of group C is not the transfer law itself but the geometry of its orientation
factor. `kappaSq_le_four` is the batch's highest proof-risk row: the orientation factor is
bounded by `4`, which turns the convention comparison into a *finite* band. The route (plan
§4/§5, dry-run in `theories/Forster/probes/Forster-api-probe.lean`) uses no eigenvalues and no
rotations:
1. with `a := sinθ_D·sinθ_A`, `b := 2·cosθ_D·cos_A`, the triangle inequality plus
   `|cosφ| ≤ 1` give `|a·cosφ − b| ≤ |a| + |b|`;
2. Cauchy–Schwarz in `ℝ²` bounds `(|a| + |b|)²` by
   `(sin²θ_D + 4cos²θ_D)·(sin²θ_A + cos²θ_A)` — discharged by `nlinarith` with the witness
   `(x₁y₂ − x₂y₁)² ≥ 0`;
3. `sin²θ_A + cos²θ_A = 1` and `sin²θ_D + 4cos²θ_D = 1 + 3cos²θ_D ≤ 4`, hence `|a·cosφ − b| ≤ 2`
   and `kappaSq ≤ 4`.
The delivered proof takes the square-root form of step 2 (`Real.sqrt_le_sqrt` on the squared
Cauchy–Schwarz bound) because the triangle step produces an inequality of absolute values; the
kernel then closes `|x| ≤ 2` and the row follows by `sq_abs`.

Honest scope, stated up front:
* every positivity premise of the law rows is an explicit hypothesis, never a hidden side
  condition of a definition (engine rule 3);
* `0 ≤ r6` is a load-bearing premise of `fretEff_via_lifetime'` — the unpremised form is FALSE
  under totalized division at `r6 = −R⁶` (counterexample probe-proved in
  `Forster-api-probe.lean`; skeleton correction §3.1 item 2);
* the ratio band `[0, 6]` is a statement about the *tabulated* `R₀⁶` under the `2/3` convention;
  the convention's failure towards the blind spot (`κ² → 0`) is the strict inequality of
  `fret_blind_spot`, not a continuity claim (no limits are formalized, plan §1.3).

Statement authority: `theories/Forster/probes/Forster-statement-skeleton.lean` § FO-C; every
signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.Forster.Criterion` (exit 0);
`proofs/scripts/check.sh --strict`;
`proofs/scripts/axioms.sh PhotoLean.Forster.Criterion PhotoLean.Forster.kappaSq_le_four`.
-/
import PhotoLean.Forster.Basic

set_option autoImplicit false

namespace PhotoLean

namespace Forster

/-! ## FO-C — law layer -/

/-- Plan §4, FO-C1. Nonnegativity of the orientation factor. Route: `sq_nonneg`. -/
theorem kappaSq_nonneg (θD θA φ : ℝ) : 0 ≤ kappaSq θD θA φ := by
  rw [kappaSq]
  exact sq_nonneg _

/-- Plan §4, FO-C2. **The geometric bound** `κ² ≤ 4`. Route (pre-validated in
`Forster-api-probe.lean`): with `a := sinθD·sinθA`, `b := 2·cosθD·cosθA`, the triangle
inequality and `|cosφ| ≤ 1` give `|a·cosφ − b| ≤ |a| + |b|`; Cauchy–Schwarz on ℝ² (closed by
`nlinarith [sq_nonneg (x₁·y₂ − x₂·y₁)]`) bounds `(|sinθD|·|sinθA| + 2|cosθD||cosθA|)²` by
`(sin²θD + 4cos²θD)·(sin²θA + cos²θA) = 1 + 3cos²θD ≤ 4` (`Real.sin_sq_add_cos_sq`,
`Real.cos_sq_le_one`); `sq_le_sq` + `abs_le` finish. -/
theorem kappaSq_le_four (θD θA φ : ℝ) : kappaSq θD θA φ ≤ 4 := by
  rw [kappaSq]
  set x := Real.sin θD * Real.sin θA * Real.cos φ - 2 * Real.cos θD * Real.cos θA with hx
  set p := |Real.sin θD| * |Real.sin θA| + 2 * |Real.cos θD| * |Real.cos θA| with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  -- Step 1: the triangle inequality, with `|cosφ| ≤ 1` folded into the first summand.
  have h_tri : |x| ≤ p := by
    rw [hx, hp]
    have h1 : |Real.sin θD * Real.sin θA * Real.cos φ - 2 * Real.cos θD * Real.cos θA|
        ≤ |Real.sin θD * Real.sin θA * Real.cos φ| + |2 * Real.cos θD * Real.cos θA| :=
      abs_sub _ _
    have h2 : |Real.sin θD * Real.sin θA * Real.cos φ| ≤ |Real.sin θD| * |Real.sin θA| := by
      have hfac : |Real.sin θD * Real.sin θA * Real.cos φ|
          = (|Real.sin θD| * |Real.sin θA|) * |Real.cos φ| := by
        simp only [abs_mul]
      have hle : (|Real.sin θD| * |Real.sin θA|) * |Real.cos φ|
          ≤ (|Real.sin θD| * |Real.sin θA|) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one φ) (by positivity)
      rw [hfac]
      linarith
    have h3 : |2 * Real.cos θD * Real.cos θA| = 2 * |Real.cos θD| * |Real.cos θA| := by
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  -- Step 2: Cauchy–Schwarz on ℝ², discharged by `nlinarith` with the cross-term witness.
  have h_p2 : p ^ 2 ≤ 2 ^ 2 := by
    have h_cs_sq : p ^ 2 ≤ (Real.sin θD ^ 2 + 4 * Real.cos θD ^ 2) *
        (Real.sin θA ^ 2 + Real.cos θA ^ 2) := by
      rw [hp]
      have h := sq_nonneg
        (|Real.sin θD| * |Real.cos θA| - 2 * |Real.cos θD| * |Real.sin θA|)
      nlinarith [sq_abs (Real.sin θD), sq_abs (Real.sin θA), sq_abs (Real.cos θD),
        sq_abs (Real.cos θA)]
    have h_y : Real.sin θA ^ 2 + Real.cos θA ^ 2 ≤ 1 := by
      have h := Real.sin_sq_add_cos_sq θA
      linarith
    have h_x : Real.sin θD ^ 2 + 4 * Real.cos θD ^ 2 ≤ 4 := by
      have h1 := Real.cos_sq_le_one θD
      have h2 := Real.sin_sq_add_cos_sq θD
      nlinarith
    have h_xy : (Real.sin θD ^ 2 + 4 * Real.cos θD ^ 2) *
        (Real.sin θA ^ 2 + Real.cos θA ^ 2) ≤ 4 := by
      have hy0 : (0 : ℝ) ≤ Real.sin θA ^ 2 + Real.cos θA ^ 2 := by positivity
      nlinarith
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    linarith
  have h_le2 : |x| ≤ 2 := by
    have h1 : |x| ≤ Real.sqrt (p ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hp0]
      exact h_tri
    have h2 : Real.sqrt (p ^ 2) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt h_p2
    have h3 : Real.sqrt ((2 : ℝ) ^ 2) = 2 := by
      rw [Real.sqrt_sq_eq_abs]
      norm_num
    linarith
  calc x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ 2 ^ 2 := sq_le_sq' (by linarith [abs_nonneg x]) h_le2
    _ = 4 := by norm_num

/-- Plan §4, FO-C3 (zero witness). The blind-spot geometry exists: donor perpendicular to the
separation, acceptor along it. Route: `simp [kappaSq, Real.sin_pi_div_two, Real.sin_zero,
Real.cos_zero, Real.cos_pi_div_two]`-style normalization (probed). -/
theorem kappaSq_eq_zero_witness : ∃ θD θA φ : ℝ, kappaSq θD θA φ = 0 := by
  refine ⟨Real.pi / 2, 0, 0, ?_⟩
  rw [kappaSq, Real.sin_pi_div_two, Real.sin_zero, Real.cos_zero, Real.cos_pi_div_two]
  norm_num

/-- Plan §4, FO-C3 (maximal witness). Both dipoles along the separation give `κ² = 4`. -/
theorem kappaSq_eq_four_witness : ∃ θD θA φ : ℝ, kappaSq θD θA φ = 4 := by
  refine ⟨0, 0, 0, ?_⟩
  rw [kappaSq, Real.sin_zero, Real.cos_zero]
  norm_num

/-- Plan §4, FO-C4. The certificate between the radius form and the `R⁶`-space form. Route:
`div_pow`, `field_simp` (probed; `field_simp` closes the normalized goal). -/
theorem fretEff_eq (R0 R : ℝ) (hR0 : 0 < R0) : fretEff R0 R = fretEff6 (R0 ^ 6) R := by
  have hsum' : R0 ^ 6 + R ^ 6 ≠ 0 := by
    have h1 : (0 : ℝ) < R0 ^ 6 := pow_pos hR0 6
    have h2 : (0 : ℝ) ≤ R ^ 6 := by positivity
    exact ne_of_gt (by linarith)
  rw [fretEff, fretEff6, div_pow]
  field_simp

/-- Plan §4, FO-C5. The meaning of `R₀`: efficiency `1/2` at `R = R₀`. Route: FO-C4 +
`norm_num`. -/
theorem fretEff_self (R0 : ℝ) (hR0 : 0 < R0) : fretEff R0 R0 = 1 / 2 := by
  rw [fretEff, div_self (ne_of_gt hR0)]
  norm_num

/-- Plan §4, FO-C6. The efficiency is strictly increasing in `R₀⁶` at any positive separation.
Route (probed): `div_lt_div_iff₀` + `nlinarith [mul_lt_mul_of_pos_right ...]`. -/
theorem fretEff6_strictMono_r6 (R : ℝ) (hR : 0 < R) :
    StrictMonoOn (fun r6 : ℝ => fretEff6 r6 R) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hR6 : (0 : ℝ) < R ^ 6 := by positivity
  have h1 : (0 : ℝ) < a + R ^ 6 := by linarith
  have h2 : (0 : ℝ) < b + R ^ 6 := by linarith
  have h3 : a * (b + R ^ 6) < b * (a + R ^ 6) := by
    nlinarith [mul_lt_mul_of_pos_right hab hR6]
  unfold fretEff6
  exact (div_lt_div_iff₀ h1 h2).mpr h3

/-- Plan §4, FO-C7 (the convention-bias ratio). The tabulated-`R₀⁶` misestimate factor is
exactly `κ²/(2/3)`. Route (probed): `field_simp` + `ring` with the positivity side-conditions. -/
theorem r0six_ratio {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (kappasq : ℝ) : r0six C kappasq Φ J n / r0six C (2 / 3) Φ J n = kappasq / (2 / 3) := by
  have hn4 : n ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hn)
  have hCFJ : C * (2 / 3) * Φ * J ≠ 0 := by positivity
  rw [r0six, r0six]
  rw [div_div_div_cancel_right₀ hn4]
  rw [div_eq_div_iff hCFJ (by norm_num : (2 : ℝ) / 3 ≠ 0)]
  ring

/-- Plan §4, FO-C7 (the misestimate band). The ratio lies in `[0, 6]` — the convention
underestimates the true `R₀⁶` by at most a factor `6` (at `κ² = 4`) and overestimates without
bound in ratio towards the blind spot (`κ² → 0`). Route: FO-C1/FO-C2 + `r0six_ratio` +
positivity. -/
theorem r0six_ratio_mem {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (θD θA φ : ℝ) :
    r0six C (kappaSq θD θA φ) Φ J n / r0six C (2 / 3) Φ J n ∈ Set.Icc (0 : ℝ) 6 := by
  rw [r0six_ratio hC hΦ hJ hn]
  refine Set.mem_Icc.mpr ⟨div_nonneg (kappaSq_nonneg θD θA φ) (by norm_num), ?_⟩
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)]
  nlinarith [kappaSq_le_four θD θA φ]

/-- Plan §4, FO-C8 (**the blind spot**). At `κ² = 0` no transfer happens at any separation
while the `2/3` convention predicts transfer — the convention's silent failure, witnessed.
Route (probed): `zero_div` and `div_pos`. -/
theorem fret_blind_spot {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) :
    fretEff6 (r0six C 0 Φ J n) R = 0 ∧ 0 < fretEff6 (r0six C (2 / 3) Φ J n) R := by
  have hzero : r0six C 0 Φ J n = 0 := by
    rw [r0six]
    ring
  have hpos : (0 : ℝ) < r0six C (2 / 3) Φ J n := by
    rw [r0six]
    positivity
  constructor
  · rw [hzero, fretEff6, zero_div]
  · rw [fretEff6]
    exact div_pos hpos (by
      have hR6 : (0 : ℝ) < R ^ 6 := by positivity
      linarith)

/-- Plan §4, FO-C9. The observable's κ² dependency: the efficiency strictly increases in the
orientation factor. Route: `r0six` is strictly monotone in `κ²` (linear, `C·Φ·J/n⁴ > 0`), then
FO-C6. -/
theorem fretEff6_mono_kappa {C Φ J n : ℝ} (hC : 0 < C) (hΦ : 0 < Φ) (hJ : 0 < J) (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) {κ₁ κ₂ : ℝ} (h1 : 0 < κ₁) (h : κ₁ < κ₂) :
    fretEff6 (r0six C κ₁ Φ J n) R < fretEff6 (r0six C κ₂ Φ J n) R := by
  have hr : r0six C κ₁ Φ J n < r0six C κ₂ Φ J n := by
    simp only [r0six]
    have h4 : (0 : ℝ) < n ^ 4 := by positivity
    rw [div_lt_div_iff₀ h4 h4]
    have hC4 : (0 : ℝ) < C * Φ * J := by positivity
    nlinarith [mul_lt_mul_of_pos_right h hC4]
  have h2 : κ₂ ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hS := fretEff6_strictMono_r6 R hR
  have hp1 : (0 : ℝ) < r0six C κ₁ Φ J n := by rw [r0six]; positivity
  have hp2 : (0 : ℝ) < r0six C κ₂ Φ J n := by
    have hk2 : (0 : ℝ) < κ₂ := by linarith
    rw [r0six]
    positivity
  exact hS hp1 hp2 hr

/-- Plan §4, FO-C10 (first lifetime form). Route (probed): `field_simp`, `ring_nf`, then the
trivial clearance side condition `Or.inl trivial`. -/
theorem fretEff_via_lifetime {kD kF : ℝ} (hkD : 0 < kD) (hkF : 0 ≤ kF) :
    1 - (1 / (kD + kF)) / (1 / kD) = (kF / kD) / (kF / kD + 1) := by
  have hkD' : kD ≠ 0 := ne_of_gt hkD
  have hsum' : kD + kF ≠ 0 := ne_of_gt (by linarith)
  have hkF' : kF / kD + 1 ≠ 0 := by
    have h1 : (0 : ℝ) ≤ kF / kD := div_nonneg hkF (le_of_lt hkD)
    exact ne_of_gt (by linarith)
  field_simp
  ring_nf
  exact Or.inl trivial

/-- Plan §4, FO-C10b (second lifetime form — carries the probe-mandated premise `0 ≤ r6`; the
unpremised form is false at `r6 = −R⁶` under totalized division, counterexample probe-proved in
`Forster-api-probe.lean`). Route: `field_simp` + `ring`. -/
theorem fretEff_via_lifetime' {kD r6 R : ℝ} (hkD : 0 < kD) (hR : 0 < R) (hr6 : 0 ≤ r6) :
    1 - (1 / (kD + kD * (r6 / R ^ 6))) / (1 / kD) = fretEff6 r6 R := by
  have hR6 : (0 : ℝ) < R ^ 6 := by positivity
  have hr6' : (0 : ℝ) ≤ r6 / R ^ 6 := div_nonneg hr6 (le_of_lt hR6)
  have hden' : kD + kD * (r6 / R ^ 6) ≠ 0 :=
    ne_of_gt (by have := mul_nonneg (le_of_lt hkD) hr6'; linarith)
  have hsum' : r6 + R ^ 6 ≠ 0 := ne_of_gt (by linarith)
  unfold fretEff6
  field_simp
  ring_nf

/-- Plan §4, FO-C11. The sixth-power law's steepness, kernel-computed. Route (probed):
`div_pow`, `field_simp`, `norm_num`. -/
theorem fretEff_at_twoR0 (R0 : ℝ) (hR0 : 0 < R0) : fretEff R0 (2 * R0) = 1 / 65 := by
  rw [fretEff]
  have h : 2 * R0 / R0 = (2 : ℝ) := by field_simp
  rw [h]
  norm_num

end Forster

end PhotoLean
