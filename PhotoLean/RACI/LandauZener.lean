import Mathlib

namespace PhotoLean


/-!
# RACI M3 — LandauZener: monotonicity of the LZ probability

Upstream provenance: the ChemLean RACI plan §6.1, §6.2, §6.4 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan; the deviation from the draft:
per the upstream proof steps, §6.2 states `0 < c0` as an explicit premise (this file carries `(hc0 : 0 < c0)`).
Upstream owner: prover_m3 (exclusive file).
-/

namespace RACI

/-- The Landau–Zener-type probability `P = exp(−(c·a))` (the constants are absorbed into `c`; upstream plan §6.1). -/
noncomputable def lzProbability (c a : ℝ) : ℝ :=
  Real.exp (-(c * a))

/-- M3.1: the abstract exponential is antitone (`Real.exp_strictMono`; upstream plan §6.1, upstream API-NOTES item 8). -/
theorem lz_antitone (hc : 0 < c) {a b : ℝ} (hab : a < b) :
    lzProbability c b < lzProbability c a := by
  have h1 : c * a < c * b := mul_lt_mul_of_pos_left hab hc
  have h2 : -(c * b) < -(c * a) := neg_lt_neg h1
  have h3 := Real.exp_strictMono h2
  simpa [lzProbability] using h3

/-- M3.2: the LZ probability is antitone in the squared gap (upstream plan §6.2; `0 < c0` is an explicit premise). -/
theorem lz_probability_antitone_in_gap
    {Δ1 Δ2 v F c0 : ℝ}
    (hv : 0 < v) (hF : 0 < F) (hc0 : 0 < c0)
    (hΔ0 : 0 ≤ Δ1) (hΔ : Δ1 < Δ2) :
    lzProbability (c0 / (v * F)) (Δ2 ^ 2) <
      lzProbability (c0 / (v * F)) (Δ1 ^ 2) := by
  have hsq : Δ1 ^ 2 < Δ2 ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_nonneg hΔ0, abs_of_pos (lt_of_le_of_lt hΔ0 hΔ)] using hΔ
  exact lz_antitone (div_pos hc0 (mul_pos hv hF)) hsq

/-- M3.4 (optional): the FGR Lorentzian line shape is antitone in the gap (upstream plan §6.4). -/
noncomputable def lorentzian (σ x : ℝ) : ℝ :=
  1 / (1 + (x / σ) ^ 2)

theorem lorentzian_antitone_on_norm
    (hσ : 0 < σ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    lorentzian σ y < lorentzian σ x := by
  have h1 : x / σ < y / σ := div_lt_div_of_pos_right hxy hσ
  have hx' : 0 ≤ x / σ := div_nonneg hx hσ.le
  have h2 : (x / σ) ^ 2 < (y / σ) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_nonneg hx', abs_of_pos (lt_of_le_of_lt hx' h1)] using h1
  have h3 : 1 + (x / σ) ^ 2 < 1 + (y / σ) ^ 2 := by linarith
  have h4 : 0 < 1 + (x / σ) ^ 2 := by
    have : 0 ≤ (x / σ) ^ 2 := sq_nonneg (x / σ)
    linarith
  have h5 : 1 / (1 + (y / σ) ^ 2) < 1 / (1 + (x / σ) ^ 2) :=
    one_div_lt_one_div_of_lt h4 h3
  simpa [lorentzian] using h5

end RACI


end PhotoLean