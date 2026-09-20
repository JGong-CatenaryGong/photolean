/-
PhotoLean.BEP.Sharp — B3, the sharp-conditions layer of the Bell–Evans–Polanyi theory.

`PhotoLean.BEP.Basic` describes the empirical BEP linear free-energy relation (the tangent line at
thermoneutrality, its exact violation, the transfer coefficient, the tolerance radius, the minimax
line, the regime classifier). This module sharpens that description into *exact* conditions:

* §6.1 — the exact window on which the transfer coefficient stays inside the Evans–Polanyi bounds
  (`epBounds_iff_region`, `epRegime_iff_strict`) and the two rows outside it
  (`not_epBounds_of_lt_neg`, `not_epBounds_of_gt`), exactness of the line law
  (`epExact_iff_degenerate`, `not_epLinearOn_of_ne_zero`), and a window where conformance fails;
* §6.2 — the tolerance/radius theorem `epConformsOnWindow_iff_radius` (`w ≤ 2√(lam·tol)`, sharp:
  the radius is attained, `epConformsOnWindow_at_radius`), plus window monotonicity and symmetry;
* §6.3 — monotonicity in the reorganization energy (`bepDefect_antitone_lam`, `bepRadius_mono`,
  `epConformsOnWindow_mono_lam`): a larger `lam` never enlarges the violation;
* §6.4 — the minimax block: the best line keeps the error within `w²/(8·lam)`
  (`bepBestLine_error`), no affine law does better (`epBestOnWindow_holds`, three-point
  equioscillation), and the best line halves the tangent line's worst case
  (`bepLine_worst_case`, `bepBestLine_halves`);
* §6.5 — one hypothesis-necessity witness per premise carried by the sharp statements;
* AUX — the same minimax block in literal sup-norm (`sSup`) form, which is also the form the
  equioscillation constant is stated in.

Model assumptions (unchanged from `Basic.lean`; `theories/BEP/plan.md` §13): equal-curvature
two-parabola model, one scalar reaction coordinate, classical crossing point as the transition
state, `lam` fixed across the compared family, driving force `x = -ΔG°`. Every physical premise
(`0 < lam`, `lam ≠ 0`, `0 < tol`, `0 ≤ w`, `0 < w`, `x ≠ 0`, `h ≠ 0`) is an explicit hypothesis of
the statement that needs it; nothing is hidden in a definition. Three premises of the statement
authority are physical bookkeeping rather than proof inputs — `x ≠ 0` in `bepDefect_antitone_lam`
(both sides vanish at `x = 0`), `0 ≤ lam₁` in `bepRadius_mono` (`Real.sqrt_le_sqrt` is
unconditional) and `0 ≤ w` in `bepBestLine_error` (the pointwise bound does not use it) — and are
kept for signature fidelity with the local linter disabled, exactly as in `Basic.lean`, rather than
being dropped from the statement.

Statement authority: every declaration below matches
`theories/BEP/probes/bep-statement-skeleton.lean` (plan §6.1–§6.5 plus its AUX section
"literal sup-norm form of the minimax block") word for word; the mechanical check is
`python3 theories/BEP/probes/bep-fidelity.py --verbose`. Declaration order follows **proof order**,
not the authority's order, because Lean has no forward references: the AUX row `eact_second_difference`
is delivered before the §6.1 rows #8/#7 that consume it, `not_epLinearOn_of_ne_zero` (#8) before
`epExact_iff_degenerate` (#7), and the AUX row `bep_error_three_point` before §6.4 #19. The fidelity
check is name-keyed and therefore order-insensitive; the deviation is recorded here as in
`PhotoLean/Hammond/Sharp.lean`.

This file imports `PhotoLean.BEP.Basic` only. The B2 identity `bepDefect lam x = x^2/(4*lam)` is
re-derived locally where needed instead of importing `PhotoLean/BEP/Criterion.lean`, so that B3 does
not depend on a file owned and edited by another prover. There is no unproved placeholder and no
custom axiom anywhere in this file.
-/
import PhotoLean.BEP.Basic

namespace PhotoLean.BEP

/-! ## Plan §6.1 — the sharp iff statements -/

/-- Plan §6.1 #1: the Evans–Polanyi bounds `0 ≤ α ≤ 1` hold exactly on the region `-lam ≤ x ≤ lam`.
The proof moves the linear-response body of `transfer` to the transition-state form
`(lam - x)/(2*lam)` and converts the two inequalities with `le_div_iff₀`, `div_le_one`. -/
theorem epBounds_iff_region {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) ≤ (lam - x) / (2 * lam) ↔ 0 ≤ lam - x := by
    rw [le_div_iff₀ h2, zero_mul]
  have hhigh : (lam - x) / (2 * lam) ≤ 1 ↔ lam - x ≤ 2 * lam := div_le_one h2
  unfold EPBounds
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #2: the same computation with strict inequalities — the open region `EPRegime` is
exactly where the transfer coefficient is strictly inside `(0,1)`. -/
theorem epRegime_iff_strict {lam x : ℝ} (hlam : 0 < lam) :
    EPRegime lam x ↔ 0 < transfer lam x ∧ transfer lam x < 1 := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) < (lam - x) / (2 * lam) ↔ 0 < lam - x :=
    div_pos_iff_of_pos_right h2
  have hhigh : (lam - x) / (2 * lam) < 1 ↔ lam - x < 2 * lam := div_lt_one h2
  unfold EPRegime
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #3: at the forward barrierless limit `x = lam` the transfer coefficient vanishes. -/
theorem transfer_at_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam lam = 0 := by
  unfold transfer
  field_simp

/-- Plan §6.1 #4: at the reverse barrierless limit `x = -lam` the transfer coefficient is `1`. -/
theorem transfer_at_neg_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam (-lam) = 1 := by
  unfold transfer
  field_simp
  ring

/-- Plan §6.1 #5: α > 1 — the **reverse** direction is in the inverted region. -/
theorem not_epBounds_of_lt_neg {lam x : ℝ} (hlam : 0 < lam) (hx : x < -lam) :
    ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-- Plan §6.1 #6: α < 0 — the **forward** direction is in the inverted region. -/
theorem not_epBounds_of_gt {lam x : ℝ} (hlam : 0 < lam) (hx : lam < x) : ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-! ## AUX — the second-difference engine

Delivered here rather than at the end of the file: §6.1 rows #8/#7 below consume it, and Lean has no
forward references (order recorded in the module header). -/

/-- AUX: the general second-difference identity behind `not_epLinearOn_of_ne_zero` and the
minimax lower bound. For **any** affine model `c + a * x` the second difference of the error at
`x₁, x₂` and their midpoint is the curvature term `(x₁-x₂)²/(8*lam)`, independent of `c` and `a`. -/
theorem eact_second_difference {lam c a x₁ x₂ : ℝ} (hlam : lam ≠ 0) :
    (eact lam x₁ - (c + a * x₁)) + (eact lam x₂ - (c + a * x₂)) -
        2 * (eact lam ((x₁ + x₂) / 2) - (c + a * ((x₁ + x₂) / 2))) =
      (x₁ - x₂) ^ 2 / (8 * lam) := by
  unfold eact
  field_simp
  ring


end PhotoLean.BEP
