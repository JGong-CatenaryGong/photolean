/-
theories/BEP/probes/bep-risk-probe.lean

Sprint-0 lead risk probe for the BEP theory (`theories/BEP/plan.md` §6). The mathematically
riskiest statement forms of milestone B3 are proved here, in full, *before* B3 is dispatched, so
that the pre-registered fallbacks of plan §11 can be chosen on kernel evidence instead of
guesswork.

This is a probe, not a deliverable:
* it lives outside the contract's scan/build range (`SOURCE_DIRS="PhotoLean"`,
  `PROBES_BEP="theories/BEP/probes"`), so it is not part of the library build;
* it re-defines the model locally (namespace `PhotoLean.BEP.RiskProbe`) so that it does not depend
  on `PhotoLean/BEP/Basic.lean`, which does not exist yet;
* it contains no `sorry` and no custom `axiom` — the whole point is kernel evidence. The
  `#print axioms` block at the end makes the kernel print the axiom footprint of every theorem.

Model (equal-curvature two-parabola model, plan §2), driving force `x = -ΔG°`:

  eact lam x       = (lam - x)^2 / (4*lam)        barrier
  bepLine lam x    = lam/4 - x/2                  tangent (BEP) line at thermoneutrality
  bepDefect lam x  = eact lam x - bepLine lam x   exact violation  = x^2/(4*lam) for lam ≠ 0
  transfer lam x   = 1/2 - x/(2*lam)              BEP / Brønsted / Leffler coefficient
  bepRadius lam tol= 2 * Real.sqrt (lam*tol)      tolerance radius of the linear law
  bepBestLine lam w x = lam/4 + w^2/(8*lam) - x/2 minimax affine law on [-w, w]
-/
import Mathlib

namespace PhotoLean.BEP.RiskProbe

noncomputable section

/-! ## 1. Model definitions (local copies mirroring plan §2) -/

/-- Forward activation barrier `Ea(x) = (λ - x)^2 / (4λ)` of the equal-curvature two-parabola
model. -/
def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The BEP / linear-free-energy line at thermoneutrality: `λ/4 - x/2`, slope exactly `1/2`. -/
def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2

/-- Exact violation of the line law, `eact - bepLine`; equals `x^2/(4λ)` when `λ ≠ 0`. -/
def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x

/-- BEP / Brønsted / Leffler transfer coefficient in linear-response form `1/2 - x/(2λ)`. -/
def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)

/-- Tolerance radius `2√(λ·tol)`: half-width of the largest symmetric window on which the BEP
line reproduces the model barrier within `tol`. -/
noncomputable def bepRadius (lam tol : ℝ) : ℝ := 2 * Real.sqrt (lam * tol)

/-- The minimax affine law on the symmetric window `[-w, w]`: the tangent line shifted by
`w^2/(8λ)`. -/
def bepBestLine (lam w x : ℝ) : ℝ := lam / 4 + w ^ 2 / (8 * lam) - x / 2

/-! ## 2. Risk form 1 — exact defect expansion (plan §6 table row 5.2/6.10)

`bepDefect lam x = x^2/(4*lam)` for `lam ≠ 0`: the BEP violation is a pure square, so the line
law is *exactly* the first-order (linear-response) truncation of the barrier parabola. -/

theorem risk_defect_expansion (lam x : ℝ) (hlam : lam ≠ 0) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold bepDefect eact bepLine
  field_simp
  ring

/-! ## 3. Risk form 2 — secant/midpoint identity (the observable BEP slope)

`(Ea(x) - Ea(x+h))/h = α(x + h/2)` for `h ≠ 0`: the *measured* finite-difference slope of barrier
data is the model transfer coefficient at the window midpoint. This is the mean-value identity
that makes the transfer coefficient observable, and it is the algebraic core of the rational
`qAlphaObs` layer (plan §8.1). -/

theorem risk_secant_midpoint (lam x h : ℝ) (hlam : lam ≠ 0) (hh : h ≠ 0) :
    (eact lam x - eact lam (x + h)) / h = transfer lam (x + h / 2) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold eact transfer
  field_simp
  ring

/-! ## 4. Risk form 3 — the tolerance/radius theorem

`(∀ x ∈ [-w, w], |bepDefect lam x| ≤ tol) ↔ w ≤ 2√(λ·tol)` for `λ > 0`, `tol > 0`, `w ≥ 0`.
This is the only statement in the BEP plan that needs `Real.sqrt` on `ℝ` (plan §11, first risk
row). The proof goes through the squared form `w^2 ≤ 4λ·tol` and the two monotonicity facts below;
no `sqrt`-elimination lemma is needed beyond `Real.sq_sqrt` and `sq_le_sq`. -/

/-- On the physical branch `λ > 0` the defect is nonnegative, so the absolute value is the defect
itself. -/
theorem risk_defect_abs_of_pos (lam x : ℝ) (hlam : 0 < lam) :
    |bepDefect lam x| = x ^ 2 / (4 * lam) := by
  rw [risk_defect_expansion lam x (ne_of_gt hlam), abs_of_nonneg]
  positivity

/-- Squared form of the window bound: on `[-w, w]` with `w ≥ 0` one has `x^2 ≤ w^2`. -/
theorem risk_sq_le_of_mem (w x : ℝ) (hw : 0 ≤ w) (hx : x ∈ Set.Icc (-w) w) :
    x ^ 2 ≤ w ^ 2 := by
  rw [Set.mem_Icc] at hx
  have habs : |x| ≤ w := abs_le.mpr ⟨hx.1, hx.2⟩
  rw [sq_le_sq, abs_of_nonneg hw]
  exact habs

/-- Key equivalence behind the tolerance/radius theorem: the squared window bound
`w^2/(4λ) ≤ tol` holds **iff** `w ≤ 2√(λ·tol)` (for `λ, tol > 0`, `w ≥ 0`). Route: multiply by
`4λ > 0` (`div_le_iff₀`), recognise `tol * (4λ) = (2√(λ·tol))^2` (`Real.sq_sqrt`), then use that
squaring is monotone on the nonnegative reals (`sq_le_sq` + `abs_of_nonneg`). -/
theorem risk_radius_sq_iff (lam tol w : ℝ) (hlam : 0 < lam) (htol : 0 < tol) (hw : 0 ≤ w) :
    w ^ 2 / (4 * lam) ≤ tol ↔ w ≤ bepRadius lam tol := by
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have hprod : 0 ≤ lam * tol := le_of_lt (mul_pos hlam htol)
  have htwo : 0 ≤ 2 * Real.sqrt (lam * tol) := by positivity
  have hsq : (2 * Real.sqrt (lam * tol)) ^ 2 = 4 * (lam * tol) := by
    rw [mul_pow, Real.sq_sqrt hprod]
    norm_num
  have hden : tol * (4 * lam) = (2 * Real.sqrt (lam * tol)) ^ 2 := by
    rw [hsq]
    ring
  rw [bepRadius, div_le_iff₀ h4, hden, sq_le_sq, abs_of_nonneg hw, abs_of_nonneg htwo]

/-- The same radius equivalence through the *canonical* sqrt-elimination lemma `Real.le_sqrt`:
`2√(λ·tol)` is rewritten as `√(4·λ·tol)` (`Real.sqrt_mul` + `norm_num` for `√4 = 2`), and
`Real.le_sqrt` turns `w ≤ √(4λ·tol)` into `w^2 ≤ 4λ·tol`. Kept as a second, independent route so
that the fallback choice in plan §11 does not depend on one API name. -/
theorem risk_radius_sq_iff_via_le_sqrt (lam tol w : ℝ) (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) :
    w ^ 2 / (4 * lam) ≤ tol ↔ w ≤ bepRadius lam tol := by
  have hprod : 0 ≤ lam * tol := le_of_lt (mul_pos hlam htol)
  have h4nonneg : 0 ≤ 4 * (lam * tol) := by positivity
  have hsqrt4 : Real.sqrt (4 * (lam * tol)) = 2 * Real.sqrt (lam * tol) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [bepRadius, ← hsqrt4, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * lam),
    Real.le_sqrt hw h4nonneg]
  ring_nf

/-- **Tolerance/radius theorem (risk form 3).** For `λ, tol > 0` and `w ≥ 0`, the BEP line holds
within `tol` on the whole symmetric window `[-w, w]` **iff** the half-width is at most the radius
`2√(λ·tol)`. Both directions are sharp: the forward direction is tested at `x = w`, the backward
direction uses `x^2 ≤ w^2` on the window. -/
theorem risk_radius_iff (lam tol w : ℝ) (hlam : 0 < lam) (htol : 0 < tol) (hw : 0 ≤ w) :
    ((∀ x, x ∈ Set.Icc (-w) w → |bepDefect lam x| ≤ tol) ↔
      w ≤ bepRadius lam tol) := by
  have h4pos : 0 < 4 * lam := by linarith
  have key : w ^ 2 / (4 * lam) ≤ tol ↔ w ≤ bepRadius lam tol :=
    risk_radius_sq_iff lam tol w hlam htol hw
  constructor
  · intro h
    have hwmem : w ∈ Set.Icc (-w) w := Set.right_mem_Icc.mpr (by linarith)
    have h1 : |bepDefect lam w| ≤ tol := h w hwmem
    rw [risk_defect_abs_of_pos lam w hlam] at h1
    exact key.mp h1
  · intro h x hx
    have hx2 : x ^ 2 ≤ w ^ 2 := risk_sq_le_of_mem w x hw hx
    have h2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
      div_le_div_of_nonneg_right hx2 (le_of_lt h4pos)
    rw [risk_defect_abs_of_pos lam x hlam]
    exact le_trans h2 (key.mpr h)

/-! ## 5. Risk form 4 — worst-case error of the minimax line (attainment)

The shifted line `λ/4 + w²/(8λ) - x/2` reproduces the barrier within `w²/(8λ)` on the whole
window; the extreme error is attained at both endpoints. -/

/-- Residual of the best line, in closed form. -/
theorem risk_best_line_residual (lam w x : ℝ) (hlam : lam ≠ 0) :
    eact lam x - bepBestLine lam w x = x ^ 2 / (4 * lam) - w ^ 2 / (8 * lam) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  have h8 : (8 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  unfold eact bepBestLine
  field_simp
  ring

/-- **Best-line error bound (risk form 4).** For `λ > 0` and `w ≥ 0`, every point of `[-w, w]` is
reproduced by the minimax line within `w²/(8λ)`. -/
theorem risk_best_line_error (lam w : ℝ) (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∀ x ∈ Set.Icc (-w) w, |eact lam x - bepBestLine lam w x| ≤ w ^ 2 / (8 * lam) := by
  intro x hx
  have h4pos : 0 < 4 * lam := by linarith
  have hx2 : x ^ 2 ≤ w ^ 2 := risk_sq_le_of_mem w x hw hx
  have h2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
    div_le_div_of_nonneg_right hx2 (le_of_lt h4pos)
  have h3 : w ^ 2 / (4 * lam) = 2 * (w ^ 2 / (8 * lam)) := by
    have h4 : (4 : ℝ) * lam ≠ 0 := ne_of_gt h4pos
    have h8 : (8 : ℝ) * lam ≠ 0 := by positivity
    field_simp
    ring
  rw [risk_best_line_residual lam w x (ne_of_gt hlam), abs_le]
  constructor
  · have hnonneg : 0 ≤ x ^ 2 / (4 * lam) := div_nonneg (sq_nonneg x) (le_of_lt h4pos)
    linarith
  · linarith

/-! ## 6. Risk form 5 — optimality of the minimax line (three-point equioscillation)

For *every* affine law `c + a·x` some point of `[-w, w]` has residual at least `w²/(8λ)` in
absolute value, so form 4 is exactly the minimax constant. The proof is the classical
equioscillation argument at the three points `-w, 0, w`:

  `e(-w) + e(w) - 2·e(0) = w²/(2λ)`   (the affine part cancels identically)

hence `|e(-w)| + |e(w)| + 2|e(0)| ≥ w²/(2λ)`; if all three were `< w²/(8λ)` the left-hand side
would be `< w²/(2λ)`, a contradiction. -/

/-- Triangle-inequality estimate used by the equioscillation argument:
`A + B - 2C ≤ |A| + |B| + 2|C|`. -/
theorem three_point_abs_bound (A B C : ℝ) :
    A + B - 2 * C ≤ |A| + |B| + 2 * |C| := by
  have h1 : A + B - 2 * C = (A + B) + -(2 * C) := by ring
  have h2 : |-(2 * C)| = 2 * |C| := by
    rw [abs_neg, abs_mul]
    norm_num
  calc A + B - 2 * C = (A + B) + -(2 * C) := h1
    _ ≤ |(A + B) + -(2 * C)| := le_abs_self _
    _ ≤ |A + B| + |-(2 * C)| := abs_add _ _
    _ ≤ (|A| + |B|) + 2 * |C| := by
        rw [h2]
        exact add_le_add (abs_add A B) le_rfl

/-- **Three-point equioscillation (risk form 5, explicit disjunction form).** For every affine law
`c + a·x` at least one of the three points `-w, 0, w` carries a residual of absolute value at
least `w²/(8λ)`. -/
theorem equioscillation_three (hlam : 0 < lam) (w c a : ℝ) :
    w ^ 2 / (8 * lam) ≤ |eact lam (-w) - (c + a * (-w))| ∨
      w ^ 2 / (8 * lam) ≤ |eact lam 0 - (c + a * 0)| ∨
      w ^ 2 / (8 * lam) ≤ |eact lam w - (c + a * w)| := by
  set A : ℝ := eact lam (-w) - (c + a * (-w)) with hA
  set B : ℝ := eact lam 0 - (c + a * 0) with hB
  set C : ℝ := eact lam w - (c + a * w) with hC
  -- the second difference of the barrier against any affine law is the constant w²/(2λ)
  have hsecond : A + C - 2 * B = w ^ 2 / (2 * lam) := by
    rw [hA, hB, hC]
    unfold eact
    field_simp
    ring
  have htri : w ^ 2 / (2 * lam) ≤ |A| + |C| + 2 * |B| := by
    rw [← hsecond]
    exact three_point_abs_bound A C B
  have hrepr : w ^ 2 / (8 * lam) + w ^ 2 / (8 * lam) + 2 * (w ^ 2 / (8 * lam)) =
      w ^ 2 / (2 * lam) := by
    field_simp
    ring
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h⟩ := h
  rw [not_or] at h
  obtain ⟨h2', h3⟩ := h
  rw [not_le] at h1 h2' h3
  have hle : |A| + |C| + 2 * |B| < w ^ 2 / (2 * lam) := by linarith
  linarith

/-- **Minimax optimality of the best line (risk form 5, `∃ x ∈ [-w, w]` form).** For `λ > 0`,
`w > 0` and every affine law `c + a·x` there is a point of the window whose residual reaches
`w²/(8λ)`; together with `risk_best_line_error` this pins the minimax constant exactly. -/
theorem risk_best_line_optimal (lam w : ℝ) (hlam : 0 < lam) (hw : 0 < w) :
    ∀ c a : ℝ, ∃ x ∈ Set.Icc (-w) w,
      w ^ 2 / (8 * lam) ≤ |eact lam x - (c + a * x)| := by
  intro c a
  rcases equioscillation_three hlam w c a with h | h | h
  · exact ⟨-w, ⟨le_rfl, by linarith⟩, h⟩
  · exact ⟨0, ⟨by linarith, le_of_lt hw⟩, h⟩
  · exact ⟨w, ⟨by linarith, le_rfl⟩, h⟩

/-! ## 7. Risk form 6 — the best line halves the tangent line's worst case -/

/-- **Halving (risk form 6).** For `λ > 0` and `w > 0` the minimax worst case `w²/(8λ)` is
*strictly* smaller than the tangent line's worst case `w²/(4λ)` — the best line is not the tangent
line. -/
theorem risk_best_line_halves (lam w : ℝ) (hlam : 0 < lam) (hw : 0 < w) :
    w ^ 2 / (8 * lam) < w ^ 2 / (4 * lam) := by
  have h8 : (0 : ℝ) < 8 * lam := by linarith
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have hw2 : 0 < w ^ 2 := by positivity
  rw [div_lt_div_iff₀ h8 h4]
  nlinarith [hw2, hlam]

/-! ## 8. Risk form 7 — two-point reconstruction of the reorganization energy

Subtracting the two barrier equations gives `4λ(y₁ - y₂) = 2λ(x₂ - x₁) + (x₁² - x₂²)`, linear in
`λ` after expansion, hence `λ = (x₂² - x₁²)/(2(x₂ - x₁) - 4(y₁ - y₂))`.

**Finding of this probe.** The statement as handed to this probe — with numerator
`x₁² - x₂²` over the denominator `2(x₂ - x₁) - 4(y₁ - y₂)` — is **false**: the numerator sign is
inconsistent with the denominator sign, so the right-hand side is the *negation* of `λ`.
`risk_pair_solver_literal_refuted` below is the kernel-checked counterexample. The corrected
statement (denominator kept as handed, numerator sign fixed) is `risk_pair_solver`; the two
premises that both forms need in addition are recorded there. -/

/-- **Two-point solver (risk form 7, corrected sign).** If the two measured barriers `y₁, y₂` come
from the model at two distinct driving forces and the denominator does not vanish, then `λ` is
reconstructed exactly from the pair. Hypotheses: `λ ≠ 0` (the barrier formula is the degenerate
`0` map at `λ = 0`, where the identity fails), `x₁ ≠ x₂`, and a nonvanishing denominator. -/
theorem risk_pair_solver (lam x₁ x₂ y₁ y₂ : ℝ) (hlam : lam ≠ 0) (hy₁ : y₁ = eact lam x₁)
    (hy₂ : y₂ = eact lam x₂)
    (hden : 2 * (x₂ - x₁) - 4 * (y₁ - y₂) ≠ 0) :
    lam = (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (y₁ - y₂)) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  -- difference of the two barrier equations
  have hdiff : 4 * lam * (y₁ - y₂) = 2 * lam * (x₂ - x₁) + (x₁ ^ 2 - x₂ ^ 2) := by
    rw [hy₁, hy₂]
    unfold eact
    field_simp
    ring
  have hprod : lam * (2 * (x₂ - x₁) - 4 * (y₁ - y₂)) = x₂ ^ 2 - x₁ ^ 2 := by
    nlinarith [hdiff]
  rw [eq_div_iff hden]
  exact hprod

/-- The same reconstruction with the sign convention of the handed statement: keeping the
numerator `x₁² - x₂²` requires the *negated* denominator `4(y₁ - y₂) - 2(x₂ - x₁)`. This is the
statement that matches the derivation without any sign fix, and it shows that the defect of the
handed form is exactly one overall sign. -/
theorem risk_pair_solver_alt (lam x₁ x₂ y₁ y₂ : ℝ) (hlam : lam ≠ 0) (hy₁ : y₁ = eact lam x₁)
    (hy₂ : y₂ = eact lam x₂)
    (hden : 4 * (y₁ - y₂) - 2 * (x₂ - x₁) ≠ 0) :
    lam = (x₁ ^ 2 - x₂ ^ 2) / (4 * (y₁ - y₂) - 2 * (x₂ - x₁)) := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  have hdiff : 4 * lam * (y₁ - y₂) = 2 * lam * (x₂ - x₁) + (x₁ ^ 2 - x₂ ^ 2) := by
    rw [hy₁, hy₂]
    unfold eact
    field_simp
    ring
  have hprod : lam * (4 * (y₁ - y₂) - 2 * (x₂ - x₁)) = x₁ ^ 2 - x₂ ^ 2 := by
    nlinarith [hdiff]
  rw [eq_div_iff hden]
  exact hprod

/-- **The nondegeneracy premise of risk form 7 is not implied by `x₁ ≠ x₂`.** For model data the
denominator is exactly `(x₂² - x₁²)/λ`, so it vanishes precisely when `x₂² = x₁²`, i.e. when
`x₁ = x₂` **or** `x₁ = -x₂`: the premise is a genuinely separate hypothesis (equivalently
`x₁ ≠ -x₂`), not a consequence of the two distinct sample points. -/
theorem risk_pair_denominator_eq (lam x₁ x₂ : ℝ) (hlam : lam ≠ 0) :
    2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂) = (x₂ ^ 2 - x₁ ^ 2) / lam := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  have hdiff : 4 * lam * (eact lam x₁ - eact lam x₂) = 2 * lam * (x₂ - x₁) + (x₁ ^ 2 - x₂ ^ 2) := by
    unfold eact
    field_simp
    ring
  have hprod : lam * (2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂)) = x₂ ^ 2 - x₁ ^ 2 := by
    nlinarith [hdiff]
  rw [eq_div_iff hlam]
  linarith [hprod]

/-- **The handed statement of risk form 7 is refutable.** Concrete model data: `λ = 2`, `x₁ = 0`,
`x₂ = 1`, so `y₁ = Ea(0) = 1/2` and `y₂ = Ea(1) = 1/8`. Every hypothesis of the handed form holds
(`x₁ ≠ x₂`, denominator `= 1/2 ≠ 0`), yet the right-hand side is `-2`, not `λ = 2`. -/
theorem risk_pair_solver_literal_refuted :
    ∃ lam x₁ x₂ : ℝ, x₁ ≠ x₂ ∧
      2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂) ≠ 0 ∧
      lam ≠ (x₁ ^ 2 - x₂ ^ 2) / (2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂)) := by
  refine ⟨(2 : ℝ), 0, 1, by norm_num, ?_, ?_⟩
  · norm_num [eact]
  · norm_num [eact]

/-- **Second hypothesis-necessity witness for risk form 7.** Even with the sign corrected, the
reconstruction needs `λ ≠ 0`: at `λ = 0` the model barrier `(λ-x)^2/(4λ)` degenerates to the
constant `0` map, so both measured barriers vanish, and the corrected right-hand side returns
`(x₂²-x₁²)/(2(x₂-x₁)) = 1/2` instead of `λ = 0` while the denominator `2 ≠ 0`. -/
theorem risk_pair_solver_needs_lam_ne_zero :
    ∃ lam x₁ x₂ : ℝ, x₁ ≠ x₂ ∧
      2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂) ≠ 0 ∧
      lam ≠ (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (eact lam x₁ - eact lam x₂)) := by
  refine ⟨0, 0, 1, by norm_num, ?_, ?_⟩
  · norm_num [eact]
  · norm_num [eact]

/-! ## 9. Kernel axiom footprint of every theorem above -/

#print axioms risk_defect_expansion
#print axioms risk_secant_midpoint
#print axioms risk_defect_abs_of_pos
#print axioms risk_sq_le_of_mem
#print axioms risk_radius_sq_iff
#print axioms risk_radius_sq_iff_via_le_sqrt
#print axioms risk_radius_iff
#print axioms risk_best_line_residual
#print axioms risk_best_line_error
#print axioms three_point_abs_bound
#print axioms equioscillation_three
#print axioms risk_best_line_optimal
#print axioms risk_best_line_halves
#print axioms risk_pair_solver
#print axioms risk_pair_solver_alt
#print axioms risk_pair_solver_literal_refuted
#print axioms risk_pair_solver_needs_lam_ne_zero
#print axioms risk_pair_denominator_eq

end

end PhotoLean.BEP.RiskProbe
