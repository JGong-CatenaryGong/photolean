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

/-- Plan §6.1 #8: no affine law reproduces the barrier on a non-degenerate interval. Corollary of
`eact_second_difference`: the three points `a < (a+b)/2 < b` would force `(a-b)²/(8*lam) = 0`. -/
theorem not_epLinearOn_of_ne_zero {lam a b : ℝ} (hlam : lam ≠ 0) (hab : a < b) :
    ¬ EPLinearOn lam (Set.Icc a b) := by
  rintro ⟨c, k, hlin⟩
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, le_of_lt hab⟩
  have hb : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_rfl⟩
  have hm : (a + b) / 2 ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have key := eact_second_difference (c := c) (a := k) (x₁ := a) (x₂ := b) hlam
  rw [hlin a ha, hlin b hb, hlin ((a + b) / 2) hm] at key
  have hne : (a - b) ^ 2 / (8 * lam) ≠ 0 := by
    refine div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_lt hab))) ?_
    exact mul_ne_zero (by norm_num) hlam
  have hzero : (a - b) ^ 2 / (8 * lam) = 0 := by
    rw [← key]
    ring
  exact hne hzero

/-- Plan §6.1 #7: over the whole line the barrier is affine exactly at `lam = 0`, where
`eact 0 x = x²/0 = 0` by the totalised-division convention; the affine witness is the constant
`0` law. -/
theorem epExact_iff_degenerate (lam : ℝ) : EPExact lam ↔ lam = 0 := by
  constructor
  · intro h
    by_contra hlam
    have h' : EPLinearOn lam (Set.Icc 0 1) :=
      ⟨h.choose, h.choose_spec.choose, fun x _ => h.choose_spec.choose_spec x trivial⟩
    exact not_epLinearOn_of_ne_zero hlam (by norm_num) h'
  · intro h
    subst h
    refine ⟨0, 0, fun x _ => ?_⟩
    unfold eact
    norm_num

/-- Plan §6.1 #9: conformance is not automatic — on the window `[-1, 1]` at `lam = 2` the BEP line
misses the barrier by `1/8` at `x = 1`, which exceeds the tolerance `1/16`. -/
theorem exists_conforms_fails : ∃ lam tol w : ℝ, 0 < lam ∧ 0 < tol ∧
    ¬ EPConformsOnWindow lam tol (-w) w := by
  refine ⟨2, 1 / 16, 1, by norm_num, by norm_num, ?_⟩
  intro h
  have hx : (1 : ℝ) ∈ Set.Icc (-(1 : ℝ)) 1 := by norm_num
  have h1 : |bepDefect 2 1| ≤ 1 / 16 := h.2.2 1 hx
  have hval : bepDefect 2 1 = 1 / 8 := by
    unfold bepDefect bepLine eact
    norm_num
  rw [hval, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h1
  norm_num at h1

/-! ## Plan §6.2 — the tolerance/radius theorem -/

/-- Plan §6.2 #10: the absolute defect with the sign of `lam` kept explicit. -/
theorem bepDefect_abs_eq {lam x : ℝ} (hlam : lam ≠ 0) :
    |bepDefect lam x| = x ^ 2 / (4 * |lam|) := by
  have hdef : bepDefect lam x = x ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  rw [hdef, abs_div, abs_of_nonneg (sq_nonneg x), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]

/-- Plan §6.2 #11: **the tolerance/radius theorem** (the sharp validity condition of the BEP line).
For `lam > 0`, `tol > 0` and `w ≥ 0` the line law holds within `tol` on the whole symmetric window
`[-w, w]` **iff** the half-width is at most `bepRadius lam tol = 2√(lam·tol)`. The forward direction
is tested at the endpoint `x = w`; the backward direction uses `x² ≤ w²` on the window. The
`Real.sqrt` is eliminated through `Real.sqrt_mul` (`√(4·(lam·tol)) = 2√(lam·tol)`) and
`Real.le_sqrt`. -/
theorem epConformsOnWindow_iff_radius {lam tol w : ℝ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol := by
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have hdef : ∀ y : ℝ, |bepDefect lam y| = y ^ 2 / (4 * lam) := by
    intro y
    have h : bepDefect lam y = y ^ 2 / (4 * lam) := by
      unfold bepDefect bepLine eact
      field_simp
      ring
    rw [h, abs_of_nonneg (div_nonneg (sq_nonneg y) (le_of_lt h4))]
  have h4nonneg : 0 ≤ 4 * (lam * tol) := by positivity
  have hsqrt4 : Real.sqrt (4 * (lam * tol)) = 2 * Real.sqrt (lam * tol) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have key : w ^ 2 / (4 * lam) ≤ tol ↔ w ≤ bepRadius lam tol := by
    rw [bepRadius, ← hsqrt4, div_le_iff₀ h4, Real.le_sqrt hw h4nonneg]
    ring_nf
  unfold EPConformsOnWindow
  constructor
  · rintro ⟨-, -, h⟩
    have hwmem : w ∈ Set.Icc (-w) w := Set.right_mem_Icc.mpr (by linarith)
    have h1 : w ^ 2 / (4 * lam) ≤ tol := by
      simpa [hdef w] using h w hwmem
    exact key.mp h1
  · intro h
    refine ⟨hlam, htol, fun x hx => ?_⟩
    have hxabs : |x| ≤ w := abs_le.mpr hx
    have hxsq : x ^ 2 ≤ w ^ 2 := by
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
    have h2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
      div_le_div_of_nonneg_right hxsq (le_of_lt h4)
    rw [hdef x]
    exact le_trans h2 (key.mpr h)

/-- Plan §6.2 #12: the radius is attained, not an estimate — the window of half-width exactly
`bepRadius lam tol` is still conforming. -/
theorem epConformsOnWindow_at_radius {lam tol : ℝ} (hlam : 0 < lam) (htol : 0 < tol) :
    EPConformsOnWindow lam tol (-(bepRadius lam tol)) (bepRadius lam tol) :=
  (epConformsOnWindow_iff_radius hlam htol (by unfold bepRadius; positivity)).mpr le_rfl

/-- Plan §6.2 #13: shrinking the window preserves conformance (with the same tolerance and `lam`). -/
theorem epConformsOnWindow_mono {lam tol a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    EPConformsOnWindow lam tol a b → EPConformsOnWindow lam tol a' b' := by
  rintro ⟨h1, h2, h⟩
  exact ⟨h1, h2, fun x hx => h x ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩

/-- Plan §6.2 #14: mirroring the window does not change conformance — `bepDefect` is even in the
driving force at `lam ≠ 0` (the evenness is `field_simp; ring` under that premise, which is why the
premise is taken from the conformance hypothesis rather than from the statement). -/
theorem epConformsOnWindow_symm {lam tol a b : ℝ} :
    EPConformsOnWindow lam tol a b ↔ EPConformsOnWindow lam tol (-b) (-a) := by
  unfold EPConformsOnWindow
  constructor
  · rintro ⟨h1, h2, h⟩
    have heven : ∀ x : ℝ, bepDefect lam (-x) = bepDefect lam x := by
      intro x
      unfold bepDefect bepLine eact
      field_simp
      ring
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [heven x] using h (-x) hmem
  · rintro ⟨h1, h2, h⟩
    have heven : ∀ x : ℝ, bepDefect lam (-x) = bepDefect lam x := by
      intro x
      unfold bepDefect bepLine eact
      field_simp
      ring
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc (-b) (-a) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [heven x] using h (-x) hmem

/-! ## Plan §6.3 — monotonicity in the reorganization energy -/

/- The premise `hx : x ≠ 0` is the plan's strictness convention and is not consumed by the proof
(both sides vanish at `x = 0`); it is kept for signature fidelity and the unused-variable linter is
disabled locally, as in `Basic.lean`. -/
set_option linter.unusedVariables false in
/-- Plan §6.3 #15: a larger reorganization energy `lam` never enlarges the violation — the defect
`x²/(4*lam)` is antitone in `lam` at fixed `x ≠ 0`. -/
theorem bepDefect_antitone_lam {lam₁ lam₂ x : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (hx : x ≠ 0) : bepDefect lam₂ x ≤ bepDefect lam₁ x := by
  have h₂ : 0 < lam₂ := lt_of_lt_of_le h0 hle
  have e₁ : bepDefect lam₁ x = x ^ 2 / (4 * lam₁) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  have e₂ : bepDefect lam₂ x = x ^ 2 / (4 * lam₂) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  rw [e₂, e₁, div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * lam₂)
    (by linarith : (0 : ℝ) < 4 * lam₁)]
  exact mul_le_mul_of_nonneg_left (by linarith : 4 * lam₁ ≤ 4 * lam₂) (sq_nonneg x)

/- The premise `h0 : 0 ≤ lam₁` is not consumed: `Real.sqrt_le_sqrt` is unconditional, so the
essential premise is `0 ≤ tol` (with `tol < 0` the statement is false, e.g. `tol = -1`, `lam₁ = -2`,
`lam₂ = -1`). Kept for signature fidelity with the linter disabled locally. -/
set_option linter.unusedVariables false in
/-- Plan §6.3 #16: the tolerance radius is monotone in the reorganization energy. -/
theorem bepRadius_mono {lam₁ lam₂ tol : ℝ} (h0 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) (htol : 0 ≤ tol) :
    bepRadius lam₁ tol ≤ bepRadius lam₂ tol := by
  unfold bepRadius
  have hprod : lam₁ * tol ≤ lam₂ * tol := mul_le_mul_of_nonneg_right hle htol
  linarith [Real.sqrt_le_sqrt hprod]

/-- Plan §6.3 #17: conformance on a fixed window is preserved when the reorganization energy grows
(the plan leaves the hypotheses as `(…)`; resolved by the statement authority as positivity of
`lam₁` plus `lam₁ ≤ lam₂`, which is what the proof of #15/#16 consumes). -/
theorem epConformsOnWindow_mono_lam {lam₁ lam₂ tol a b : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂) :
    EPConformsOnWindow lam₁ tol a b → EPConformsOnWindow lam₂ tol a b := by
  intro h
  have h₂ : 0 < lam₂ := lt_of_lt_of_le h0 hle
  have h4₂ : (0 : ℝ) < 4 * lam₂ := by linarith
  have e₁ : ∀ y : ℝ, bepDefect lam₁ y = y ^ 2 / (4 * lam₁) := by
    intro y
    unfold bepDefect bepLine eact
    field_simp
    ring
  have e₂ : ∀ y : ℝ, bepDefect lam₂ y = y ^ 2 / (4 * lam₂) := by
    intro y
    unfold bepDefect bepLine eact
    field_simp
    ring
  refine ⟨h₂, h.2.1, fun x hx => ?_⟩
  have hb : |bepDefect lam₁ x| ≤ tol := h.2.2 x hx
  rcases eq_or_ne x 0 with hx0 | hxne
  · subst hx0
    rw [e₂ 0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, abs_zero]
    exact le_of_lt h.2.1
  · have hmono : x ^ 2 / (4 * lam₂) ≤ x ^ 2 / (4 * lam₁) := by
      have h' : bepDefect lam₂ x ≤ bepDefect lam₁ x := bepDefect_antitone_lam h0 hle hxne
      rwa [e₂ x, e₁ x] at h'
    rw [e₂ x, abs_of_nonneg (div_nonneg (sq_nonneg x) (le_of_lt h4₂))]
    rw [e₁ x, abs_of_nonneg (div_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 4 * lam₁))] at hb
    linarith

/-! ## AUX — the symmetric three-point identity

Delivered here rather than in the AUX section at the end of the file: §6.4 #19 below consumes it. -/

/-- AUX: the symmetric three-point identity quoted by plan §6.4 #19, with
`f y = eact lam y - (c + a * y)`: `f(-w) + f(w) - 2·f(0) = w²/(2·lam)` — the affine part cancels. -/
theorem bep_error_three_point {lam c a w : ℝ} (hlam : lam ≠ 0) :
    (eact lam (-w) - (c + a * (-w))) + (eact lam w - (c + a * w)) -
        2 * (eact lam 0 - (c + a * 0)) = w ^ 2 / (2 * lam) := by
  unfold eact
  field_simp
  ring

/-! ## Plan §6.4 — the best BEP line (minimax block) -/

/- The premise `hw : 0 ≤ w` is not consumed by the pointwise bound (it is consumed by the
attainment statements, which need `0 ∈ Set.Icc (-w) w`); kept for signature fidelity with the
linter disabled locally. -/
set_option linter.unusedVariables false in
/-- Plan §6.4 #18: the minimax line `bepBestLine` reproduces the barrier within `w²/(8·lam)` at
every point of the window `[-w, w]`. -/
theorem bepBestLine_error {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∀ x ∈ Set.Icc (-w) w, |eact lam x - bepBestLine lam w x| ≤ w ^ 2 / (8 * lam) := by
  intro x hx
  have hxabs : |x| ≤ w := abs_le.mpr hx
  have hxsq : x ^ 2 ≤ w ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hkey : eact lam x - bepBestLine lam w x = (x ^ 2 - w ^ 2 / 2) / (4 * lam) := by
    unfold eact bepBestLine
    field_simp
    ring
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  rw [hkey, abs_div, abs_of_pos h4, div_le_iff₀ h4]
  have hmid : |x ^ 2 - w ^ 2 / 2| ≤ w ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> linarith [sq_nonneg x, hxsq]
  calc |x ^ 2 - w ^ 2 / 2| ≤ w ^ 2 / 2 := hmid
    _ = w ^ 2 / (8 * lam) * (4 * lam) := by
        field_simp
        ring

/-- Plan §6.4 #19: **the minimax optimality statement** (three-point equioscillation). For every
affine law `c + a·x` some point of `[-w, w]` carries a residual of absolute value at least
`w²/(8·lam)`: if all of `-w, 0, w` were strictly below that, the exact identity
`bep_error_three_point` would give `w²/(2·lam) < 4·(w²/(8·lam)) = w²/(2·lam)`. -/
theorem epBestOnWindow_holds {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    EPBestOnWindow lam w := by
  refine ⟨hlam, hw, fun c a => ?_⟩
  by_contra h
  push_neg at h
  have hm : (-w) ∈ Set.Icc (-w) w := ⟨le_rfl, by linarith⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (-w) w := ⟨by linarith, le_of_lt hw⟩
  have hp : w ∈ Set.Icc (-w) w := ⟨by linarith, le_rfl⟩
  have key := bep_error_three_point (c := c) (a := a) (w := w) (ne_of_gt hlam)
  have h1 := (abs_lt.mp (h (-w) hm)).1
  have h2 := (abs_lt.mp (h (-w) hm)).2
  have h3 := (abs_lt.mp (h w hp)).1
  have h4 := (abs_lt.mp (h w hp)).2
  have h5 := (abs_lt.mp (h 0 h0)).1
  have h6 := (abs_lt.mp (h 0 h0)).2
  have hsum : w ^ 2 / (2 * lam) = 4 * (w ^ 2 / (8 * lam)) := by
    field_simp
    ring
  linarith

/-- Plan §6.4 #20: the tangent line's worst case on the window — the witness is the endpoint
`x = w`, where the absolute defect is exactly `w²/(4·lam)`. -/
theorem bepLine_worst_case {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∃ x ∈ Set.Icc (-w) w, |bepDefect lam x| = w ^ 2 / (4 * lam) := by
  have hdef : bepDefect lam w = w ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  exact ⟨w, ⟨by linarith, le_rfl⟩, by rw [hdef, abs_of_nonneg (by positivity)]⟩

/-- Plan §6.4 #21: the best line halves the tangent line's worst case, and is *strictly* better —
it is not the tangent line. -/
theorem bepBestLine_halves {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    w ^ 2 / (8 * lam) = (w ^ 2 / (4 * lam)) / 2 ∧ w ^ 2 / (8 * lam) < w ^ 2 / (4 * lam) := by
  constructor
  · field_simp
    ring
  · have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero (ne_of_gt hw)
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * lam) (by linarith : (0 : ℝ) < 4 * lam)]
    nlinarith

/-! ## Plan §6.5 — hypothesis necessity -/

/-- Plan §6.5 #22: the defect identity `bepDefect lam x = x²/(4·lam)` needs `lam ≠ 0` — at `lam = 0`
the actual defect at `x = 1` is `1/2` while the right-hand side `1²/(4·0)` is `0`. -/
theorem bepDefect_zero_lam_witness : bepDefect 0 1 = 1 / 2 ∧ ((1 : ℝ) ^ 2 / (4 * 0)) = 0 := by
  constructor
  · unfold bepDefect bepLine eact
    norm_num
  · norm_num

/-- Plan §6.5 #23: the nonnegativity statements need `0 < lam` — at `lam = -1` the defect at
`x = 1` is `-1/4`. -/
theorem bepDefect_neg_lam_witness : bepDefect (-1) 1 = -(1 / 4) := by
  unfold bepDefect bepLine eact
  norm_num


end PhotoLean.BEP
