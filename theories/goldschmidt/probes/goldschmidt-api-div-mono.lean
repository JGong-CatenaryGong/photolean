/-
  PhotoLean — theories/goldschmidt/probes/goldschmidt-api-div-mono.lean

  mathlib API calibration for the Goldschmidt theory, dispatch items (b) squaring equivalences and
  (c) division/monotonicity, plus the two G3 headline rows that consume them
  (`conforms_iff_radius_window`, `conforms_iff_sq`, plan §6).

  Run from the repository root:

      proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-div-mono.lean

  Lean 4.17.0 + mathlib v4.17.0. Every `#check` line below is verbatim output; every `example` /
  `theorem` is kernel-checked. Status: 0 error / 0 warning.
-/
import Mathlib

noncomputable section

/-! ## (b) squaring equivalences — confirmed signatures (verbatim `#check @`, wraps joined) -/

#check @sq_le_sq'
#check @sq_le_sq
#check @sq_lt_sq
#check @sq_lt_sq'
#check @sq_le_sq₀
#check @sq_lt_sq₀
#check @pow_le_pow_left₀
#check @pow_lt_pow_left₀
#check @abs_le
#check @abs_sub_le_iff
#check @sq_nonneg
#check @Real.sqrt_le_sqrt
#check @Real.sqrt_le_sqrt_iff

/-
  Measured drift: the unsuffixed `pow_le_pow_left` still exists but is **deprecated**
  (`warning: `pow_le_pow_left` has been deprecated: use `pow_le_pow_left₀` instead`) — do not
  `#check` it inside a warning-free probe; use the `₀` form. `sq_lt_sq_iff` does not exist.
-/

/-! ## (c) division / monotonicity — confirmed signatures -/

#check @div_lt_div_of_pos_right
#check @div_lt_div_of_pos_left
#check @div_lt_div_iff_of_pos_right
#check @div_lt_div_iff_of_pos_left
#check @div_le_div_of_nonneg_left
#check @div_le_div_of_nonneg_right
#check @div_le_div_iff_of_pos_right
#check @div_le_div_iff_of_pos_left
#check @div_le_iff₀
#check @le_div_iff₀
#check @div_lt_iff₀
#check @lt_div_iff₀
#check @div_eq_one_iff_eq
#check @div_eq_div_iff
#check @div_eq_iff
#check @eq_div_iff
#check @one_div
#check @inv_mul_cancel₀
#check @div_add_div_same
#check @add_div
#check @div_sub_div_same
#check @sub_div

/-
  Measured drift (the whole point of this log): the unsuffixed `div_le_iff` / `le_div_iff` still
  exist but are **deprecated** in v4.17.0
  (`warning: `div_le_iff` has been deprecated: use `div_le_iff₀` instead`, same for `le_div_iff`);
  the working names are `div_le_iff₀` / `le_div_iff₀`. `div_lt_iff` / `lt_div_iff` are likewise
  deprecated in favour of `div_lt_iff₀` / `lt_div_iff₀` (already recorded in the Marcus round).
-/

/-! ## (b) the recipe the dispatch asked for: `0 ≤ a → 0 ≤ b → (a² ≤ b² ↔ a ≤ b)` -/

/-- The v4.17.0 form of the squared-order equivalence is `sq_le_sq₀` (hypotheses first). -/
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b := sq_le_sq₀ ha hb

/-- The strict twin. -/
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b := sq_lt_sq₀ ha hb

/-- `sq_le_sq'` is the *hypothesis-shaped* implication (no nonnegativity side conditions). -/
example {a b : ℝ} (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := sq_le_sq' h1 h2

/-- `abs_le` gives the two-sided window; `abs_sub_le_iff` is its `a - b` specialization. -/
example {a b : ℝ} : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := abs_le

example {a b c : ℝ} : |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := abs_sub_le_iff

/-! ## (c) usage forms in the shapes the theory needs

  The two denominators of the theory are `√2 * (rB + rO)`, so the patterns are
  `div_lt_div_of_pos_right` for the `rA` row and `div_lt_div_of_pos_left` for the `rB` row (the
  latter's three hypotheses are `0 < a`, `0 < c`, `c < b` — the *denominator* order is reversed). -/

/-- Mirror of plan §2 for this probe. -/
def tolFac (rA rB rO : ℝ) : ℝ := (rA + rO) / (Real.sqrt 2 * (rB + rO))

/-- G3 `tolFac_strictMono_rA`: same denominator, so one `div_lt_div_of_pos_right` closes it. -/
theorem tolFac_strictMono_rA {rA rA' rB rO : ℝ} (hB : 0 < rB + rO) (h : rA < rA') :
    tolFac rA rB rO < tolFac rA' rB rO := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  unfold tolFac
  exact div_lt_div_of_pos_right (by linarith) hd

/-- G3 `tolFac_strictAnti_rB`: `div_lt_div_of_pos_left hA hd hlt` with the *denominator* inequality
`c < b` in the last slot. -/
theorem tolFac_strictAnti_rB {rA rB rB' rO : ℝ} (hA : 0 < rA + rO) (hB : 0 < rB + rO)
    (h : rB < rB') :
    tolFac rA rB' rO < tolFac rA rB rO := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hlt : Real.sqrt 2 * (rB + rO) < Real.sqrt 2 * (rB' + rO) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    have : rB + rO < rB' + rO := by linarith
    nlinarith
  unfold tolFac
  exact div_lt_div_of_pos_left hA hd hlt

/-! ## The G3 headline rows, kernel-checked end to end

  These are the two equivalences whose algebra `proofs/API-NOTES.md` records as the theory's
  highest API risk: the radius window (`conforms_iff_radius_window`) and its `√2`-free squared
  form (`conforms_iff_sq`). Both are proved here on the probe's own `tolFac` mirror. -/

/-- `conforms_iff_radius_window` (no squaring): `lo ≤ t ∧ t ≤ hi ↔ lo·(√2(rB+rO)) ≤ rA+rO ≤ hi·(√2(rB+rO))`.
Recipe: `le_div_iff₀` + `div_le_iff₀` with the *positive* denominator, then `and_congr`. -/
theorem conforms_iff_radius_window {rA rB rO lo hi : ℝ} (hB : 0 < rB + rO) :
    (lo ≤ tolFac rA rB rO ∧ tolFac rA rB rO ≤ hi) ↔
      (lo * (Real.sqrt 2 * (rB + rO)) ≤ rA + rO ∧
        rA + rO ≤ hi * (Real.sqrt 2 * (rB + rO))) := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  rw [tolFac]
  exact and_congr (le_div_iff₀ hd) (div_le_iff₀ hd)

/-- One-sided squared form: `lo ≤ t ↔ 2·lo²·(rB+rO)² ≤ (rA+rO)²` (needs `0 ≤ lo`, `0 ≤ rA+rO`).
Recipe: `le_div_iff₀`, then `sq_le_sq₀` applied **backwards** (`.symm`) after the `ring` identity
`(lo·(√2(rB+rO)))² = 2·lo²·(rB+rO)²`. -/
theorem le_tolFac_iff_sq {rA rB rO lo : ℝ} (hlo : 0 ≤ lo) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) :
    lo ≤ tolFac rA rB rO ↔ 2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (lo * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * lo ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [tolFac, le_div_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ (mul_nonneg hlo (le_of_lt hd)) hA).symm

/-- The other side: `t ≤ hi ↔ (rA+rO)² ≤ 2·hi²·(rB+rO)²`. -/
theorem tolFac_le_iff_sq {rA rB rO hi : ℝ} (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) :
    tolFac rA rB rO ≤ hi ↔ (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 := by
  have hd : 0 < Real.sqrt 2 * (rB + rO) :=
    mul_pos (Real.sqrt_pos_of_pos (by norm_num)) hB
  have hsq : (hi * (Real.sqrt 2 * (rB + rO))) ^ 2 = 2 * hi ^ 2 * (rB + rO) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [tolFac, div_le_iff₀ hd, ← hsq]
  exact (sq_le_sq₀ hA (mul_nonneg hhi (le_of_lt hd))).symm

/-- **`conforms_iff_sq`** — the delivered headline row (plan §6), assembled from the two halves. -/
theorem conforms_iff_sq {rA rB rO lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    (lo ≤ tolFac rA rB rO ∧ tolFac rA rB rO ≤ hi) ↔
      (2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
        (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2) :=
  and_congr (le_tolFac_iff_sq hlo hB hA) (tolFac_le_iff_sq hhi hB hA)

/-- `div_eq_one_iff_eq` in the `t = 1` shape (G1 row `contact_iff_tolFac_one`). -/
theorem tolFac_eq_one_iff {rA rB rO : ℝ} (hB : rB + rO ≠ 0) :
    tolFac rA rB rO = 1 ↔ rA + rO = Real.sqrt 2 * (rB + rO) := by
  unfold tolFac
  rw [div_eq_one_iff_eq (mul_ne_zero ((Real.sqrt_ne_zero').mpr (by norm_num)) hB)]

/-! ## G2 `chiTol_anti` — statement-direction check (dispatch item (c)'s order layer)

  Plan §2 defines `chiTol tol₀ k χ χ' = tol₀ - k * |χ - χ'|`, and plan §5 sketches
  `chiTol_anti : |χ'' - χ| ≤ |χ' - χ| → 0 ≤ k → chiTol tol₀ k χ χ'' ≤ chiTol tol₀ k χ χ'`.

  **The sketched conclusion is inverted.** `chiTol` is *antitone* in `|Δχ|` (a larger
  electronegativity mismatch gives a smaller tolerance), so the closer `χ''` must give the **larger**
  `chiTol`: the true row is `chiTol tol₀ k χ χ' ≤ chiTol tol₀ k χ χ''`. Both the corrected row and a
  kernel-checked falsification of the sketch are below. The tool is `sub_le_sub_left`
  (`a ≤ b → c - b ≤ c - a`: the subtraction reverses the order). -/

#check @sub_le_sub_left

/-- Plan §2 mirror of the electronegativity-dressed radius tolerance. -/
def chiTol (tol0 k chi chi' : ℝ) : ℝ := tol0 - k * |chi - chi'|

/-- **Corrected `chiTol_anti`**: the closer electronegativity gets the larger tolerance. -/
theorem chiTol_anti_corrected {tol0 k chi chi' chi'' : ℝ}
    (h : |chi - chi''| ≤ |chi - chi'|) (hk : 0 ≤ k) :
    chiTol tol0 k chi chi' ≤ chiTol tol0 k chi chi'' := by
  unfold chiTol
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left h hk) tol0

/-- The same row in the plan's exact hypothesis spelling (`|χ'' - χ| ≤ |χ' - χ|`). -/
theorem chiTol_anti_corrected' {tol0 k chi chi' chi'' : ℝ}
    (h : |chi'' - chi| ≤ |chi' - chi|) (hk : 0 ≤ k) :
    chiTol tol0 k chi chi' ≤ chiTol tol0 k chi chi'' := by
  rw [abs_sub_comm chi'' chi, abs_sub_comm chi' chi] at h
  exact chiTol_anti_corrected h hk

/-- **The authority's exact `chiTol_anti` signature**
(`goldschmidt-statement-skeleton.lean:216`, delivered in `Rules.lean`): the hypothesis puts the
*farther* mismatch `χ''` on the right and the conclusion puts it on the left, which is the
same corrected direction as above (the authority fixed the plan sketch by swapping the hypothesis
instead of the conclusion; both fixes are the same theorem up to renaming). -/
theorem chiTol_anti_authority {tol0 k chi chi' chi'' : ℝ} (hk : 0 ≤ k)
    (h : |chi' - chi| ≤ |chi'' - chi|) : chiTol tol0 k chi chi'' ≤ chiTol tol0 k chi chi' := by
  rw [abs_sub_comm chi' chi, abs_sub_comm chi'' chi] at h
  exact chiTol_anti_corrected h hk

/-- **The plan's sketched `chiTol_anti` is false** — its hypothesis is satisfied and its conclusion
fails at `χ = 0`, `χ' = 1`, `χ'' = 0` (where `chiTol 0 1 0 0 = 0` and `chiTol 0 1 0 1 = -1`). -/
theorem chiTol_anti_sketch_counterexample :
    ¬ (∀ (tol0 k chi chi' chi'' : ℝ), |chi'' - chi| ≤ |chi' - chi| → 0 ≤ k →
        chiTol tol0 k chi chi'' ≤ chiTol tol0 k chi chi') := by
  intro h
  have hh : |(0 : ℝ) - 0| ≤ |(1 : ℝ) - 0| := by norm_num
  have hc := h 0 1 0 1 0 hh (by norm_num)
  norm_num [chiTol] at hc

/-! ## Auxiliary lemmas quoted in the API-NOTES entry

  These are the order / algebra / `Finset`-membership lemmas used in the recipes above and in the
  verbatim code snippets of `proofs/API-NOTES.md` §Goldschmidt. They are `#check`ed here so that no
  mathlib name quoted in that entry is unverified. -/

#check @mul_ne_zero
#check @div_ne_zero
#check @div_nonneg
#check @div_eq_mul_inv
#check @mul_inv_cancel₀
#check @one_mul
#check @mul_pos
#check @le_of_lt
#check @le_of_not_gt
#check @not_le
#check @not_lt_of_ge
#check @lt_trans
#check @absurd
#check @iff_of_true
#check @iff_of_false
#check @and_congr
#check @add_comm
#check @abs_sub_comm
#check @abs_of_nonneg
#check @div_pow
#check @mul_pow
#check @Finset.mem_erase
#check @Finset.mem_univ

end
