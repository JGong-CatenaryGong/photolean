/-
BEP milestone — API probe (topic D): the minimax (best uniform affine approximation) layer.

Scope. Plan §6.4 states the minimax block of B3 as (i) the error bound of the best line
`bepBestLine`, (ii) the optimality form `EPBestOnWindow`, (iii) the tangent line's worst case and
(iv) the halving comparison. This probe calibrates all four with kernel-checked proofs, plus:

* the exactness layer `not_epLinearOn_of_ne_zero` / `EPExact ↔ lam = 0` (plan §6.1 #7/#8), both
  corollaries of the three-point identity. Note that `EPExact lam` at `lam = 0` holds *only* because
  `ℝ`'s division is totalised: `eact 0 x = x ^ 2 / 0 = 0`;
* the sup-norm error as a literal `sSup` of an image set, including the `BddAbove` witness that
  `le_csSup` requires (`sSup` of an unbounded set is `0` in `ℝ`, so a missing boundedness proof
  silently falsifies the sharpness statement);
* the ε-free equivalent of the sup-norm statements (`bep_minimax_pointwise`), which is what a
  prover should use.

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-minimax.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

namespace PhotoLean.BEP.ProbeMinimax

/-! ## Local copies of the B1/B3 definitions (plan §4.1 / statement skeleton) -/

noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2

noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x

/-- Minimax affine BEP law on a symmetric window of half-width `w`. -/
noncomputable def bepBestLine (lam w x : ℝ) : ℝ := lam / 4 + w ^ 2 / (8 * lam) - x / 2

def EPLinearOn (lam : ℝ) (s : Set ℝ) : Prop := ∃ c a : ℝ, ∀ x ∈ s, eact lam x = c + a * x

def EPExact (lam : ℝ) : Prop := EPLinearOn lam Set.univ

def EPBestOnWindow (lam w : ℝ) : Prop :=
  0 < lam ∧ 0 < w ∧ ∀ c a : ℝ, ∃ x ∈ Set.Icc (-w) w,
    w ^ 2 / (8 * lam) ≤ |eact lam x - (c + a * x)|

/-- Uniform (sup-norm) error of the affine model `c + a * x` against `eact lam` on the window
`[-w, w]`, as the least upper bound of the pointwise absolute errors. -/
noncomputable def epSupError (lam w c a : ℝ) : ℝ :=
  sSup ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w)

/-! ## `#check` — the supremum API -/

#check @sSup
#check @csSup_le
#check @le_csSup
#check @csSup_eq_of_forall_le_of_forall_lt_exists_gt
#check @isLUB_csSup
#check @bddAbove_def
#check @Set.Nonempty
#check @Set.Nonempty.mono
#check @Set.image
#check @upperBounds
#check @Real.instConditionallyCompleteLinearOrder
#check @Real.sSup_def
#check @abs_lt
#check @abs_le
#check @abs_add
#check @not_or
#check @not_le

/-! ## The second-difference (three-point) identity — the engine of the whole block -/

/-- Three-point identity, general form: for **any** affine model `c + a * x` the second difference
of the error is the curvature term, independent of `c` and `a` (`field_simp; ring`). -/
theorem eact_second_difference {lam c a x₁ x₂ : ℝ} (hlam : lam ≠ 0) :
    (eact lam x₁ - (c + a * x₁)) + (eact lam x₂ - (c + a * x₂)) -
        2 * (eact lam ((x₁ + x₂) / 2) - (c + a * ((x₁ + x₂) / 2))) =
      (x₁ - x₂) ^ 2 / (8 * lam) := by
  unfold eact
  field_simp
  ring

/-- The symmetric specialization used by the equioscillation argument, with
`f y = eact lam y - (c + a * y)`: `f(-w) + f(w) - 2 * f(0) = w ^ 2 / (2 * lam)`. -/
theorem bep_error_three_point {lam c a w : ℝ} (hlam : lam ≠ 0) :
    (eact lam (-w) - (c + a * (-w))) + (eact lam w - (c + a * w)) -
        2 * (eact lam 0 - (c + a * 0)) = w ^ 2 / (2 * lam) := by
  unfold eact
  field_simp
  ring

/-! ## Plan §6.1 #7/#8 — the exactness layer -/

/-- Plan §6.1 #8: no affine model is exact on a non-degenerate interval. Corollary of
`eact_second_difference`: the three points `a < (a + b)/2 < b` would force
`(a - b)^2 / (8 * lam) = 0`. -/
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
`eact 0 x = x ^ 2 / 0 = 0` by the totalised-division convention. -/
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

/-! ## Plan §6.4 #18–#21 — the minimax block -/

set_option linter.unusedVariables false in
/-- Plan §6.4 #18: the best line keeps the error within `w^2/(8*lam)` on the whole window. The
premise `0 ≤ w` is not consumed by the pointwise bound (it is consumed by the attainment/`sSup`
statements, which need `0 ∈ Set.Icc (-w) w`); the linter is off locally. -/
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
    _ = w ^ 2 / (8 * lam) * (4 * lam) := by field_simp; ring

set_option linter.unusedVariables false in
/-- Plan §6.4 #18 (attainment half): the bound is attained at the thermoneutral point, so it is the
sup-norm and not merely an upper bound. The `hw`-free statement is deliberate (the plan's row 18
carries `0 ≤ w`; the pointwise bound does not need it) — the linter is off locally. -/
theorem bepBestLine_error_attained {lam w : ℝ} (hlam : 0 < lam) :
    |eact lam 0 - bepBestLine lam w 0| = w ^ 2 / (8 * lam) := by
  have h0 : eact lam 0 - bepBestLine lam w 0 = -(w ^ 2 / (8 * lam)) := by
    unfold eact bepBestLine
    field_simp
    ring
  rw [h0, abs_neg, abs_of_nonneg (by positivity)]

/-- Plan §6.4 #19: **the minimax optimality statement** — no affine law beats
`w^2/(8*lam)` on `[-w, w]`. The proof is the three-point equioscillation: if every sampled error
were strictly below `w^2/(8*lam)`, then
`w^2/(2*lam) = f(-w) + f(w) - 2*f(0) < 4*(w^2/(8*lam)) = w^2/(2*lam)`.
`push_neg`/`not_forall` are **not** needed (contradiction taken with `by_contra` + `push_neg` on the
one existential goal, then `linarith`). -/
theorem bep_minimax_pointwise {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∃ x ∈ Set.Icc (-w) w, w ^ 2 / (8 * lam) ≤ |eact lam x - (c + a * x)| := by
  by_contra h
  push_neg at h
  have hm : (-w) ∈ Set.Icc (-w) w := ⟨le_rfl, by linarith⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (-w) w := ⟨by linarith, hw⟩
  have hp : w ∈ Set.Icc (-w) w := ⟨by linarith, le_rfl⟩
  have key := bep_error_three_point (c := c) (a := a) (w := w) (ne_of_gt hlam)
  have h1 := (abs_lt.mp (h (-w) hm)).1
  have h2 := (abs_lt.mp (h (-w) hm)).2
  have h3 := (abs_lt.mp (h w hp)).1
  have h4 := (abs_lt.mp (h w hp)).2
  have h5 := (abs_lt.mp (h 0 h0)).1
  have h6 := (abs_lt.mp (h 0 h0)).2
  have hsum : w ^ 2 / (2 * lam) = 4 * (w ^ 2 / (8 * lam)) := by field_simp; ring
  linarith

/-- Plan §6.4 #19 in the plan's spelling. -/
theorem epBestOnWindow_holds {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    EPBestOnWindow lam w :=
  ⟨hlam, hw, fun c a => bep_minimax_pointwise (lam := lam) (w := w) (c := c) (a := a) hlam
    (le_of_lt hw)⟩

/-- Plan §6.4 #20: the tangent line's worst case on the window (witness `x = w`). -/
theorem bepLine_worst_case {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∃ x ∈ Set.Icc (-w) w, |bepDefect lam x| = w ^ 2 / (4 * lam) := by
  have hdef : bepDefect lam w = w ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  exact ⟨w, ⟨by linarith, le_rfl⟩, by rw [hdef, abs_of_nonneg (by positivity)]⟩

/-- Plan §6.4 #21: the best line halves the tangent line's worst case (and is strictly better). -/
theorem bepBestLine_halves {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    w ^ 2 / (8 * lam) = (w ^ 2 / (4 * lam)) / 2 ∧ w ^ 2 / (8 * lam) < w ^ 2 / (4 * lam) := by
  constructor
  · field_simp
    ring
  · have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero (ne_of_gt hw)
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * lam) (by linarith : (0 : ℝ) < 4 * lam)]
    nlinarith

/-! ## The literal sup-norm (`sSup`) form of the block -/

/-- An upper bound plus an attained value pin down `sSup` — the reusable recipe of this round.
Do **not** try `rw [← hval]` inside a goal that still mentions the `sSup` of a set built from
`hval`'s subterms: `rw` rewrites inside the set as well and silently changes the statement
(measured). -/
theorem sSup_eq_of_le_of_mem {s : Set ℝ} {b : ℝ} (hne : s.Nonempty) (hbdd : BddAbove s)
    (hle : ∀ a ∈ s, a ≤ b) (hmem : b ∈ s) : sSup s = b :=
  le_antisymm (csSup_le hne hle) (le_csSup hbdd hmem)

set_option linter.unusedVariables false in
/-- The error set of the sup-norm is bounded above, with an explicit witness: this is the side
condition `le_csSup` needs (without it `sSup` of an unbounded set is `0`). -/
theorem epSupError_bddAbove {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    BddAbove ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w) := by
  refine ⟨lam / 4 + w / 2 + w ^ 2 / (4 * lam) + (|c| + |a| * w), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxabs : |x| ≤ w := abs_le.mpr hx
  have hxsq : x ^ 2 ≤ w ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have he : eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
    unfold eact
    field_simp
    ring
  have hx2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
    div_le_div_of_nonneg_right hxsq (by linarith : (0 : ℝ) ≤ 4 * lam)
  have hx2' : (0 : ℝ) ≤ x ^ 2 / (4 * lam) := by positivity
  have hlin : |c + a * x| ≤ |c| + |a| * w := by
    have hax : |a * x| ≤ |a| * w := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hxabs (abs_nonneg a)
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self c, neg_le_abs c, le_abs_self (a * x), neg_le_abs (a * x)]
  have hlin' := abs_le.mp hlin
  have hxlow : -w ≤ x := hx.1
  have hxhigh : x ≤ w := hx.2
  rw [abs_le]
  constructor <;> rw [he] <;> linarith

/-- The sup-norm error of `bepBestLine` is exactly `w^2/(8*lam)`: `csSup_le` for `≤`, `le_csSup`
(with the boundedness witness) plus attainment at `x = 0` for `≥`. -/
theorem epSupError_bestLine {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    epSupError lam w (lam / 4 + w ^ 2 / (8 * lam)) (-(1 / 2)) = w ^ 2 / (8 * lam) := by
  have herr : (0 : ℝ) ≤ w ^ 2 / (8 * lam) := by positivity
  have hg : ∀ x ∈ Set.Icc (-w) w,
      |eact lam x - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * x)| ≤ w ^ 2 / (8 * lam) := by
    intro x hx
    have h := bepBestLine_error hlam hw x hx
    convert h using 2
    unfold bepBestLine
    ring
  have hval : |eact lam 0 - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * 0)| = w ^ 2 / (8 * lam) := by
    have h0 : eact lam 0 - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * 0) = -(w ^ 2 / (8 * lam)) := by
      unfold eact
      field_simp
      ring
    rw [h0, abs_neg, abs_of_nonneg herr]
  have hmem1 : w ^ 2 / (8 * lam)
      ∈ (fun x => |eact lam x - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * x)|) '' Set.Icc (-w) w :=
    ⟨0, ⟨by linarith, hw⟩, hval⟩
  unfold epSupError
  refine sSup_eq_of_le_of_mem ⟨_, hmem1⟩ (epSupError_bddAbove hlam hw) ?_ hmem1
  rintro y ⟨x, hx, rfl⟩
  exact hg x hx

/-- The sup-norm sharpness statement: **every** affine model has sup-norm error at least
`w^2/(8*lam)` on `[-w, w]`, so `bepBestLine` is optimal (the ε-free form is
`bep_minimax_pointwise`). -/
theorem epSupError_sharp {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    w ^ 2 / (8 * lam) ≤ epSupError lam w c a := by
  obtain ⟨x, hx, hxerr⟩ := bep_minimax_pointwise (lam := lam) (w := w) (c := c) (a := a) hlam hw
  have hmem : |eact lam x - (c + a * x)| ∈ (fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w :=
    ⟨x, hx, rfl⟩
  have hsup : |eact lam x - (c + a * x)| ≤ epSupError lam w c a := by
    unfold epSupError
    exact le_csSup (epSupError_bddAbove hlam hw) hmem
  linarith

/-! ## Measured notes of this topic

* **The equioscillation lower bound needs neither `push_neg` nor `not_forall`**: the goal
  `∃ x ∈ Set.Icc (-w) w, w^2/(8*lam) ≤ |…|` is refuted by `by_contra h; push_neg at h` (the single
  existential negates into a `∀` of strict bounds), and the contradiction is pure `linarith` over
  the three sampled errors and the three-point identity. This is the *opposite* of what the plan's
  risk register expected (it pre-registered `push_neg`/`not_forall` as the risk).
* `le_csSup` has binder order `BddAbove s → a ∈ s → a ≤ sSup s` (boundedness **first**);
  `csSup_le` has `s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a`.
* `sSup` for `ℝ` is `Real.sSup_def`: outside `s.Nonempty ∧ BddAbove s` it returns `0`.
* `Real.instConditionallyCompleteLinearOrder` is the instance that supplies `sSup` on `ℝ`.
* `div_lt_div_iff₀` (not the deprecated `div_lt_div_iff`) is the strict comparison route used by
  `bepBestLine_halves`.
-/

end PhotoLean.BEP.ProbeMinimax
