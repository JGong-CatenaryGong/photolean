/-
Hammond milestone — API probe (topic B): field normalization on the five core identities.

This probe answers, for each planned identity, (i) the shortest closing tactic sequence,
(ii) which hypotheses the chosen sequence *consumes* (unconsumed hypotheses trigger
`warning: unused variable ...`), and (iii) whether bare `ring` / `ring_nf` (no hypotheses)
can close it, i.e. whether it is a definitional field identity.  Answer to (iii): **no** for
all five — each one is false or unreachable for the degenerate value `lam = 0`, so a
nonzero/positivity hypothesis must stay in the statement.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-field-identities.lean
Status:   0 errors / 0 warnings.

Legend used in the comments below:
  [C1] `have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hlam` is needed because
       `eq_div_iff` must be told which denominator is nonzero (the implicit `b` of
       `eq_div_iff (b ≠ 0) : c = a / b ↔ c * b = a` is fixed by the goal).
  [C2] `field_simp` reads the `≠ 0` / `0 <` hypotheses of the local context itself: with
       `hlam` in scope it discharges `2 * lam ≠ 0` and `4 * lam ≠ 0` without help, so the
       `have h4 / have h2` lines that older probes carried are NOT needed.
  [C3] A quotient by `x₂ - x₁` is not discharged from `h12 : x₁ ≠ x₂`; that hypothesis must
       be restated as `x₂ - x₁ ≠ 0` (via `sub_ne_zero.mpr h12.symm`) or passed to
       `field_simp` as a simp lemma.
-/
import Mathlib

namespace PhotoLean.Hammond.ProbeField

/-- Reactant surface: minimum at `q = 0`, curvature `2 * lam`. -/
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2

/-- Product surface: minimum at `q = 1`, same curvature, offset by `dG`. -/
noncomputable def productSurface (lam dG q : ℝ) : ℝ := lam * (q - 1) ^ 2 + dG

/-- Transition-state coordinate (driving-force convention `x = -dG`). -/
noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- Forward barrier (reactant well up to the crossing point). -/
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Reverse barrier (product well up to the crossing point). -/
noncomputable def gapProduct (lam x : ℝ) : ℝ := (lam + x) ^ 2 / (4 * lam)

/-- Leffler secant through the two barrier values (no mean-value theorem: `gapReactant` is
a quadratic in `x`, so the finite difference is exactly the derivative at the midpoint). -/
noncomputable def lefflerSecant (lam x₁ x₂ : ℝ) : ℝ :=
  -(gapReactant lam x₂ - gapReactant lam x₁) / (x₂ - x₁)

/-! ## Supporting names used by the recipes (all `#check`ed) -/

#check @div_sub_div_same
#check @mul_ne_zero
#check @two_ne_zero
#check @sub_ne_zero
#check @ne_of_gt
#check @sub_self
#check @zero_div

/-! ## B1 — crossing uniqueness: `reactantSurface = productSurface ↔ q = tsCoord lam (-dG)` -/

/-- B1, shortest form.  `hlam` is consumed by `[C1]`.  `nlinarith` (not `linarith`) is
required: the hypothesis carries `(q - 1) ^ 2`, which only the nonlinear preprocessor
expands into `q ^ 2`. -/
theorem crossing_iff_shortest {lam dG q : ℝ} (hlam : lam ≠ 0) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG) := by
  have h2 : (2 * lam : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hlam
  unfold reactantSurface productSurface tsCoord
  rw [eq_div_iff h2]
  constructor <;> intro h <;> nlinarith [h]

/-- B1 with the natural physical premise `0 < lam`; `positivity` supplies `2 * lam ≠ 0`. -/
theorem crossing_iff_of_pos {lam dG q : ℝ} (hlam : 0 < lam) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG) := by
  have h2 : (2 * lam : ℝ) ≠ 0 := by positivity
  unfold reactantSurface productSurface tsCoord
  rw [eq_div_iff h2]
  constructor <;> intro h <;> nlinarith [h]

/-- B1, per-direction form (the `(⟸)` half alone is `rw [h]; field_simp; ring`). -/
theorem crossing_iff_per_direction {lam dG q : ℝ} (hlam : lam ≠ 0) :
    reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG) := by
  unfold reactantSurface productSurface tsCoord
  constructor
  · intro h
    rw [eq_div_iff (mul_ne_zero (by norm_num) hlam)]
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring

/-! ## B2 — `gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG))` -/

/-- B2, recommended.  `hlam` is consumed by `[C2]` (`field_simp` discharges `2 * lam ≠ 0`
and `4 * lam ≠ 0` from it), so no explicit `have` is needed and no unused-variable warning
appears. -/
theorem gapReactant_eq_surface {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG)) := by
  unfold gapReactant reactantSurface tsCoord
  field_simp
  ring

/-- B2 also holds at the degenerate point `lam = 0` (both sides collapse to `0` by the
`x / 0 = 0` convention), but the `field_simp` route cannot see that: it needs a case split.
Useful only as documentation — the planned signature keeps `hlam`. -/
theorem gapReactant_eq_surface_unconditional (lam dG : ℝ) :
    gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG)) := by
  by_cases hlam : lam = 0
  · subst hlam
    unfold gapReactant reactantSurface tsCoord
    norm_num
  · unfold gapReactant reactantSurface tsCoord
    field_simp
    ring

/-! ## B3 — `lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2)` -/

/-- B3, recommended with the planned premises `0 < lam` and `x₁ ≠ x₂`.
`hlam` is consumed by `[C2]`; `h12` must be restated by `[C3]`. -/
theorem lefflerSecant_eq_tsCoord {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h12 : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2) := by
  have hx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  unfold lefflerSecant gapReactant tsCoord
  field_simp
  ring

/-- B3 without the `have` line: pass the restated hypothesis to `field_simp` directly
(`field_simp` accepts extra simp lemmas for the discharge step). -/
theorem lefflerSecant_eq_tsCoord_simp_arg {lam x₁ x₂ : ℝ} (hlam : 0 < lam)
    (h12 : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2) := by
  unfold lefflerSecant gapReactant tsCoord
  field_simp [sub_ne_zero.mpr h12.symm]
  ring

/-- B3 needs only `lam ≠ 0`, not `0 < lam` (the identity is a rational-function identity):
the weaker hypothesis also compiles, which shows `0 < lam` is a physical premise, not a
proof-technical one. -/
theorem lefflerSecant_eq_tsCoord_weaker_hyp {lam x₁ x₂ : ℝ} (hlam : lam ≠ 0)
    (h12 : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁ + x₂) / 2) := by
  have hx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  unfold lefflerSecant gapReactant tsCoord
  field_simp
  ring

/-! ## B4 — reverse-reaction symmetry: `tsCoord lam (-x) = 1 - tsCoord lam x` -/

/-- B4.  `hlam` is consumed by `[C2]`; the statement is false without it (`lam = 0` gives
`0 = 1`). -/
theorem tsCoord_neg {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    tsCoord lam (-x) = 1 - tsCoord lam x := by
  unfold tsCoord
  field_simp
  ring

/-! ## B5 — reverse-barrier identity: `gapProduct lam x - gapReactant lam x = x` -/

/-- B5, recommended.  `hlam` is consumed by `[C2]`; the statement is false without it. -/
theorem gapProduct_sub_gapReactant {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  unfold gapProduct gapReactant
  field_simp
  ring

/-- B5, alternative: combine the two divisions first with `div_sub_div_same`. -/
theorem gapProduct_sub_gapReactant_alt {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    gapProduct lam x - gapReactant lam x = x := by
  unfold gapProduct gapReactant
  rw [div_sub_div_same]
  field_simp
  ring

/-! ## The remaining identities committed to by the statement skeleton (same recipes) -/

/-- B2 for the reverse barrier: `gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG`
(measured from the product well, which is not the energy zero). -/
theorem gapProduct_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
    gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG := by
  unfold gapProduct productSurface tsCoord
  field_simp
  ring

/-- Reverse-reaction symmetry of the two barriers: **no hypothesis**, pure `ring`. -/
theorem gapProduct_eq_gapReactant_neg (lam x : ℝ) :
    gapProduct lam x = gapReactant lam (-x) := by
  unfold gapProduct gapReactant
  ring

/-- Thermoneutrality puts the transition state halfway. -/
theorem tsCoord_zero {lam : ℝ} (hlam : lam ≠ 0) : tsCoord lam 0 = 1 / 2 := by
  unfold tsCoord
  field_simp
  ring

/-- The rate-maximizing driving force sits exactly at the reactant geometry.
**No hypothesis needed** (it is `(lam - lam) / (2 * lam) = 0 / (2 * lam) = 0`, valid at
`lam = 0` too) — keeping the skeleton's `hlam : lam ≠ 0` here would trigger
`warning: unused variable 'hlam'`. -/
theorem tsCoord_at_lam (lam : ℝ) : tsCoord lam lam = 0 := by
  unfold tsCoord
  rw [sub_self, zero_div]

/-- Pointwise Brønsted coefficient via a symmetric finite difference.  Here `field_simp`
discharges `(x + 1) - (x - 1) = 2 ≠ 0` and the `lam` denominators from `hlam` on its own. -/
theorem lefflerSecant_symm {lam x : ℝ} (hlam : 0 < lam) :
    lefflerSecant lam (x - 1) (x + 1) = tsCoord lam x := by
  unfold lefflerSecant gapReactant tsCoord
  field_simp
  ring

/-- Composition pattern for the milestone's sign statements: rewrite the secant to the
midpoint coordinate (`lefflerSecant_eq_tsCoord`) and reuse `tsCoord`'s sign lemma. -/
theorem lefflerSecant_neg_iff_midpoint {lam x₁ x₂ : ℝ} (hlam : 0 < lam) (h : x₁ ≠ x₂) :
    lefflerSecant lam x₁ x₂ < 0 ↔ lam < (x₁ + x₂) / 2 := by
  rw [lefflerSecant_eq_tsCoord hlam h]
  unfold tsCoord
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  rw [div_lt_iff₀ h2, zero_mul]
  constructor <;> intro hh <;> linarith

/-! ## Measured negative results (documented, not reproducible as live code)

All of the following were run in scratch probes and FAILED; they are listed so that no
prover retries them.

* `unfold ...; ring` and `unfold ...; ring_nf` on B1–B5 **with no hypothesis**: unsolved
  goals in every case.  Example (B4, no hypothesis):
      ⊢ lam * lam⁻¹ * (1 / 2) + x * lam⁻¹ * (1 / 2)
        = 1 + lam * lam⁻¹ * (-1 / 2) + x * lam⁻¹ * (1 / 2)
  `ring`/`ring_nf` never consume hypotheses, so they cannot see `lam ≠ 0`.
* B2 without any hypothesis: `unfold ...; field_simp; ring` fails — `field_simp` cannot
  discharge `lam ≠ 0`, and the residual goal still contains `lam⁻¹`.  (Use the case split
  `gapReactant_eq_surface_unconditional` instead.)
* B3 with `h12 : x₁ ≠ x₂` but without restating it as `x₂ - x₁ ≠ 0`: `field_simp; ring`
  fails and leaves the goal in the form
      ⊢ ... * (-(lam * x₁ * 4) + lam * x₂ * 4)⁻¹ * 4 + ... = lam * 2 + (-x₁ - x₂)
  i.e. `field_simp` *did* clear the `lam` denominators but not `x₂ - x₁`.
* B3 without `h12` at all: the statement is false (`x₁ = x₂` gives `0 = tsCoord lam x₁`),
  so the hypothesis is logically necessary, not merely a proof convenience.
* B1: the statement is false without `hlam` (`lam = 0, dG = 0` makes the left side true for
  every `q` while the right side reads `q = 0`), so `hlam` is logically necessary.
* `eq_div_iff` only matches goals of the shape `?c = ?a / ?b`: using it to rewrite
  `tsCoord lam x = 1 / 2` fails with
      error: tactic 'rewrite' failed, did not find instance of the pattern in the target
        expression ?m = ?m / (2 * lam)
  because the given nonzero proof fixes the implicit denominator to `2 * lam`.
  For that orientation use `div_eq_iff (b ≠ 0) : a / b = c ↔ a = c * b`.
-/

end PhotoLean.Hammond.ProbeField
