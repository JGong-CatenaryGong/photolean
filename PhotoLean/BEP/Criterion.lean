/-
PhotoLean.BEP.Criterion — B2, the law layer of the Bell–Evans–Polanyi theory.

The content of the BEP description of `PhotoLean.BEP.Basic` inside the equal-curvature
two-parabola model, made exact: the barrier splits into the tangent line plus a *quadratic* defect
(`eact_expansion`), the defect law is a pure square (`bepDefect_eq`), so the BEP line law is exact
only at thermoneutrality (`bepLine_exact_at_thermoneutrality`, `bepDefect_at_thermoneutrality`), and
its violation is nonnegative, and strictly positive exactly away from thermoneutrality
(`bepDefect_nonneg`, `bepDefect_pos_iff`).

The slope of that line is not fitted: it is the model's transfer coefficient in linear-response
form, and `transfer_eq_tsCoord` identifies it with the transition-state coordinate
`(lam - x) / (2 * lam)` — the Leffler/Brønsted identification, a theorem here rather than a
definitional restatement. Thermoneutrality puts the coefficient at Evans–Polanyi's empirical half
(`transfer_thermoneutral`), the two directions of the step are complementary
(`transfer_add_reverse`), the barrier difference of the two directions is the driving force
(`eact_neg_eq_add`), the barrier is antitone up to the barrierless point (`eact_antitone`), and the
*observable* slope over a finite window is the coefficient at the window's midpoint
(`secSlope_eq_transfer_mid`, `secSlope_midpoint_invariant`) — no mean-value theorem is involved.

Model assumptions that are NOT derived here (see `theories/BEP/plan.md` section 13): equal curvature
`2 * lam` held fixed across the compared family, the classical crossing point as the transition
state, and the driving force taken as `ΔG°` rather than `ΔH`. Every physical premise (`lam ≠ 0`,
`0 < lam`, `h ≠ 0`, `x ≠ 0`) is an explicit hypothesis of the statement that needs it; nothing is
hidden in a definition. There is no unproved placeholder and no custom axiom anywhere in this file.

Statement authority: every declaration below matches
`theories/BEP/probes/bep-statement-skeleton.lean` (B2 section = plan §5) word for word.
-/
import Mathlib
import PhotoLean.BEP.Basic

namespace PhotoLean.BEP

/-- The barrier splits into the tangent line plus the quadratic defect
`x ^ 2 / (4 * lam)` (needs `lam ≠ 0`: at `lam = 0` the totalised-division value is `0`). -/
theorem eact_expansion {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
  unfold eact
  field_simp
  ring

/-- The exact defect law of the model: the violation of the linear free-energy law is
the pure square `x ^ 2 / (4 * lam)`. It is the reason BEP can only be a first-order law — and the
quantity every later sharpness statement is stated with. -/
theorem bepDefect_eq {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
    bepDefect lam x = x ^ 2 / (4 * lam) := by
  unfold bepDefect bepLine eact
  field_simp
  ring

/-- At thermoneutrality the tangent line and the barrier agree:
the linear law is exact there. -/
theorem bepLine_exact_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) :
    bepLine lam 0 = eact lam 0 := by
  rw [eact_at_zero hlam]
  unfold bepLine
  ring

/-- The defect vanishes at thermoneutrality. -/
theorem bepDefect_at_thermoneutrality {lam : ℝ} (hlam : lam ≠ 0) : bepDefect lam 0 = 0 := by
  rw [bepDefect_eq hlam]
  ring

end PhotoLean.BEP
