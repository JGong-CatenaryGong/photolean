/-
Hammond milestone — API probe (topic C): transferring the 7-branch ℚ classifier to ℝ.

This is the highest-risk item of the Hammond milestone: `hammondZoneQ` (over ℚ) and
`hammondZone` (over ℝ) are the *same* seven-branch `if`-chain, and one must prove

    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ)        -- no hypotheses

**Verdict: `unfold` the two definitions and run `norm_cast`.  Two lines, no hypotheses.**
`norm_cast` rewrites every ℝ-side test (`↑x = ↑lam`, `↑x = -↑lam`, `↑x < -↑lam`,
`↑lam < ↑x`, `↑x = 0`, `0 < ↑x`) back into its ℚ-side twin, including the literal `0`
(or the `-↑lam` shape, which it normalises through `Rat.cast_neg`), after which the two
`if`-chains are syntactically identical.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-cast-classifier.lean
Status:   0 errors / 0 warnings.
-/
import Mathlib

namespace PhotoLean.Hammond.ProbeCast

/-- Zone classification of the Hammond reaction-coordinate picture. -/
inductive HZone where
  | early | half | late | atReactant | atProduct | beyondReactant | beyondProduct
  deriving DecidableEq, Repr

/-- ℚ-side classifier (computable: equality and order on `Rat` are decidable). -/
def hammondZoneQ (lam x : ℚ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-- ℝ-side classifier (the same chain; `noncomputable` because `ℝ`'s order is classical). -/
noncomputable def hammondZone (lam x : ℝ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-! ## The cast lemmas used by the transfer (all `#check`ed) -/

#check @Rat.cast_lt
#check @Rat.cast_le
#check @Rat.cast_eq_zero
#check @Rat.cast_neg
#check @Rat.cast_inv
#check @Rat.cast_div
#check @Rat.cast_ofNat
#check @Rat.cast_zero
#check @Rat.cast_inj
#check @Rat.cast_sub
#check @Rat.cast_mul
#check @Rat.cast_pow

/-! ## The transfer lemma (recommended recipe) -/

/-- Main transfer lemma: the ℚ-side decision agrees with the ℝ-side classification.
Two tactic lines; no hypotheses (the `lam = 0` branch is transferred too). -/
theorem hammondZoneQ_cast (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ) := by
  unfold hammondZoneQ hammondZone
  norm_cast

/-- The same proof in its `simp only`-free, one-shot form (also compiles). -/
theorem hammondZoneQ_cast_single_line (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ) := by
  simp only [hammondZoneQ, hammondZone]
  norm_cast

/-- Downstream shape: a decision taken over ℚ is binding on the ℝ-side classifier.
This is the `hammondZoneQ` analogue of Marcus's `zoneQ_inverted_iff`. -/
theorem hammondZoneQ_eq_iff (lam x : ℚ) (z : HZone) :
    hammondZoneQ lam x = z ↔ hammondZone (lam : ℝ) (x : ℝ) = z := by
  rw [hammondZoneQ_cast]

/-! ## The numeric bridge for the ℚ-side coordinate (needed by the ℚ instance layer) -/

def tsCoordQ (lam x : ℚ) : ℚ := (lam - x) / (2 * lam)

noncomputable def tsCoord (lam x : ℝ) : ℝ := (lam - x) / (2 * lam)

/-- The ℚ-side coordinate casts to the ℝ-side one; no hypotheses (division by zero is
handled by the `x / 0 = 0` convention on both sides).  Route: `push_cast` does **not**
close the goal by itself, `ring` must follow. -/
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ) := by
  unfold tsCoordQ tsCoord
  push_cast
  ring

/-! ## Measured negative results (documented, not reproducible as live code)

* `unfold hammondZoneQ hammondZone; push_cast; rfl` — FAILS:
      error: tactic 'rfl' failed, the left-hand side
        if x = lam then HZone.atReactant else ... if 0 < x then HZone.early else HZone.late
      is not definitionally equal to the right-hand side
        if ↑x = ↑lam then HZone.atReactant else ... if 0 < ↑x then HZone.early else HZone.late
  `push_cast` only pushes casts *inward* (it turns `↑(a + b)` into `↑a + ↑b`); it has no
  cast-carrying subterms to work on here, so it is a no-op.

* `simp only [hammondZoneQ, hammondZone, Rat.cast_lt, Rat.cast_inj, Rat.cast_eq_zero,
  ← Rat.cast_neg, ← Rat.cast_zero]` — FAILS:
      error: tactic 'simp' failed, nested error: maximum recursion depth has been reached
  the backward `← Rat.cast_neg` rewrite loops.

* `split_ifs with h1 … h6 <;> simp_all [Rat.cast_lt, Rat.cast_inj, Rat.cast_eq_zero,
  Rat.cast_neg, Rat.cast_zero]` — FAILS with many `⊢ False` goals: `split_ifs` splits the
  *goal's* `if`s into a 12-condition case tree and `simp_all` cannot reconcile the ℚ-side
  and ℝ-side hypotheses for the nested branches.

* The `by_cases`-hierarchy transcription of Marcus's `zoneQ_eq_zone` (three branches:
  `by_cases h : x < lam` / `simp [h, h']` with casted counterparts) does NOT scale to seven
  branches: the `simp [h, h']` steps stop at the nested `if`s, e.g. the leftover goal
      ⊢ (if -lam = lam then HZone.atReactant else HZone.atProduct) =
        if -↑lam = ↑lam then HZone.atReactant else HZone.atProduct
  which needs the casted counterparts of *all six* conditions, in both polarities
  (31 lines, and still fragile).  Use `norm_cast` instead.
-/

end PhotoLean.Hammond.ProbeCast
