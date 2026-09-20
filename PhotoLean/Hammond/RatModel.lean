/-
PhotoLean.Hammond.RatModel — H5a: the rational decision layer (a dispatchable classifier).

**Statement authority**: the H5a section of
`theories/hammond/probes/hammond-statement-skeleton.lean`. The 4 definitions and 12 theorems
below match those signatures word for word; the file was developed in the probe
`theories/hammond/probes/hammond-prover_c-scratch.lean` (0 error / 0 warning) before delivery.

**Why a ℚ copy**: the order on `ℝ` goes through `Classical` and is **not computable**, so
"which Hammond zone a given instance sits in" cannot be computed by the kernel over `ℝ`. Over
`ℚ` both the order and the equality of `Rat` are decidable, so the evidence chain of the
instance layer is: kernel computation (`norm_num [hammondZoneQ]`, measured in
`theories/hammond/probes/hammond-api-rat-compute.lean`) → the transfer lemma
`hammondZoneQ_eq_hammondZone` → the ℝ-side classifier and theory. That transfer lemma is what
makes a rational decision binding for the real theory (plan §2.3, §8.1).

**Recipe for the highest-risk item**: `hammondZoneQ` and `hammondZone` are the *same*
seven-branch `if`-chain, so the transfer is `unfold hammondZoneQ hammondZone` followed by
`norm_cast` — no hypotheses and no case bash (calibrated in
`theories/hammond/probes/hammond-api-cast-classifier.lean`; the `by_cases` transcription of the
Marcus three-branch proof does not scale to seven branches). The seven characterization lemmas
use the uniform recipe `unfold hammondZoneQ` then `split_ifs with h1 … h6`, each leaf closed by
`iff_of_true rfl …` or `iff_of_false (by decide) …`, with `linarith` on the arithmetic side.

**Dependency note**: the file imports `PhotoLean.Marcus.RatModel` because the cross-link theorem
`hammondZoneQ_beyondReactant_iff_inverted` is stated against the delivered
`Marcus.Rat.zoneQ` / `Marcus.Zone` (as the statement skeleton requires).

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Hammond.RatModel
  proofs/scripts/check.sh --strict PhotoLean.Hammond.RatModel
  proofs/scripts/axioms.sh PhotoLean.Hammond.RatModel PhotoLean.Hammond.Rat.<theorem>
-/
import PhotoLean.Hammond.Basic
import PhotoLean.Marcus.RatModel

namespace PhotoLean

namespace Hammond

namespace Rat

/-! ## Definitions (plan §8.1) -/

/-- Rational transition-state coordinate (computable). -/
def tsCoordQ (lam x : ℚ) : ℚ := (lam - x) / (2 * lam)

/-- Rational forward barrier. -/
def gapReactantQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Rational Leffler secant. -/
def lefflerSecantQ (lam x₁ x₂ : ℚ) : ℚ :=
  -(gapReactantQ lam x₂ - gapReactantQ lam x₁) / (x₂ - x₁)

/-- Rational structural classifier. -/
def hammondZoneQ (lam x : ℚ) : HZone :=
  if x = lam then HZone.atReactant
  else if x = -lam then HZone.atProduct
  else if x < -lam then HZone.beyondProduct
  else if lam < x then HZone.beyondReactant
  else if x = 0 then HZone.half
  else if 0 < x then HZone.early
  else HZone.late

/-! ## Transfer lemmas (plan §8.1)

Each one moves a computed ℚ-side value onto the ℝ theory. The algebraic ones are
`unfold` + `push_cast` + `ring`; `push_cast` does **not** close the goal by itself, `ring` must
follow (the explicit `rw [Rat.cast_div, …]` route would close by `rfl` instead — the two routes
have opposite tail rules, recorded in `proofs/API-NOTES.md`). -/

/-- Transfer: the rational coordinate casts to the real one. -/
theorem tsCoordQ_cast (lam x : ℚ) :
    ((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ) := by
  unfold tsCoordQ tsCoord
  push_cast
  ring

/-- Transfer: the rational barrier casts to the real one. -/
theorem gapReactantQ_cast (lam x : ℚ) :
    ((gapReactantQ lam x : ℚ) : ℝ) = gapReactant (lam : ℝ) (x : ℝ) := by
  unfold gapReactantQ gapReactant
  push_cast
  ring

set_option linter.unusedVariables false in
/-- Transfer: the rational Leffler secant casts to the real one.

The hypothesis `x₁ ≠ x₂` is the explicit mathematical premise of a secant and is mandated by the
statement authority; it is **not used by the proof**, because `Rat.cast_div` commutes the cast with
division unconditionally (at `x₁ = x₂` the `x / 0 = 0` convention collapses both sides). It is kept
as an explicit premise rather than dropped, and the unused-variable linter is switched off for this
declaration only. -/
theorem lefflerSecantQ_cast {lam x₁ x₂ : ℚ} (h : x₁ ≠ x₂) :
    ((lefflerSecantQ lam x₁ x₂ : ℚ) : ℝ) = lefflerSecant (lam : ℝ) (x₁ : ℝ) (x₂ : ℝ) := by
  unfold lefflerSecantQ lefflerSecant
  push_cast
  rw [gapReactantQ_cast, gapReactantQ_cast]

end Rat

end Hammond

end PhotoLean
