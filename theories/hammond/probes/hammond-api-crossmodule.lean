/-
Hammond milestone — API probe (topic F): cross-module names to import from the Marcus layer,
and the definitional bridge `gapReactant = barrier`.

All names below are `#check`ed against the delivered Marcus modules
(`PhotoLean/Marcus/{Basic,Rate,RatModel,Reorg,Sharp}.lean`, all of them already built).
Note the extra import: `descriptor_sharp` lives in `PhotoLean.Marcus.Sharp`, which is **not**
imported by `Basic` / `Rate` / `RatModel` / `Reorg`, so the Hammond module that wants to cite
it must import `PhotoLean.Marcus.Sharp` explicitly.

The bridge is definitional: Marcus's `barrier` and the planned `gapReactant` have the same
body `(lam - x) ^ 2 / (4 * lam)`, so the Hammond bridge theorem is `rfl`, not `ring`.

Running:  proofs/scripts/lake env lean theories/hammond/probes/hammond-api-crossmodule.lean
Status:   0 errors / 0 warnings.
-/
import PhotoLean.Marcus.Basic
import PhotoLean.Marcus.Rate
import PhotoLean.Marcus.RatModel
import PhotoLean.Marcus.Reorg
import PhotoLean.Marcus.Sharp

namespace PhotoLean.Hammond.ProbeCross

/-! ## `#check` of every cross-module name the Hammond milestone needs -/

#check @PhotoLean.Marcus.barrier
#check @PhotoLean.Marcus.InvertedRegion
#check @PhotoLean.Marcus.Zone
#check @PhotoLean.Marcus.zone
#check @PhotoLean.Marcus.rate
#check @PhotoLean.Marcus.Rat.zoneQ
#check @PhotoLean.Marcus.Rat.barrierQ
#check @PhotoLean.Marcus.lamInner
#check @PhotoLean.Marcus.lamOuter
#check @PhotoLean.Marcus.lamInner_pos
#check @PhotoLean.Marcus.lam_total_pos
#check @PhotoLean.Marcus.hgeom_of_nonoverlap
#check @PhotoLean.Marcus.descriptor_sharp

-- Additional bridges that already exist in the Marcus ℚ layer and can be reused verbatim
-- (they are the template for the Hammond `hammondZoneQ_cast` / `tsCoordQ_cast`):
#check @PhotoLean.Marcus.Rat.zoneQ_eq_zone
#check @PhotoLean.Marcus.Rat.barrierQ_cast
#check @PhotoLean.Marcus.Rat.zoneQ_inverted_iff

/-! ## The definitional bridge `barrier = gapReactant` -/

/-- Planned Hammond definition, copied verbatim from the milestone statement. -/
noncomputable def gapReactant (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The Marcus barrier has literally the same body — `rfl` closes the equation. -/
example (lam x : ℝ) : PhotoLean.Marcus.barrier lam x = (lam - x) ^ 2 / (4 * lam) := rfl

/-- Hence the Hammond bridge theorem can (and should) be proved by `rfl`. -/
theorem gapReactant_eq_barrier (lam x : ℝ) : gapReactant lam x = PhotoLean.Marcus.barrier lam x :=
  rfl

/-- The same in the direction the plan states it (`barrier` on the left). -/
theorem barrier_eq_gapReactant (lam x : ℝ) : PhotoLean.Marcus.barrier lam x = gapReactant lam x :=
  rfl

/-- Marcus's `InvertedRegion` is a `def`, so the two sides of the plan's statement are the
same proposition by definition — no lemma needed to unfold it. -/
example (lam x : ℝ) : PhotoLean.Marcus.InvertedRegion lam x = (lam < x) := rfl

/-- Marcus's `rate` is the exponential of the (negated) Marcus barrier; the Hammond layer can
rewrite with it directly. -/
example (A lam kB T x : ℝ) :
    PhotoLean.Marcus.rate A lam kB T x
      = A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T)) := rfl

end PhotoLean.Hammond.ProbeCross
