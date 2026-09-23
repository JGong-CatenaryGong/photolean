/-
PhotoLean.EnergyGapLaw.RatModel — EG4, the rational decision layer of the energy-gap law.

The real layer (`Basic`, `Criterion`, `Sharp`) states the law with `Real.exp`/`Real.log`. Every
*decision* the theory asks for, however, is a comparison of rational numbers: which gap is
inverted, which barrier is larger, whether the aromatic series decreases. This module delivers the
computable ℚ shadow that those decisions are made in — with **no transcendental function anywhere
in the layer** (hard constraint 3): the gap classifier compares `lam` and `x` on ℚ, and the rate
ordering is decided **on the barrier side**, never on `Real.exp`.

* EG-R1 `Rat.nrBarrier` — the computable ℚ copy of the nonradiative barrier; pure polynomial
  division. `Rat.nrBarrier_cast` is the cast-coherence row: the ℚ shadow computes the real
  barrier at cast parameters.
* EG-R2 `EGZone` (`normal` / `barrierless` / `inverted`) and the classifier `egZoneQ`, with the
  correctness row `egZoneQ_eq_inverted_iff`: the classifier returns `inverted` **iff**
  `(lam : ℝ) < (x : ℝ)`. The trichotomy is decided on ℚ (`if x < lam … else if lam < x … else …`);
  the cast is pulled off with `Rat.cast_lt`, and the off-diagonal branches are closed by
  `EGZone.noConfusion`.
* EG-R3 `nrRate_decidable_order` — the decidable rate ordering, stated on the barrier side:
  `decide (Rat.nrBarrier lam x₂ < Rat.nrBarrier lam x₁)`. Since `Real.exp` is strictly monotone
  and `exp` of the negated barrier is strictly *anti*tone in the barrier, the strict rate increase
  from gap `x₁` to gap `x₂` is exactly the strict barrier decrease — a comparison the kernel can
  run on rational literals. This is the row every `Instances.lean` verdict consumes; no `Real.exp`
  evaluation enters it.

On the cast-coherence row and the shadowing pitfall. A declaration whose name carries a namespace
prefix (`theorem Rat.nrBarrier_cast`) elaborates its own type inside that namespace, so an
unqualified right-hand side can silently resolve to the ℚ shadow and the row degenerates into the
vacuous identity `↑x = ↑x` (the cross-cutting pitfall found in the SternVolmer batch, SV-R1).
Here the two occurrences are therefore named **unchanged** — the left `nrBarrier` is
`PhotoLean.EnergyGapLaw.Rat.nrBarrier` (the shadow), the right one is written fully qualified as
`PhotoLean.EnergyGapLaw.nrBarrier` (the real copy). The delivered proof is a real bridge: it
unfolds both sides, pushes the cast through the rational arithmetic (`push_cast`), and closes the
resulting identity `(↑lam - ↑x)²/(4·↑lam) = (↑lam - ↑x)²/(4·↑lam)` by `ring`. A scratch `#print`
of the row was taken during delivery and shows the cast-division/cast-power chain, i.e. the
non-vacuous form; it is **not** a `rfl`-level `↑x = ↑x`.

Plan locus: `theories/EnergyGapLaw/plan.md` §4 (EG-R rows), §5 (routes); sprint EG4; board
`theories/EnergyGapLaw/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.EnergyGapLaw.RatModel
    proofs/scripts/check.sh --strict PhotoLean.EnergyGapLaw.RatModel
    proofs/scripts/axioms.sh PhotoLean.EnergyGapLaw.RatModel PhotoLean.EnergyGapLaw.<theorem>

Statement authority: every declaration below matches
`theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` word for word (plan §3.1
entry 4: `EGZone`/`egZoneQ` live in the main namespace, and the rate-ordering decision is stated
on the barrier side). The routes are the ones the api-probe calibrated. The delivered file
contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of
every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately:
the two keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out
anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import PhotoLean.EnergyGapLaw.Basic

set_option autoImplicit false

namespace PhotoLean

namespace EnergyGapLaw

namespace Rat

/-- The computable ℚ shadow of the nonradiative barrier. Plan section 4, row EG-R1.
Pure polynomial division — no transcendental anywhere in the layer (hard constraint 3). -/
def nrBarrier (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Cast coherence: the ℚ shadow computes the real barrier at cast parameters. Plan section 4,
row EG-R1 (cast row; name assigned in Sprint 0). Proof route: `unfold` + `push_cast` + `ring`
(dry-run in the api-probe). -/
theorem nrBarrier_cast (lam x : ℚ) :
    (nrBarrier lam x : ℝ) = PhotoLean.EnergyGapLaw.nrBarrier (lam : ℝ) (x : ℝ) := by
  unfold nrBarrier PhotoLean.EnergyGapLaw.nrBarrier
  push_cast
  ring

end Rat

/-- The three-zone verdict of the gap-law model: `normal` (`x < lam`), `barrierless`
(`x = lam`, the regime boundary), `inverted` (`lam < x`). Plan section 4, row EG-R2. -/
inductive EGZone | normal | barrierless | inverted
  deriving DecidableEq

/-- The zone classifier at rational parameters. Plan section 4, row EG-R2 (comparisons
decidable on ℚ; instance verdicts by `norm_num [egZoneQ]` — calibrated in the api-probe). -/
def egZoneQ (lam x : ℚ) : EGZone :=
  if x < lam then EGZone.normal
  else if lam < x then EGZone.inverted
  else EGZone.barrierless

/-- Zone correctness at cast parameters, `inverted` row — the row shape the plan writes
explicitly. Plan section 4, row EG-R2. Proof route: `Rat.cast_lt` to pull the cast off, unfold
the classifier, trichotomy by `by_cases` on the two comparisons, `EGZone.noConfusion` on the
off-diagonal branches (dry-run in the api-probe). -/
theorem egZoneQ_eq_inverted_iff (lam x : ℚ) :
    egZoneQ lam x = .inverted ↔ (lam : ℝ) < (x : ℝ) := by
  rw [Rat.cast_lt]
  unfold egZoneQ
  by_cases h1 : x < lam
  · rw [if_pos h1]
    exact ⟨fun h => EGZone.noConfusion h, fun h => absurd h (not_lt_of_gt h1)⟩
  · rw [if_neg h1]
    by_cases h2 : lam < x
    · rw [if_pos h2]
      exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg h2]
      exact ⟨fun h => EGZone.noConfusion h,
             fun h => absurd (le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)) (ne_of_lt h)⟩

/-- The decidable rate ordering, stated on the barrier side: `nrRate_decidable_order lam x₁ x₂`
decides the strict rate increase from gap `x₁` to gap `x₂` as the barrier comparison
`Rat.nrBarrier lam x₂ < Rat.nrBarrier lam x₁` (exp strict monotonicity consumes it on ℝ; **no**
`Real.exp` evaluation enters any instance row — hard constraint 3). Plan section 4, row EG-R3.
Verdicts by `decide_eq_true_eq` + `norm_num` (calibrated in the api-probe; the bare
decision procedure does not reduce ℚ-literal Bools in the kernel — the ICvsISC note). -/
def nrRate_decidable_order (lam x₁ x₂ : ℚ) : Bool :=
  decide (Rat.nrBarrier lam x₂ < Rat.nrBarrier lam x₁)

end EnergyGapLaw

end PhotoLean
