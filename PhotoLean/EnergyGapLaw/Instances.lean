/-
PhotoLean.EnergyGapLaw.Instances — EG5, the named rational models and their verdicts.

The theorem layer of this theory is quantitative: the gap law's direction holds on the inverted
region and reverses on the normal region (`Criterion.lean`), the tangent overestimates with an
exact defect and no affine law is exact on a window (`Sharp.lean`). This module pins those claims
to **named rational models** so that a reader can check the regime boundary, the reversal and the
defect magnitude on printed numbers rather than on the general statements:

* EG-I1 `aromaticSeries` — the representative aromatic series: `lam = 1/2`, `kB * T = 1/40`,
  gaps `x ∈ {1, 3/2, 2}`, all three **inverted**. The barrier chain `1/8 < 1/2 < 9/8` decides the
  strict rate decrease on the barrier side, and the zone classifier returns `inverted` at all
  three gaps — the gap law at ℚ.
* EG-I2 `normalRegionCounter` — the normal-region counter: `lam = 2`, gaps `x ∈ {1/2, 1}`, both
  **normal**. The barriers *decrease* in the gap (`9/32` down to `1/8`), so the rate *increases*
  with the gap: the refuting instance for a regime-free gap law. This is the model that makes
  EG-C2's premise `lam < x₁` load-bearing (plan §4, row EG-I2).
* EG-I3 `tangentWitness` — the tangent witness: `lam = 1/2`, `kB * T = 1/40` (printed as `kB = 1`,
  `T = 1/40`), reference gap `x* = 3/2`, evaluated at `x = 2`. The exact defect is
  `−(2 − 3/2)²/(4·(1/2)·(1/40)) = −5`, so the row states `lnRate 2 = eglTangent (3/2) 2 − 5`.
  Plan §3.1 entry 1 records the Sprint-0 arithmetic correction: the plan's parenthetical draft
  computed `−20`; the literature round's note and the api-probe `norm_num` recomputation fix the
  magnitude at **5**, and the skeleton carries the corrected row.

Every verdict is decided by kernel computation on rational literals — the same ladders the api
probe pre-computed (`theories/EnergyGapLaw/probes/EnergyGapLaw-api-probe.lean`) — with the rate
ordering read on the **barrier side** (`Rat.nrBarrier`), never through `Real.exp` (hard
constraint 3). The route for the ℚ-literal rows is `norm_num [Rat.nrBarrier, egZoneQ,
nrRate_decidable_order, decide_eq_true_eq]`: the bare decision procedure does not reduce ℚ-literal
Bools in the kernel (the ICvsISC note), so the `decide`-iff lemma is applied before `norm_num`.
The route for EG-I3 is the one the api-probe calibrated: EG-C1 at both gaps, after which the two
`Real.log A` terms cancel and the remaining atom-carrying linear identity is closed by `ring`
(bare `norm_num` leaves it — API-NOTES §photobatch).

What is NOT derived here: the three models are **representative rational models, not fitted
spectroscopic data** (plan §9 honesty table row 4); they are named because their verdicts are
machine-checkable, not because they describe a particular molecule. The theory's judgement on
measured rates is outside the formalization (LITERATURE.md, source S3 wording discipline).

Plan locus: `theories/EnergyGapLaw/plan.md` §4 (EG-I rows), §8 (the probe-recompute discipline),
§9 (honesty table); sprint EG5; board `theories/EnergyGapLaw/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.EnergyGapLaw.Instances
    proofs/scripts/check.sh --strict PhotoLean.EnergyGapLaw.Instances
    proofs/scripts/axioms.sh PhotoLean.EnergyGapLaw.Instances PhotoLean.EnergyGapLaw.<theorem>

Statement authority: every declaration below matches
`theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` word for word. The delivered
file contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms`
of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note
deliberately: the two keyword literals that `proofs/scripts/check.sh --strict` scans for are not
spelled out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block
comments.
-/
import PhotoLean.EnergyGapLaw.RatModel
import PhotoLean.EnergyGapLaw.Sharp

set_option autoImplicit false

namespace PhotoLean

namespace EnergyGapLaw

/-! ## EG-I — named rational models -/

/-- **Aromatic-like series** (representative rational model, plan §9 row 4): `lam = 1/2`,
`kB * T = 1/40`, gaps `x ∈ {1, 3/2, 2}`, all inverted — the barrier chain `1/8 < 1/2 < 9/8`
decides the strict rate decrease on the barrier side (the gap law at ℚ). Plan section 4,
row EG-I1. Facts about printed rationals, decided by `norm_num`/`decide_eq_true_eq` (routes
calibrated in the api-probe). -/
theorem aromaticSeries :
    Rat.nrBarrier (1 / 2) 1 = 1 / 8 ∧ Rat.nrBarrier (1 / 2) (3 / 2) = 1 / 2 ∧
    Rat.nrBarrier (1 / 2) 2 = 9 / 8 ∧
    Rat.nrBarrier (1 / 2) 1 < Rat.nrBarrier (1 / 2) (3 / 2) ∧
    Rat.nrBarrier (1 / 2) (3 / 2) < Rat.nrBarrier (1 / 2) 2 ∧
    egZoneQ (1 / 2) 1 = .inverted ∧ egZoneQ (1 / 2) (3 / 2) = .inverted ∧
    egZoneQ (1 / 2) 2 = .inverted ∧
    nrRate_decidable_order (1 / 2) (3 / 2) 1 = true ∧
    nrRate_decidable_order (1 / 2) 2 (3 / 2) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Rat.nrBarrier, egZoneQ, nrRate_decidable_order, decide_eq_true_eq]

/-- **Normal-region counter** (representative rational model): `lam = 2`, gaps `x ∈ {1/2, 1}`,
both normal — the barriers *decrease* in the gap (`9/32` down to `1/8`), so the rate *increases*
with the gap: the refuting instance for a regime-free gap law (pins the EG-C2 premise
`lam < x₁` as load-bearing). Plan section 4, row EG-I2. Facts about printed rationals, decided
by `norm_num`/`decide_eq_true_eq`. -/
theorem normalRegionCounter :
    Rat.nrBarrier 2 (1 / 2) = 9 / 32 ∧ Rat.nrBarrier 2 1 = 1 / 8 ∧
    Rat.nrBarrier 2 1 < Rat.nrBarrier 2 (1 / 2) ∧
    egZoneQ 2 (1 / 2) = .normal ∧ egZoneQ 2 1 = .normal ∧
    nrRate_decidable_order 2 (1 / 2) 1 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Rat.nrBarrier, egZoneQ, nrRate_decidable_order, decide_eq_true_eq]

/-- **Tangent witness**: `lam = 1/2`, `kB * T = 1/40` (printed as `kB = 1`, `T = 1/40`), reference
gap `x* = 3/2`, evaluated at `x = 2`: the exact defect is
`−(2 − 3/2)² / (4 * (1/2) * (1/40)) = −5`, so `lnRate 2 = eglTangent (3/2) 2 − 5`. Plan
section 4, row EG-I3 — with the Sprint-0 arithmetic correction: the plan's parenthetical draft
computed `−20`; the literature round's note (LITERATURE.md, statement-impact summary, item 1)
and the api-probe `norm_num` recomputation fix the magnitude at **5**. Proof route: EG-C1 on
both sides, then `ring` (dry-run in the api-probe: after the rewrite the goal is the
atom-carrying identity `Real.log A − 45 = Real.log A − 20 + −20 − 5`, which bare `norm_num`
leaves open and `ring` closes). -/
theorem tangentWitness {A : ℝ} (hA : 0 < A) :
    lnRate A (1 / 2) 1 (1 / 40) 2 = eglTangent A (1 / 2) 1 (1 / 40) (3 / 2) 2 - 5 := by
  have key : ∀ x : ℝ,
      lnRate A (1 / 2) 1 (1 / 40) x
        = Real.log A - (1 / 2 - x) ^ 2 / (4 * (1 / 2) * (1 * (1 / 40))) := by
    intro x
    exact lnRate_eq hA (by norm_num) (by norm_num) (x := x)
  unfold eglTangent
  rw [key 2, key (3 / 2)]
  ring

end EnergyGapLaw

end PhotoLean
