/-
energyGapLaw-statement-skeleton.lean — the STATEMENT AUTHORITY of the EnergyGapLaw theory.

Statement-first (iron rule 2): every declaration below is the agreed statement verbatim; the theorem
bodies are placeholders on purpose (definitions carry their real bodies). This file must compile at
0 error
(`proofs/scripts/lake env lean theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean`)
BEFORE any proof work starts; delivery replaces the bodies verbatim and
`python3 theories/BEP/probes/bep-fidelity.py --theory EnergyGapLaw` compares the delivered
signatures to this file word for word.

Plan: `theories/EnergyGapLaw/plan.md` (the frozen design; photophysics batch 2026-09-22, group B —
two-parabola basis, reusing the Marcus kernel, first theory of the group).
Milestones: EG-B (Basic: kernel/Marcus copies + certificates + the log-rate), EG-C (Criterion:
the exact quadratic law and its regime directions), EG-S (Sharp: the affine tangent reading and its
defect), EG-R (RatModel: the rational decision layer), EG-I (Instances: named rational models and
their verdicts).

The theory reads the kernel's equal-curvature two-parabola model as the classical energy-gap law
(Englman–Jortner form): the nonradiative rate is the Marcus rate at the gap
(`x = −ΔG = ΔE` up to the sign convention); the exact law is the quadratic
`log k(x) = log A − (lam − x)²/(4·lam·kB·T)`; the decrease direction holds exactly on the inverted
region `lam < x` and reverses in the normal region (the gap law is an inverted-regime law); the
textbook affine law is the tangent at a reference gap `xStar` with the exact quadratic defect
`−(x − xStar)²/(4·lam·kB·T)`, overestimating the log-rate everywhere off the tangent point; and no
affine law is exact on any non-degenerate window (the BEP second-difference pattern transplanted).
The theory's theorems are statements about the classical model, never about measured rates
(LITERATURE.md, source S3 wording discipline). Literature anchors:
`theories/EnergyGapLaw/LITERATURE.md`.

Sprint-0 statement notes (all calibrated in `EnergyGapLaw-api-probe.lean`):
* EG-S4: the plan's draft carries `(hA : 0 < A)`, which the statement cannot consume (no `A`
  occurs in it); dropped under the weakest-premise standard (iron rule 3) — plan §3.1 item.
* EG-C4 corollary `secant_slope_neg_iff`: stated as the iff the plan's "negative exactly when"
  wording fixes (the plan's signature sketch shows the midpoint premise `hx`; the iff carries it
  on the right).
* EG-I3 `tangentWitness`: the plan's parenthetical draft defect `−20` is an arithmetic slip; the
  literature round's note (LITERATURE.md, statement-impact summary, item 1) and the probe's
  `norm_num` recomputation fix the magnitude at **5**, and the row states `lnRate 2 = eglTangent
  2 − 5`. The plan's `kB * T = 1/40` is printed as `kB = 1`, `T = 1/40`.
-/
import Mathlib
import PhotoLean.Kernel
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace EnergyGapLaw

/-! ## EG-B — description layer (`PhotoLean/EnergyGapLaw/Basic.lean`) -/

/-- Nonradiative crossing barrier at reorganization energy `lam` and gap `x` (driving-force
convention `x = −ΔG°`). Plan section 4, row EG-B1. This theory's own copy, pinned to
`PhotoLean.Kernel.barrier` by `cert_nrBarrier` (hard constraint 1). -/
noncomputable def nrBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Kernel certificate: the nonradiative barrier IS `PhotoLean.Kernel.barrier`.
Plan section 4, row EG-B1. Proof route (plan §4): `rfl` (definitional copy — the pointwise row;
dry-run in the api-probe). -/
theorem cert_nrBarrier (lam x : ℝ) : nrBarrier lam x = PhotoLean.Kernel.barrier lam x := by
  sorry

/-- Nonradiative rate with prefactor `A` at thermal energy `kB * T`: the Arrhenius/Marcus rate
over the crossing barrier. Plan section 4, row EG-B2. This theory's own copy, pinned to
`PhotoLean.Marcus.rate` by `cert_nrRate` (hard constraint 1). -/
noncomputable def nrRate (A lam kB T x : ℝ) : ℝ :=
  A * Real.exp (-(nrBarrier lam x) / (kB * T))

/-- Marcus certificate: the nonradiative rate IS `PhotoLean.Marcus.rate` (the Marcus body is
`A * Real.exp (-(Marcus.barrier lam x) / (kB * T))`). Plan section 4, row EG-B2.
Proof route (plan §4): `unfold` + `rfl` (plain `rfl` already closes it in the api-probe). -/
theorem cert_nrRate (A lam kB T x : ℝ) :
    nrRate A lam kB T x = PhotoLean.Marcus.rate A lam kB T x := by
  sorry

/-- The inverted-gap predicate: the gap exceeds the reorganization energy. Plan section 4,
row EG-B3. This theory's own copy, pinned to `PhotoLean.Marcus.InvertedRegion` by
`cert_invertedGap` (hard constraint 1). -/
def InvertedGap (lam x : ℝ) : Prop := lam < x

/-- Marcus certificate: the inverted-gap predicate IS `PhotoLean.Marcus.InvertedRegion`.
Plan section 4, row EG-B3. Proof route (plan §4): `Iff.rfl`. -/
theorem cert_invertedGap (lam x : ℝ) :
    InvertedGap lam x ↔ PhotoLean.Marcus.InvertedRegion lam x := by
  sorry

/-- The log-rate: `Real.log` of the nonradiative rate. Plan section 4, row EG-B4. (The rate is
positive under `0 < A`, so no totalization issue arises — the premise is carried on the rows
that consume it, plan §2.) -/
noncomputable def lnRate (A lam kB T x : ℝ) : ℝ := Real.log (nrRate A lam kB T x)

/-! ## EG-C — law layer (`PhotoLean/EnergyGapLaw/Criterion.lean`) -/

/-- **The exact quadratic gap law**: the log-rate is `log A` minus the barrier over `kB * T`.
Plan section 4, row EG-C1. Weakest-premise standard (plan §4): `lam ≠ 0` suffices for the
algebra — positivity is needed only where the *order* matters. Proof route (plan §5):
`Real.log_mul` (`A ≠ 0` from `hA`, `Real.exp_ne_zero`), `Real.log_exp`, then `field_simp` +
`ring` (dry-run in the api-probe). -/
theorem lnRate_eq {A lam kB T x : ℝ} (hA : 0 < A) (hlam : lam ≠ 0) (hkT : 0 < kB * T) :
    lnRate A lam kB T x = Real.log A - (lam - x) ^ 2 / (4 * lam * (kB * T)) := by
  sorry

/-- **The gap-law direction**: within the inverted region the log-rate strictly decreases in the
gap. Plan section 4, row EG-C2. Proof route (plan §5): rewrite by EG-C1; the quadratic comparison
factors as `(x₂ − x₁) * (x₁ + x₂ − 2 * lam)`, whose sign the region premise fixes; close by
`nlinarith` (dry-run in the api-probe). -/
theorem lnRate_strictAnti_on_inverted {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (hx1 : lam < x₁) (h : x₁ < x₂) :
    lnRate A lam kB T x₂ < lnRate A lam kB T x₁ := by
  sorry

/-- **The reversal**: within the normal region the log-rate strictly *increases* in the gap —
together with EG-C2 this pins the gap law to its regime (the boundary `x = lam` is the
barrierless point, `nrBarrier lam lam = 0`). Plan section 4, row EG-C3. Proof route (plan §5):
rewrite by EG-C1; same factorization, opposite sign; `nlinarith` (dry-run in the api-probe). -/
theorem lnRate_strictMono_on_normal {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (hx2 : x₂ < lam) (h : x₁ < x₂) :
    lnRate A lam kB T x₁ < lnRate A lam kB T x₂ := by
  sorry

/-- The secant slope of the log-rate is the midpoint form. Plan section 4, row EG-C4.
Proof route (plan §5): EG-C1 + `field_simp` + `ring`. -/
theorem secant_slope_exact {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hlam : lam ≠ 0)
    (hkT : 0 < kB * T) (h : x₁ ≠ x₂) :
    (lnRate A lam kB T x₂ - lnRate A lam kB T x₁) / (x₂ - x₁)
      = (2 * lam - x₁ - x₂) / (4 * lam * (kB * T)) := by
  sorry

/-- The secant is negative exactly when the window midpoint is inverted. Plan section 4,
row EG-C4 (corollary; the iff the plan's "negative exactly when" wording fixes — the sketch's
midpoint premise `hx` is the iff's right side). Proof route: rewrite by `secant_slope_exact`;
the denominator is positive under `hlam`, `hkT`, so the sign is the numerator's; field-order
lemmas + `linarith`. -/
theorem secant_slope_neg_iff {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (h : x₁ ≠ x₂) :
    (lnRate A lam kB T x₂ - lnRate A lam kB T x₁) / (x₂ - x₁) < 0
      ↔ lam < (x₁ + x₂) / 2 := by
  sorry

/-! ## EG-S — tangent layer, the Englman–Jortner reading (`PhotoLean/EnergyGapLaw/Sharp.lean`) -/

/-- The affine gap law at the reference gap `xStar`: the tangent of the exact quadratic, with
slope `(lam − xStar) / (2 * lam * (kB * T))`. Plan section 4, row EG-S1. -/
noncomputable def eglTangent (A lam kB T xStar x : ℝ) : ℝ :=
  lnRate A lam kB T xStar + (lam - xStar) / (2 * lam * (kB * T)) * (x - xStar)

/-- The tangent overestimates the log-rate everywhere off the tangent point, with equality only
at the reference gap. Plan section 4, row EG-S2. Proof route (plan §5): EG-C1 + the defect
identity EG-S2a (`ring`) + `div_nonneg`/`sq_nonneg`; the equality direction by
`sq_eq_zero_iff`. -/
theorem eglTangent_overestimates {A lam kB T xStar x : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) :
    lnRate A lam kB T x ≤ eglTangent A lam kB T xStar x ∧
      (lnRate A lam kB T x = eglTangent A lam kB T xStar x ↔ x = xStar) := by
  sorry

/-- The exact defect: the tangent sits above the log-rate by the quadratic
`(x − xStar)² / (4 * lam * (kB * T))`. Plan section 4, row EG-S2 (defect row EG-S2a).
Proof route (plan §5): EG-C1 on both `lnRate`s + `ring`. -/
theorem eglTangent_defect {A lam kB T xStar x : ℝ} (hA : 0 < A) (hlam : lam ≠ 0)
    (hkT : 0 < kB * T) :
    lnRate A lam kB T x
      = eglTangent A lam kB T xStar x - (x - xStar) ^ 2 / (4 * lam * (kB * T)) := by
  sorry

/-- No affine gap law is exact on any non-degenerate window — the second-difference engine,
mirroring `PhotoLean.BEP.not_epLinearOn_of_ne_zero` (the pattern calibrated there). Plan
section 4, row EG-S3. Proof route (plan §5): three evaluations (`p`, `(p + q) / 2`, `q`) of the
purported affine law force the second difference to vanish, but the exact law's second
difference is `−(q − p)² / (…)` after EG-C1 — contradiction by `nlinarith`. -/
theorem not_affine_on_window {A lam kB T p q : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (hpq : p < q) :
    ¬ ∃ c k : ℝ, ∀ x ∈ Set.Icc p q, lnRate A lam kB T x = c + k * x := by
  sorry

/-- The tangent slope steepens with the reference gap — the formal reading of why each
homologous series fits its own line. Plan section 4, row EG-S4. (Sprint-0 statement note: the
plan's draft carries `(hA : 0 < A)`, which the statement cannot consume — no `A` occurs in it;
dropped under the weakest-premise standard, iron rule 3; plan §3.1 item.) Proof route (plan §5):
clear the positive denominator `2 * lam * (kB * T)`, then `linarith`. -/
theorem eglTangent_slope_strictAnti {lam kB T x₁ x₂ : ℝ} (hlam : 0 < lam) (hkT : 0 < kB * T)
    (h : x₁ < x₂) :
    (lam - x₂) / (2 * lam * (kB * T)) < (lam - x₁) / (2 * lam * (kB * T)) := by
  sorry

/-! ## EG-R — the rational decision layer (`PhotoLean/EnergyGapLaw/RatModel.lean`) -/

namespace Rat

/-- The computable ℚ shadow of the nonradiative barrier. Plan section 4, row EG-R1.
Pure polynomial division — no transcendental anywhere in the layer (hard constraint 3). -/
def nrBarrier (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Cast coherence: the ℚ shadow computes the real barrier at cast parameters. Plan section 4,
row EG-R1 (cast row; name assigned in Sprint 0). Proof route: `unfold` + `push_cast` + `ring`
(dry-run in the api-probe). -/
theorem nrBarrier_cast (lam x : ℚ) :
    (nrBarrier lam x : ℝ) = PhotoLean.EnergyGapLaw.nrBarrier (lam : ℝ) (x : ℝ) := by
  sorry

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
  sorry

/-- The decidable rate ordering, stated on the barrier side: `nrRate_decidable_order lam x₁ x₂`
decides the strict rate increase from gap `x₁` to gap `x₂` as the barrier comparison
`Rat.nrBarrier lam x₂ < Rat.nrBarrier lam x₁` (exp strict monotonicity consumes it on ℝ; **no**
`Real.exp` evaluation enters any instance row — hard constraint 3). Plan section 4, row EG-R3.
Verdicts by `decide_eq_true_eq` + `norm_num` (calibrated in the api-probe; bare `by decide` does
not reduce ℚ-literal Bools in the kernel — the ICvsISC note). -/
def nrRate_decidable_order (lam x₁ x₂ : ℚ) : Bool :=
  decide (Rat.nrBarrier lam x₂ < Rat.nrBarrier lam x₁)

/-! ## EG-I — instances and verdicts (`PhotoLean/EnergyGapLaw/Instances.lean`) -/

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
  sorry

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
  sorry

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
  sorry

end EnergyGapLaw

end PhotoLean
