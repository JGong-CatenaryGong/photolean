/-
PhotoLean.QuantumYield.RatModel — milestone QY3, the computable rational decision layer.

The order of `ℝ` is not computable, so a verdict about a *measured* channel-rate triple cannot be
decided by the kernel over `ℝ` (the repository's standing structural solution: an `ℝ` theory plus a
`ℚ` shadow plus cast bridges). This module carries the shadow of the total rate and the yield
(QY-R1), the decidability instance of the shadow's premise bundle, and the cast coherence rows
(QY-R2) that make the ℚ copy the real thing rather than an analogy: each shadow computes the
corresponding `ℝ` quantity of `Basic`.

At the named instances the cast bridges are what the verdict rows of `Instances` use: a ℚ verdict
about a measured rate triple is a statement about the corresponding real system.

**Statement-incident check (the cross-cutting namespace-shadowing pitfall found on this batch).**
A declaration whose name is namespace-prefixed (e.g. `Rat.totalRate_cast`) elaborates its own *type*
inside that namespace, so an unqualified right-hand side would resolve to the ℚ shadow and the row
would silently become the vacuous identity `↑x = ↑x`, closable by `rfl`. Both cast rows below were
`#print`-inspected after proving (scratch probe, no delivered artifact): the printed types carry the
fully-qualified `PhotoLean.QuantumYield.totalRate` / `.yieldOf` on the right, i.e. the intended
bridges — no statement incident for this theory. The authority's right-hand sides are already
fully qualified, unlike the first freeze of the sibling SternVolmer theory.

Measured boundaries (api probe, `proofs/API-NOTES.md` §photobatch): `decide` does not reduce ℚ
division (kernel-stuck at well-founded `Nat.gcd`), so the verdict rows of the next module close by
`norm_num`; the cast rows move through `Rat.cast_div` / `norm_cast` plus the delivered total-rate
bridge.

Statement authority: `theories/QuantumYield/probes/QuantumYield-statement-skeleton.lean` § QY-R;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.QuantumYield.RatModel` (exit 0);
`proofs/scripts/check.sh --strict`;
`proofs/scripts/axioms.sh PhotoLean.QuantumYield.RatModel PhotoLean.QuantumYield.Rat.yieldOf_cast`.
-/
import PhotoLean.QuantumYield.Basic

open scoped BigOperators

set_option autoImplicit false

namespace PhotoLean

namespace QuantumYield

/-! ## QY-R — the rational decision layer -/

namespace Rat

/-- Rational total rate.
Plan section 4, row QY-R1. -/
def totalRate {n : ℕ} (k : Fin n → ℚ) : ℚ := ∑ i, k i

/-- Rational yield of channel `i`.
Plan section 4, row QY-R1. -/
def yieldOf {n : ℕ} (k : Fin n → ℚ) (i : Fin n) : ℚ := k i / totalRate k

/-- The premise bundle in the decision layer.
Plan section 4, row QY-R1. -/
structure QYData {n : ℕ} (k : Fin n → ℚ) : Prop where
  /-- every channel rate is nonnegative -/
  nonneg : ∀ i, 0 ≤ k i
  /-- the total rate is positive -/
  total_pos : 0 < totalRate k

/-- Decidability of the decision-layer premise bundle (plan section 4, row QY-R1). Calibration
note (api-probe): `decide` closes the fieldwise `nonneg` half but cannot evaluate the
`Finset.univ` sum inside `total_pos` (kernel-stuck at `Rat.blt` via well-founded `Nat.gcd`);
concrete `total_pos` goals go through `norm_num [totalRate, Fin.sum_univ_three, …]`. -/
instance instDecidableQYData {n : ℕ} (k : Fin n → ℚ) : Decidable (QYData k) :=
  decidable_of_iff ((∀ i, 0 ≤ k i) ∧ 0 < totalRate k)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.nonneg, h.total_pos⟩⟩

/-- Cast coherence of the total rate: the rational total casts to the real total of the cast
rates.
Plan section 4, row QY-R2, first form. -/
theorem totalRate_cast {n : ℕ} (kq : Fin n → ℚ) :
    (totalRate kq : ℝ) = PhotoLean.QuantumYield.totalRate (fun i => (kq i : ℝ)) := by
  -- Proof route (API-calibrated): `Rat.cast_sum Finset.univ kq`.
  unfold Rat.totalRate PhotoLean.QuantumYield.totalRate
  rw [Rat.cast_sum]

/-- Cast coherence of the yield: the rational yield casts to the real yield of the cast rates.
Plan section 4, row QY-R2, second form. -/
theorem yieldOf_cast {n : ℕ} (kq : Fin n → ℚ) (i : Fin n) :
    (yieldOf kq i : ℝ) = PhotoLean.QuantumYield.yieldOf (fun i => (kq i : ℝ)) i := by
  -- Proof route (API-calibrated): unfold; `Rat.cast_div` + `Rat.cast_sum`.
  unfold Rat.yieldOf PhotoLean.QuantumYield.yieldOf
  rw [Rat.cast_div, ← totalRate_cast]

end Rat

end QuantumYield

end PhotoLean
