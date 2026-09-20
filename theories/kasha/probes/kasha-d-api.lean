/-
theories/kasha/probes/kasha-d-api.lean

API probe for milestone K4 (composition and bridges) — prover_d, 2026-09-20.

Why this probe exists. The K4-facing recipes are calibrated in three other probes
(`kasha-api-cascade.lean`, `kasha-api-logexp.lean`, `kasha-risk-probe.lean`), but all three work
against *local copies* of the K1 definitions. The three recipes below are the ones that have to hold
against the **delivered** definitions of `PhotoLean/Kasha/Basic.lean`, so they are kernel-checked
here (and only here) by importing that module — plus `PhotoLean.Marcus.Basic` for the cross-module
bridge `PhotoLean.Marcus.barrier`:

1. the block-splitting identity of the cascade probability (plan §7.2 #1), which the plan's §10 risk
   register calls the most likely friction point of the milestone (the `Finset` index surgery of
   `Icc (i+1) N` at an interior level `M`);
2. the premise-free level-1 toolkit `cascade f g 0 1 = icBranch f g 1`,
   `upperYield f g 1 = radBranch f g 1`, `fluoYield f g 1 = radBranch f g 0 * icBranch f g 1 +
   radBranch f g 1` — rows 5–9 and 12 of §7.2 run it on the **effective** two-level data, which
   carries no `RateData` instance, so the `RateData`-carrying K1 rows cannot be used there;
3. the two closing steps: `(A / B) / (C / B) = A / C` (row 7) and `w ^ 2 ≤ R ↔ |w| ≤ √R` under
   `0 ≤ R` (row 14, the BEP-notes `sqrt` recipe applied to the K4 window).

Names whose calibration lives elsewhere and is not repeated here: `Finset.Icc_self`,
`Finset.sum_singleton`, `Finset.prod_singleton`, `Finset.sum_insert`, `Finset.prod_Icc_succ_top`
(`kasha-api-cascade.lean`); `Real.log_le_iff_le_exp`, `Real.log_div`, `Real.log_one`,
`PhotoLean.Marcus.barrier` (`kasha-api-logexp.lean`); `Real.sqrt_sq_eq_abs`, `Real.sq_sqrt`,
`Real.sqrt_le_sqrt`, `sq_abs`, `pow_le_pow_left₀`, `div_le_iff₀`, `le_div_iff₀`, `div_le_div_iff₀`
(`theories/BEP/probes/bep-api-abs-sqrt.lean` and `proofs/API-NOTES.md` §Marcus groups B/C/D).

Running:  proofs/scripts/lake env lean theories/kasha/probes/kasha-d-api.lean
Status:   0 errors / 0 warnings (measured 2026-09-20).
-/
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Marcus.Basic

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean
namespace Kasha
namespace ProbeD

/-! ## Names this milestone needs that were not in `proofs/API-NOTES.md` yet -/

-- `Nat.le_induction` carries the bound as an *argument of the motive* (`P : (n : ℕ) → m ≤ n → Prop`),
-- so `induction N, h2 using Nat.le_induction` gives the cases `base` and `succ N hM ih`.
#check @Nat.le_induction
-- Over ℝ the `Group` version `div_div_div_cancel_right` does **not** apply (`Group ℝ` does not
-- exist: `0` has no inverse) — `failed to synthesize Group ℝ`, measured. The usable name is the
-- `GroupWithZero` version `div_div_div_cancel_right₀ (h : c ≠ 0) (a b) : a / c / (b / c) = a / b`,
-- exactly the row-7 shape `(e₀ / (u+C)) / (u / (u+C)) = e₀ / u`.
#check @div_div_div_cancel_right
#check @div_div_div_cancel_left
#check @div_div_div_cancel_right₀
-- The monotone-cancellation form of row 8/9 (multiplication by `upperYield N + cascade 0 N > 0`).
#check @mul_le_mul_iff_of_pos_right

/-! ## Recipe 1 — the block split of the cascade probability (plan §7.2 #1, risk register §10)

`Icc (i+1) N` splits at an interior level `M`; peeling the *top* index with
`Finset.prod_Icc_succ_top` and inducting on the gap `N - M` (`Nat.le_induction`) avoids any
`Icc`-union lemma, and the step is finished by associativity. Kernel-checked against the delivered
`cascade`. -/

example {rad ic : ℕ → ℝ} {i M N : ℕ} (h1 : i ≤ M) (h2 : M ≤ N) :
    cascade rad ic i N = cascade rad ic i M * cascade rad ic M N := by
  induction N, h2 using Nat.le_induction with
  | base => rw [cascade_self, mul_one]
  | succ N hM ih =>
    have hstep : ∀ a : ℕ, a ≤ N →
        cascade rad ic a (N + 1) = cascade rad ic a N * icBranch rad ic (N + 1) := by
      intro a ha
      unfold cascade
      rw [Finset.prod_Icc_succ_top (by omega : a + 1 ≤ N + 1)]
    rw [hstep i (le_trans h1 hM), hstep M hM, ih, mul_assoc]

/-! ## Recipe 2 — the level-1 toolkit against the delivered definitions (plan §7.2 #5–#9, #12)

All four facts are premise-free: the effective two-level data of rows 5–9 has no `RateData`
instance, and row 12 needs the level-1 split of the *given* ladder. -/

/-- `cascade f g 0 1 = icBranch f g 1` (the level-1 empty-product reduction). -/
example (f g : ℕ → ℝ) : cascade f g 0 1 = icBranch f g 1 := by
  unfold cascade
  have hset : Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hset, Finset.prod_singleton]

/-- `upperYield f g 1 = radBranch f g 1`. -/
example (f g : ℕ → ℝ) : upperYield f g 1 = radBranch f g 1 := by
  unfold upperYield
  rw [Finset.Icc_self, Finset.sum_singleton]
  exact emitYield_self f g 1

/-- `emitYield f g 0 1 = radBranch f g 0 * icBranch f g 1`. -/
example (f g : ℕ → ℝ) : emitYield f g 0 1 = radBranch f g 0 * icBranch f g 1 := by
  have hC : cascade f g 0 1 = icBranch f g 1 := by
    unfold cascade
    have hset : Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hset, Finset.prod_singleton]
  unfold emitYield
  rw [hC]

/-- `fluoYield f g 1 = radBranch f g 0 * icBranch f g 1 + radBranch f g 1` (the level-1 split, no
physical premise needed — the shape rows 5–9 run on the *effective* data, which has no `RateData`
instance). -/
example (f g : ℕ → ℝ) :
    fluoYield f g 1 = radBranch f g 0 * icBranch f g 1 + radBranch f g 1 := by
  have hC : cascade f g 0 1 = icBranch f g 1 := by
    unfold cascade
    have hset : Finset.Icc (0 + 1) 1 = ({1} : Finset ℕ) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hset, Finset.prod_singleton]
  have hE : emitYield f g 0 1 = radBranch f g 0 * icBranch f g 1 := by
    unfold emitYield
    rw [hC]
  have hU : upperYield f g 1 = radBranch f g 1 := by
    unfold upperYield
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact emitYield_self f g 1
  have hsplit : fluoYield f g 1 = emitYield f g 0 1 + upperYield f g 1 := by
    unfold fluoYield upperYield
    have hset : Finset.range (1 + 1) = insert 0 (Finset.Icc 1 1) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
  rw [hsplit, hE, hU]

/-! ## Recipe 3a — the row-7 cancellation `(e₀ / B) / (u / B) = e₀ / u` -/

example {e₀ u B : ℝ} (hB : B ≠ 0) : e₀ / B / (u / B) = e₀ / u :=
  div_div_div_cancel_right₀ hB e₀ u

/-! ## Recipe 3b — the row-14 square/sqrt step `w ^ 2 ≤ R ↔ |w| ≤ √R` for `0 ≤ R`

Squaring route (the one recorded in the BEP notes): forward via
`Real.sqrt_sq_eq_abs` + `Real.sqrt_le_sqrt`, backward via `pow_le_pow_left₀`, `sq_abs` and
`Real.sq_sqrt`. -/

example {w R : ℝ} (hR : 0 ≤ R) : w ^ 2 ≤ R ↔ |w| ≤ Real.sqrt R := by
  constructor
  · intro hh
    calc |w| = Real.sqrt (w ^ 2) := (Real.sqrt_sq_eq_abs w).symm
      _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hh
  · intro hh
    have hsq : |w| ^ 2 ≤ (Real.sqrt R) ^ 2 := pow_le_pow_left₀ (abs_nonneg w) hh 2
    rwa [sq_abs, Real.sq_sqrt hR] at hsq

end ProbeD
end Kasha
end PhotoLean
