/-
PhotoLean.EnergyGapLaw.Sharp — EG3, the tangent layer of the energy-gap law (the Englman–Jortner
reading).

`PhotoLean.EnergyGapLaw.Criterion` proves the exact laws of the model: the log-rate is the exact
quadratic `log k(x) = log A - (lam - x)²/(4·lam·kB·T)` (EG-C1), strictly decreasing in the gap in
the inverted region and strictly increasing in the normal region (EG-C2/C3). This module delivers
the layer the textbook form of the gap law lives on:

* EG-S1 `eglTangent` — the affine gap law at the reference gap `xStar`: the tangent of the exact
  quadratic, with slope `(lam - xStar)/(2·lam·kB·T)`;
* EG-S2a `eglTangent_defect` — **the exact defect**: the tangent sits above the log-rate by
  exactly `(x - xStar)²/(4·lam·kB·T)`;
* EG-S2 `eglTangent_overestimates` — therefore the tangent overestimates the log-rate everywhere
  off the tangent point, with equality **iff** `x = xStar`;
* EG-S3 `not_affine_on_window` — **no affine law is exact on any non-degenerate window**: three
  evaluations (`p`, the midpoint `(p+q)/2`, `q`) of a purported affine law force its second
  difference to vanish, while the exact quadratic law's second difference is
  `-(p - q)²/(2·(4·lam·kB·T))` (`lnRate_second_difference`, the auxiliary row below). This mirrors
  `PhotoLean.BEP.not_epLinearOn_of_ne_zero` — the same second-difference engine, transplanted from
  the barrier to its logarithm (plan §10, shape edge to BEP);
* EG-S4 `eglTangent_slope_strictAnti` — the tangent slope steepens as the reference gap grows: at
  fixed `lam`, `kB·T`, the slope `(lam - xStar)/(2·lam·kB·T)` is strictly antitone in `xStar`. This
  is the formal reading of why each homologous series fits its own line (plan §1.1).

Two notes on premises and on the proofs.

* EG-S4 carries **no** premise `0 < A`: the plan's draft had one, but no `A` occurs in the
  statement, so the premise was unconsumable and was dropped under the weakest-premise standard
  (iron rule 3; plan §3.1 entry 2). The delivered row carries `0 < lam` and `0 < kB * T` only —
  exactly the two premises the positive denominator `2·lam·kB·T` consumes.
* EG-S4's proof clears the **positive** denominator with `div_lt_div_iff₀` rather than dividing an
  inequality by it: the two denominators are equal, so the goal reduces to
  `(lam - x₂)·d < (lam - x₁)·d`, i.e. `-(x₂ - x₁)·d < 0`, which `nlinarith` closes from
  `x₁ < x₂` and `d > 0`.

Every physical premise is explicit on the row that needs it; nothing is hidden in a definition.

Plan locus: `theories/EnergyGapLaw/plan.md` §4 (EG-S rows), §5 (routes), §10 (BEP shape edge);
sprint EG3; board `theories/EnergyGapLaw/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.EnergyGapLaw.Sharp
    proofs/scripts/check.sh --strict PhotoLean.EnergyGapLaw.Sharp
    proofs/scripts/axioms.sh PhotoLean.EnergyGapLaw.Sharp PhotoLean.EnergyGapLaw.<theorem>

Statement authority: every declaration below matches
`theories/EnergyGapLaw/probes/EnergyGapLaw-statement-skeleton.lean` word for word, except the
auxiliary row `lnRate_second_difference` (declared below and consumed by EG-S3), which is not a
declaration of the authority and therefore leaves the fidelity diff at zero. The delivered file
contains no unfinished-proof placeholder and no custom axiomatic declaration; `#print axioms` of
every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`. Note deliberately:
the two keyword literals that `proofs/scripts/check.sh --strict` scans for are not spelled out
anywhere in this file — the scan covers `PhotoLean/**/*.lean` including block comments.
-/
import PhotoLean.EnergyGapLaw.Criterion

set_option autoImplicit false

namespace PhotoLean

namespace EnergyGapLaw

/-! ## EG-S — the tangent layer -/

/-- The affine gap law at the reference gap `xStar`: the tangent of the exact quadratic, with
slope `(lam − xStar) / (2 * lam * (kB * T))`. Plan section 4, row EG-S1. -/
noncomputable def eglTangent (A lam kB T xStar x : ℝ) : ℝ :=
  lnRate A lam kB T xStar + (lam - xStar) / (2 * lam * (kB * T)) * (x - xStar)

/-- The exact defect: the tangent sits above the log-rate by the quadratic
`(x − xStar)² / (4 * lam * (kB * T))`. Plan section 4, row EG-S2 (defect row EG-S2a).
Proof route (plan §5): EG-C1 on both `lnRate`s + `ring`. -/
theorem eglTangent_defect {A lam kB T xStar x : ℝ} (hA : 0 < A) (hlam : lam ≠ 0)
    (hkT : 0 < kB * T) :
    lnRate A lam kB T x
      = eglTangent A lam kB T xStar x - (x - xStar) ^ 2 / (4 * lam * (kB * T)) := by
  have h1 := lnRate_eq hA hlam hkT (x := x)
  have h2 := lnRate_eq hA hlam hkT (x := xStar)
  unfold eglTangent
  rw [h1, h2]
  field_simp
  ring

/-- The tangent overestimates the log-rate everywhere off the tangent point, with equality only
at the reference gap. Plan section 4, row EG-S2. Proof route (plan §5): EG-C1 + the defect
identity EG-S2a (`ring`) + `div_nonneg`/`sq_nonneg`; the equality direction by
`sq_eq_zero_iff`. -/
theorem eglTangent_overestimates {A lam kB T xStar x : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) :
    lnRate A lam kB T x ≤ eglTangent A lam kB T xStar x ∧
      (lnRate A lam kB T x = eglTangent A lam kB T xStar x ↔ x = xStar) := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hdef := eglTangent_defect (A := A) (lam := lam) (kB := kB) (T := T) (xStar := xStar)
    (x := x) hA hne hkT
  have hden : 0 ≤ 4 * lam * (kB * T) := by
    have h4 : (0 : ℝ) ≤ 4 * lam := by linarith
    exact mul_nonneg h4 (le_of_lt hkT)
  have hdenpos : (0 : ℝ) < 4 * lam * (kB * T) := by
    have h4 : (0 : ℝ) < 4 * lam := by linarith
    exact mul_pos h4 hkT
  have hsub : 0 ≤ (x - xStar) ^ 2 / (4 * lam * (kB * T)) := div_nonneg (sq_nonneg _) hden
  constructor
  · linarith
  · constructor
    · intro h
      have hzero : (x - xStar) ^ 2 / (4 * lam * (kB * T)) = 0 := by linarith
      have hnum : (x - xStar) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp hzero with h' | h'
        · exact h'
        · exact absurd h' (ne_of_gt hdenpos)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hnum)
    · intro h
      subst h
      have hzero : (x - x) ^ 2 / (4 * lam * (kB * T)) = 0 := by ring_nf
      linarith

/-! ## AUX — the second-difference engine of EG-S3

Delivered as a separate row because EG-S3 consumes it: the identity is about the exact law
(EG-C1) and mirrors the BEP engine `eact_second_difference`. Not a declaration of the statement
authority. -/

/-- AUX: the second difference of the exact quadratic law at the three points `p`, `(p+q)/2`, `q`
is `-(p - q)²/(2·(4·lam·kB·T))`, independent of `log A`. Plan section 4, row EG-S3 (the
computation its proof route asks for). -/
theorem lnRate_second_difference {A lam kB T p q : ℝ} (hA : 0 < A) (hlam : lam ≠ 0)
    (hkT : 0 < kB * T) :
    lnRate A lam kB T p - 2 * lnRate A lam kB T ((p + q) / 2) + lnRate A lam kB T q
      = -((p - q) ^ 2) / (2 * (4 * lam * (kB * T))) := by
  have h1 := lnRate_eq hA hlam hkT (x := p)
  have h2 := lnRate_eq hA hlam hkT (x := q)
  have h3 := lnRate_eq hA hlam hkT (x := (p + q) / 2)
  rw [h1, h2, h3]
  field_simp
  ring

/-- No affine gap law is exact on any non-degenerate window — the second-difference engine,
mirroring `PhotoLean.BEP.not_epLinearOn_of_ne_zero` (the pattern calibrated there). Plan
section 4, row EG-S3. Proof route (plan §5): three evaluations (`p`, `(p + q) / 2`, `q`) of the
purported affine law force the second difference to vanish, but the exact law's second
difference is `−(p − q)² / (…)` after EG-C1 — contradiction. -/
theorem not_affine_on_window {A lam kB T p q : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) (hpq : p < q) :
    ¬ ∃ c k : ℝ, ∀ x ∈ Set.Icc p q, lnRate A lam kB T x = c + k * x := by
  rintro ⟨c, k, hlin⟩
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hp : p ∈ Set.Icc p q := ⟨le_rfl, le_of_lt hpq⟩
  have hq : q ∈ Set.Icc p q := ⟨le_of_lt hpq, le_rfl⟩
  have hm : (p + q) / 2 ∈ Set.Icc p q := ⟨by linarith, by linarith⟩
  have h1 := hlin p hp
  have h2 := hlin q hq
  have h3 := hlin ((p + q) / 2) hm
  have key0 : lnRate A lam kB T p - 2 * lnRate A lam kB T ((p + q) / 2) + lnRate A lam kB T q
      = 0 := by
    rw [h1, h2, h3]
    ring
  have key5 := lnRate_second_difference (A := A) (lam := lam) (kB := kB) (T := T)
    (p := p) (q := q) hA hne hkT
  have hden : (0 : ℝ) < 2 * (4 * lam * (kB * T)) := by
    have h4 : (0 : ℝ) < 4 * lam * (kB * T) := by
      have h4' : (0 : ℝ) < 4 * lam := by linarith
      exact mul_pos h4' hkT
    linarith
  have hnum : -((p - q) ^ 2) = 0 := by
    rw [key5] at key0
    rcases div_eq_zero_iff.mp key0 with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hden)
  have hsq : (p - q) ^ 2 = 0 := by linarith
  exact absurd hsq (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_lt hpq)))

/-- The tangent slope steepens with the reference gap — the formal reading of why each
homologous series fits its own line. Plan section 4, row EG-S4. (Sprint-0 statement note: the
plan's draft carries `(hA : 0 < A)`, which the statement cannot consume — no `A` occurs in it;
dropped under the weakest-premise standard, iron rule 3; plan §3.1 item.) Proof route (plan §5):
clear the positive denominator `2 * lam * (kB * T)`, then `linarith`. -/
theorem eglTangent_slope_strictAnti {lam kB T x₁ x₂ : ℝ} (hlam : 0 < lam) (hkT : 0 < kB * T)
    (h : x₁ < x₂) :
    (lam - x₂) / (2 * lam * (kB * T)) < (lam - x₁) / (2 * lam * (kB * T)) := by
  have hden : (0 : ℝ) < 2 * lam * (kB * T) := by
    have h2 : (0 : ℝ) < 2 * lam := by linarith
    exact mul_pos h2 hkT
  rw [div_lt_div_iff₀ hden hden]
  nlinarith

end EnergyGapLaw

end PhotoLean
