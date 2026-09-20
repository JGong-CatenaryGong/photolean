/-
theories/BEP/probes/bep-prover_d-scratch.lean

Scratch calibration probe for milestone **B3** (`PhotoLean/BEP/Sharp.lean`, owner `prover_d`).

Every declaration of the B3 block of the statement authority
(`theories/BEP/probes/bep-statement-skeleton.lean`, plan §6.1–§6.5, 25 rows) and of its AUX block
`literal sup-norm form of the minimax block` (7 rows) is stated with the authority's signature and
proved here *before* it is copied into the delivered module, so that no intermediate commit of
`PhotoLean/BEP/Sharp.lean` can carry an unproved placeholder. This file lives outside the
contract's `SOURCE_DIRS` (`PhotoLean`), hence outside the strict scan scope; the delivered module is
the artifact.

Proof routes are the ones already kernel-verified in `bep-risk-probe.lean` (Sprint-0 lead probe),
`theories/BEP/probes/bep-api-abs-sqrt.lean`, `bep-api-algebra.lean` and `bep-api-minimax.lean`.
The B2 identity `bepDefect lam x = x^2/(4*lam)` is re-derived locally (`have`, `field_simp; ring`)
instead of being imported from `PhotoLean/BEP/Criterion.lean`, because B3 imports `Basic.lean` only
(one owner per file; `Criterion.lean` is `prover_a`'s deliverable and is edited concurrently).

Running: proofs/scripts/lake env lean theories/BEP/probes/bep-prover_d-scratch.lean
-/
import PhotoLean.BEP.Basic

namespace PhotoLean.BEP.ProverDScratch

/-! ## Plan §6.1 — the sharp iff statements (rows 1–6, 8, 7, 9) -/

/-- Plan §6.1 #1. -/
theorem epBounds_iff_region {lam x : ℝ} (hlam : 0 < lam) :
    EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) ≤ (lam - x) / (2 * lam) ↔ 0 ≤ lam - x := by
    rw [le_div_iff₀ h2, zero_mul]
  have hhigh : (lam - x) / (2 * lam) ≤ 1 ↔ lam - x ≤ 2 * lam := div_le_one h2
  unfold EPBounds
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #2. -/
theorem epRegime_iff_strict {lam x : ℝ} (hlam : 0 < lam) :
    EPRegime lam x ↔ 0 < transfer lam x ∧ transfer lam x < 1 := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hts : transfer lam x = (lam - x) / (2 * lam) := by
    unfold transfer
    field_simp
  have hlow : (0 : ℝ) < (lam - x) / (2 * lam) ↔ 0 < lam - x :=
    div_pos_iff_of_pos_right h2
  have hhigh : (lam - x) / (2 * lam) < 1 ↔ lam - x < 2 * lam := div_lt_one h2
  unfold EPRegime
  rw [hts, hlow, hhigh]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Plan §6.1 #3. -/
theorem transfer_at_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam lam = 0 := by
  unfold transfer
  field_simp

/-- Plan §6.1 #4. -/
theorem transfer_at_neg_lam {lam : ℝ} (hlam : 0 < lam) : transfer lam (-lam) = 1 := by
  unfold transfer
  field_simp
  ring

/-- Plan §6.1 #5: α > 1 — the reverse direction is in the inverted region. -/
theorem not_epBounds_of_lt_neg {lam x : ℝ} (hlam : 0 < lam) (hx : x < -lam) :
    ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-- Plan §6.1 #6: α < 0 — the forward direction is in the inverted region. -/
theorem not_epBounds_of_gt {lam x : ℝ} (hlam : 0 < lam) (hx : lam < x) : ¬ EPBounds lam x := by
  intro h
  have := (epBounds_iff_region hlam).mp h
  linarith

/-! ## AUX — second-difference engine (delivered early: rows §6.1 #8/#7 consume it, and Lean has no
forward references) -/

/-- AUX: the general second-difference identity behind `not_epLinearOn_of_ne_zero` and the
minimax lower bound. -/
theorem eact_second_difference {lam c a x₁ x₂ : ℝ} (hlam : lam ≠ 0) :
    (eact lam x₁ - (c + a * x₁)) + (eact lam x₂ - (c + a * x₂)) -
        2 * (eact lam ((x₁ + x₂) / 2) - (c + a * ((x₁ + x₂) / 2))) =
      (x₁ - x₂) ^ 2 / (8 * lam) := by
  unfold eact
  field_simp
  ring

/-- Plan §6.1 #8. -/
theorem not_epLinearOn_of_ne_zero {lam a b : ℝ} (hlam : lam ≠ 0) (hab : a < b) :
    ¬ EPLinearOn lam (Set.Icc a b) := by
  rintro ⟨c, k, hlin⟩
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, le_of_lt hab⟩
  have hb : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_rfl⟩
  have hm : (a + b) / 2 ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have key := eact_second_difference (c := c) (a := k) (x₁ := a) (x₂ := b) hlam
  rw [hlin a ha, hlin b hb, hlin ((a + b) / 2) hm] at key
  have hne : (a - b) ^ 2 / (8 * lam) ≠ 0 := by
    refine div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_lt hab))) ?_
    exact mul_ne_zero (by norm_num) hlam
  have hzero : (a - b) ^ 2 / (8 * lam) = 0 := by
    rw [← key]
    ring
  exact hne hzero

/-- Plan §6.1 #7. -/
theorem epExact_iff_degenerate (lam : ℝ) : EPExact lam ↔ lam = 0 := by
  constructor
  · intro h
    by_contra hlam
    have h' : EPLinearOn lam (Set.Icc 0 1) :=
      ⟨h.choose, h.choose_spec.choose, fun x _ => h.choose_spec.choose_spec x trivial⟩
    exact not_epLinearOn_of_ne_zero hlam (by norm_num) h'
  · intro h
    subst h
    refine ⟨0, 0, fun x _ => ?_⟩
    unfold eact
    norm_num

/-- Plan §6.1 #9. -/
theorem exists_conforms_fails : ∃ lam tol w : ℝ, 0 < lam ∧ 0 < tol ∧
    ¬ EPConformsOnWindow lam tol (-w) w := by
  refine ⟨2, 1 / 16, 1, by norm_num, by norm_num, ?_⟩
  intro h
  have hx : (1 : ℝ) ∈ Set.Icc (-(1 : ℝ)) 1 := by norm_num
  have h1 : |bepDefect 2 1| ≤ 1 / 16 := h.2.2 1 hx
  have hval : bepDefect 2 1 = 1 / 8 := by
    unfold bepDefect bepLine eact
    norm_num
  rw [hval, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h1
  norm_num at h1

/-! ## Plan §6.2 — the tolerance/radius theorem (rows 10–14) -/

/-- Plan §6.2 #10. -/
theorem bepDefect_abs_eq {lam x : ℝ} (hlam : lam ≠ 0) :
    |bepDefect lam x| = x ^ 2 / (4 * |lam|) := by
  have hdef : bepDefect lam x = x ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  rw [hdef, abs_div, abs_of_nonneg (sq_nonneg x), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]

/-- Plan §6.2 #11: **the tolerance/radius theorem** (sharp validity condition). -/
theorem epConformsOnWindow_iff_radius {lam tol w : ℝ} (hlam : 0 < lam) (htol : 0 < tol)
    (hw : 0 ≤ w) : EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol := by
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  have hdef : ∀ y : ℝ, |bepDefect lam y| = y ^ 2 / (4 * lam) := by
    intro y
    have h : bepDefect lam y = y ^ 2 / (4 * lam) := by
      unfold bepDefect bepLine eact
      field_simp
      ring
    rw [h, abs_of_nonneg (div_nonneg (sq_nonneg y) (le_of_lt h4))]
  have h4nonneg : 0 ≤ 4 * (lam * tol) := by positivity
  have hsqrt4 : Real.sqrt (4 * (lam * tol)) = 2 * Real.sqrt (lam * tol) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have key : w ^ 2 / (4 * lam) ≤ tol ↔ w ≤ bepRadius lam tol := by
    rw [bepRadius, ← hsqrt4, div_le_iff₀ h4, Real.le_sqrt hw h4nonneg]
    ring_nf
  unfold EPConformsOnWindow
  constructor
  · rintro ⟨-, -, h⟩
    have hwmem : w ∈ Set.Icc (-w) w := Set.right_mem_Icc.mpr (by linarith)
    have h1 : w ^ 2 / (4 * lam) ≤ tol := by
      simpa [hdef w] using h w hwmem
    exact key.mp h1
  · intro h
    refine ⟨hlam, htol, fun x hx => ?_⟩
    have hxabs : |x| ≤ w := abs_le.mpr hx
    have hxsq : x ^ 2 ≤ w ^ 2 := by
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
    have h2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
      div_le_div_of_nonneg_right hxsq (le_of_lt h4)
    rw [hdef x]
    exact le_trans h2 (key.mpr h)

/-- Plan §6.2 #12: the radius is attained, not an estimate. -/
theorem epConformsOnWindow_at_radius {lam tol : ℝ} (hlam : 0 < lam) (htol : 0 < tol) :
    EPConformsOnWindow lam tol (-(bepRadius lam tol)) (bepRadius lam tol) :=
  (epConformsOnWindow_iff_radius hlam htol (by unfold bepRadius; positivity)).mpr le_rfl

/-- Plan §6.2 #13: shrinking the window preserves conformance. -/
theorem epConformsOnWindow_mono {lam tol a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    EPConformsOnWindow lam tol a b → EPConformsOnWindow lam tol a' b' := by
  rintro ⟨h1, h2, h⟩
  exact ⟨h1, h2, fun x hx => h x ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩

/-- Plan §6.2 #14. -/
theorem epConformsOnWindow_symm {lam tol a b : ℝ} :
    EPConformsOnWindow lam tol a b ↔ EPConformsOnWindow lam tol (-b) (-a) := by
  unfold EPConformsOnWindow
  constructor
  · rintro ⟨h1, h2, h⟩
    have heven : ∀ x : ℝ, bepDefect lam (-x) = bepDefect lam x := by
      intro x
      unfold bepDefect bepLine eact
      field_simp
      ring
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [heven x] using h (-x) hmem
  · rintro ⟨h1, h2, h⟩
    have heven : ∀ x : ℝ, bepDefect lam (-x) = bepDefect lam x := by
      intro x
      unfold bepDefect bepLine eact
      field_simp
      ring
    refine ⟨h1, h2, fun x hx => ?_⟩
    have hmem : -x ∈ Set.Icc (-b) (-a) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa [heven x] using h (-x) hmem

/-! ## Plan §6.3 — monotonicity in the reorganization energy (rows 15–17) -/

set_option linter.unusedVariables false in
/-- Plan §6.3 #15. -/
theorem bepDefect_antitone_lam {lam₁ lam₂ x : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (hx : x ≠ 0) : bepDefect lam₂ x ≤ bepDefect lam₁ x := by
  have h₂ : 0 < lam₂ := lt_of_lt_of_le h0 hle
  have e₁ : bepDefect lam₁ x = x ^ 2 / (4 * lam₁) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  have e₂ : bepDefect lam₂ x = x ^ 2 / (4 * lam₂) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  rw [e₂, e₁, div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * lam₂)
    (by linarith : (0 : ℝ) < 4 * lam₁)]
  exact mul_le_mul_of_nonneg_left (by linarith : 4 * lam₁ ≤ 4 * lam₂) (sq_nonneg x)

set_option linter.unusedVariables false in
/-- Plan §6.3 #16. -/
theorem bepRadius_mono {lam₁ lam₂ tol : ℝ} (h0 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) (htol : 0 ≤ tol) :
    bepRadius lam₁ tol ≤ bepRadius lam₂ tol := by
  unfold bepRadius
  have hprod : lam₁ * tol ≤ lam₂ * tol := mul_le_mul_of_nonneg_right hle htol
  linarith [Real.sqrt_le_sqrt hprod]

/-- Plan §6.3 #17. -/
theorem epConformsOnWindow_mono_lam {lam₁ lam₂ tol a b : ℝ} (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂) :
    EPConformsOnWindow lam₁ tol a b → EPConformsOnWindow lam₂ tol a b := by
  intro h
  have h₂ : 0 < lam₂ := lt_of_lt_of_le h0 hle
  have h4₂ : (0 : ℝ) < 4 * lam₂ := by linarith
  have e₁ : ∀ y : ℝ, bepDefect lam₁ y = y ^ 2 / (4 * lam₁) := by
    intro y
    unfold bepDefect bepLine eact
    field_simp
    ring
  have e₂ : ∀ y : ℝ, bepDefect lam₂ y = y ^ 2 / (4 * lam₂) := by
    intro y
    unfold bepDefect bepLine eact
    field_simp
    ring
  refine ⟨h₂, h.2.1, fun x hx => ?_⟩
  have hb : |bepDefect lam₁ x| ≤ tol := h.2.2 x hx
  rcases eq_or_ne x 0 with hx0 | hxne
  · subst hx0
    rw [e₂ 0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, abs_zero]
    exact le_of_lt h.2.1
  · have hmono : x ^ 2 / (4 * lam₂) ≤ x ^ 2 / (4 * lam₁) := by
      have h' : bepDefect lam₂ x ≤ bepDefect lam₁ x := bepDefect_antitone_lam h0 hle hxne
      rwa [e₂ x, e₁ x] at h'
    rw [e₂ x, abs_of_nonneg (div_nonneg (sq_nonneg x) (le_of_lt h4₂))]
    rw [e₁ x, abs_of_nonneg (div_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 4 * lam₁))] at hb
    linarith

/-! ## AUX — the symmetric three-point identity (delivered before §6.4 #19, its consumer) -/

/-- AUX: the symmetric three-point identity quoted by plan §6.4 #19, with
`f y = eact lam y - (c + a * y)`. -/
theorem bep_error_three_point {lam c a w : ℝ} (hlam : lam ≠ 0) :
    (eact lam (-w) - (c + a * (-w))) + (eact lam w - (c + a * w)) -
        2 * (eact lam 0 - (c + a * 0)) = w ^ 2 / (2 * lam) := by
  unfold eact
  field_simp
  ring

/-! ## Plan §6.4 — the best BEP line (rows 18–21) -/

set_option linter.unusedVariables false in
/-- Plan §6.4 #18: the error bound of the minimax line. -/
theorem bepBestLine_error {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∀ x ∈ Set.Icc (-w) w, |eact lam x - bepBestLine lam w x| ≤ w ^ 2 / (8 * lam) := by
  intro x hx
  have hxabs : |x| ≤ w := abs_le.mpr hx
  have hxsq : x ^ 2 ≤ w ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hkey : eact lam x - bepBestLine lam w x = (x ^ 2 - w ^ 2 / 2) / (4 * lam) := by
    unfold eact bepBestLine
    field_simp
    ring
  have h4 : (0 : ℝ) < 4 * lam := by linarith
  rw [hkey, abs_div, abs_of_pos h4, div_le_iff₀ h4]
  have hmid : |x ^ 2 - w ^ 2 / 2| ≤ w ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> linarith [sq_nonneg x, hxsq]
  calc |x ^ 2 - w ^ 2 / 2| ≤ w ^ 2 / 2 := hmid
    _ = w ^ 2 / (8 * lam) * (4 * lam) := by
        field_simp
        ring

/-- Plan §6.4 #19: **the minimax optimality statement** (three-point equioscillation). -/
theorem epBestOnWindow_holds {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    EPBestOnWindow lam w := by
  refine ⟨hlam, hw, fun c a => ?_⟩
  by_contra h
  push_neg at h
  have hm : (-w) ∈ Set.Icc (-w) w := ⟨le_rfl, by linarith⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (-w) w := ⟨by linarith, le_of_lt hw⟩
  have hp : w ∈ Set.Icc (-w) w := ⟨by linarith, le_rfl⟩
  have key := bep_error_three_point (c := c) (a := a) (w := w) (ne_of_gt hlam)
  have h1 := (abs_lt.mp (h (-w) hm)).1
  have h2 := (abs_lt.mp (h (-w) hm)).2
  have h3 := (abs_lt.mp (h w hp)).1
  have h4 := (abs_lt.mp (h w hp)).2
  have h5 := (abs_lt.mp (h 0 h0)).1
  have h6 := (abs_lt.mp (h 0 h0)).2
  have hsum : w ^ 2 / (2 * lam) = 4 * (w ^ 2 / (8 * lam)) := by
    field_simp
    ring
  linarith

/-- Plan §6.4 #20: the tangent line's worst case on the window. -/
theorem bepLine_worst_case {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    ∃ x ∈ Set.Icc (-w) w, |bepDefect lam x| = w ^ 2 / (4 * lam) := by
  have hdef : bepDefect lam w = w ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  exact ⟨w, ⟨by linarith, le_rfl⟩, by rw [hdef, abs_of_nonneg (by positivity)]⟩

/-- Plan §6.4 #21: the best line halves the tangent line's worst case. -/
theorem bepBestLine_halves {lam w : ℝ} (hlam : 0 < lam) (hw : 0 < w) :
    w ^ 2 / (8 * lam) = (w ^ 2 / (4 * lam)) / 2 ∧ w ^ 2 / (8 * lam) < w ^ 2 / (4 * lam) := by
  constructor
  · field_simp
    ring
  · have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero (ne_of_gt hw)
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * lam) (by linarith : (0 : ℝ) < 4 * lam)]
    nlinarith

/-! ## Plan §6.5 — hypothesis necessity (rows 22–25) -/

/-- Plan §6.5 #22. -/
theorem bepDefect_zero_lam_witness : bepDefect 0 1 = 1 / 2 ∧ ((1 : ℝ) ^ 2 / (4 * 0)) = 0 := by
  constructor
  · unfold bepDefect bepLine eact
    norm_num
  · norm_num

/-- Plan §6.5 #23. -/
theorem bepDefect_neg_lam_witness : bepDefect (-1) 1 = -(1 / 4) := by
  unfold bepDefect bepLine eact
  norm_num

/-- Plan §6.5 #24. -/
theorem bepDefect_sign_flips {lam x : ℝ} (hlam : lam < 0) (hx : x ≠ 0) : bepDefect lam x < 0 := by
  have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) (ne_of_lt hlam)
  have hdef : bepDefect lam x = x ^ 2 / (4 * lam) := by
    unfold bepDefect bepLine eact
    field_simp
    ring
  rw [hdef]
  exact div_neg_of_pos_of_neg (sq_pos_iff.mpr hx) (by linarith)

/-- Plan §6.5 #25. -/
theorem secSlope_needs_h_ne_zero : secSlope 1 0 0 = 0 ∧ transfer 1 0 ≠ 0 := by
  refine ⟨secSlope_zero_h 1 0, ?_⟩
  unfold transfer
  norm_num

/-! ## AUX — literal sup-norm form of the minimax block -/

/-- Uniform (sup-norm) error of the affine model `c + a * x` on the window `[-w, w]`. -/
noncomputable def epSupError (lam w c a : ℝ) : ℝ :=
  sSup ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w)

/-- AUX: an upper bound plus an attained value pin down a supremum (the `sSup` recipe). -/
theorem sSup_eq_of_le_of_mem {s : Set ℝ} {b : ℝ} (hne : s.Nonempty) (hbdd : BddAbove s)
    (hle : ∀ a ∈ s, a ≤ b) (hmem : b ∈ s) : sSup s = b :=
  le_antisymm (csSup_le hne hle) (le_csSup hbdd hmem)

set_option linter.unusedVariables false in
/-- AUX: the error set of the sup-norm is bounded above (side condition of `le_csSup`). -/
theorem epSupError_bddAbove {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    BddAbove ((fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w) := by
  refine ⟨lam / 4 + w / 2 + w ^ 2 / (4 * lam) + (|c| + |a| * w), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxabs : |x| ≤ w := abs_le.mpr hx
  have hxsq : x ^ 2 ≤ w ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ w ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have he : eact lam x = lam / 4 - x / 2 + x ^ 2 / (4 * lam) := by
    unfold eact
    field_simp
    ring
  have hx2 : x ^ 2 / (4 * lam) ≤ w ^ 2 / (4 * lam) :=
    div_le_div_of_nonneg_right hxsq (by linarith : (0 : ℝ) ≤ 4 * lam)
  have hx2' : (0 : ℝ) ≤ x ^ 2 / (4 * lam) := by positivity
  have hlin : |c + a * x| ≤ |c| + |a| * w := by
    have hax : |a * x| ≤ |a| * w := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hxabs (abs_nonneg a)
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self c, neg_le_abs c, le_abs_self (a * x), neg_le_abs (a * x)]
  have hlin' := abs_le.mp hlin
  have hxlow : -w ≤ x := hx.1
  have hxhigh : x ≤ w := hx.2
  rw [abs_le]
  constructor <;> rw [he] <;> linarith

/-- AUX: the sup-norm error of `bepBestLine` is exactly `w^2/(8*lam)`. -/
theorem epSupError_bestLine {lam w : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    epSupError lam w (lam / 4 + w ^ 2 / (8 * lam)) (-(1 / 2)) = w ^ 2 / (8 * lam) := by
  have herr : (0 : ℝ) ≤ w ^ 2 / (8 * lam) := by positivity
  have hg : ∀ x ∈ Set.Icc (-w) w,
      |eact lam x - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * x)| ≤ w ^ 2 / (8 * lam) := by
    intro x hx
    have h := bepBestLine_error hlam hw x hx
    convert h using 2
    unfold bepBestLine
    ring
  have hval : |eact lam 0 - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * 0)| = w ^ 2 / (8 * lam) := by
    have h0 : eact lam 0 - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * 0) = -(w ^ 2 / (8 * lam)) := by
      unfold eact
      field_simp
      ring
    rw [h0, abs_neg, abs_of_nonneg herr]
  have hmem1 : w ^ 2 / (8 * lam)
      ∈ (fun x => |eact lam x - (lam / 4 + w ^ 2 / (8 * lam) + -(1 / 2) * x)|) '' Set.Icc (-w) w :=
    ⟨0, ⟨by linarith, hw⟩, hval⟩
  unfold epSupError
  refine sSup_eq_of_le_of_mem ⟨_, hmem1⟩ (epSupError_bddAbove hlam hw) ?_ hmem1
  rintro y ⟨x, hx, rfl⟩
  exact hg x hx

/-- AUX: every affine model has sup-norm error at least `w^2/(8*lam)` (the `sSup` form of
`epBestOnWindow_holds`). -/
theorem epSupError_sharp {lam w c a : ℝ} (hlam : 0 < lam) (hw : 0 ≤ w) :
    w ^ 2 / (8 * lam) ≤ epSupError lam w c a := by
  rcases eq_or_lt_of_le hw with hw0 | hwpos
  · subst hw0
    have hmem : |eact lam 0 - (c + a * 0)| ∈
        (fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-0) 0 :=
      ⟨0, ⟨by norm_num, le_rfl⟩, rfl⟩
    have hle := le_csSup (epSupError_bddAbove hlam hw) hmem
    have hzero : (0 : ℝ) ^ 2 / (8 * lam) = 0 := by norm_num
    rw [hzero]
    unfold epSupError
    linarith [abs_nonneg (eact lam 0 - (c + a * 0))]
  · obtain ⟨x, hx, hxerr⟩ := (epBestOnWindow_holds hlam hwpos).2.2 c a
    have hmem : |eact lam x - (c + a * x)| ∈
        (fun x => |eact lam x - (c + a * x)|) '' Set.Icc (-w) w := ⟨x, hx, rfl⟩
    have hle := le_csSup (epSupError_bddAbove hlam hw) hmem
    unfold epSupError
    linarith

end PhotoLean.BEP.ProverDScratch
