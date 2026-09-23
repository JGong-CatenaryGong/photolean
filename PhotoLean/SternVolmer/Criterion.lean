/-
PhotoLean.SternVolmer.Criterion — milestone SV2, the law layer and the **D1 core**.

The adjudication (plan `theories/SternVolmer/plan.md`, §1.1, §4): Stern–Volmer practice treats a
linear `I₀/I` plot as evidence of dynamic quenching, but linearity alone cannot carry that
inference. Three delivered facts pin the boundary exactly.

* **D1a — the conflation (SV-C7).** With matched parameters (`Ka = KSV k0 kq`) the dynamic and the
  static mechanism give pointwise-identical intensity ratios at *every* concentration, so the
  intensity-only observation map is not injective on the two-mechanism model space. The named
  witness pair of SV-I3 (`conflation_witness`) exhibits it at `(k0, kq, Ka) = (2, 2, 1)`.
* **D1b — the boundary (SV-C8).** Within that model space the discriminating channel is the
  lifetime ratio: `LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn`, with `0 < Ka` load-bearing (at
  `Ka = 0` the static plot is flat and tracking holds there too) and *no* hypothesis on `kq` — at
  `kq = 0` the dynamic plot is flat and tracking still holds (weakest-premise standard, plan §4).
* **D1c — coexistence (SV-C9).** The combined mechanism curves upward: its second difference is
  the constant `2·KSV·Ka·h² > 0`, while each single mechanism has vanishing second difference, so
  curvature is a positive witness of coexistence.

`d1_verdict` (SV-C10) is the single row carrying all three conjuncts — the row a verdict cites.

Measured proof boundaries (API round, `theories/SternVolmer/probes/SternVolmer-api-probe.lean`,
`proofs/API-NOTES.md` §photobatch): the linearity shape `(k0 + kq·q)/k0 = 1 + (kq/k0)·q` is closed
by `field_simp` alone at `k0 ≠ 0` (a following `ring` errors "no goals to be solved"), while the
two-factor (combined-mechanism) rows need `field_simp` *then* `ring`; the monotonicity rows go
through `mul_lt_mul_of_pos_left` + `add_lt_add_left` + `div_lt_div_iff_of_pos_right`; the curvature
positivity is `mul_pos`-chained from `div_pos` and `sq_pos_of_ne_zero`.

Statement authority: `theories/SternVolmer/probes/SternVolmer-statement-skeleton.lean` § SV-C;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. Acceptance:
`proofs/scripts/lake build PhotoLean.SternVolmer.Criterion` (exit 0);
`proofs/scripts/check.sh --strict`;
`proofs/scripts/axioms.sh PhotoLean.SternVolmer.Criterion PhotoLean.SternVolmer.d1_verdict`.
-/
import PhotoLean.SternVolmer.Basic

set_option autoImplicit false

namespace PhotoLean

namespace SternVolmer

/-! ## SV-C — laws and the D1 core -/

/-- The dynamic mechanism's identity: the lifetime ratio IS the intensity ratio at every
concentration — definitional (the two bodies are identical); the content is the contrast SV-C2.
Plan section 4, row SV-C1. Proof route: `rfl` (definitional unfolding row). -/
theorem dyn_lifetime_tracks_intensity (k0 kq : ℝ) :
    ∀ q, tauRatioDyn k0 kq q = svRatioDyn k0 kq q := by
  intro q
  rfl

/-- The static lifetime channel is flat at every concentration. Plan section 4, row SV-C2.
Proof route: `rfl` (definitional unfolding row). -/
theorem stat_lifetime_flat (Ka : ℝ) : ∀ q, tauRatioStat Ka q = 1 := by
  intro q
  rfl

/-- The static lifetime channel separates from the intensity channel at every positive
concentration — the discriminator's static side. Plan section 4, row SV-C2.
Proof route: `tauRatioStat` unfolds to `1`; `1 ≠ 1 + Ka·q` from `0 < Ka·q` (`mul_pos`). -/
theorem stat_lifetime_separates (Ka q : ℝ) (hKa : 0 < Ka) (hq : 0 < q) :
    tauRatioStat Ka q ≠ svRatioStat Ka q := by
  unfold tauRatioStat svRatioStat
  have hpos : 0 < Ka * q := mul_pos hKa hq
  linarith

/-- The dynamic plot is exactly linear with slope `KSV` and intercept `1`.
Plan section 4, row SV-C3. Proof route: unfold, `field_simp` at `hk0`, `ring` (plan §5). -/
theorem svRatioDyn_linear (k0 kq q : ℝ) (hk0 : k0 ≠ 0) :
    svRatioDyn k0 kq q = 1 + KSV k0 kq * q := by
  unfold svRatioDyn dynDecay KSV
  field_simp

/-- The static plot is exactly linear with slope `Ka` and intercept `1` — definitional;
registered so that "both linear" is a theorem pair, not a slogan. Plan section 4, row SV-C4.
Proof route: `rfl` (definitional unfolding row). -/
theorem svRatioStat_linear (Ka q : ℝ) : svRatioStat Ka q = 1 + Ka * q := by
  rfl

/-- The dynamic ratio at zero quencher is `1` (intercept calibration).
Plan section 4, row SV-C5. Proof route: unfold, `field_simp` at `hk0`. -/
theorem svRatioDyn_at_zero (k0 kq : ℝ) (hk0 : k0 ≠ 0) : svRatioDyn k0 kq 0 = 1 := by
  unfold svRatioDyn dynDecay
  field_simp

/-- The static ratio at zero quencher is `1` (intercept calibration).
Plan section 4, row SV-C5. Proof route: `ring` after unfolding. -/
theorem svRatioStat_at_zero (Ka : ℝ) : svRatioStat Ka 0 = 1 := by
  unfold svRatioStat
  ring

/-- The dynamic plot is strictly increasing in the quencher concentration.
Plan section 4, row SV-C6. Proof route: `mul_lt_mul_of_pos_left` + `add_lt_add_left` on the
linear form, the division by the positive `k0` via `div_lt_div_iff₀`-free `lt` algebra
(plan §5 monotonicity rows). -/
theorem svRatioDyn_strictMono_q (k0 kq q₁ q₂ : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq)
    (h : q₁ < q₂) : svRatioDyn k0 kq q₁ < svRatioDyn k0 kq q₂ := by
  unfold svRatioDyn dynDecay
  have h1 : k0 + kq * q₁ < k0 + kq * q₂ :=
    add_lt_add_left (mul_lt_mul_of_pos_left h hkq) k0
  exact (div_lt_div_iff_of_pos_right hk0).mpr h1

/-- The static plot is strictly increasing in the quencher concentration.
Plan section 4, row SV-C6. Proof route: `mul_lt_mul_of_pos_left h hKa` then
`add_lt_add_left` (plan §5). -/
theorem svRatioStat_strictMono_q (Ka q₁ q₂ : ℝ) (hKa : 0 < Ka) (h : q₁ < q₂) :
    svRatioStat Ka q₁ < svRatioStat Ka q₂ := by
  unfold svRatioStat
  exact add_lt_add_left (mul_lt_mul_of_pos_left h hKa) 1

/-- **D1a, the conflation.** Matched parameters (`KSV k0 kq = Ka`) give pointwise-identical
intensity plots at **every** concentration: the intensity-only observation map is not injective
on the mechanism space. Plan section 4, row SV-C7.
Proof route: `svRatioDyn_linear` then rewrite along `hK` (plan §5: field algebra). -/
theorem intensity_curve_coincidence {k0 kq Ka : ℝ} (hk0 : k0 ≠ 0) (hK : KSV k0 kq = Ka) :
    ∀ q, svRatioDyn k0 kq q = svRatioStat Ka q := by
  intro q
  rw [svRatioDyn_linear k0 kq q hk0, hK]
  exact (svRatioStat_linear Ka q).symm

/-- **D1b, the boundary.** Within the two-mechanism model space, lifetime-tracking decides the
mechanism exactly. Weakest-premise note (plan §4): no hypothesis on `kq` — at `kq = 0` the
dynamic plot is flat and tracking still holds; `0 < Ka` is load-bearing — at `Ka = 0` the
static plot is flat and tracking holds there too. Plan section 4, row SV-C8.
Proof route: cases on `m`; `LifetimeTracks Mech.dyn` holds by SV-C1; `¬ LifetimeTracks Mech.stat`
instantiates the universal at `q = 1` and refutes by `stat_lifetime_separates` (plan §5). -/
theorem lifetimeTracks_iff_dyn {k0 kq Ka : ℝ} (hk0 : 0 < k0) (hKa : 0 < Ka) :
    ∀ m : Mech, (LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn) := by
  intro m
  cases m with
  | dyn =>
      constructor
      · intro _
        rfl
      · intro _ q _
        rfl
  | stat =>
      constructor
      · intro h
        exact absurd (h 1 zero_lt_one) (stat_lifetime_separates Ka 1 hKa zero_lt_one)
      · intro h
        exact absurd h (by intro hh; cases hh)

/-- The combined-mechanism plot in closed form: linear terms plus the `KSV·Ka·q²` cross term —
the algebraic source of upward curvature. Plan section 4, row SV-C9.
Proof route: unfold, `field_simp` at `hk0`, `ring` (plan §5). -/
theorem svRatioBoth_eq (k0 kq Ka q : ℝ) (hk0 : k0 ≠ 0) :
    svRatioBoth k0 kq Ka q = 1 + (KSV k0 kq + Ka) * q + KSV k0 kq * Ka * q ^ 2 := by
  unfold svRatioBoth svRatioDyn svRatioStat dynDecay KSV
  field_simp
  ring

/-- The second difference of the combined plot is the constant `2·KSV·Ka·h²`.
Plan section 4, row SV-C9. Proof route: `svRatioBoth_eq` three times, then `ring`. -/
theorem svRatioBoth_secondDifference (k0 kq Ka : ℝ) (hk0 : k0 ≠ 0) (x h : ℝ) :
    svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x + svRatioBoth k0 kq Ka (x - h)
      = 2 * KSV k0 kq * Ka * h ^ 2 := by
  rw [svRatioBoth_eq k0 kq Ka (x + h) hk0, svRatioBoth_eq k0 kq Ka x hk0,
    svRatioBoth_eq k0 kq Ka (x - h) hk0]
  ring

/-- The second difference of the dynamic plot vanishes — no single mechanism curves.
Plan section 4, row SV-C9. Proof route: `svRatioDyn_linear` three times, then `ring`. -/
theorem svRatioDyn_secondDifference (k0 kq : ℝ) (hk0 : k0 ≠ 0) (x h : ℝ) :
    svRatioDyn k0 kq (x + h) - 2 * svRatioDyn k0 kq x + svRatioDyn k0 kq (x - h) = 0 := by
  rw [svRatioDyn_linear k0 kq (x + h) hk0, svRatioDyn_linear k0 kq x hk0,
    svRatioDyn_linear k0 kq (x - h) hk0]
  ring

/-- The second difference of the static plot vanishes — no single mechanism curves.
Plan section 4, row SV-C9. Proof route: `svRatioStat_linear` three times, then `ring`. -/
theorem svRatioStat_secondDifference (Ka x h : ℝ) :
    svRatioStat Ka (x + h) - 2 * svRatioStat Ka x + svRatioStat Ka (x - h) = 0 := by
  rw [svRatioStat_linear Ka (x + h), svRatioStat_linear Ka x, svRatioStat_linear Ka (x - h)]
  ring

/-- **D1c, coexistence is positively witnessed.** Upward curvature (a strictly positive second
difference) occurs under the combined mechanism whenever all three constants are positive and
the step is nonzero — and by the two vanishing rows above, no single mechanism produces it.
Plan section 4, row SV-C9. Proof route: `svRatioBoth_secondDifference` + positivity of
`2·KSV·Ka·h²` (`div_pos`, `mul_pos`, `sq_pos_of_ne_zero`). -/
theorem curvature_witnesses_coexistence (k0 kq Ka x h : ℝ) (hk0 : 0 < k0) (hkq : 0 < kq)
    (hKa : 0 < Ka) (hh : h ≠ 0) :
    0 < svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x +
      svRatioBoth k0 kq Ka (x - h) := by
  rw [svRatioBoth_secondDifference k0 kq Ka (ne_of_gt hk0) x h]
  exact mul_pos (mul_pos (mul_pos two_pos (div_pos hkq hk0)) hKa) (sq_pos_of_ne_zero hh)

/-- **D1 verdict** — one row with the three conjuncts: both plots linear (SV-C3/C4 at the
parameters, paired pointwise under one universal), the coincidence (SV-C7 at `Ka = KSV k0 kq`,
instantiated by `refl`/the hypothesis chain), and the boundary (SV-C8).
Plan section 4, row SV-C10. The persistence explanation is prose in RESULTS (Phase 3): routine
practice measures intensity only; lifetime resolution is a separate experiment. -/
theorem d1_verdict {k0 kq Ka : ℝ} (hk0 : 0 < k0) (hkq : 0 < kq) (hKa : 0 < Ka) :
    (∀ q, svRatioDyn k0 kq q = 1 + KSV k0 kq * q ∧ svRatioStat Ka q = 1 + Ka * q) ∧
      (∀ q, svRatioDyn k0 kq q = svRatioStat (KSV k0 kq) q) ∧
        ∀ m : Mech, (LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact ⟨svRatioDyn_linear k0 kq q (ne_of_gt hk0), svRatioStat_linear Ka q⟩
  · intro q
    exact intensity_curve_coincidence (k0 := k0) (kq := kq) (Ka := KSV k0 kq)
      (ne_of_gt hk0) rfl q
  · exact lifetimeTracks_iff_dyn hk0 hKa

end SternVolmer

end PhotoLean
