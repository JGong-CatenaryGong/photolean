/-
PhotoLean.StokesShift.Criterion — milestone SS-C, the law layer.

The laws of the Stokes shift rule inside the two-parabola model of milestone SS-B, plus the
boundary identification with `PhotoLean.Marcus.InvertedRegion` (the nonradiative twin of the
same two surfaces). All rows are pure polynomial algebra over `ℝ` — the lightest layer of the
photophysics batch, and the reason no division, no limit and no premise appears here.

The three headlines:
* `stokesShift_eq_two_lam` — the Stokes shift is exactly `2 * lam`, **independent of the 0-0
  energy** `e00`; that independence is the whole content of the rule;
* `mirror_midpoint` / `abs_sub_e00_eq_e00_sub_em` — absorption and emission are mirror-symmetric
  about `e00`: their mean is `e00` and the two Franck–Condon offsets from it are equal;
* `emEnergy_pos_iff_inverted` — a positive vertical emission photon exists exactly in the
  Marcus-inverted regime of the nonradiative twin (`InvertedRegion lam e00`, i.e. `lam < e00`).

Statement-correction note (plan §3.1, entry 1, Sprint-0 calibration). The plan's first form of
the last row was `e00 < lam ↔ PhotoLean.Marcus.InvertedRegion lam e00`, which unfolds to
`e00 < lam ↔ lam < e00` and is **false** — kernel-checked counterexample `lam = 1, e00 = 2` in
`theories/StokesShift/probes/StokesShift-api-probe.lean`. The delivered row is the corrected one
carried by the statement authority: the *open* emission window (`0 < emEnergy`, i.e. `lam < e00`)
is the inverted region read at the gap. The statement was corrected at Phase 1, before any proof
work; nothing was weakened here.

Statement authority: `theories/StokesShift/probes/StokesShift-statement-skeleton.lean` § SS-C;
every signature below is identical to its authority row. There is no unproved placeholder and no
custom axiomatic declaration anywhere in this file. The `#print axioms` gate of every theorem
below lists at most `propext`, `Classical.choice`, `Quot.sound`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.StokesShift.Criterion
  proofs/scripts/check.sh --strict PhotoLean.StokesShift.Criterion
  proofs/scripts/axioms.sh PhotoLean.StokesShift.Criterion PhotoLean.StokesShift.stokesShift_eq_two_lam
-/
import PhotoLean.StokesShift.Basic
import PhotoLean.Marcus.Basic

set_option autoImplicit false

namespace PhotoLean

namespace StokesShift

/-! ## SS-C — law layer -/

/-- Absorption at the ground minimum costs exactly `lam + e00`.
Plan section 4, row SS-C1. Proof route (plan §5): `unfold` + `ring`. -/
theorem absEnergy_eq (lam e00 : ℝ) : absEnergy lam e00 = lam + e00 := by
  unfold absEnergy s1Surface s0Surface
  ring

/-- Emission at the excited minimum releases exactly `e00 - lam`.
Plan section 4, row SS-C2. Proof route (plan §5): `unfold` + `ring`. -/
theorem emEnergy_eq (lam e00 : ℝ) : emEnergy lam e00 = e00 - lam := by
  unfold emEnergy s1Surface s0Surface
  ring

/-- **The headline.** The Stokes shift is exactly twice the reorganization energy, independent
of the 0-0 energy. Plan section 4, row SS-C3. Proof route (plan §5): `unfold` + `ring`. -/
theorem stokesShift_eq_two_lam (lam e00 : ℝ) : stokesShift lam e00 = 2 * lam := by
  unfold stokesShift absEnergy emEnergy s1Surface s0Surface
  ring

/-- Positivity of the shift is exactly physical curvature.
Plan section 4, row SS-C4. Proof route (plan §5): rewrite by SS-C3, then `linarith`. -/
theorem stokesShift_pos_iff (lam e00 : ℝ) : 0 < stokesShift lam e00 ↔ 0 < lam := by
  rw [stokesShift_eq_two_lam]
  constructor <;> intro h <;> linarith

/-- The emission window: the vertical emission photon energy is positive exactly when
`lam < e00`. Plan section 4, row SS-C5. Proof route (plan §5): rewrite by SS-C2, then
`linarith` (`sub_pos`). -/
theorem emEnergy_pos_iff (lam e00 : ℝ) : 0 < emEnergy lam e00 ↔ lam < e00 := by
  rw [emEnergy_eq]
  exact sub_pos

/-- Mirror symmetry about the 0-0 energy: the mean of absorption and emission is `e00`.
Plan section 4, row SS-C6. Proof route (plan §5): `unfold` + `ring`. -/
theorem mirror_midpoint (lam e00 : ℝ) : (absEnergy lam e00 + emEnergy lam e00) / 2 = e00 := by
  rw [absEnergy_eq, emEnergy_eq]
  ring

/-- The two Franck–Condon offsets from `e00` are equal.
Plan section 4, row SS-C7. Proof route (plan §5): `unfold` + `ring`. -/
theorem abs_sub_e00_eq_e00_sub_em (lam e00 : ℝ) :
    absEnergy lam e00 - e00 = e00 - emEnergy lam e00 := by
  rw [absEnergy_eq, emEnergy_eq]
  ring

/-- The emission window's edge: at `e00 = lam` the vertical emission energy vanishes.
Plan section 4, row SS-C8 (edge). Proof route (plan §5): `unfold` + `ring`. -/
theorem emission_window_closes (lam : ℝ) : emEnergy lam lam = 0 := by
  rw [emEnergy_eq]
  ring

/-- Beyond the window's edge the vertical emission is negative (no photon): the model's own
boundary. Plan section 4, row SS-C8 (corner). Proof route (plan §5): `unfold` + `linarith`. -/
theorem inverted_corner {lam e00 : ℝ} (h : e00 < lam) : emEnergy lam e00 < 0 := by
  rw [emEnergy_eq]
  linarith

/-- **The boundary identification (corrected form).** The emission window — a positive
vertical photon exists — IS the Marcus inverted region read at the gap; imports
`PhotoLean.Marcus.Basic`. Plan section 4, row SS-C9, **amended at Sprint 0** (plan §3.1 entry
1): the plan's first form `e00 < lam ↔ InvertedRegion lam e00` unfolds to `e00 < lam ↔
lam < e00`, which is FALSE (kernel-checked counterexample `lam = 1, e00 = 2` in
`StokesShift-api-probe.lean`); the physically correct reading is that the open emission window
(`0 < emEnergy`, i.e. `lam < e00`) coincides with the inverted region — in this model the
regime where a vertical photon exists is exactly the Marcus-inverted regime of the
nonradiative twin. Proof route: unfold `emEnergy` (SS-B4), `s1Surface`, `s0Surface`; both sides
reduce to `lam < e00` by `ring_nf`-level algebra. -/
theorem emEnergy_pos_iff_inverted (lam e00 : ℝ) :
    0 < emEnergy lam e00 ↔ PhotoLean.Marcus.InvertedRegion lam e00 := by
  rw [emEnergy_pos_iff]
  rfl

end StokesShift

end PhotoLean
