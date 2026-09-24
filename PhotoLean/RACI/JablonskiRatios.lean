import Mathlib
import PhotoLean.RACI.Jablonski

namespace PhotoLean


/-!
# RACI M4+ — the generalized emission-enhancement criterion

AIE only needs `Φ_agg > Φ_sol`; the equality `kr_agg = kr_free` need not be imposed.
This file generalizes the equal-kr version of M4 to the **knr/kr ratio criterion**:
`Φ_agg > Φ_sol ⟺ knr_agg/kr_agg < knr_sol/kr_sol`。
-/

namespace RACI

/-- The quantum-yield difference identity (at positive denominators). -/
theorem quantumYield_sub_eq
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 - quantumYield kr1 knr1
      = (kr2 * knr1 - kr1 * knr2) / ((kr2 + knr2) * (kr1 + knr1)) := by
  unfold quantumYield
  have hd1 : kr1 + knr1 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hd2 : kr2 + knr2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hkr2 hknr2)
  field_simp [hd1, hd2]
  ring

/-- The generalized main criterion: `Φ_agg > Φ_sol ⟺ knr_agg/kr_agg < knr_sol/kr_sol`. -/
theorem quantumYield_gt_iff_ratio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 / kr2 < knr1 / kr1 := by
  have hden : 0 < (kr2 + knr2) * (kr1 + knr1) :=
    mul_pos (add_pos_of_pos_of_nonneg hkr2 hknr2) (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hsub := quantumYield_sub_eq hkr1 hkr2 hknr1 hknr2
  constructor
  · intro h
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := sub_pos.mpr h
    rw [hsub] at hq
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := (div_pos_iff_of_pos_right hden).mp hq
    have hlt : knr2 * kr1 < knr1 * kr2 := by linarith
    exact (div_lt_div_iff₀ hkr2 hkr1).mpr hlt
  · intro h
    have hlt : knr2 * kr1 < knr1 * kr2 := (div_lt_div_iff₀ hkr2 hkr1).mp h
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := by linarith
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := by
      rw [hsub]
      exact (div_pos_iff_of_pos_right hden).mpr hnum
    exact sub_pos.mp hq

/-- The one-way version: a drop in `knr/kr` implies a rise in Φ. -/
theorem quantumYield_gt_of_ratio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2)
    (h : knr2 / kr2 < knr1 / kr1) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 :=
  (quantumYield_gt_iff_ratio_lt hkr1 hkr2 hknr1 hknr2).mpr h

/-- Sufficient condition: the radiative rate does not drop (`kr_agg ≥ kr_sol`) and the nonradiative rate drops ⇒ `Φ_agg > Φ_sol`. -/
theorem quantumYield_gt_of_knr_lt_of_kr_le
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2)
    (hkr_le : kr1 ≤ kr2) (hknr : knr2 < knr1) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 := by
  apply quantumYield_gt_of_ratio_lt hkr1 hkr2 hknr1 hknr2
  have h1 : knr2 / kr2 < knr1 / kr2 := div_lt_div_of_pos_right hknr hkr2
  have h2 : knr1 / kr2 ≤ knr1 / kr1 := div_le_div_of_nonneg_left hknr1 hkr1 hkr_le
  exact lt_of_lt_of_le h1 h2

/-- The generalized RACI template: only a drop of the `knr/kr` ratio is required, not `kr` equality. -/
theorem raci_emission_enhancement_general
    {kr_free kr_agg knr_free knr_agg : ℝ}
    (hkr_free : 0 < kr_free) (hkr_agg : 0 < kr_agg)
    (hknr_free : 0 ≤ knr_free) (hknr_agg : 0 ≤ knr_agg)
    (hratio : knr_agg / kr_agg < knr_free / kr_free) :
    quantumYield kr_agg knr_agg > quantumYield kr_free knr_free :=
  quantumYield_gt_of_ratio_lt hkr_free hkr_agg hknr_free hknr_agg hratio


/-- The competition ratio: the nonradiative-over-radiative rate ratio that fixes the emission branching. -/
noncomputable def competitionRatio (kr knr : ℝ) : ℝ := knr / kr

/-- `Φ = 1 / (1 + competitionRatio)` (for `kr ≠ 0`). -/
theorem quantumYield_eq_inv_one_add_competitionRatio {kr knr : ℝ} (hkr : kr ≠ 0) :
    quantumYield kr knr = 1 / (1 + competitionRatio kr knr) := by
  unfold quantumYield competitionRatio
  field_simp [hkr]

/-- A drop in `knr/kr` ⟺ a rise in Φ (synonym of `quantumYield_gt_iff_ratio_lt`). -/
theorem quantumYield_gt_iff_competitionRatio_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      competitionRatio kr2 knr2 < competitionRatio kr1 knr1 := by
  simpa [competitionRatio] using quantumYield_gt_iff_ratio_lt hkr1 hkr2 hknr1 hknr2

/-- The nonradiative channel decomposition: `knr = kCI + kOther`. -/
theorem competitionRatio_add {kr kCI kOther : ℝ} (hkr : kr ≠ 0) :
    competitionRatio kr (kCI + kOther) = kCI / kr + kOther / kr := by
  unfold competitionRatio
  field_simp [hkr]

/-- Channel-competition form: even when `kr_agg < kr_sol`, emission is still enhanced as long as
    the CI channel's ratio drops sufficiently and the other nonradiative channels' ratios do not
    rise. No assumption `kr_agg/kr_sol > 1` is made here. -/
theorem quantumYield_gt_of_channel_ratios
    {kr1 kr2 kCI1 kCI2 kOther1 kOther2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hkCI1 : 0 ≤ kCI1) (hkCI2 : 0 ≤ kCI2)
    (hkOther1 : 0 ≤ kOther1) (hkOther2 : 0 ≤ kOther2)
    (hOther_le : competitionRatio kr2 kOther2 ≤ competitionRatio kr1 kOther1)
    (hCI_lt : competitionRatio kr2 kCI2 < competitionRatio kr1 kCI1) :
    quantumYield kr2 (kCI2 + kOther2) > quantumYield kr1 (kCI1 + kOther1) := by
  have htotal :
      competitionRatio kr2 (kCI2 + kOther2) < competitionRatio kr1 (kCI1 + kOther1) := by
    rw [competitionRatio_add hkr2.ne', competitionRatio_add hkr1.ne']
    exact add_lt_add_of_lt_of_le hCI_lt hOther_le
  exact quantumYield_gt_of_ratio_lt hkr1 hkr2
    (add_nonneg hkCI1 hkOther1) (add_nonneg hkCI2 hkOther2)
    (by simpa [competitionRatio] using htotal)


/-- The a-priori AIE criterion (multiplicative form, with no statistical or experimental term):
    `Φ_agg > Φ_sol ⟺ knr_agg * kr_sol < knr_sol * kr_agg`.
    This is the **necessary and sufficient condition** within the two-state Jablonski model. -/
theorem aie_iff_mul
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 * kr1 < knr1 * kr2 := by
  have hden : 0 < (kr2 + knr2) * (kr1 + knr1) :=
    mul_pos (add_pos_of_pos_of_nonneg hkr2 hknr2) (add_pos_of_pos_of_nonneg hkr1 hknr1)
  have hsub := quantumYield_sub_eq hkr1 hkr2 hknr1 hknr2
  constructor
  · intro h
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := sub_pos.mpr h
    rw [hsub] at hq
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := (div_pos_iff_of_pos_right hden).mp hq
    linarith
  · intro h
    have hnum : 0 < kr2 * knr1 - kr1 * knr2 := by linarith
    have hq : 0 < quantumYield kr2 knr2 - quantumYield kr1 knr1 := by
      rw [hsub]
      exact (div_pos_iff_of_pos_right hden).mpr hnum
    exact sub_pos.mp hq

/-- Suppression-factor form: with `c = knr_agg/knr_sol` and `d = kr_agg/kr_sol`, AIE holds
    ⟺ the nonradiative suppression factor is smaller than the radiative one, `c < d`.
    Note: **`kr_agg ≥ kr_sol` is NOT required.** -/
theorem aie_iff_knr_suppression_lt_kr_suppression
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr1 : 0 < kr1) (hkr2 : 0 < kr2)
    (hknr1 : 0 < knr1) (hknr2 : 0 ≤ knr2) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 ↔
      knr2 / knr1 < kr2 / kr1 := by
  have h := aie_iff_mul hkr1 hkr2 hknr1.le hknr2
  constructor
  · intro hΦ
    have hmul : knr2 * kr1 < knr1 * kr2 := h.mp hΦ
    exact (div_lt_div_iff₀ hknr1 hkr1).mpr (by simpa [mul_comm] using hmul)
  · intro hratio
    have hmul' : knr2 * kr1 < knr1 * kr2 := by
      have := (div_lt_div_iff₀ hknr1 hkr1).mp hratio
      simpa [mul_comm] using this
    exact h.mpr hmul'

end RACI


end PhotoLean