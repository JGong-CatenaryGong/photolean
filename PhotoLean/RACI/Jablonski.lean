import Mathlib

namespace PhotoLean


/-!
# RACI M4 — Jablonski: the quantum-yield algebra

Upstream provenance: the ChemLean RACI plan §7.1, §7.2 (integration record: theories/RACI/plan.md §3.1).
Status note (upstream header, preserved): the statements were transcribed from the upstream plan.
Upstream owner: prover_m4 (exclusive file).
-/

namespace RACI

/-- The quantum yield `kr / (kr + knr)` (upstream plan §2.3). -/
noncomputable def quantumYield (kr knr : ℝ) : ℝ :=
  kr / (kr + knr)

/-- M4.1: the quantum yield is strictly antitone in `k_nr` (upstream plan §7.1). -/
theorem quantumYield_strictMono_of_knr_lt
    {kr1 kr2 knr1 knr2 : ℝ}
    (hkr_pos : 0 < kr1)
    (hknr1 : 0 ≤ knr1) (hknr2 : 0 ≤ knr2)
    (hkr_eq : kr2 = kr1)
    (hknr : knr2 < knr1) :
    quantumYield kr2 knr2 > quantumYield kr1 knr1 := by
  unfold quantumYield
  rw [hkr_eq]
  have hden1 : 0 < kr1 + knr1 := add_pos_of_pos_of_nonneg hkr_pos hknr1
  have hden2 : 0 < kr1 + knr2 := add_pos_of_pos_of_nonneg hkr_pos hknr2
  have hdiff : 0 < kr1 / (kr1 + knr2) - kr1 / (kr1 + knr1) := by
    have hkey : kr1 / (kr1 + knr2) - kr1 / (kr1 + knr1)
        = kr1 * (knr1 - knr2) / ((kr1 + knr2) * (kr1 + knr1)) := by
      field_simp [hden1.ne', hden2.ne']
      ring
    rw [hkey]
    exact div_pos (mul_pos hkr_pos (sub_pos.mpr hknr)) (mul_pos hden2 hden1)
  linarith

/-- M4.2: the RACI template theorem (upstream plan §7.2; `hknr` is an explicit premise, not an axiom). -/
theorem raci_emission_enhancement
    {kr_free kr_agg knr_free knr_agg : ℝ}
    (hkr : kr_agg = kr_free)
    (hknr : knr_agg < knr_free)
    (hkr_pos : 0 < kr_free)
    (hknr_free : 0 ≤ knr_free) (hknr_agg : 0 ≤ knr_agg) :
    quantumYield kr_agg knr_agg > quantumYield kr_free knr_free := by
  exact quantumYield_strictMono_of_knr_lt hkr_pos hknr_free hknr_agg hkr hknr

end RACI


end PhotoLean