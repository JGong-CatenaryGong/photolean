import Mathlib

namespace PhotoLean


/-!
# RACI M4 — Jablonski：量子产率代数

来源：plan.md §7.1、§7.2。
状态：**SKELETON** —— 语句从 plan.md 转写。
属主：prover_m4（独占文件）。
-/

namespace RACI

/-- 量子产率：kr / (kr + knr)（plan §2.3） -/
noncomputable def quantumYield (kr knr : ℝ) : ℝ :=
  kr / (kr + knr)

/-- M4.1：量子产率关于 k_nr 严格反单调（plan §7.1） -/
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

/-- M4.2：RACI 模板定理（plan §7.2；hknr 是显式前提，不是公理） -/
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