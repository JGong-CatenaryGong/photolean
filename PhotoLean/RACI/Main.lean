import Mathlib
import PhotoLean.RACI.Torsion
import PhotoLean.RACI.Barrier
import PhotoLean.RACI.Jablonski
import PhotoLean.RACI.JablonskiRatios

namespace PhotoLean


/-!
# RACI M4 — Main：RACI 模板定理 + torsion-gap 实例

来源：plan.md §7.3–§7.5。
状态：**SKELETON** —— 语句从 plan.md 转写；与草稿的差异：
`accessGap` 中 `|·| '' allowed` 写作显式 lambda `(fun θ => |θ|) '' allowed`（记号等价）。
依赖：M2（Allowed）、M3（barrierRate_antitone）、M4.1/M4.2（quantumYield 代数）。
属主：prover_m4（独占文件）。
-/

open TwoState

namespace RACI

/-- 可达性参数：所有允许构型上的最小能隙（plan §7.3） -/
noncomputable def accessGap (allowed : Set ℝ) : ℝ :=
  2 * sInf ((fun θ : ℝ => |θ|) '' allowed)

/-- M4.3 L1：自由相允许 θ=0，最小能隙为 0（plan §7.3） -/
theorem accessGap_univ : accessGap Set.univ = 0 := by
  unfold accessGap
  have hsInf : sInf ((fun θ : ℝ => |θ|) '' Set.univ) = 0 := by
    have h0in : (0 : ℝ) ∈ (fun θ : ℝ => |θ|) '' Set.univ := by
      refine ⟨0, by simp⟩
    have hnonneg : ∀ b ∈ (fun θ : ℝ => |θ|) '' Set.univ, (0 : ℝ) ≤ b := by
      rintro b ⟨θ, hθ, rfl⟩
      exact abs_nonneg θ
    have hbdd : BddBelow ((fun θ : ℝ => |θ|) '' Set.univ) := ⟨0, hnonneg⟩
    exact le_antisymm (csInf_le hbdd h0in) (le_csInf ⟨0, h0in⟩ hnonneg)
  rw [hsInf, mul_zero]

/-- M4.3 L2：聚集相只允许 |θ| ≥ δ，最小能隙为 2δ（plan §7.3） -/
theorem accessGap_allowed (hδ : 0 < δ) : accessGap (Allowed δ) = 2 * δ := by
  unfold accessGap
  have hsInf : sInf ((fun θ : ℝ => |θ|) '' Allowed δ) = δ := by
    have hδin : δ ∈ (fun θ : ℝ => |θ|) '' Allowed δ := by
      refine ⟨δ, ?_, ?_⟩
      · exact le_abs_self δ
      · exact abs_of_pos hδ
    have hge : ∀ b ∈ (fun θ : ℝ => |θ|) '' Allowed δ, δ ≤ b := by
      rintro b ⟨θ, hθ, rfl⟩
      exact hθ
    have hbdd : BddBelow ((fun θ : ℝ => |θ|) '' Allowed δ) := ⟨δ, hge⟩
    exact le_antisymm (csInf_le hbdd hδin) (le_csInf ⟨δ, hδin⟩ hge)
  rw [hsInf]

/-- M4.3 L3：几何约束使可达性参数变大（plan §7.3） -/
theorem accessGap_lt (hδ : 0 < δ) :
    accessGap Set.univ < accessGap (Allowed δ) := by
  rw [accessGap_univ, accessGap_allowed hδ]
  linarith

/-- M4.4：把几何阻断接到速率单调性（plan §7.4） -/
theorem torsion_knr_lt
    {A β δ : ℝ} (hA : 0 < A) (hβ : 0 < β) (hδ : 0 < δ) :
    barrierRate A β (accessGap (Allowed δ)) <
      barrierRate A β (accessGap Set.univ) := by
  exact barrierRate_antitone hA hβ (accessGap_lt hδ)

/-- M4.5：第一个完整 RACI 实例定理（plan §7.5；`#print axioms` 必须干净） -/
theorem torsion_raci_emission_enhancement
    {A β δ kr : ℝ}
    (hA : 0 < A) (hβ : 0 < β) (hδ : 0 < δ)
    (hkr_pos : 0 < kr) :
    quantumYield kr (barrierRate A β (accessGap (Allowed δ))) >
      quantumYield kr (barrierRate A β (accessGap Set.univ)) := by
  apply raci_emission_enhancement
  · rfl
  · exact torsion_knr_lt hA hβ hδ
  · exact hkr_pos
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap Set.univ))))
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap (Allowed δ)))))


/-- M4.5+：广义 torsion-RACI 实例（M4+ 通道竞争版）。
    不要求 kr_agg = kr_free；只要求 CI 通道竞争比下降。 -/
theorem torsion_raci_emission_enhancement_general
    {A β δ kr_free kr_agg : ℝ}
    (hA : 0 < A)
    (hkr_free : 0 < kr_free) (hkr_agg : 0 < kr_agg)
    (hratio : barrierRate A β (accessGap (Allowed δ)) / kr_agg <
                barrierRate A β (accessGap Set.univ) / kr_free) :
    quantumYield kr_agg (barrierRate A β (accessGap (Allowed δ))) >
      quantumYield kr_free (barrierRate A β (accessGap Set.univ)) := by
  apply raci_emission_enhancement_general
  · exact hkr_free
  · exact hkr_agg
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap Set.univ))))
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap (Allowed δ)))))
  · exact hratio

/-- M4.5+ 充分条件版：若 kr_agg ≥ kr_free，则原 knr 下降结论已足够。 -/
theorem torsion_raci_emission_enhancement_of_kr_le
    {A β δ kr_free kr_agg : ℝ}
    (hA : 0 < A) (hβ : 0 < β) (hδ : 0 < δ)
    (hkr_free : 0 < kr_free) (hkr_agg : 0 < kr_agg)
    (hkr_le : kr_free ≤ kr_agg) :
    quantumYield kr_agg (barrierRate A β (accessGap (Allowed δ))) >
      quantumYield kr_free (barrierRate A β (accessGap Set.univ)) := by
  apply quantumYield_gt_of_knr_lt_of_kr_le hkr_free hkr_agg
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap Set.univ))))
  · unfold barrierRate
    exact mul_nonneg hA.le (le_of_lt (Real.exp_pos (-(β * accessGap (Allowed δ)))))
  · exact hkr_le
  · exact torsion_knr_lt hA hβ hδ

end RACI



end PhotoLean