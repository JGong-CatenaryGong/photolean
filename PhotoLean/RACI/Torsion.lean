import Mathlib
import PhotoLean.RACI.Accessibility

namespace PhotoLean


/-!
# RACI M2 — Torsion：扭转角模型与路径阻断定理

来源：plan.md §5.1–§5.4。
状态：**SKELETON** —— 语句从 plan.md 转写；与草稿的差异：
`torsion_blocks_ci` 中 FC 作为 `Set ℝ` 变量（plan §5.1 说 FC 具体定义在使用处给出；
M2.3 实例里 FC 不参与）。
属主：prover_m2（独占文件）。
-/

open TwoState

namespace RACI

/-- 允许构型：|θ| ≥ δ（聚集相；CI 位于 θ=0，plan §5.1） -/
def Allowed (δ : ℝ) : Set ℝ := {θ | δ ≤ |θ|}

/-- M2.1：IVT 穿越引理 —— 从 θ≥θ0 连续走到 0 必经过 |θ| < δ（plan §5.2） -/
theorem exists_cross_forbidden
    {δ θ0 : ℝ} (hδ : 0 < δ) (hθ : δ < θ0)
    {γ : ℝ → ℝ} (hγ : Continuous γ)
    (h0 : θ0 ≤ γ 0) (h1 : γ 1 = 0) :
    ∃ t : ℝ, |γ t| < δ := by
  let c : ℝ := δ / 2
  have hc_pos : 0 < c := by
    unfold c
    exact div_pos hδ (by norm_num)
  have hc_lt : c < δ := by
    unfold c
    linarith
  have hγ0 : c ≤ γ 0 := le_trans hc_lt.le (le_trans hθ.le h0)
  have hc_mem : c ∈ Set.uIcc (γ 0) (γ 1) := by
    rw [Set.mem_uIcc]
    right
    constructor
    · rw [h1]
      exact le_of_lt hc_pos
    · exact hγ0
  rcases (intermediate_value_uIcc hγ.continuousOn) hc_mem with ⟨t, ht, ht_eq⟩
  refine ⟨t, ?_⟩
  rw [ht_eq, abs_of_pos hc_pos]
  exact hc_lt

/-- M2.2：torsion 约束阻断所有 FC→CI 路径（对所有 ε 成立；plan §5.3） -/
theorem torsion_blocks_ci
    {M : TwoState ℝ} {FC : Set ℝ} {δ θ0 : ℝ}
    (hδ : 0 < δ) (hθ : δ < θ0)
    (hFC : FC ⊆ {θ | θ0 ≤ θ})
    (hCI : TwoState.conicalSet M ⊆ {θ | θ = 0}) :
    ∀ ε, BlockedBelow M (Allowed δ) FC ε := by
  intro ε
  rintro ⟨A⟩
  have hstart : θ0 ≤ A.path 0 := hFC A.starts_fc
  have hend : A.path 1 = 0 := hCI A.ends_ci
  rcases exists_cross_forbidden hδ hθ A.cont hstart hend with ⟨t, ht⟩
  have hstay : δ ≤ |A.path t| := A.stays_allowed t
  linarith

/-- M2.3：对角 torsion Hamiltonian：H(θ) = diag(θ, -θ)，CI 在 θ=0，能隙 2|θ|（plan §5.4） -/
def torsionH (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![θ, 0; 0, -θ]

/-- M2.3：torsionH 的对称性（逐分量；plan §5.4） -/
theorem torsionH_symm : ∀ θ, Matrix.IsSymm (torsionH θ) := by
  intro θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torsionH, Matrix.transpose]

/-- M2.3：torsionH 的连续性（分量是恒等与负恒等；plan §5.4） -/
theorem torsionH_cont : Continuous torsionH := by
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j
  · simpa [torsionH] using (continuous_id : Continuous fun a : ℝ => a)
  · simpa [torsionH] using (continuous_const : Continuous fun a : ℝ => (0 : ℝ))
  · simpa [torsionH] using (continuous_const : Continuous fun a : ℝ => (0 : ℝ))
  · simpa [torsionH] using (continuous_neg : Continuous fun a : ℝ => -a)

/-- M2.3：torsionH 的 CI 集恰为 {0}（plan §5.4） -/
theorem torsionH_conicalSet :
    TwoState.conicalSet (⟨torsionH, torsionH_symm, torsionH_cont⟩ : TwoState ℝ) = {0} := by
  ext θ
  constructor
  · intro hθ
    have hθθ : θ = -θ := by
      simpa [TwoState.a, TwoState.d, torsionH] using hθ.1
    have hθ0 : θ = 0 := by linarith
    simpa using hθ0
  · intro hθ
    have hθ0 : θ = 0 := by
      simpa using hθ
    constructor
    · simp [TwoState.a, TwoState.d, torsionH, hθ0]
    · simp [TwoState.b, torsionH]

end RACI


end PhotoLean