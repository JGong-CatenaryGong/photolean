# plan.md — PhotoLean 形式化规划：Marcus 反转区（M1–M5）

> 项目：把"马库斯反转区（Marcus inverted region）"变成一个**机器可检查**的定理集。
> 目标系统：Lean 4.17.0 + mathlib（`MODULE_PREFIX=PhotoLean`，见 `proofs/ENGINE.yml`）。
> 状态：规划已定稿（人类确认于 2026-09-20），实现未开始。
> 权威契约：`proofs/ENGINE.yml`；任务板：`proofs/TASKS.md`；经验库：`proofs/EXPERIENCE.md`。

---

## 1. 总体目标与边界

### 1.1 项目总目标

在经典马库斯模型（单一反应坐标、抛物线势、经典核运动、Condon 近似）中形式化并证明：

> **主定理**：只要重组能 `λ > 0`、热能 `k_B T > 0`、前置因子 `A > 0`，则**反转区**
> （驱动力 `x = -ΔG° > λ`）内"驱动力越大、速率越小"成立；
> 并且这三个条件是**锐利的（充要）** —— 缺任何一个，该描述失效。

这就是"马库斯反转区"的可执行版本：**势垒 `ΔG‡ = (λ - x)²/(4λ)` 在 `x = λ` 处最小（无势垒），
因此速率在 `x = λ` 处取极大，两侧分别单调上升（正常区）与单调下降（反转区）。**

**引用归属（文献分支核实后的更正）**：反转区的**首次提出**是
**Marcus 1960, *Discuss. Faraday Soc.* **29**, p. 28 §(v)，标题即 "Possibility of 'inverted' chemical behaviour"**
（原文：*"If ΔF° becomes too negative, intersection of the two surfaces becomes possible only at
high potential energies … m² eventually increases with increasing −ΔF°, and the rate constant decreases."*
⇒ 与 `ΔG° < -λ` ⟺ `x > λ` 一致）。**Marcus 1956 全篇无 "inverted" 字样**（已全文检索确认），
不应把反转区的出处记在 1956。势垒公式本身的原始印刷体出处仍是 1956（Eq. (38), p. 974）。

### 1.2 人类需求 → 里程碑的对应（三部分）

| 人类需求 | 里程碑 | 交付物 |
|---|---|---|
| ① 把 Marcus 反转区转化为形式化描述 | **M1**（描述层） | `Marcus/Basic.lean`：`barrier` / `rate` / 区域谓词 / `InvertedDescriptor` / 可判定分类器 `zone` |
| ②a 证明这个描述 | **M2 + M3**（势垒代数 + 速率层） | `Marcus/Barrier.lean`（全代数）、`Marcus/Rate.lean`（exp 层 + 主定理的单调性内核） |
| ②b 找到这个描述的**成立条件** | **M4**（锐利刻画 + 微观充分条件） | `Marcus/Sharp.lean`（⟺ 充要刻画）、`Marcus/Reorg.lean`（`lam = lamIn + lamOut`、Pekar 因子正性 ⇒ `lam > 0`）、`Marcus/Compose.lean`（复合） |
| ③ 用实例代入并判断是否符合 | **M5**（实例与判定） | `Marcus/RatModel.lean`（ℚ 可计算判定 + 转移引理）、`Marcus/Instances.lean`（实例集） |

### 1.3 明确不做（防范围蔓延）

- **不做量子振动修正**（Bixon–Jortner / Jortner 能隙律 / 振动模式求和 / Franck–Condon 因子）：
  经典模型下反转区是**严格单调下降**，量子修正使其饱和；后者需要无穷级数与振动配分函数，
  在 mathlib 下代价过高。仅作为文献记录与"下一站"写入，不进里程碑。
- **不做非绝热电子耦合的推导**（`V` 的指数衰减、超交换机制）、不做电子转移的量子力学推导、
  不做溶剂连续介质静电学的第一性推导（Pekar 因子**作为显式前提**给出，不推导）。
- **不做 Marcus 交叉关系**（`k₁₂ = √(k₁₁k₂₂K₁₂)`）、不做振动模式求和、不做自旋-轨道耦合。
- **不做竞争反应通道**（本形式化只刻画**单一机理**下的经典马库斯速率）。这条**不是我们的发明**，
  而是原始文献自带的免责：1960 §(v) 原文即写明 *"unless in such cases a more favourable reaction
  mechanism is found"*。它正是 M5 实例层只能用"区域判定 + 经典描述成立"、**不能**声称预测实测速率的原因之一
  （与 §8.3 的定量警示同源）。
- 不引入任何**自定义 `axiom`** 或 `sorry`（判据由 `proofs/scripts/check.sh --strict` 与
  `proofs/scripts/axioms.sh` 执行）。
- **不声称**形式化结论比经典理论更强或更普适：本项目的价值是**把隐式前提挖出来并锐利化**
  （见 §7.1 的关键发现）。

---

## 2. 形式化系统设计

### 2.1 嵌入策略：不造新内核，在 Lean 中做嵌入理论

全部对象落在 `ℝ`（判定层落在 `ℚ`）上，用 mathlib 的序、除法、`Real.exp` 与其单调性。
**`exp` 的单调性是唯一的实分析工具**，其余全是 `ℝ` 上的代数不等式。
这一选择是刻意的：把 API 风险压缩到一小组 `Real.exp_*` 引理（见 §12）。

### 2.2 全局基础定义（M1；`Marcus/Basic.lean`）

```lean
import Mathlib

namespace PhotoLean.Marcus

/-- 经典马库斯势垒：驱动力 `x = -ΔG°`（放能反应取 `x > 0`），重组能 `lam`。
    **约定**：`lam = 0` 时按 Lean 的除零约定 `x / 0 = 0` 取值，故 `barrier 0 x = 0`；
    这是 M4 锐利性的一个分支，必须显式处理，不能假设 `lam ≠ 0`。--/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- 马库斯速率（Arrhenius/Eyring 型）：`k = A · exp(-ΔG‡/(k_B T))`。--/
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

/-- 反转区：驱动力超过重组能。--/
def InvertedRegion (lam x : ℝ) : Prop := lam < x

/-- 正常区：驱动力小于重组能。--/
def NormalRegion (lam x : ℝ) : Prop := x < lam

/-- **反转区描述**（本项目的形式化目标）：反转区内速率随驱动力严格递减。--/
def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

/-- 正常区描述：正常区内速率随驱动力严格递增。--/
def NormalDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate A lam kB T x₁ < rate A lam kB T x₂

/-- 区域分类（M5 判定层的载体）。--/
inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

/-- 分类器：`x < lam` 正常区；`x = lam` 无势垒点；`x > lam` 反转区。--/
noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

end PhotoLean.Marcus
```

**✅ Sprint 0 已实测**：以上全部定义与 M1–M5 的定理签名已在
`proofs/probes/marcus-statement-skeleton.lean` 中编译通过（31 处 `sorry` warning、**0 error**）。
**该骨架文件是语句的唯一权威**：`PhotoLean/Marcus/*.lean` 的签名必须与它逐字一致。

**设计说明（为什么把描述写成谓词而不是一条"曲线定理"）**：
`InvertedDescriptor` 是**可嵌套否定与合取**的命题（M4 的锐利性需要 `¬ InvertedDescriptor`），
而 `zone` 让"判断某个实例属于哪个区"变成**内核可计算的等式判定**（M5）。
两者由 `zone_eq_inverted_iff` 等定理桥接，避免"判定"与"描述"两套语义漂移。

### 2.3 判定层与转移（M5；`Marcus/RatModel.lean`）

`ℝ` 上的序是**不可计算**的（用 `Classical`），因此 M5 在 `ℚ` 上复制一份：

```lean
namespace PhotoLean.Marcus.Rat

/-- ℚ 上的分类器：**完全可计算**（`Rat` 的序与相等是可判定的）。--/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- 转移引理：ℚ 上的判定与 ℝ 上的分类一致 —— 这是"实例判定"对 ℝ 理论有约束力的依据。--/
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ)

end PhotoLean.Marcus.Rat
```

实例的"判断"因此有三条**独立证据链**（任一即可单独作证，M5 全部给出）：
1. 内核计算：`example : zoneQ 1 3 = Zone.inverted := by decide`；
2. 转移到 ℝ 定理层：`zoneQ_eq_zone` + `zone_eq_inverted_iff` ⇒ `InvertedRegion 1 3`；
3. 实例化主定理：`InvertedDescriptor 1 1 1 1`（由 `inverted_descriptor_holds` + `norm_num`）。

### 2.4 证明纪律（不可协商）

1. 交付定理不得含 `sorry` / 自定义 `axiom`；`#print axioms` 只允许
   `propext` / `Classical.choice` / `Quot.sound`；
2. **物理近似全部显式化**为定理前提（`0 < λ`、`0 < k_B T`、`0 < A`、`λ = λ_in + λ_out`、
   `1/ε_s < 1/n²`、几何因子不等式……），不得藏在定义或类型里；
3. 每 lemma 一个 commit：`feat(<area>): <lemma>`（`<area>` = M1…M5）；
4. API 名不猜：先查 `proofs/API-NOTES.md`，否则交 `api_researcher`；
5. 文件所有权独占（见 §10）。**`lake build` 通过不是验收**（`sorry`/`axiom` 都返回 0）。

**命名约定（工具链硬约束）**：Lean 4 中 `λ` 是 lambda 关键字，**不能作标识符**
（Sprint 0 实测：`(λ x : ℝ)` 直接报 `unexpected token 'λ'`）。因此 Lean 侧一律用 ASCII：
重组能 `lam`、驱动力 `x`、前置因子 `A`、`kB`、`T`、内外层 `lamIn`/`lamOut`、
静态介电常数 `epsS`、折射率平方 `nSq`、半径 `a1`/`a2`、电荷转移量 `dE`、位移 `dq`。
**文档里的希腊字母只是物理记号，不是 Lean 标识符。**

**statement-first 的落盘机制**（本项目特有，必须遵守）：
`SOURCE_DIRS="PhotoLean"` 内**任何位置**出现 `sorry` 都会被 `check.sh --strict` 拦住，
因此**语句骨架写在 `proofs/probes/` 内**（不在 `SOURCE_DIRS`，用 `sorry` 占位允许），
骨架编译通过后再逐条搬进 `PhotoLean/Marcus/*.lean` 并当场补证明。
骨架文件：`proofs/probes/marcus-statement-skeleton.lean`（Sprint 0 验收物）。

---

## 3. 文件布局与依赖

```text
PhotoLean/
  Smoke.lean                 -- 既有：环境冒烟（保留）
  Marcus/
    Basic.lean               -- M1  ：barrier / rate / 区域谓词 / 描述谓词 / Zone / zone
    Barrier.lean             -- M2  ：势垒纯代数（非负、x=lam 零势垒、对称、两支单调、峰值、lam=0 退化）
    Rate.lean                -- M3  ：exp 层（核心转移引理）＋速率层的正常区/反转区/峰值
    Sharp.lean               -- M4a ：描述的锐利刻画（⟺）与非正 lam 的失效定理
    Reorg.lean               -- M4b ：lam = lamIn + lamOut、Pekar 因子正性（**只 import Mathlib**）
    Compose.lean             -- M4c ：复合定理（import Sharp + Reorg ⇒ 微观正性 ⇒ 描述成立）
    RatModel.lean            -- M5a ：ℚ 分类器 / barrierQ / 转移引理
    Instances.lean           -- M5b ：实例集（正常区、反转区、无势垒、反例、非物理分支）
proofs/probes/
  marcus-statement-skeleton.lean    -- Sprint 0：全部语句编译（含 sorry 占位，不进源码树）
  marcus-{exp,order,tactic}-api.lean -- api_researcher 的 #check 探针
```

依赖图（`→` 表示 import）：

```text
Basic.lean ──→ Barrier.lean ──→ Rate.lean ──→ Sharp.lean ──┐
    │                                                        ├──→ Compose.lean
    ├──→ RatModel.lean ──┐                                   │
    │                    └──────────────→ Instances.lean ←───┘
    └──→ （无依赖）Reorg.lean ─────────────────────────────────┘
```

**关键路径是单链**（Basic → Barrier → Rate → Sharp → Compose），可并行的是两条支线：
`Reorg.lean`（**只 import Mathlib，零依赖 —— 可与 Basic 同时开工**）与
`RatModel.lean`（只需 Basic）。把复合定理单独放进 `Compose.lean` 就是为了
**不让 Reorg 的独立 lemma 被 Sharp 阻塞**（依赖图内并行，见铁律 5）。§10 按此排期。

---

## 4. M1 — 描述层（`Marcus/Basic.lean`；属主 prover_a）

**目标**：把"反转区"变成 Lean 里可嵌套、可否定、可判定的对象；语句全部编译通过（`stmt`）。

### 4.1 定义（§2.2 的全部内容）

### 4.2 分类器的正确性

```lean
theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x
theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam
theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x
theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted
```

**证明步骤**：对 `x < λ` 做 `by_cases`，`simp [zone, NormalRegion, InvertedRegion, h]`；
剩余分支用 `push_neg` + `lt_trichotomy`（或 `le_antisymm`）。`zone_trichotomy` 用 `cases zone λ x <;> tauto`。

**验收**：`check.sh --strict PhotoLean.Marcus.Basic` PASS；`axioms.sh` 四条定理干净。

---

## 5. M2 — 势垒代数（`Marcus/Barrier.lean`；属主 prover_a）

**目标**：`barrier` 的完整单调性图景（正的 λ、负的 λ、零 λ 三种情形），**不涉及 `exp`**。

```lean
/-- lam>0 时势垒非负。--/
theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x

/-- 无势垒点：`x = lam` 处势垒为零（**无需前提**）。--/
theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0

/-- 抛物线对称性：以 `x = lam` 为轴。--/
theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x)

/-- 峰值（势垒最小）：`lam>0` 时 `x = lam` 是全局最小点。--/
theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x

/-- `lam>0`、反转区：势垒严格递增（这是反转区的代数内核）。--/
theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂

/-- `lam>0`、正常区：势垒严格递减。--/
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁

/-- `lam<0`：反转区内的方向**反转**（势垒递减）。M4 锐利性的必要分支。--/
theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁

/-- `lam=0` 的退化：除零约定使势垒恒为零（M4 锐利性的另一必要分支）。--/
theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0

/-- 结构定理：三种情形穷尽。--/
theorem barrier_mono_cases (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0)
```

**证明草图**：
- `barrier_mono_of_pos`：`λ ≤ x₁ < x₂ ⇒ 0 ≤ x₁ - λ < x₂ - λ`；由 `(λ-x)² = (x-λ)²`（`ring_nf`）
  转到 `(x-λ)²`，用 `pow_lt_pow_left₀`（或 `mul_self_lt_mul_self`）得平方严格单增，
  再 `div_lt_div_of_pos_right _ (by positivity : 0 < 4*λ)`。**先用 `have` 建正性**，别指望 `nlinarith` 自动补前提。
- `barrier_antitone_of_pos`：同法，但要 `x₁ < x₂ ≤ λ ⇒ 0 ≤ λ - x₂ < λ - x₁`，
  把目标 `(λ-x₂)²/(4λ) < (λ-x₁)²/(4λ)` 归约到平方比较（`sq_lt_sq` 类引理需注意绝对值形式）。
- `barrier_antitone_of_neg`：`λ < 0` 时 `(x-λ)²` 仍严格递增，但除以 `4λ < 0` 反转方向
  （`div_lt_div_of_neg_right`，或先证 `4λ < 0` 再用 `div_lt_div_iff_of_neg`）。
- `barrier_at_lam` / `barrier_zero_lam`：`simp [barrier]` / `norm_num [barrier]`。
- `barrier_symm`：`(λ-x)² = (λ-(2λ-x))²` —— `ring_nf` 可收，但**注意除零约定**
  （`λ ≠ 0` 前提是否真的必要，实测后写入 `proofs/API-NOTES.md`）。

**fallback**：若 `sq_lt_sq` 类引理在 v4.17 的名字/形态不顺，改用
`nlinarith [sq_nonneg (x₁ - λ), sq_nonneg (x₂ - x₁)]` 直接碾平方比较 —— 这类目标是 `nlinarith` 的甜点区。

**验收**：`check.sh --strict PhotoLean.Marcus.Barrier` PASS；`axioms.sh` 逐条干净。

---

## 6. M3 — 速率层（`Marcus/Rate.lean`；属主 prover_b）

**目标**：把势垒的单调性推到速率上。**全部 `exp` 风险集中在这一个文件**，靠一条核心引理隔离。

```lean
/-- 前置因子正 ⇒ 速率正（M4 锐利性的显式前提之一就是它）。--/
theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x

/-- **核心转移引理**：势垒更小 ⇒ 速率更大。整个项目唯一的 exp 单调性使用点。--/
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x

/-- 定量形式（可选/拉伸目标）：反转区抑制因子的指数形式。--/
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T))

/-- 正常区：驱动力越大速率越大。--/
theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂

/-- 反转区：驱动力越大速率越小 —— 马库斯反转区。--/
theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    rate A lam kB T x₂ < rate A lam kB T x₁

/-- 峰值：`x = lam` 处速率最大（最快反应的驱动力恰等于重组能）。--/
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam
```

**证明草图**：`rate_gt_of_barrier_lt` 是全项目**最省事也最关键**的一条：
由 `h : Φx < Φy` 得 `-(Φy)/(kBT) < -(Φx)/(kBT)`（先 `neg_lt_neg`，再 `div_lt_div_of_pos_right` 用 `hkT`），
再 `Real.exp_lt_exp`（**方向必须是 `exp a < exp b ↔ a < b`，已交 api_researcher 实测**）
得 `exp(-(Φy)/(kBT)) < exp(-(Φx)/(kBT))`，最后 `mul_lt_mul_of_pos_left _ hA` 收尾。
三条速率定理都是 `barrier_mono_*` + `rate_gt_of_barrier_lt` 的两行组合。

**风险**：`Real.exp` 相关名字是本项目唯一可能"猜错"的地方 → **禁止猜名**，先读 `proofs/API-NOTES.md`。
`rate_ratio` 为拉伸目标（`Real.exp_sub` + `div_eq_mul_inv` + `ring_nf`），若 20 分钟内不收敛就标 `todo` 并在任务板注明，**不阻塞 M4/M5**。

**验收**：`check.sh --strict PhotoLean.Marcus.Rate` PASS；`axioms.sh` 逐条干净。

---

## 7. M4 — 成立条件（锐利刻画 + 微观充分条件）

### 7.1 M4a 锐利刻画（`Marcus/Sharp.lean`；属主 prover_c）

**规划期发现（本项目的物理核心，必须写进定理）**：
如果只写 `InvertedDescriptor`，它**并不蕴含 `λ > 0`**。反例（非物理分支）：
`A < 0 ∧ λ < 0 ∧ k_B T > 0` 时，`λ<0` 使 `x ↦ barrier λ x` 在反转区**递减**，
于是 `exp(-Φ/(kBT))` 递增、再乘负的 `A` 得**严格递减** —— 描述成立但速率是**负的**。
**因此"速率正性"（等价于 `A > 0`）是描述有意义的前提，必须显式化。**

```lean
/-- 主定理：`A>0 ∧ lam>0 ∧ k_B T>0` ⇒ 反转区描述成立。--/
theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T

/-- 正常区描述同样成立（与反转区一起构成完整速率-驱动力曲线）。--/
theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    NormalDescriptor A lam kB T

/-- **锐利刻画（成立条件）**：在物理正性前提 `k_B > 0, T > 0` 下，
    "速率处处为正 且 反转区描述成立" ⟺ `A > 0 ∧ lam > 0`。--/
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam

/-- 必要性的"失效"形态：`lam ≤ 0` 时描述必然失效（物理正性前提下）。--/
theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T

/-- [拉伸] 非物理分支确实满足描述 —— 说明"速率正性"前提不可去。--/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T
```

**⚠️ 表述精度（避免过度声称）**：速率只依赖**乘积** `τ := kB * T`，因此
`(∀x, 0<rate) ∧ 描述 ⟺ 0<A ∧ 0<lam ∧ 0<τ` 是**关于乘积**的刻画；
把 `0 < kB`、`0 < T` 作为**显式物理前提**（温度为正）时，`kB`、`T` 各自都不构成"必要条件"
（`kB < 0 ∧ T < 0` 也给 `τ > 0`）。`descriptor_sharp` 因此只在 `A` 与 `lam` 上陈述 `⟺`，
`kB`、`T` 只作为前提 —— **不要**在文档里声称"`kB`、`T` 各自都必要"。

**证明草图**：
- `(⟸)`：`inverted_descriptor_holds` ← `inverted_rate_decreases`（M3）对任意
  `λ < x₁ < x₂` 直接实例化；`(∀x, 0 < rate _)` ← `rate_pos`。
- `(⟹) A > 0`：取 `x := λ`，`0 < A * exp(…)` 且 `exp(…) > 0` ⇒ `A > 0`
  （`pos_of_mul_pos_right` / `lt_of_mul_lt_mul_left`）。
- `(⟹) λ > 0`：反证 `λ ≤ 0`，`rcases lt_or_eq_of_le hλ` 分两支 ——
  - `λ = 0`：`barrier_zero_lam` ⇒ `rate = A * exp 0 = A`，取 `x₁ = 1 < 2 = x₂`
    得 `A < A`，矛盾；
  - `λ < 0`：`barrier_antitone_of_neg` ⇒ 反转区内 `Φ` 递减 ⇒（`hkT > 0`）`rate` 递增，
    与描述要求的严格递减矛盾（取 `x₁ = λ+1 < λ+2`）。
  两支都只需 M2 的现成引理 + `norm_num` 定界。
- `descriptor_fails_of_nonpos_lam` 是上式必要性的直接推论。

**验收**：`check.sh --strict PhotoLean.Marcus.Sharp` PASS；`axioms.sh` 逐条干净；
**verifier 必须重点复核 `descriptor_sharp` 的两个必要性分支**（这是本项目最容易偷偷依赖
"除零 = 0"约定而漏掉分支的地方）。

### 7.2 M4b 微观充分条件（`Marcus/Reorg.lean`；属主 prover_d）

**目标**：把前提 `λ > 0` 从"假设"降级为"**由微观参数推出**" —— 这才是"找到成立条件"的完整形态。

```lean
/-- 内层（内球）重组能：简正模式力常数 × 位移平方 / 2。--/
noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

/-- 外层（外球/溶剂）重组能（两球连续介质模型，Pekar 形式）：
    `Δe² · (1/(2a₁) + 1/(2a₂) - 1/R) · (1/n² - 1/ε_s)`。--/
noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq
theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) : 0 < lamInner kk dq

/-- **Pekar 因子正性**：`n² < ε_s`（光学折射率平方小于静态介电常数）+ 几何因子正
    ⇒ 外层重组能为正。这是"反转区存在"的溶剂侧充分条件。--/
theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS

/-- [拉伸·强烈建议] 几何因子正性**可由"两球不重叠"推出**，不必当假设：
    `a1 + a2 ≤ R ⇒ 1/R < 1/(2*a1) + 1/(2*a2)`（因 `1/R ≤ 1/(a1+a2)`，且
    `1/(2a1)+1/(2a2)-1/(a1+a2) = (a1²+a2²)/(2a1a2(a1+a2)) > 0`）。
    这是本计划**唯一真正需要不等式**的几何引理，不依赖任何物理近似。--/
theorem hgeom_of_nonoverlap {a1 a2 R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)

/-- 重组能分解的加性：正性在加法下保持。--/
theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut

/-- **复合定理**：微观正性 ⇒ 主定理的前提成立 ⇒ 反转区描述成立。
    把 `lam > 0` 这个"假设"替换为物理上更基本的条件。--/
theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T
```

**证明草图**：`lamInner_pos`/`lambdaOuter_pos`：`mul_pos` + `one_div_pos` + `linarith` 处理
`1/(2a₁) + 1/(2a₂) - 1/R > 0` 与 `1/nSq - 1/εs > 0`（先把 `1/εs < 1/nSq` 转成 `1/nSq - 1/εs > 0`）。
复合定理：`lam_total_pos` 得 `λ > 0`，再 `inverted_descriptor_holds`（需 import `Sharp`）。

**验收**：`check.sh --strict PhotoLean.Marcus.Reorg` PASS；`axioms.sh` 逐条干净；
每个物理前提（`hnSq`、`hεs`、`hPekar`、`hgeom`）必须在定理签名里可见，**不得折叠进定义**。

---

## 8. M5 — 实例与判定（`Marcus/RatModel.lean` + `Marcus/Instances.lean`；属主 prover_b）

**目标**：把实例代进去，**判断**它是否符合反转区描述；判定必须由内核计算/证明给出，不是脚本断言。

### 8.1 判定层（`RatModel.lean`）

```lean
def zoneQ (lam x : ℚ) : Zone
def barrierQ (lam x : ℚ) : ℚ
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)
theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ)
```

**验收**：`check.sh --strict PhotoLean.Marcus.RatModel` PASS；`axioms.sh` 干净。

### 8.2 实例集（`Instances.lean`）—— 每类实例给一条**判断**证据

| # | 实例 | 期望判断 | 证据形态 |
|---|---|---|---|
| I1 | `λ = 1, x = 3`（纯数，反转区） | 符合（在反转区） | `by decide` 算 `zoneQ` + 转移 |
| I2 | `λ = 1, x = 3/4`（正常区） | 不符合（正常区） | `by decide` 得 `zoneQ = .normal` |
| I3 | `x = λ`（无势垒点） | 边界（速率最大） | `zoneQ` + `rate_peak_at_lam` 实例化 |
| I4 | 文献参数：反转区对 | 符合 | `norm_num` + 转移引理 |
| I5 | 文献参数：正常区对 | 不符合反转区描述 | 同上 + `normal_rate_increases` |
| I6 | `λ = -1/2, A = 1, kT = 1`（非物理） | **不符合**描述 | `descriptor_fails_of_nonpos_lam` |
| I7 | `A = -1, λ = -1, kT = 1`（非物理分支） | 描述成立但**速率非正** ⇒ 判为不可采纳 | `inverted_descriptor_holds_of_neg`（拉伸）+ 正性反证 |

```lean
-- 形态示例（I1；**已由 M5a 交付者实测跑通**，见 proofs/probes/marcus-prover_c-scratch.lean 的 F1–F7）
-- ⚠️ 三处纠正（原计划写法不可编译，M5a 交付者实测）：
--   (1) `rw` 的方向**取决于改写对象里出现的是哪个符号**（M5a/M5b 交付者各实测一半，此处给统一规则）：
--       * 改写**假设** `h : Rat.zoneQ lam x = ...`（含 `zoneQ`）→ 用**正向** `rw [Rat.zoneQ_eq_zone] at h`
--         （规则的 LHS 是 `zoneQ`，能对上）；写 `←` 会报 `did not find instance of the pattern`。
--       * 改写**目标**里已有的 `zone ↑lam ↑x` → 用**反向** `rw [← Rat.zoneQ_eq_zone]`
--         （`←` 的模式是 `zone ↑?lam ↑?x`）。M5b 的 `normalRegion_of_zoneQ_normal` 正是这一支。
--       一句话：**看模式，不看直觉** —— `zoneQ` 在式子里就用正向，`zone ↑↑` 在式子里就用反向。
--   (2) cast 字面量 ≠ `OfNat` 字面量（**定义层不等**）：转移后 ℝ 侧参数是 `↑(1:ℚ)`，
--       直接 `exact (zone_eq_inverted_iff 1 3).mp h` 会 type mismatch
--       （`↑1 < ↑3` vs `(1:ℝ) < 3`）。出路：ℝ 侧参数写成 `((·:ℚ):ℝ)` 与引理结论逐字对齐，
--       或 `show (1:ℝ) < 3` + `exact_mod_cast` 桥接。
--   (3) `rw [← zoneQ_inverted_iff]` **不会展开 `InvertedRegion` 这个 def**（`rw` 不走 defeq）；
--       需先 `show` 出展开形态，而 `exact (…).mp/.mpr` 走 defeq、无此限制。
example : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : InvertedRegion ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) := by
  have h : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
  rw [Rat.zoneQ_eq_zone] at h              -- 正向（见纠正 (1)）
  exact (zone_eq_inverted_iff _ _).mp h

-- 形态示例（I2：含除法的有理字面量 —— **必须用 norm_num，不能用 decide**，
--   实测见 proofs/probes/marcus-statement-skeleton.lean 的 R1 与 proofs/API-NOTES.md）
example : Rat.zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [Rat.zoneQ]
example : ¬ InvertedRegion ((1 : ℚ) : ℝ) (((3 : ℚ) / 4 : ℚ) : ℝ) := by
  show ¬ (((1 : ℚ) : ℝ) < (((3 : ℚ) / 4 : ℚ) : ℝ))   -- 先 show 出展开形态（见纠正 (3)）
  rw [← Rat.zoneQ_inverted_iff]
  norm_num [Rat.zoneQ]

-- 形态示例（I6：判定"不符合"）
example : ¬ InvertedDescriptor 1 (-1/2) 1 1 :=
  descriptor_fails_of_nonpos_lam (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- 形态示例（I7：非物理分支满足描述但速率非正 ⇒ 实例被拒绝）
example : InvertedDescriptor (-1) (-1) 1 1 :=
  inverted_descriptor_holds_of_neg (by norm_num) (by norm_num) (by norm_num)
example : ¬ (∀ x, 0 < rate (-1) (-1) 1 1 x) := by
  intro h; have := h 0; norm_num [rate, barrier] at this
```

### 8.3 文献参数表（M5 的输入）—— 已回填（`proofs/LITERATURE.md` §实例参数候选表）

> **⚠️ 定量警示（决定实例层文案的边界，必须遵守）**：把 `lam=1.2`、`T=298.15 K` 代入经典公式，
> `x=2.0 → ΔG‡=0.1333` eV、`x=2.4 → ΔG‡=0.30` eV，相对速率从 `5.6×10⁻³` 掉到 `8.5×10⁻⁶`
> （**约 5 个数量级**）；而**实验只降约 2 个数量级** —— 即**经典公式在反转区下降过快**（这正是
> 量子振动修正/Bixon–Jortner 的动机，见 §1.3 与 §14）。
> 因此实例层的结论只能写成：**"该体系落在反转区，且经典 Marcus 模型在该 (lam, x, T, A) 上满足反转区描述"**；
> **不得**写成"该体系的反转区速率随驱动力递减"（那是对实验的断言，文献不支持其严格性）。
>
> **用文献的逐化合物数据做的定量对照（最锋利的证据）**：同一 MCC 系列内，
> `x: 1.23 → 2.40` eV（`lam = 1.20` eV，`T = 296 K` ⇒ `k_BT = 25.51` meV）时，
> **经典公式预言速率降 5.1 个数量级**（`7.86×10⁻⁶`），**实测只降 1.46 个数量级**（`3.5×10⁻²`）
> —— 经典公式**下降过快约 3.6 个数量级**（前置因子近似相同；`2×10⁹` 是仪器上限故实测降幅为下界、方向不变）。
> 这正是量子振动修正（Nobel Fig. 8 平滑曲线含 `ω = 1500 cm⁻¹`）存在的理由，也是 §1.3 把它列为"明确不做"的代价。

约定 `x := -ΔG°`；**区域判定只用 (lam, x)，与 T、A 无关**。只用 `已核实` 的条目进 Lean：

| 体系（来源：Marcus Nobel Lecture 1992 图/正文与 C&EN 1984-06-04 62(23):42–44，`proofs/LITERATURE.md` 逐条定位） | `lam`/eV | `x = -ΔG°`/eV | 实测 `k`/s⁻¹ | 判定 |
|---|---|---|---|---|
| MCC 联苯–androstane–2-naphthyl（10 Å，脉冲辐解） | 1.20 | 0.05 | ≈ 1.5×10⁶ | **深度正常区** |
| MCC 同上（最优/无势垒点） | 1.20 | 1.23 | ≳ 2×10⁹（仪器上限） | **边界**（`x ≈ lam`） |
| MCC 同上（2-(5,6-dichlorobenzoquinonyl)） | 1.20 | 2.40 | ≈ 7×10⁷ | **明显反转区** |
| MCC 同上（Nobel Fig. 8 左支读数） | 1.20 | 0.60 | — | **正常区** |
| 光合反应中心 BPh⁻→BChl₂⁺ 回传 | 0.25 | 1.10 | — | **反转区**（`x ≫ lam`） |

> **温度的处理（文献订正）**：C&EN 图注为 **296 K**，且图注写 THF、正文写 MTHF（**原文真实温度未核实**）。
> ⇒ 实例层**不要把某个温度当成实验事实**：`T` 作为**显式前提 `0 < T`**（区域判定与单调性都与 `T` 的具体值无关）；
> 若某条实例需要一个具体数值，写成"本实例取 T = 296 K 作为**建模选择**"。

基本常数（**精确值**，2019 SI 后 `k_B`、`e` 均为 exact）：`k_B·T(298.15 K) = 0.025693` eV。
实例层写成"本实例取 T = 298.15 K 作为**建模选择**，只需 `0 < k_B*T`"——
**不要声称 298.15 K 是某实验的真实温度**（区域判定与单调性与 T 的具体值无关）。

规划约束：文献只用于**确定参数取值**，不用于替代证明；`仅量级` 的条目**不进 Lean**。
每条参数标注核实状态（`已核实` / `凭记忆待人类复核` / `仅量级`）。

**实例层必须显式断言物理定义域**（verifier 在 M1/M4b 验收中提出的边界）：若某实例用到 `lamOuter`，
必须在实例定理里显式带上 `0 < a1`、`0 < a2`、`a1 + a2 ≤ R` 等定义域前提 ——
因为 `lamOuter_pos` 的前提在数学上并不排除负半径/负间距（结论仍为真），
**几何约定不在 Lean 语句里**，只能由实例层自己断言。

**验收**：`check.sh --strict PhotoLean.Marcus.Instances` PASS；`axioms.sh` 逐条干净；
**verifier 必须确认每个实例的"判断"确实由 `decide` / 定理实例化给出**，而不是注释里的声称。

---

## 9. 证明依赖图（关键路径加粗）

```text
M1 Basic ──► **M2 Barrier** ──► **M3 Rate** ──► **M4a Sharp** ──► M4b Reorg
   │
   ├──► M5a RatModel ──────────────┐
   └──────────────────────────────►┴──► M5b Instances
```

- 依赖 M3 的只有 M4a；依赖 M4a 的只有 M4b 与 M5b 的 I6/I7。
- M5a（ℚ 判定层）与 M4b（微观 λ）**只依赖 M1**，是与关键路径并行的两条支线。

---

## 10. Sprint 顺序与并行边界

**原则**：先啃最不可形式化的那一步（关键路径法）。本项目的风险集中在两处：
(a) `Real.exp` 的单调性 API 名字与方向（M3）；(b) 锐利性必要性方向里 `λ = 0` 的除零约定（M4a）。
**两者都排在最前**：Sprint 1 就要把它们打通，而不是等 M2 全绿。

| Sprint | 内容 | 属主（文件独占） | 并行度 |
|---|---|---|---|
| **S0（已收尾）** | `plan.md` 落盘 ✅、语句骨架 `proofs/probes/marcus-statement-skeleton.lean` 编译通过（31 sorry / 0 error）✅、`git init` + 基线 commit ✅、API 校准（`api_researcher`，进行中）、文献参数（`literature_researcher`，进行中） | lead | 3 路（lead + 2 researcher） |
| **S1** | M1 `Basic.lean`（关键路径起点）；M4b `Reorg.lean`（**零依赖**，只 import Mathlib，可与 Basic 同时开工） | prover_a / prover_d | 2 路并行（文件互不相交） |
| **S2** | M2 `Barrier.lean`（关键路径）；M3 `Rate.lean` 的**核心引理** `rate_gt_of_barrier_lt` + `rate_pos`（只依赖 M1）；M5a `RatModel.lean`（只依赖 M1） | prover_a / prover_b / prover_c | 3 路 |
| **S3** | M3 收尾（三条速率定理，依赖 M2）；M5b `Instances.lean` 的 I1–I3（依赖 M1+M5a） | prover_b / prover_c | 2 路 |
| **S4** | M4a `Sharp.lean`（`(⟸)` 先行，再攻必要性两支） | prover_a | 1 路（关键路径） |
| **S5** | M4c `Compose.lean`（依赖 Sharp+Reorg）；M5b 的 I4–I7（依赖文献表 + Sharp） | prover_d / prover_c | 2 路 |
| **S6** | 全量验收 + 每 lemma commit 复查 + 经验库回写 + 文献/API 日志归档 | verifier + lead | — |

**并行硬约束**：同一文件同一时间只有一个属主；跨 Sprint 交接 = verifier PASS + lead 更新
`proofs/TASKS.md` 的属主列。任何 `BLOCKED` 立即回写 `EXPERIENCE.md`（含失败路径）。

**工程配套（lead 负责）**：`lakefile.toml` 的 `defaultTargets` 随每个里程碑补入已交付模块
（否则裸跑 `check.sh --strict` 只构建 `PhotoLean.Smoke` —— **扫描覆盖全目录但构建不覆盖**，
这是一个必须堵住的验收漏洞）；`proofs/probes/` 目录随 S0 建立。

---

## 11. 验收标准（脚本级，不靠自觉）

每个里程碑的每一条定理，逐条执行契约 §3 的四步：

```bash
proofs/scripts/lake build <Module>                            # 1. 编译
proofs/scripts/check.sh --strict <Module>                     # 2. sorry/axiom 扫描 + 构建
proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>   # 3. #print axioms 只含基础设施公理
git log -1 --oneline                                          # 4. feat(<area>): <lemma>
```

- **任何一步都不能省**：`lake build` 对 `sorry` 与自定义 `axiom` **都返回 0**（见 `proofs/EXPERIENCE.md` 首条实测）。
- M5 额外要求：实例的判定证据必须是 `by decide` 或定理实例化，verifier 逐条复核。
- M4a 额外要求：verifier 独立复核 `descriptor_sharp` 的必要性两支（`λ = 0` 与 `λ < 0`）。

---

## 12. mathlib 适配清单（交 `api_researcher` 逐条落实 → `proofs/API-NOTES.md`）

| 类 | 清单 | 用途 |
|---|---|---|
| exp 层 | `Real.exp_lt_exp`（**方向**）、`Real.exp_le_exp`、`Real.exp_pos`、`Real.exp_neg`、`Real.exp_sub`、`Real.exp_zero`、`Real.exp_strictMono` | M3 核心引理、`rate_ratio` |
| 除法/序 | `div_lt_div_of_pos_right`、`div_lt_div_iff_of_pos_right`、`div_lt_iff`、`lt_div_iff`、`div_pos`、`one_div_pos`、`neg_lt_neg_iff`、`div_eq_mul_inv` | M2/M4b |
| 平方单调 | `sq_lt_sq`（形态/绝对值）、`pow_lt_pow_left₀`、`mul_self_lt_mul_self`、`sq_pos_of_ne_zero`、`sq_nonneg` | M2 全部 |
| 乘法/序 | `mul_lt_mul_of_pos_left`、`mul_pos`、`pos_of_mul_pos_right` | M3/M4a |
| ℚ 层 | `Rat.cast_lt`、`Rat.cast_le`、`Rat.cast_pos`、`Rat.cast_inj`；`by decide` 对 `(1:ℚ) < 3` 是否可算 | M5a 转移引理 |
| 策略 | `positivity`、`nlinarith`、`norm_num`、`ring_nf`、`field_simp`、`gcongr` | 全部 |

**规范**：本表的每一项都必须由 `api_researcher` 用 `proofs/probes/marcus-*-api.lean` 的
`#check` 实测后勾选；**未实测的名字禁止出现在证明里**。

---

## 13. 关键参考文献与显式物理近似

**参考文献**（已由 `literature_researcher` 回填，逐条核实见 `proofs/LITERATURE.md`）：
**Marcus 1960**（Discuss. Faraday Soc. 29, p.28 §(v)：**反转区的首次提出**）、
**Marcus 1956**（Eq. (38) p.974：势垒公式；p.971：`D_op = n²` 的明文定义 ⇒ 本形式化直接用 `nSq` 是**忠实**的而非简化）、
Marcus 1992 Nobel Lecture（Eq. (5b) p.78 印刷体势垒式；Eq. (6)/(7)）、
Miller–Calcaterra–Closs 1984（**DOI 10.1021/ja00322a058**, JACS 106(10) 3047–3049：反转区实验证据）。
⚠️ **未取到正文**（不得引用式号）：Marcus & Sutin 1985（Elsevier 付费）、Marcus 1964（403）——
work terms 的简化式仅由 secondary 来源支持，但结论不受影响（我们采用 `w_r = w_p = 0`，
该简化式已由 1992 Eq. (5b) 逐字核实）。
⚠️ **引用归属更正**：`(4πλk_BT)^(-1/2)` **不在** Marcus 1956 中（1956 是 `k = Z·exp(-ΔF*/kT)`，`Z` = 碰撞数）。

**必须显式化的物理近似（定理前提，不得藏在定义里）**：

| # | 近似 | 在 Lean 中的形态 |
|---|---|---|
| 1 | 抛物线（谐振）势能面、单一反应坐标 | `barrier` 的定义本身（在 plan 中声明） |
| 2 | 经典核运动（无核隧穿） | 速率取 Arrhenius 形式 `A·exp(-ΔG‡/(kBT))` |
| 3 | Condon 近似 / 电子耦合与核坐标无关 | 前置因子 `A` 与驱动力 `x` 无关（`rate` 的定义） |
| 4 | 温度为正、`k_B > 0` | 定理前提 `0 < kB`、`0 < T` |
| 5 | 速率常数为正（前置因子正） | 定理前提 `0 < A`（**M4a 证明它不可去**） |
| 6 | 重组能为正 | 定理前提 `0 < λ`，在 M4b 中由 `λ_in + λ_out` 与 Pekar 因子正性**推出** |
| 7 | 外层重组能的两球连续介质模型 | `lamOuter` 的定义 + 前提 `0 < nSq`、`0 < εs`、`1/εs < 1/nSq`、`hgeom` |
| 8 | **work terms 取零**：`w_r = w_p = 0`（综述级完整式含 `w_r, w_p`，本形式化隐含它们为 0） | 显式写入文档与定理注释；将来若要保留需新增前提 |
| 9 | 前置因子与驱动力无关 | `rate` 的定义（`A` 不依赖 `x`）。**稳健性备注**：若改用 TST 前置因子 `(4·π·lam·τ)^(-1/2)·κ·ν`，它只是与 `x` 无关的**正**因子 ⇒ 全部单调性与锐利性结论**不变**（文献 §附） |

---

## 14. 完成后的下一站（预览，不在 M1–M5 范围；排序依据见 `proofs/LITERATURE.md` §不可表达清单排序）

**优先级（按"对 M1–M5 的影响 × 实现成本"）**：
① **Franck–Condon 因子/振动重叠积分** —— 对 M1–M5 影响为零，但是量子修正的直接前置，
且 mathlib 已有 `Lp`/Hilbert 空间/特殊函数基础可复用 ⇒ **低成本高收益，建议先做**；
② Marcus 交叉关系 —— 形式上是 `Real.sqrt` 层代数恒等式（**可表达**），但真正障碍是它依赖"同 `lam`"假设
⇒ 若要做必须写成**前提**而非定理（**最便宜但最容易做出过强主张**的一项）；
③ Fermi 黄金规则 + 振动热浴无穷求和 —— 需在 ① 之后自建配分函数层（mathlib 无）；
④ 电子耦合指数衰减/超交换 —— 无量子力学谱理论应用层；
⑤ **溶剂静电学第一性推导 —— 建议永久排除**（mathlib 无 PDE/边值问题库；`lamOuter` 保持为定义是对的）。

**量纲警告**：mathlib 无单位系统，**量纲错误不会被内核拦住** —— 只能靠实例层的注释与 `#check` 人眼复核（§13）。


- **量子振动修正**：Bixon–Jortner 型速率（振动模式求和使反转区饱和）—— 需要无穷级数与
  振动配分函数，是"反转区为何在实验中被削弱"的下一步。
- **温度依赖的量化**：`rate_ratio` 的完整热力学形式与活化参数的显式表达。
- **Marcus 交叉关系**与电子耦合的指数衰减（`V(R) = V₀ exp(-β(R-R₀))`）。
