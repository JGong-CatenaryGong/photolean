# RESULTS.md — Marcus 反转区的形式化：三部分需求的机器可检查答复

> 本文件是**面向人类提问的答复**（不是引擎的叶子数据面）。契约与规划见 `proofs/ENGINE.yml`
> 与 `plan.md`；状态真源是 `proofs/TASKS.md`；验收证据由 `proofs/scripts/*.sh` 产出。
>
> 提问：*"marcus 反转区理论如何形式化为一个可以通过 lean 证明或者验证的理论？
> 这个工作分为三个部分：第一，把 marcus 反转区转化为形式化描述；
> 第二，证明这个描述或者找到这个描述的成立条件；
> 第三，用一些实例代入这个形式化理论，判断该实例是否会符合 marcus 反转区的描述。"*
>
> 本文档按这三部分逐条回答，**每条结论都可被仓库内的一条命令复核**。

---

## 0. 一句话结论

经典马库斯反转区被形式化为"**抛物线势垒上的速率单调性**"，其**成立条件是锐利的**：

```
(∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T   ⟺   0 < A ∧ 0 < lam
```

即：**只要前置因子为正、重组能为正**（温度为正作为显式物理前提），反转区内"驱动力越大速率越小"
就成立；**每一项都不可去** —— 这不是我们的断言，而是被证明的等价式，其中"速率正性"必须
**并入左边**才构成充要条件（见 §2.3 的规划期发现与反例）。

**证明零 `sorry`、零自定义公理**：全部已交付定理的 `#print axioms` 只含
`propext` / `Classical.choice` / `Quot.sound`。判定由脚本执行，不由模型自称。

---

## 1. 第一部分：把"马库斯反转区"转化为形式化描述

**载体**：`ℝ` 上的初等代数 + 一个实分析工具（`Real.exp` 的单调性）。不造新内核、不引入新公理。

### 1.1 描述层的对象（`PhotoLean/Marcus/Basic.lean`）

| 形式化对象 | 定义 | 物理含义 |
|---|---|---|
| `barrier lam x := (lam - x)^2 / (4*lam)` | 势垒 | `ΔG‡ = (λ - x)²/(4λ)`，`x := -ΔG°` 为驱动力、`lam := λ` 为重组能 |
| `rate A lam kB T x := A * Real.exp (-(barrier lam x) / (kB*T))` | 速率 | Arrhenius/Eyring 型，`A` 前置因子、`kB*T` 热能 |
| `InvertedRegion lam x := lam < x` | 反转区 | 驱动力超过重组能 |
| `NormalRegion lam x := x < lam` | 正常区 | 驱动力小于重组能 |
| `InvertedDescriptor A lam kB T := ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate … x₂ < rate … x₁` | **反转区描述** | 反转区内速率随驱动力**严格递减** |
| `NormalDescriptor` | 对偶谓词 | 正常区内速率随驱动力**严格递增** |
| `Zone`（`normal`/`barrierless`/`inverted`）+ `zone : ℝ → ℝ → Zone` | 区域分类器 | 把 `(lam, x)` 判到三个区（`x = lam` 为无势垒点） |

**三个关键设计决定**（都由实测驱动，不是风格偏好）：
1. **描述写成谓词而非"一条曲线定理"** —— 因为"找到成立条件"需要 `¬ InvertedDescriptor`（反例判定）与合取（正性），
   谓词形态让这两件事都可表达；分类器则让"判断某实例属于哪个区"变成**可计算等式**。
2. **Lean 标识符一律 ASCII**（`lam` 而非 `λ`）—— Lean 4 里 `λ` 是 lambda 关键字，**不能作标识符**（实测 parse error）。
3. **除零约定显式声明** —— `barrier 0 x = 0`（因 Lean 取 `x/0 = 0`）。这一个约定制造出 `lam = 0` 的退化分支，
   是"锐利性"证明里最容易被漏掉的一支（见 §2.3）。

### 1.2 判定层（`PhotoLean/Marcus/RatModel.lean`）

`ℝ` 上的序不可计算（需要 `Classical`），故在 `ℚ` 上复制一份**可计算**的分类器：

```lean
def zoneQ (lam x : ℚ) : Zone := if x < lam then .normal else if x = lam then .barrierless else .inverted
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)   -- 转移引理
```

**转移引理是"实例判定"对 `ℝ` 理论有约束力的唯一桥梁**：内核在 `ℚ` 上算出的判定值，
经它搬到 `ℝ` 定理层。实测边界（`proofs/API-NOTES.md`）：`decide` 对**整数**字面量可算，
对**含除法/十进制**的有理字面量会卡在 `Rat` 的 gcd 归约上 → 必须用 `norm_num`。

---

## 2. 第二部分：证明描述，并找到它的成立条件

### 2.1 势垒代数（`PhotoLean/Marcus/Barrier.lean`，9 条）

`barrier` 的**完整单调性图景**（三种 `lam` 符号 × 两个区域）：

| 情形 | 结论 | 定理 |
|---|---|---|
| `0 < lam`，反转区 | 势垒**严格递增**（反转区的代数内核） | `barrier_mono_of_pos` |
| `0 < lam`，正常区 | 势垒**严格递减** | `barrier_antitone_of_pos` |
| `lam < 0`，反转区 | 方向**反转**：势垒递减（锐利性必要支） | `barrier_antitone_of_neg` |
| `lam = 0` | 除零约定 ⇒ 势垒恒为零（另一必要支） | `barrier_zero_lam` |
| `0 < lam` | `lam` 处**全局最小**（无势垒点）+ 抛物线对称 | `barrier_min_at_lam`、`barrier_symm` |
| 全部 | 非负、`lam` 处为零、四情形穷尽 | `barrier_nonneg`、`barrier_at_lam`、`barrier_mono_cases` |

### 2.2 速率层（`PhotoLean/Marcus/Rate.lean`，6 条）

全项目**唯一的实分析风险**被隔离在一条引理里：

```lean
theorem rate_gt_of_barrier_lt (hA : 0 < A) (hkT : 0 < kB * T) (h : barrier lam x < barrier lam y) :
    rate A lam kB T y < rate A lam kB T x
```

其余五条都是"势垒单调性 + 这条引理"的组合：`rate_pos`（速率正）、`normal_rate_increases`（正常区速率升）、
`inverted_rate_decreases`（**反转区速率降**）、`rate_peak_at_lam`（峰值在 `x = lam`）、
`rate_ratio`（抑制因子的指数形式，拉伸项）。

### 2.3 成立条件：锐利刻画（`PhotoLean/Marcus/Sharp.lean`，9 条）

**主定理**：

```lean
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam
```

**规划期发现（本项目的物理内核）**：如果只写 `InvertedDescriptor`（不要正性那一项），
它**推不出** `lam > 0` —— 反例 `A < 0 ∧ lam < 0 ∧ kB*T > 0`：`lam<0` 使势垒在反转区**递减**，
于是 `exp(-Φ/(kBT))` 递增、乘上负的 `A` 后**严格递减** ⇒ 描述成立，**但速率是负的**。
所以必须把"速率正性"并入刻画。这个反例被保留成一条定理作为证据：

```lean
theorem inverted_descriptor_holds_of_neg (hA : A < 0) (hkT : 0 < kB * T) (hlam : lam < 0) :
    InvertedDescriptor A lam kB T          -- 描述成立（但速率非正 ⇒ 不可采纳）
```

**必要性的三分支结构**（逐条可验，`lam = 0` 支被**单独**覆盖，不会与 `lam < 0` 支混淆）：

| 分支 | 内核 | 机理 |
|---|---|---|
| 速率正 ⇒ `A > 0` | `sharp_A_pos` | 在 `x = lam` 处 `0 < A * exp(…)` 且 `exp > 0` |
| `lam < 0` ⇒ 矛盾 | `sharp_lam_pos_of_lt` | 势垒递减 ⇒ 速率递增，与描述要求的递减冲突 |
| `lam = 0` ⇒ 矛盾 | `sharp_lam_pos_of_eq` | 除零约定 ⇒ 速率恒为 `A` ⇒ 得 `A < A`（**签名里无任何正性前提**） |
| 组装 | `sharp_lam_pos` | `rcases lt_trichotomy lam 0` 三支真分支 |

`#print` 的证明项确认三支都出现在项里；在 `lam = 0` 处的实例化 `¬ InvertedDescriptor 1 0 1 1`
由内核造出，必然经过中间支。配套：`inverted_descriptor_holds`、`normal_descriptor_holds`、
`descriptor_fails_of_nonpos_lam`（`lam ≤ 0` ⇒ 描述失效）。

### 2.4 成立条件的"微观化"（`PhotoLean/Marcus/Reorg.lean` + `Compose.lean`）

把 `lam > 0` 从**假设**降级为**推导**：

```
lam = lamIn + lamOut
lamOut = dE² · (1/(2·a1) + 1/(2·a2) - 1/R) · (1/nSq - 1/epsS)      -- 两球连续介质（Pekar 形式）
```
- `lamInner_nonneg` / `lamInner_pos` / `lamTotal_pos`：内层非负（可为零）；
- `lamOuter_pos`：**Pekar 因子正性**（`1/epsS < 1/nSq` ⟺ `n² < ε_s`）**加上**几何因子正性 ⇒ 外层为正；
- `hgeom_of_nonoverlap`：几何因子正性其实**可由"两球不重叠"推出**（`a1 + a2 ≤ R` ⇒ `1/R < 1/(2a1)+1/(2a2)`），
  即把一条假设变成一条**推导**；
- `descriptor_holds_of_microscopic`：微观正性 ⇒ 主定理前提成立 ⇒ **反转区描述成立**。

**诚实边界**：`lam = lamIn + lamOut` 的可加性是**建模假设**（源自把坐标集分成内层/外层 + 配分函数因子化），
不是定理；Pekar 公式作为**定义/前提**给出，不做溶剂静电学的第一性推导（见 §5）。

### 2.5 验收（脚本级，不靠自觉）

```bash
proofs/scripts/check.sh --strict <Module>                     # 构建 + 全目录 sorry/axiom 扫描
proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>   # #print axioms 只含基础设施公理
```
`lake build` 返回 0 **不构成**通过（`sorry`/自定义 `axiom` 都返回 0）；三层（构建 + 扫描 + `#print axioms`）
齐备并由**不写证明的角色**独立执行。各里程碑的 verifier 判决与证据见 `proofs/TASKS.md` 的"验收记录"表。

---

## 3. 第三部分：实例代入与判定

### 3.1 判定机制（三条独立证据链）

| 链 | 形态 | 用途 |
|---|---|---|
| 内核计算 | `by decide`（整数参数）/ `norm_num [Rat.zoneQ]`（含除法） | `ℚ` 层区域判定 |
| 转移引理 | `Rat.zoneQ_eq_zone`、`zoneQ_inverted_iff`、`normalRegion_of_zoneQ_normal`、`not_invertedRegion_of_zoneQ_normal` | 把判定搬到 `ℝ` 定理层 |
| 定理实例化 | `inverted_descriptor_holds`、`descriptor_fails_of_nonpos_lam`、`inverted_rate_decreases` … | 判定"是否**符合描述**" |

### 3.2 实例与判定结论（`PhotoLean/Marcus/Instances.lean`）

| # | 实例 | 判定 | 证据 |
|---|---|---|---|
| I1 | `lam = 1, x = 3`（纯数） | **在反转区** | `decide` 算 `zoneQ` + 转移引理 |
| I2 | `lam = 1, x = 3/4` | **不在反转区**（正常区） | `norm_num [zoneQ]` + 排除反转区引理 |
| I3 | 文献 MCC 系列的无势垒点 `lam = 1.20, x = 1.23` | **在反转区**（边界侧）；且 `barrier 1.20 1.23 = 0.0001875` **与文献 `ΔG‡ ≈ 0.0002 eV` 吻合** | `norm_num [barrier]` + 转移引理 |
| I4 | 文献 MCC 系列高放能支：`x = 2.40`（与 `2.00`） | **明显反转区** | 文献参数 + 转移引理 |
| I5 | 文献 MCC 系列正常支：`x = 0.60` | **不在反转区**（正常区） | 同上 + 排除反转区引理 |
| I6 | 文献光合反应中心：`lam = 0.25, x = 1.10` | **深反转区**（`x ≫ lam`） | 同上 |
| I7 | 非物理参数（`lam = -1/2`；及 `A = -1 ∧ lam = -1`） | **不符合 / 不可采纳** | *（batch 2 交付中）* 依据已就绪：`descriptor_fails_of_nonpos_lam`；`inverted_descriptor_holds_of_neg` + 速率非正反证 |

> 每条实例都是**有名字的定理**（可被 `axioms.sh` 单独复核），不是注释里的声称。

### 3.3 文献参数（可核查来源）

`lam = 1.20` eV（Miller–Calcaterra–Closs 联苯–androstane–受体自由基负离子，10 Å，`lam_s = 0.75 + lam_v = 0.45`）；
`x = 1.23 / 2.00 / 2.40 / 0.60` eV；光合反应中心 `lam = 0.25, x = 1.10` eV。
逐条定位（图/页/DOI）见 `proofs/LITERATURE.md`。区域判定**只用 `(lam, x)`，与 `T`、`A` 无关**，
故 `T` 作为显式建模选择而非"实验事实"（原文温度未核实）。

### 3.4 ⚠️ 实例层文案的边界（必须与结论一起报告）

用同一批文献的**逐化合物实测速率**做定量对照：`x: 1.23 → 2.40` eV（`lam = 1.20` eV，`T = 296 K`）时，
**经典公式预言速率降 5.1 个数量级，实测只降 1.46 个数量级** —— 经典公式**下降过快约 3.6 个数量级**。
因此实例的判定结论**只能**表述为：

> "该体系落在反转区，且**经典 Marcus 模型**在该 `(lam, x, T, A)` 上满足反转区描述"，

**不能**表述为"该体系的反转区速率随驱动力递减"（那是对实验的断言，文献不支持其严格性）。
这正是量子振动修正（Bixon–Jortner 型）存在的理由，也是本项目**明确不做**的部分。

---

## 4. 明确不声称的事（诚实边界清单）

1. **不声称预测实测速率**：只声称经典模型在给定参数上满足反转区描述（§3.4 的定量对照）。
2. **不声称量子效应**：无核隧穿、无振动模式求和；经典模型下反转区是**严格单调下降**。
3. **不做竞争反应通道**：只刻画单一机理（原始文献自带免责："unless a more favourable reaction mechanism is found"）。
4. **`lam = 0` 分支依赖除零约定**：`x/0 = 0` 是 Lean 的**形式约定**，不是物理事实（已列入 `plan.md` §13 第 10 条）。
5. **几何约定不在 Lean 语句里**：`lamOuter_pos` 的前提在数学上不排除负半径/负间距 ⇒ 实例层若用到 `lamOuter`
   必须**显式断言物理定义域**。
6. **`zone_trichotomy` 强度弱**：它对任意 `ℝ→ℝ→Zone` 函数都成立；真正钉住语义的是三条 `zone_eq_*_iff`
   （穷尽且一致）。文档不得夸大前者的作用。
7. **量纲不被内核检查**：mathlib 无单位系统，单位错误只能靠实例注释与人工复核。

---

## 5. 复核方式（任何人都可复跑）

```bash
cd <repo>
proofs/scripts/check.sh --strict                # 全树扫描 + 构建（应输出 verdict: PASS）
proofs/scripts/lake env lean proofs/probes/marcus-all-axioms.lean      # ★ 一次命令体检全部定理的公理
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp   # 单条定理的公理
proofs/scripts/lake env lean proofs/probes/marcus-statement-skeleton.lean           # 语句权威
```

**结构审计（每个定义是否都被至少一条定理约束）**：对全部 10 个定义做词边界引用统计 ——
`barrier`(44 处)、`rate`(40)、`InvertedRegion`(21)、`zoneQ`(24)、`InvertedDescriptor`(16)、
`zone`(14)、`lamInner`(9)、`lamOuter`(8)、`NormalRegion`(7)、`NormalDescriptor`(1，即其自身的描述定理)。
**唯一"未被任何定理约束"的定义是 `barrierQ`** —— M3+M5a verifier 独立发现同一问题（发现 (b)），
已补上数值桥 `barrierQ_cast : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam:ℝ) (x:ℝ)`，
使 ℚ 侧势垒数值有资格作为 ℝ 理论层的证据。

**全量体检结果（2026-09-20，8 个模块 / 55 条定理）**：`marcus-all-axioms.lean` 一次运行输出 **55 条
`depends on axioms`、0 error**；其中 **54 条恰为 `[propext, Classical.choice, Quot.sound]`**，
1 条（`inst_I1_zoneQ`）**只依赖 `[propext]`**（允许集合的子集）。**无 `sorryAx`、无自定义公理、
无 `Lean.ofReduceBool`**（即无 `native_decide`）。该探针由脚本从源码树自动生成，含 `namespace` 解析，
新增定理后可重新生成。
语句权威是 `proofs/probes/marcus-statement-skeleton.lean`（全部语句在此先行编译通过）；
`PhotoLean/Marcus/*.lean` 的签名与它**逐字一致**（各里程碑由 verifier 用脚本机械比对）。

> **并发提示**：`check.sh --strict` 的扫描覆盖整个 `PhotoLean/`。若有人正在写文件，裸跑全量门可能出现
> **瞬时 FAIL/PASS**；稳定通道是逐模块 `check.sh --strict <Module>`，最终结论须在**冻结提交**上重跑。
