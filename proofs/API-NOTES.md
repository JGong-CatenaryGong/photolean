# mathlib API 校准日志

规则：

- prover 遇到不确定的 lemma 名时**不得猜测**，把问题交给 `api_researcher`。
- 每条记录格式：`## <日期> — <主题> — <校准人> — <结论>`（附 `#check` 输出、源码位置或链接）。
- `#check` 探针统一放 `theories/Marcus/probes/`，用 `proofs/scripts/lake env lean theories/Marcus/probes/<name>.lean` 运行；
  探针文件可提交（它们也是文档）。
- 校准只针对"名字/签名"层；语句/证明改动由对应 prover 执行并在此留痕。
- **mathlib 版本：v4.17.0**（rev 见 `lakefile.toml`）。名字漂移以此为基准。

**本轮（2026-09-20，Marcus 反转区）探针清单 —— 全部 0 error / 0 warning：**

| 探针 | 覆盖 | 运行 |
|---|---|---|
| `theories/Marcus/probes/marcus-exp-api.lean` | A 组（exp 层）+ D 组（乘法/序） | `proofs/scripts/lake env lean theories/Marcus/probes/marcus-exp-api.lean` |
| `theories/Marcus/probes/marcus-order-api.lean` | B 组（除法/序）+ C 组（平方/幂）+ E 组（单调性包装） | 同上换文件名 |
| `theories/Marcus/probes/marcus-tactic-api.lean` | F 组（ℚ/cast）+ G 组（战术可用性实测） | 同上 |
| `theories/Marcus/probes/marcus-ident-rat-api.lean` | 标识符禁止清单 + `decide` 对 ℚ 的可靠域 + lead 风险探针独立复核 | 同上 |
| `theories/Marcus/probes/marcus-proof-skeletons.lean` | **M1–M5a 全部定理的证明体**（36 个 theorem，无 sorry） | 同上 |
| `theories/Marcus/probes/marcus-api-closeout.lean` | **收尾追加复核**：`≤` 版引理 / `rate_ratio` 链 / `decide` 域 / plan §8.2 三处纠正 | 同上 |
| `theories/Marcus/probes/marcus-api-cast-normnum.lean` | **收尾追加复核（第 2 批）**：`Rat.cast_*` 家族 / `norm_num` 边界 / 倒数与交叉相乘 / `field_simp` 失败路径 | 同上 |

> `theories/Marcus/probes/marcus-statement-skeleton.lean` 是**语句权威**（lead 所有，含 sorry 占位）；
> `marcus-proof-skeletons.lean` 是它的**可编译完成版**，签名逐字一致、只补证明体。

---

## 禁止使用清单（不存在 / 已漂移 / 签名不符）

**A. 不存在（`unknown constant` / `unknown identifier`）—— 禁止出现在证明里：**

| 禁止名 | 实测报错 | 替代 |
|---|---|---|
| `Real.exp_lt_exp_iff` | `unknown constant` | **`Real.exp_lt_exp`**（它本身就是 `↔`！） |
| `Real.exp_le_exp_iff` | `unknown constant` | **`Real.exp_le_exp`**（本身是 `↔`） |
| `sq_lt_sq_iff` | `unknown identifier` | `sq_lt_sq₀` / `sq_lt_sq` / 裸 `nlinarith` |
| `strictMonoOn_iff` | `unknown identifier` | `Set.strictMonoOn_iff_strictMono`（语义不同，见 E 组）；或直接写 `intro a ha b hb hab` |
| `Rat.cast_pos_iff` | `unknown constant` | **`Rat.cast_pos`**（本身是 `↔`） |
| `Rat.cast_lt_cast` | `unknown constant` | `Rat.cast_lt` |
| `div_lt_div_iff_of_neg_right` | `unknown identifier` | `div_lt_div_right_of_neg`（**iff，右边是 `b < a`**） |
| `div_lt_div_of_neg_right` | `unknown identifier` | `div_lt_div_right_of_neg`；或 `div_lt_iff_of_neg` / `lt_div_iff_of_neg`；或 L5 的 `div_neg` 路线 |
| `div_lt_div_iff_of_neg_left` / `div_lt_div_of_neg_left` | `unknown identifier` | 同上；或 `div_lt_iff_of_neg` / `lt_div_iff_of_neg`；或 L5 的 `div_neg` 路线 |
| `strictAntiOn_inv` / `strictMonoOn_inv` | `unknown identifier` | 不存在；自己 `intro` + 序引理 |
| `div_neg_neg` | `unknown identifier` | `neg_div_neg_eq` |
| `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` | `invalid field notation` | 点记法不可用；手写 `intro a ha b hb hab` |
| `Real.mul_pos` | `@[deprecated mul_pos (since := "2024-08-15")]` | `mul_pos` |

**B. 已漂移（旧名 → 新名，旧名仍能编译但会 warning；新代码用新名）：**

| 旧名（deprecated） | 新名 | since | 源码 |
|---|---|---|---|
| `div_lt_iff` | **`div_lt_iff₀`** | 2024-10-02 | `Mathlib/Algebra/Order/Field/Basic.lean:37` |
| `lt_div_iff` | **`lt_div_iff₀`** | 2024-10-02 | `Mathlib/Algebra/Order/Field/Basic.lean:31` |
| `div_lt_div_right` | **`div_lt_div_iff_of_pos_right`** | 2024-11-12 | `Mathlib/Algebra/Order/Field/Basic.lean:172` |
| `div_lt_div_left` | **`div_lt_div_iff_of_pos_left`** | 2024-11-13 | 同上 |
| `pow_lt_pow_left` | **`pow_lt_pow_left₀`** | 2024-11-13 | `Mathlib/Algebra/Order/Ring/Basic.lean:99` |
| `pow_left_strictMonoOn` | **`pow_left_strictMonoOn₀`** | 2024-11-13 | 同上 |
| `lt_of_mul_self_lt_mul_self` | **`lt_of_mul_self_lt_mul_self₀`** | 2024-11-12 | `Mathlib/Algebra/Order/Ring/Basic.lean:194` |
| `Real.mul_pos` | **`mul_pos`** | 2024-08-15 | `Mathlib/Data/Real/Basic.lean:344` |

**C. 标识符禁止清单（实测，2026-09-20）：**

Lean 4 **保留 token 不能作标识符**，报错统一为 `error: unexpected token '<tok>'; expected '_' or identifier`。
实测**禁止**的 20 个：

```
λ  Π  Σ  ↓  ←  →  ↔  ∀  ∃  ∧  ∨  ¬  ≠  ≤  ≥  ∑  ∏  ∫  ∈  ⊆
```

实测**合法**的 30 个（可作绑定名，`example (ε : ℝ) : ε = ε := rfl` 通过）：

```
Λ  α  β  γ  Γ  δ  Δ  ε  ζ  η  θ  Θ  ι  κ  μ  ν  ξ  Ξ  π  ρ  σ  τ  υ  φ  Φ  χ  ψ  ω  Ω
```

- **`λ` 绝对不能用**（`(λ x : ℝ)` → `unexpected token 'λ'`）；`Λ`（大写）合法。
- 小写 `π` / `σ` 合法，但大写 `Π` / `Σ`（依值积/和记号）禁止。
- `ε` / `δ` / `Δ` / `μ` **合法** —— prover 若想用它们做物理量名是可以的；
  但本项目统一 ASCII 化（`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`）。

---

## 待校准清单

### A 组 — exp 层（M3 关键路径）

- [x] `Real.exp_lt_exp` — **存在**，且是 **`↔`**（不是 `→`）：`Real.exp x < Real.exp y ↔ x < y`。用作 `.mpr h` / `.mp h` / `rw [Real.exp_lt_exp]`
- [x] `Real.exp_le_exp` — **存在**，同样是 `↔`：`Real.exp x ≤ Real.exp y ↔ x ≤ y`
- [x] `Real.exp_le_exp_of_le` — 存在，`→` 版：`(h : x ≤ y) : exp x ≤ exp y`（收尾追加归档）
- [x] `Real.exp_le_exp_iff` — **不存在**（`Real.exp_le_exp` 已经是 iff；收尾追加复核）
- [x] `Real.exp_lt_exp_iff` — **不存在**（`Real.exp_lt_exp` 已经是 iff）
- [x] `Real.exp_pos` — 存在，`(x : ℝ) : 0 < Real.exp x`
- [x] `Real.exp_nonneg` — 存在，`(x : ℝ) : 0 ≤ Real.exp x`
- [x] `Real.exp_neg` — 存在，`exp (-x) = (exp x)⁻¹`
- [x] `Real.exp_sub` — 存在，`exp (x - y) = exp x / exp y`
- [x] `Real.exp_add` — 存在，`exp (x + y) = exp x * exp y`
- [x] `Real.exp_zero` — 存在，`exp 0 = 1`
- [x] `Real.exp_strictMono` — 存在，`StrictMono Real.exp`
- [x] `Real.exp_monotone` — 存在，`Monotone Real.exp`

### B 组 — 除法/序（M3 关键路径）

- [x] `div_lt_div_of_pos_right` — 存在，`(h : a < b) (hc : 0 < c) : a / c < b / c`
- [x] `div_lt_div_iff_of_pos_right` — 存在，**iff**，`(hc : 0 < c) : a / c < b / c ↔ a < b`
- [x] `div_lt_iff` — **已漂移** → `div_lt_iff₀`
- [x] `lt_div_iff` — **已漂移** → `lt_div_iff₀`
- [x] `div_pos` — 存在，`(ha : 0 < a) (hb : 0 < b) : 0 < a / b`
- [x] `one_div_pos` — 存在，**iff**：`0 < 1 / a ↔ 0 < a`（`inv_pos` 同形）
- [x] `neg_lt_neg_iff` — 存在，**iff**：`-a < -b ↔ b < a`（注意右边是 `b < a`）
- [x] `neg_div` — 存在，**参数顺序反直觉**：`(a b : R) : -b / a = -(b / a)`
- [x] `div_neg` — 存在，`{b} (a : R) : a / -b = -(a / b)`
- [x] `div_nonneg` — 存在，`(ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b`
- [x] `div_eq_mul_inv` — 存在，`a / b = a * b⁻¹`
- [x] `mul_div_assoc` — 存在，`a * b / c = a * (b / c)`
- [x] `div_lt_div_iff_of_neg_right` — **不存在** → 用 `div_lt_div_right_of_neg`（判断见记录 B-4）
- [x] `div_lt_div_of_neg_right` — **不存在**（收尾追加复核；见记录 B-5）
- [x] `div_lt_div_right_of_neg` — 存在，**iff**：`(hc : c < 0) : a / c < b / c ↔ b < a`（右边顺序反转）
- [x] `div_lt_iff_of_neg` / `lt_div_iff_of_neg` — 存在（负分母的 iff）
- [x] `div_le_div_of_nonneg_right` — 存在，`(hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c`（`≤` 版，M3 峰值用）
- [x] `one_div_le_one_div_of_le` — 存在，**取倒数翻转方向**：`(ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a`（收尾第 2 批补录，见记录 D-3）
- [x] `div_lt_div_iff₀` — 存在，**两个参数都是分母正性**：`(hb : 0 < b) (hd : 0 < d) : a/b < c/d ↔ a*d < c*b`（见记录 D-4）
- [x] `div_lt_iff₀` — 存在，`(hc : 0 < c) : b / c < a ↔ b < a * c`（见记录 D-4）

### C 组 — 平方/幂单调

- [x] `sq_lt_sq` — 存在，是**绝对值**版 `a^2 < b^2 ↔ |a| < |b|`
- [x] `sq_lt_sq_iff` — **不存在**
- [x] `sq_le_sq` — 存在，`a^2 ≤ b^2 ↔ |a| ≤ |b|`
- [x] `sq_lt_sq₀` — **存在，`0 ≤ a < b ⇒ a^2 < b^2` 的最省事引理**：`(ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b`
- [x] `sq_le_sq₀` — 存在，`(ha) (hb) : a^2 ≤ b^2 ↔ a ≤ b`
- [x] `sq_pos_of_ne_zero` — 存在，**`a` 是隐式参数**：`{a : R} : a ≠ 0 → 0 < a ^ 2`
- [x] `sq_nonneg` — 存在，`(a : α) : 0 ≤ a ^ 2`
- [x] `sq_eq_zero_iff` — 存在，`a^2 = 0 ↔ a = 0`
- [x] `pow_lt_pow_left₀` — 存在，`(hab : a < b) (ha : 0 ≤ a) {n : ℕ} : n ≠ 0 → a^n < b^n`
- [x] `pow_lt_pow_left` — **已漂移** → `pow_lt_pow_left₀`
- [x] `mul_self_lt_mul_self` — 存在，`(ha : 0 ≤ a) (hab : a < b) : a * a < b * b`（结论是 `*` 不是 `^`，需 `simpa only [pow_two]`）
- [x] `sq_lt_sq'` — 存在，`(h1 : -b < a) (h2 : a < b) : a^2 < b^2`

### D 组 — 乘法/序

- [x] `mul_lt_mul_of_pos_left` — 存在，`(bc : b < c) (a0 : 0 < a) : a * b < a * c`
- [x] `mul_lt_mul_of_pos_right` — 存在，`(bc : b < c) (a0 : 0 < a) : b * a < c * a`
- [x] `mul_pos` — 存在
- [x] `mul_nonneg` — 存在
- [x] `mul_lt_mul₀` — 存在，`(hab : a < b) (hcd : c < d) : a * c < b * d`
- [x] `pos_of_mul_pos_left` / `pos_of_mul_pos_right` — 存在（取左/右因子，**极易写反**，见记录 D-2）
- [x] `mul_lt_mul_of_neg_left` — 存在，签名 `(h : b < a) (hc : c < 0) : c * a < c * b`
- [x] `mul_le_mul_of_nonneg_left` — 存在，`(h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c`（`≤` 版，M3 峰值用）
- [x] `mul_div_mul_left` — 存在，`(a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b`（M3 `rate_ratio` 用）
- [x] `mul_neg_of_neg_of_pos` — 存在，`(ha : a < 0) (hb : 0 < b) : a * b < 0`（M4a 备用 verifier 用它证 `rate (-1) (-1) 1 1 x < 0`）

### E 组 — 单调性包装

- [x] `StrictMonoOn` / `StrictAntiOn` / `MonotoneOn` — 存在（`Mathlib/Order/Monotone/Defs.lean:83`）
- [x] `StrictMonoOn.lt_iff_lt` / `StrictAntiOn.lt_iff_lt` — 存在，**iff 版，实用**
- [x] `strictMonoOn_iff` — **不存在**（真名 `Set.strictMonoOn_iff_strictMono`，语义是"子类型上的 StrictMono"，对 `Ici`/`Iic` 上的单调无用）
- [x] `strictMonoOn_mul_self` — 存在，`StrictMonoOn (fun x => x * x) {x | 0 ≤ x}`
- [x] `pow_left_strictMonoOn₀` — 存在，`(hn : n ≠ 0) : StrictMonoOn (· ^ n) {a | 0 ≤ a}`
- [x] `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` — **不可用**（点记法报错）

### F 组 — ℚ 层与转移

- [x] `Rat.cast_lt` — 存在，**iff**，`↑p < ↑q ↔ p < q`
- [x] `Rat.cast_le` — 存在，**iff**
- [x] `Rat.cast_pos` — 存在，**iff**，`0 < ↑q ↔ 0 < q`
- [x] `Rat.cast_pos_iff` — **不存在**
- [x] `Rat.cast_mk` — 存在，`(a b : ℤ) : ↑(Rat.divInt a b) = ↑a / ↑b`（注意是 `Rat.divInt` 形式）
- [x] `Rat.cast_inj` / `Rat.cast_div` / `Rat.cast_one` / `Rat.cast_ofNat` — 存在
- [x] `Rat.cast_pow` / `Rat.cast_mul` / `Rat.cast_sub` / `Rat.cast_add` / `Rat.cast_inv` / `Rat.cast_natCast` / `Rat.cast_zero` — 存在（收尾追加第 2 批，见记录 F-4）
- [x] `Rat.cast_ofNat` 需要 `[n.AtLeastTwo]` 实例 — 签名核查（同上）
- [x] `Rat.cast_inj` 的 `α` 隐式 → `apply` 下卡 `CharZero ?m`，必须 `(Rat.cast_inj (α := ℝ))`（同上）
- [x] `example : (1:ℚ) < 3 := by decide` — **通过**（原样实测）
- [x] `by decide` 对含除法的 ℚ 字面量 — **失败**，必须 `norm_num [zoneQ]`（见记录 F-2）

### G 组 — 战术可用性

- [x] `nlinarith` — 可用（本项目的**主力**；在去分母后能裸证平方单调）
- [x] `positivity` — 可用（含 `p * q`、`x^2 / (4*lam)`、`1 / exp x`）
- [x] `norm_num` — 可用（十进制字面量 `0.5` / `1.2`、ℚ→ℝ 混合、`norm_num [zoneQ]`）
  - ⚠️ **可靠域边界**（收尾追加第 2 批）：`norm_num` **不认识 `Real.exp` 的正性/单调性**。
    可靠域见下方"三张可靠域表"。
- [x] `field_simp` — **条件可用**：目标是**等式 + 显式非零前提**时好用；直接作用于不等式会 `simp made no progress`
- [x] `push_cast` — 可用，但**不自带收尾**（留下 `X = X`，必须补 `ring`/`rfl`）
- [x] `ring_nf` — 可用（对称性 `barrier lam x = barrier lam (2*lam-x)`，**不需要 `lam ≠ 0`**）
- [x] `gcongr` — **条件可用**：线性/单调位置可用；直接作用于 `(lam-x₁)^2 < (lam-x₂)^2`（底数为负）**失败**
- [x] `linarith` — 可用
- [x] `split_ifs` / `rw [if_pos/if_neg]` — 可用（M1 zone 层）
- [x] `set_option linter.unusedVariables false in` **不能紧跟文档注释**（语法坑，见记录 G-4）

### 三张「可靠域」表（工具能做什么 / 不能做什么）

| 工具 | 可靠域 | **不可靠域** | 出路 |
|---|---|---|---|
| `decide` | ℚ 的**整数/无除法**字面量（含负整数） | 含除法或十进制的 ℚ 字面量（卡 `Rat.instDecidableLt` → `Int.decNonneg`） | `norm_num [zoneQ]` |
| `norm_num` | 多项式/字面量的算术归约；`norm_num [barrier]` 求势垒值 | **`Real.exp` 的正性/单调性**（会留下 `⊢ False` 未解） | `linarith [Real.exp_pos c]` |
| `field_simp` | **等式**（+ 显式非零前提） | **不等式**（`simp made no progress`） | `div_lt_div_iff₀` 交叉相乘 → `nlinarith` |
| `push_cast` | 把 cast 逐运算推进 | **不自带收尾**（留 `X = X`） | 补 `ring`（`rw` 链则相反，见 F-4） |

---

## 校准记录

<!-- 格式：## <日期> — <主题> — api_researcher — <结论> -->

## 2026-09-20 — A 组：exp 层（M3 关键路径）— api_researcher — 全部存在；关键点：`Real.exp_lt_exp` 本身就是 iff

**探针**：`theories/Marcus/probes/marcus-exp-api.lean`（0 error / 0 warning）

`#check` 原始输出（完整粘贴）：

```
Real.exp_lt_exp {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y
Real.exp_le_exp {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y
Real.exp_pos (x : ℝ) : 0 < Real.exp x
Real.exp_nonneg (x : ℝ) : 0 ≤ Real.exp x
Real.exp_neg (x : ℝ) : Real.exp (-x) = (Real.exp x)⁻¹
Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
Real.exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y
Real.exp_zero : Real.exp 0 = 1
Real.exp_strictMono : StrictMono Real.exp
Real.exp_monotone : Monotone Real.exp
```

**结论（M3 核心引理的支点，务必按此写）**：

- `Real.exp_lt_exp` 的方向是 **`↔`**：`Real.exp x < Real.exp y ↔ x < y`。
  从 `h : a < b` 出发取 `Real.exp a < Real.exp b` 用 **`.mpr h`**（或 `Real.exp_lt_exp.2 h`）；
  反向用 `.mp`。**不存在** `Real.exp_lt_exp_iff` —— 不要写这个名字。
- 等价写法：`Real.exp_strictMono h`（`StrictMono` 版）也通过。
- `Real.exp_le_exp` 同样是 `↔`（非严格版）；`Real.exp_le_exp_of_le (h : x ≤ y) : exp x ≤ exp y` 是 `→` 版。

源码位置：`Real.exp_*` 全部在 `Mathlib/Data/Complex/Exponential.lean`（namespace `Real`）：
`exp_zero:85`、`exp_add:98`、`exp_pos:268`、`exp_nonneg:274`、`exp_strictMono:284`、
`exp_lt_exp_of_lt:290`、`exp_monotone:293`、`exp_le_exp:304`、`exp_neg:148`、`exp_sub:151`、`exp_lt_exp:300`。

**M3 已实测的最短骨架（`rate_gt_of_barrier_lt`，2 行战术）**：

```lean
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA
```

链条：取负（`by linarith`）→ 除以正数（`div_lt_div_of_pos_right`）→ exp 严格单调
（`Real.exp_lt_exp.2`）→ 乘正数（`mul_lt_mul_of_pos_left`）。
可读的逐步版（同一证明展开）见 `marcus-exp-api.lean` 的 `L4_stepwise`。

## 2026-09-20 — B 组：除法/序（M3 关键路径）— api_researcher — 全部存在（2 个已漂移）

**探针**：`theories/Marcus/probes/marcus-order-api.lean`（0 error / 0 warning）

`#check` 原始输出：

```
div_lt_div_iff_of_pos_right {G₀} [GroupWithZero G₀] [LinearOrder G₀] [ZeroLEOneClass G₀] {a b c : G₀}
  [PosMulStrictMono G₀] [MulPosStrictMono G₀] (hc : 0 < c) : a / c < b / c ↔ a < b
div_lt_div_of_pos_right {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] {a b c : G₀} [MulPosStrictMono G₀] (h : a < b) (hc : 0 < c) : a / c < b / c
div_pos {G₀} ... (ha : 0 < a) (hb : 0 < b) : 0 < a / b
div_nonneg {G₀} ... (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b
one_div_pos {G₀} ... {a : G₀} : 0 < 1 / a ↔ 0 < a
div_eq_mul_inv {G} [DivInvMonoid G] (a b : G) : a / b = a * b⁻¹
mul_div_assoc {G} [DivInvMonoid G] (a b c : G) : a * b / c = a * (b / c)
neg_div {R} [DivisionMonoid R] [HasDistribNeg R] (a b : R) : -b / a = -(b / a)
div_neg {R} [DivisionMonoid R] [HasDistribNeg R] {b : R} (a : R) : a / -b = -(a / b)
neg_lt_neg_iff {α} [AddGroup α] [LT α] [AddLeftStrictMono α] {a b : α} [AddRightStrictMono α] : -a < -b ↔ b < a
div_lt_iff_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : b / c < a ↔ b < a * c
lt_div_iff_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : a < b / c ↔ b < a * c
div_lt_div_right_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : a / c < b / c ↔ b < a
div_lt_iff₀ {G₀} ... (hc : 0 < c) : b / c < a ↔ b < a * c
lt_div_iff₀ {G₀} ... (hc : 0 < c) : a < b / c ↔ a * c < b
div_lt_div_iff₀ {G₀} [CommGroupWithZero G₀] ... (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b
```

**B-1（漂移）**：`div_lt_iff` → **`div_lt_iff₀`**，`lt_div_iff` → **`lt_div_iff₀`**
（`@[deprecated … (since := "2024-10-02")]`，`Mathlib/Algebra/Order/Field/Basic.lean:31,37`）。
旧名仍能编译但产生 deprecation warning（不影响验收，但新代码用新名）。

**B-2（易混同名）**：`div_lt_div_iff₀`（**两个分母**的版本，`a/b < c/d ↔ a*d < c*b`）
与 `div_lt_div_iff_of_pos_right`（**同一个分母**）是**两个不同的引理**。barrier 的
`(…)/(4*lam) < (…)/(4*lam)` 是后者。

**B-3（参数顺序坑）**：`neg_div (a b : R) : -b / a = -(b / a)` —— 结论左边是 `-b / a`，
**不是** `-(a / b)`。要证 `-(x) / y = -(x / y)` 用 `neg_div y x`。`div_neg {b} (a) : a / -b = -(a / b)` 则正常。

**B-4（负分母，lead 报的坑 —— 已独立复核）**：
- `div_lt_div_iff_of_neg_right` / `div_lt_div_of_neg_right` **不存在**（`unknown identifier`）。
- 正确工具：`div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)`
  （`Mathlib/Algebra/Order/Field/Basic.lean:585`）—— **是 iff，右边方向是 `b < a`（反直觉）**。
- `lam < 0` 的另一条（本项目实际采用、已验证）路线：把 `4*lam` 改写成 `-(4*(-lam))`，
  用 `div_neg` + `neg_lt_neg_iff` 翻成正分母，再 `div_lt_div_iff_of_pos_right`。
  完整骨架见下方"barrier 两支单调"。

## 2026-09-20 — C 组：平方/幂单调 — api_researcher — `0 ≤ a < b ⇒ a² < b²` 最省事的是 `sq_lt_sq₀`（或裸 nlinarith）

**探针**：`theories/Marcus/probes/marcus-order-api.lean`（0 error / 0 warning）

`#check` 原始输出：

```
sq_lt_sq₀ {M₀} [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀]
  [MulPosStrictMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b
sq_le_sq₀ {M₀} ... (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b
sq_lt_sq {α} [LinearOrderedRing α] {a b : α} : a ^ 2 < b ^ 2 ↔ |a| < |b|
sq_le_sq {α} [LinearOrderedRing α] {a b : α} : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b|
sq_lt_sq' {α} [LinearOrderedRing α] {a b : α} (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2
sq_le_sq' {α} [LinearOrderedRing α] {a b : α} (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2
sq_pos_of_ne_zero {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R} : a ≠ 0 → 0 < a ^ 2
sq_nonneg {α} [Semiring α] [LinearOrder α] ... (a : α) : 0 ≤ a ^ 2
sq_eq_zero_iff {M₀} [MonoidWithZero M₀] {a : M₀} [NoZeroDivisors M₀] : a ^ 2 = 0 ↔ a = 0
mul_self_lt_mul_self {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {a b : M₀} [PosMulStrictMono M₀]
  [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) : a * a < b * b
mul_self_lt_mul_self_iff {α} [Semiring α] [LinearOrder α] [PosMulStrictMono α] [MulPosMono α] {a b : α}
  (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b
lt_of_mul_self_lt_mul_self₀ {M₀} ... (hb : 0 ≤ b) : a * a < b * b → a < b
pow_lt_pow_left₀ {M₀} ... (hab : a < b) (ha : 0 ≤ a) {n : ℕ} : n ≠ 0 → a ^ n < b ^ n
pow_left_strictMonoOn₀ {M₀} ... (hn : n ≠ 0) : StrictMonoOn (fun x => x ^ n) {a | 0 ≤ a}
```

**C-1（问题答案）**：从 `0 ≤ a < b` 推 `a^2 < b^2`，最省事的是

```lean
(sq_lt_sq₀ ha (ha.trans hab.le)).2 hab   -- 显式，不需要 |a|
-- 或直接：
by nlinarith                              -- 实测裸 nlinarith 就能过，无需任何 hint
```

`sq_lt_sq₀` 在 `Mathlib/Algebra/Order/GroupWithZero/Unbundled.lean:1322`；
`sq_pos_of_ne_zero` 是 alias，在 `Mathlib/Algebra/Order/Ring/Basic.lean:304`。
**不要用** `sq_lt_sq`（那是 `|a| < |b|` 版，会把目标变成绝对值，反而绕远）。
**不存在** `sq_lt_sq_iff`。

**C-2（隐式参数坑，lead 报 —— 已独立复核）**：`sq_pos_of_ne_zero` 的 `a` 是**隐式**：

```
@sq_pos_of_ne_zero : ∀ {R : Type u_1} [inst : LinearOrderedSemiring R] [inst_1 : ExistsAddOfLE R] {a : R},
  a ≠ 0 → 0 < a ^ 2
```

正确：`sq_pos_of_ne_zero hdq`。写成 `sq_pos_of_ne_zero dq hdq` 会报
`application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`。
⚠️ **`theories/Marcus/plan.md` §7.2 原先写成显式两参，是错的** —— 本条为正式纠正。

**C-3**：`mul_self_lt_mul_self` 的结论是 `a * a < b * b`（`*` 不是 `^`），直接 `exact` 到
`a^2 < b^2` 会 `type mismatch`；需要 `simpa only [pow_two] using mul_self_lt_mul_self ha hab`。

**C-4**：`pow_lt_pow_left` **已漂移** → `pow_lt_pow_left₀`（since 2024-11-13）；
参数顺序 `(hab : a < b) (ha : 0 ≤ a)` 后跟 `{n : ℕ}`，且 `n ≠ 0` 在**最后**（不是前提）。

## 2026-09-20 — D 组：乘法/序 — api_researcher — 全部存在；`pos_of_mul_pos_left/right` 极易写反

**探针**：`theories/Marcus/probes/marcus-exp-api.lean`（0 error / 0 warning）

`#check` 原始输出：

```
mul_lt_mul_of_pos_left {α} [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α] (bc : b < c)
  (a0 : 0 < a) : a * b < a * c
mul_lt_mul_of_pos_right {α} [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α] (bc : b < c)
  (a0 : 0 < a) : b * a < c * a
mul_pos {α} [MulZeroClass α] [Preorder α] [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b
mul_nonneg {α} [MulZeroClass α] [Preorder α] [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b
mul_lt_mul₀ {α} [LinearOrderedCommGroupWithZero α] {a b c d : α} (hab : a < b) (hcd : c < d) :
  a * c < b * d
pos_of_mul_pos_left {α} [MulZeroClass α] [Preorder α] [MulPosReflectLT α] (h : 0 < a * b)
  (hb : 0 ≤ b) : 0 < a
pos_of_mul_pos_right {α} [MulZeroClass α] [Preorder α] [PosMulReflectLT α] (h : 0 < a * b)
  (ha : 0 ≤ a) : 0 < b
mul_lt_mul_of_neg_left {α} [Semiring α] [PartialOrder α] {a b c : α} [ExistsAddOfLE α] [PosMulStrictMono α]
  [AddRightStrictMono α] [AddRightReflectLT α] (h : b < a) (hc : c < 0) : c * a < c * b
```

**D-1**：`mul_lt_mul_of_neg_left` 的**参数顺序反直觉**：`(h : b < a) (hc : c < 0) : c * a < c * b`
（第一个参数是反方向的 `b < a`）。实测
`example {A u v : ℝ} (hA : A < 0) (h : u < v) : A * v < A * u := mul_lt_mul_of_neg_left h hA` 通过。

**D-2（lead 报的坑 —— 已独立复核）**：`rate A lam kB T x = A * Real.exp (…)`，正的因子
`A` 在积的**左**边、`exp` 在**右**边。要从 `0 < A * Real.exp u` 得 `0 < A`，必须用
**`pos_of_mul_pos_left`**（它的前提是"右因子非负"）：

```lean
example {A u : ℝ} (h : 0 < A * Real.exp u) : 0 < A :=
  pos_of_mul_pos_left h (Real.exp_pos u).le
```

用 `pos_of_mul_pos_right` 会报 `application type mismatch`（它的结论是 `0 < b`，即右因子）。
两者都在 `Mathlib/Algebra/Order/GroupWithZero/Unbundled.lean:448,451`。

## 2026-09-20 — E 组：单调性包装 — api_researcher — 实用的只有 `lt_iff_lt` 与两个现成 `StrictMonoOn`

**探针**：`theories/Marcus/probes/marcus-order-api.lean`（0 error / 0 warning）

`#check` 原始输出：

```
StrictMonoOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
StrictAntiOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
MonotoneOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
StrictMonoOn.lt_iff_lt {α} {β} [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
  (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b
StrictAntiOn.lt_iff_lt {α} {β} [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
  (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a
Set.strictMonoOn_iff_strictMono {s : Set α} [Preorder α] [Preorder β] {f : α → β} :
  StrictMonoOn f s ↔ StrictMono fun a => f ↑a
strictMonoOn_mul_self {M₀} [MonoidWithZero M₀] [PartialOrder M₀] [PosMulStrictMono M₀]
  [MulPosMono M₀] : StrictMonoOn (fun x => x * x) {x | 0 ≤ x}
pow_left_strictMonoOn₀ {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {n : ℕ} [ZeroLEOneClass M₀]
  [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hn : n ≠ 0) : StrictMonoOn (fun x => x ^ n) {a | 0 ≤ a}
```

**结论**：

- `StrictMonoOn` 的定义就是 `∀ ⦃a⦄, a ∈ s → ⦃b⦄, b ∈ s → a < b → f a < f b`
  （`Mathlib/Order/Monotone/Defs.lean:83`），所以**直接写 `intro a ha b hb hab` 最省事**，
  不需要找 `*_iff` 引理。`strictMonoOn_iff` **不存在**。
- 想用 iff 形式取 `f a < f b → a < b` 时用 **`StrictMonoOn.lt_iff_lt`**
  （`Mathlib/Order/Monotone/Basic.lean:377`）/ `StrictAntiOn.lt_iff_lt`。
- `Set.strictMonoOn_iff_strictMono`（`Mathlib/Data/Set/Basic.lean:1480`）的右边是
  **子类型上的 `StrictMono`**，对 `Set.Ici`/`Set.Iic` 上的单调**没用**，别选它。
- `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` 在 v4.17 **点记法报错**，复合单调性要手写。
- **⚠️ `a ∈ Set.Ici lam` 不能直接喂给 `linarith`** —— 必须先 `rw [Set.mem_Ici] at ha hb`
  把假设变成 `lam ≤ a`。否则报 `linarith failed to find a contradiction`（`a✝ : 0 > a - lam`）。

barrier 的 `StrictMonoOn` / `StrictAntiOn` 打包形式（已实测）：

```lean
theorem barrier_strictMonoOn_Ici {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Ici lam) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

theorem barrier_strictAntiOn_Iic {lam : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Iic lam) := by
  intro a ha b hb hab
  rw [Set.mem_Iic] at ha hb
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

## 2026-09-20 — F 组：ℚ 层与 ℚ→ℝ 转移 — api_researcher — cast 引理全是 iff；`decide` 只对整数字面量可靠

**探针**：`theories/Marcus/probes/marcus-tactic-api.lean` + `theories/Marcus/probes/marcus-ident-rat-api.lean`（均 0 error）

`#check` 原始输出：

```
Rat.cast_lt {p q : ℚ} {K} [LinearOrderedField K] : ↑p < ↑q ↔ p < q
Rat.cast_le {p q : ℚ} {K} [LinearOrderedField K] : ↑p ≤ ↑q ↔ p ≤ q
Rat.cast_pos {q : ℚ} {K} [LinearOrderedField K] : 0 < ↑q ↔ 0 < q
Rat.cast_inj {p q : ℚ} {α} [DivisionRing α] [CharZero α] : ↑p = ↑q ↔ p = q
Rat.cast_div (p q : ℚ) : ↑(p / q) = ↑p / ↑q
Rat.cast_one : ↑(1 : ℚ) = 1
Rat.cast_mk (a b : ℤ) : ↑(Rat.divInt a b) = ↑a / ↑b
```

**F-1（题目要求原样报告）**：`example : (1 : ℚ) < 3 := by decide` —— **通过**（实测 0 error）。
`decide` 对 ℚ 的整数比较（`1 < 3`、`¬ (3 < 1)`、`1 ≤ 3`）均可用。
`Rat.cast_pos_iff` **不存在**（`Rat.cast_pos` 本身就是 iff）。

**F-2（M5 判定层规范，lead 报 —— 已独立复核）**：

- ✅ `zoneQ (1 : ℚ) 3 = Zone.inverted` / `zoneQ (1 : ℚ) 1 = Zone.barrierless` —— **`by decide` 通过**。
- ❌ `zoneQ (1 : ℚ) (3 / 4) = Zone.normal` —— **`by decide` 失败**，原始报错：

```
tactic 'decide' failed for proposition
  zoneQ 1 (3 / 4) = Zone.normal
since its 'Decidable' instance
  instDecidableEqZone (zoneQ 1 (3 / 4)) Zone.normal
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqBool', 'instDecidableEqNat',
'instDecidableEqZone', 'Bool.decEq', 'Int.decLt', 'Nat.decEq',
'Rat.instDecidableLt' and 'Int.decNonneg✝', reduction got stuck at the
'Decidable' instance
  match h : (zoneQ 1 (3 / 4)).toCtorIdx.beq Zone.normal.toCtorIdx with
  | true => isTrue ⋯
  | false => isFalse ⋯
```

  （卡点在 `Rat.instDecidableLt` → `Int.decNonneg` 路径，不是 `Eq`。）

- ✅ 对策：`by norm_num [zoneQ]`（走证明项而非内核归约）。实测通过：
  `zoneQ 1 (3/4) = normal`、`zoneQ 1 (6/8) = normal`、`zoneQ 1 (5/4) = inverted`、`zoneQ 1 (4/4) = barrierless`。

**规范**：**整数参数用 `decide`；含除法/约分的有理字面量用 `norm_num [zoneQ]`。**

**F-3（M5a 语法坑）**：`zoneQ_eq_zone` 里**不能**用 `rw [Rat.cast_lt, Rat.cast_inj]`，
会报 `tactic 'rewrite' failed, motive is not type correct`（依值 `Decidable` 实例）。
必须用 **`simp only [Rat.cast_lt, Rat.cast_inj]`**：

```lean
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  simp only [Rat.cast_lt, Rat.cast_inj]
```

## 2026-09-20 — G 组：战术可用性实测 — api_researcher — 三类目标形态全过；`gcongr`/`field_simp` 有条件

**探针**：`theories/Marcus/probes/marcus-tactic-api.lean`（0 error / 0 warning）

**G-1（题目指定形态 1）**：`positivity` 收尾 —— **通过**，最短就是一行：

```lean
example {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ (lam - x)^2 / (4*lam) := by positivity
```

`positivity` 还能直接从 `hlam : 0 < lam` 给出 `(0:ℝ) < 4*lam`，以及从 `h : 0 < kB*T` 给出 `0 < kB*T`。

**G-2（题目指定形态 2，最关键）—— `positivity`/`nlinarith` 最短证明（2 行战术）**：

```lean
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam-x₁)^2/(4*lam) < (lam-x₂)^2/(4*lam) := by
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

这是本主题**实测最短**的成功证明（去分母 + 裸 `nlinarith`，后者连 `sq_nonneg` hint 都不需要）。

对照（lead 在 `marcus-statement-skeleton.lean` R4 里的版本，3 行，同样通过、更稳）：

```lean
  have hpos : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq hpos
```

**失败路径（已实测，勿再走）**：

- 单个裸 `nlinarith` 直接作用于**原**目标（不去分母）→ **失败**（`a✝ : (lam-x₁)^2 ≥ (lam-x₂)^2`，分母符号没被利用）。
- `gcongr` 直接作用于 `(lam-x₁)^2 < (lam-x₂)^2` → **失败**：
  gcongr 走 `sq` 的单调性，产生子目标 `0 ≤ lam - x₁`，而 `lam ≤ x₁` 时它是 ≤ 0。
  要么先把底数改写成非负形式 `(x₁ - lam)^2`，要么改用 `nlinarith` 路线。
- L5（`lam < 0`）用 `div_lt_iff_of_neg` 再 `nlinarith` → **失败**（`rewrite` 后 RHS 变成
  `(lam-x₁)^2/(4*lam) * (4*lam)`，nlinarith 处理不了）。走 `div_neg` 路线（见下）。

**G-3（题目指定形态 3，对称性）**：`ring_nf` —— **通过，且 `hlam : lam ≠ 0` 未被证明使用（unused）**：

```lean
example (lam x : ℝ) :
    (lam - x)^2/(4*lam) = (lam - (2*lam - x))^2/(4*lam) := by ring_nf
```

原因：Lean 除零约定 `x / 0 = 0` 使 `lam = 0` 时两边同时为 0。带 `hlam` 的版本也通过
（只产生 unused-variable warning）。

**G-4（语法坑，lead 报 —— 已独立复核）**：`set_option linter.unusedVariables false in`
**不能紧跟文档注释**：

```lean
/-- doc comment -/
set_option linter.unusedVariables false in     -- ❌ error: unexpected token 'set_option'; expected 'lemma'
theorem bad (z : Zone) : z = z := rfl
```

正确顺序是「**普通块注释 → `set_option … in` → 文档注释 + 定理**」：

```lean
-- plain comment first
set_option linter.unusedVariables false in
/-- doc comment -/
theorem good (z : Zone) : z = z := rfl      -- ✅
```

最省事的替代：在文件顶部放一条不带 `in` 的 `set_option linter.unusedVariables false`。

**G-5**：其余战术全部可用 —— `nlinarith`、`linarith`、`norm_num`（十进制 `0.5` / `1.2`）、
`ring_nf`、`positivity`。`field_simp` 只在「**等式** + 显式非零前提」时好用；
直接作用于不等式报 `error: simp made no progress`。

**G-6（`nlinarith` 的边界，给 prover 的反面证据）**：下面这条**真命题**裸 `nlinarith` **失败**：

```lean
-- ❌ error: linarith failed to find a contradiction / a✝ : 0 ≥ a^2 + b^2
example {a b : ℝ} (h : a < b) : a ^ 2 + b ^ 2 > 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
```

必须把"至少一个非零"显式做出来喂给它（`marcus-tactic-api.lean` G-7 有可编译版）。
**结论：`nlinarith` 很强但非万能；卡住时补显式 `have`，不要反复调 hint。**

**G-7（M1 zone 层可用引理，prover_a 交付的一批 —— 已逐一 `#check` 复核）**：
`if_pos`、`if_neg`、`iff_of_true`、`iff_of_false`、`le_of_not_gt`、`le_of_lt`、`ne_of_lt`、
`lt_of_le_of_ne`、`Ne.symm`、`lt_irrefl`、`not_lt` —— **全部存在**。
`Zone`（`deriving DecidableEq`）构造子互异可直接 `by decide`（实测 6 组全部通过）。

推荐战术（M1 实测）：`by_cases h : x < lam` + `rw [if_pos h] / rw [if_neg h]` + `simp`。
`split_ifs <;> simp_all` 能过 `zone_trichotomy`，但对前三条会留下 `¬x = lam` / `lam < x`
之类 simp 推不出的目标，需手工补 `ne_of_lt h` 或
`lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)`。

## 2026-09-20 — barrier 两支单调与 rate 单调（M2/M3 关键目标形态）— api_researcher — 三条实测最短骨架

**探针**：`theories/Marcus/probes/marcus-proof-skeletons.lean`（35 theorem，0 error / 0 warning / 无 sorry）

**（1）右支（`0 < lam`，引理 2 / `barrier_mono_of_pos`）—— 3 行**：

```lean
theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

**（2）左支（`0 < lam`，引理 3 / `barrier_antitone_of_pos`）—— 同形，`nlinarith` 自动搞定方向**：

```lean
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

> **⚠️ 前提 `h₁ : 0 ≤ x₁` 是"证明未使用（unused）"，不是"可由其他前提推出"**
> —— **这两句话语义不同，别混**（M2 verifier 发现 A，本日志曾误写为后者，已订正）。
>
> - **正确**：该前提**未被证明使用**。去掉它定理仍然成立（内核检查通过，见
>   `marcus-proof-skeletons.lean` 与下面的 `…_no_h1` 版本），故它只产生
>   unused-variable warning。它是**显式物理前提**（驱动力非负），按"物理近似显式化"
>   铁律**保留**。用文件级 `set_option linter.unusedVariables false` 或接受 warning
>   （**warning 不影响验收**，只有 sorry / 自定义 axiom 才 FAIL）。
> - **错误（禁止再写）**："`h₁` 可由 `h₃ : x₂ ≤ lam` 与 `h₂ : x₁ < x₂` 推出"。
>   **内核反例**：`lam = 1, x₁ = -5, x₂ = -4` ⇒ `0 < 1 ✓`、`-5 < -4 ✓`、`-4 ≤ 1 ✓`，
>   但 `0 ≤ -5 ✗`。`¬ ∀ lam x₁ x₂, 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁` 已机器检查。
>   ⚠️ 把它当"可复用推理依据"会直接写出错误证明 —— 这是典型误写，引以为戒。

```lean
-- 「未被证明使用」的实证：去掉 `h₁` 定理照样过
theorem barrier_antitone_of_pos_no_h1 {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
-- 「不可推出」的实证（内核反例）
example : ¬ (∀ (lam x₁ x₂ : ℝ), 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁) := by
  intro h; have := h 1 (-5) (-4) (by norm_num) (by norm_num) (by norm_num); norm_num at this
```

**（3）`lam < 0`（引理 5 / `barrier_antitone_of_neg`）—— 4 行，负分母要绕道**：

```lean
theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
  nlinarith
```

关键：**没有 `div_lt_div_iff_of_neg_right`**。要把 `4*lam` 改写成 `-(4*(-lam))`，
再用 `div_neg`（`a / -b = -(a / b)`）把负号提到外面、`neg_lt_neg_iff`（`-a < -b ↔ b < a`）
翻转成正分母，最后 `div_lt_div_iff_of_pos_right` 收尾。
⚠️ **不要在 `unfold rate` 之后一口气套这套 rw** —— `rate` 自带一个负号，会与 `div_neg`
产生的负号叠成双重否定，`neg_lt_neg_iff` 就匹配不上（实测失败）。先把 barrier 的
不等式单独 `have` 出来，再用 `rate_gt_of_barrier_lt` 推速率层。

**（4）核心引理 4（rate 单调性 / `rate_gt_of_barrier_lt`）—— 2 行**：

```lean
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA
```

链条：`h : barrier x < barrier y` → `by linarith` 取负得 `-(barrier y) < -(barrier x)`
→ `div_lt_div_of_pos_right … hkT` 除以正数 → `Real.exp_lt_exp.2` 吃掉 exp
→ `mul_lt_mul_of_pos_left … hA` 乘正数 `A`。

**（5）`lam = 0` 分支不需要任何正性前提**（锐利性必要性，`sharp_lam_pos_of_eq` 签名
里可以完全不带 `hkB` / `hT` / `hA`）：除零约定使 `barrier 0 x = 0`，速率恒为 `A`：

```lean
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x; unfold rate; rw [barrier_zero_lam]; simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd
```

**（6）语义要点（校准中发现，影响 M4a 语句）**：`InvertedDescriptor`（"反转区内速率随
驱动力严格递减"）**只在 `lam > 0` 时成立**，在 `lam < 0` 时**为假**。因为 `lam < 0` 时
`barrier` 随 `x` **递减**（引理 5），故速率随 `x` **递增**，与描述方向相反。
`marcus-statement-skeleton.lean` 的 `inverted_descriptor_holds` 已经带 `hlam : 0 < lam`，
方向正确；`inverted_descriptor_holds_of_neg` 是带 `hA : A < 0` 的**非物理拉伸目标**，
那里 `A < 0` 的翻转让描述重新成立 —— 两个定理的前提都**不可互换或删减**。
机器检查的反例已提交在 `marcus-proof-skeletons.lean`：
`not_invertedDescriptor_of_neg_lam : ¬ InvertedDescriptor 1 (-1) 1 1`（取 `lam = -1, A = kB = T = 1`，
由 `h : rate 1 (-1) 1 1 1 < rate 1 (-1) 1 1 0` 化简得 `Real.exp 1 < Real.exp (1/4)`，
再用 `Real.exp_lt_exp.mp` 得 `1 < 1/4` 矛盾）。

## 2026-09-20 — 收尾追加：`≤` 版引理 + `rate_ratio` 链 — api_researcher — 6 个新名字全部存在，签名已归档

**探针**：`theories/Marcus/probes/marcus-api-closeout.lean`（0 error / 0 warning）

复核对象：M2/M3/M4a/M5a 交付者在各自 `#check` 中报出的一批新名字。**逐条独立重跑，非照抄。**

`#check` 原始输出：

```
Real.exp_le_exp {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y
Real.exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : Real.exp x ≤ Real.exp y
div_le_div_of_nonneg_right {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] {a b c : G₀} [MulPosMono G₀] (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
mul_le_mul_of_nonneg_left {α} [Mul α] [Zero α] [Preorder α] [PosMulMono α] (h : b ≤ c)
  (a0 : 0 ≤ a) : a * b ≤ a * c
mul_div_mul_left {G₀} [CommGroupWithZero G₀] {c : G₀} (a b : G₀) (hc : c ≠ 0) :
  c * a / (c * b) = a / b
Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
pow_lt_pow_left₀ {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {a b : M₀} [ZeroLEOneClass M₀]
  [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hab : a < b) (ha : 0 ≤ a) {n : ℕ} :
  n ≠ 0 → a ^ n < b ^ n
sq_lt_sq₀ {M₀} [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀]
  [MulPosStrictMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b
```

**确认无误（我复核后一致）**：

- `Real.exp_le_exp` **是 `↔`**（`Real.exp x ≤ Real.exp y ↔ x ≤ y`）；`Real.exp_le_exp_iff` **不存在**（复核：`unknown constant`）；
  `Real.exp_le_exp_of_le` 是 `→` 版。
- `Real.exp_sub` 的**方向**确为 `exp (x - y) = exp x / exp y` ⇒ 把"exp 相除"变"exp 差"
  必须用 **`← Real.exp_sub`**（`rate_ratio` 里就是这么用的）。
- `pow_lt_pow_left₀`：`n ≠ 0` 在**最后**（不在前提位置）。
- `sq_lt_sq₀`：`0 ≤ a < b ⇒ a² < b²` 的正解，比 `mul_self_lt_mul_self` + `sq_lt_sq'` 都省事、且不需要 `|·|`。
- `mul_le_mul_of_nonneg_left`：实际 binder 名是 `(h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c`
  （与报出的 `(h : a ≤ b) (hc : 0 ≤ c)` 只差 binder 重命名，签名等价）。

**M3 `rate_peak_at_lam`（`≤` 版峰值）实测体**（三个 `≤` 引理协同）：

```lean
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  unfold rate
  apply mul_le_mul_of_nonneg_left _ hA.le        -- 乘非负数
  rw [Real.exp_le_exp]                           -- 吃掉 exp（iff，正向）
  exact div_le_div_of_nonneg_right (by linarith [barrier_min_at_lam hlam x]) hkT.le
```

**M3 `rate_ratio` 实测体**（`mul_div_mul_left` + `← Real.exp_sub` 是关键两步）：

```lean
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring
```

## 2026-09-20 — 收尾追加：B 组禁止清单增补 — api_researcher — `div_lt_div_of_neg_right` 不存在；`sq_pos_of_ne_zero` 的 `a` 是隐式

**探针**：`theories/Marcus/probes/marcus-api-closeout.lean`（0 error / 0 warning）

- `div_lt_div_of_neg_right` —— **复核确认不存在**（`unknown identifier`）。
  负除数下唯一可用的是 `div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a`
  —— **iff，且右边是 `b < a`（顺序反转）**，M2 两支方向反转全靠它。
- `@sq_pos_of_ne_zero : ∀ {R : Type u_1} [inst : LinearOrderedSemiring R] [inst_1 : ExistsAddOfLE R] {a : R},
  a ≠ 0 → 0 < a ^ 2` —— **`a` 是隐式参数**，正确写法 `sq_pos_of_ne_zero hdq`；
  写成 `sq_pos_of_ne_zero dq hdq` 报
  `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`。
  ⚠️ 本条同时**订正 `theories/Marcus/plan.md` §7.2 的旧提示**（旧提示写成显式两参，已由 lead 修改）。

## 2026-09-20 — 收尾追加：C 组工具事实（`decide` 域 / plan §8.2 三处纠正）— api_researcher — 4 条复核，1 条按实测定性

**探针**：`theories/Marcus/probes/marcus-api-closeout.lean`（0 error / 0 warning）

**C-1 `by decide` 对 ℚ 的可靠域**（复核一致）：

- ✅ **整数/无除法字面量**（含**负整数**）可算：`zoneQ 1 3`、`zoneQ 1 (-3)`、`zoneQ 1 1`、`zoneQ 1 0` 全部 `by decide` 通过。
- ❌ **含除法或十进制**一律卡在 `Rat.instDecidableLt` → `Int.decNonneg`，报
  `'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'`（`0.5` 与 `3/4` 均复现）。
- ⇒ **规范**：整数参数用 `decide`；含除法/十进制用 `norm_num [zoneQ]`。

**C-2 `theories/Marcus/plan.md` §8.2 三处旧示例纠正**（三条我都构造了最小复现，**逐条实测**）：

1. **`rw [← zoneQ_eq_zone]` 的方向是分情形的，不是一边错**（此处按我的实测定性，比"方向反了"更准确）：
   `←` 的重写模式是 `zone ↑?lam ↑?x`，正向模式是 `zoneQ ?lam ?x`。
   - 目标是 `zoneQ lam x = …` ⇒ 必须**正向** `rw [zoneQ_eq_zone]`（§8.2 的情形，旧示例用了 `←`，故错）；
   - 目标是 `zone ↑lam ↑x = …` ⇒ `rw [← zoneQ_eq_zone]` 才对。
   两个方向我都实测通过，**选择取决于目标里出现的是哪一边**。
2. **cast 字面量 ≠ `OfNat` 字面量**（定义层不等）✅ 复核一致：
   `exact h`（`h : ↑1 < ↑3`）到目标 `InvertedRegion (1 : ℝ) 3` 报
   `type mismatch: h has type ↑1 < ↑3 but is expected to have type InvertedRegion 1 3`。
   两条出路：显式写 `((1:ℚ):ℝ)`，或 `norm_num [InvertedRegion]`。
3. **`rw` 不走 defeq** ✅ 复核一致：`rw [← zoneQ_inverted_iff]` 不展开 `def InvertedRegion`，报
   `tactic 'rewrite' failed, did not find instance of the pattern ↑?lam < ↑?x`。
   出路：`exact (zoneQ_inverted_iff lam x).mp h`（走 defeq），或先 `show (lam:ℝ) < (x:ℝ)`。

**C-3** `Zone`（`deriving DecidableEq`）构造子互异可直接 `by decide` —— 6 组全部实测通过。

## 2026-09-20 — ⚠️ 订正：「未使用的前提」≠「可推出的前提」（M2 verifier 发现 A）— api_researcher

**本日志此前（M2 段落）误写**："`barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁` 可由
`h₃ : x₂ ≤ lam` 与 `h₂ : x₁ < x₂` 推出"。**这是假命题，已改**。

- **正确表述**：`h₁` 是**证明未使用（unused）**的前提 —— 去掉它定理仍成立
  （`barrier_antitone_of_pos_no_h1` 内核通过），故只产生 unused-variable warning。
- **内核反例**（verifier 给出，我已独立复现）：`lam = 1, x₁ = -5, x₂ = -4` ⇒
  `0 < 1 ✓`、`-5 < -4 ✓`、`-4 ≤ 1 ✓`，但 `0 ≤ -5 ✗`。
  `¬ ∀ lam x₁ x₂, 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁` 已机器检查。
- **为什么必须区分**：把"未使用"说成"可推出"，后人会把它当成**可复用的推理依据**，
  写出错误证明。已连带把 G-3 里同口径的措辞（"`hlam : lam ≠ 0` 是多余的"）
  改为"**未被证明使用（unused）**"。
- 该前提作为**显式物理前提**（驱动力非负）**保留**，不因 unused 而删除。

## 2026-09-20 — 收尾追加第 2 批：F 组 `Rat.cast_*` 家族（M5a `barrierQ_cast`）— api_researcher — 10 个名字全部存在；两条"尾巴规则相反"的坑

**探针**：`theories/Marcus/probes/marcus-api-cast-normnum.lean`（0 error / 0 warning）

`#check` 原始输出（`@` 形式以暴露隐式参数）：

```
@Rat.cast_pow {α} [DivisionRing α] (p : ℚ) (n : ℕ) : ↑(p ^ n) = ↑p ^ n
@Rat.cast_mul {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p * q) = ↑p * ↑q
@Rat.cast_sub {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p - q) = ↑p - ↑q
@Rat.cast_div {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p / q) = ↑p / ↑q
@Rat.cast_add {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p + q) = ↑p + ↑q
@Rat.cast_ofNat {α} [DivisionRing α] (n : ℕ) [n.AtLeastTwo] : ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_natCast {α} [DivisionRing α] (n : ℕ) : ↑↑n = ↑n
@Rat.cast_inv {α} [DivisionRing α] [CharZero α] (p : ℚ) : ↑p⁻¹ = (↑p)⁻¹
@Rat.cast_zero {α} [DivisionRing α] : ↑0 = 0
@Rat.cast_inj {α} [DivisionRing α] [CharZero α] {p q : ℚ} : ↑p = ↑q ↔ p = q
```

**F-4（两条"尾巴规则相反"的坑，实测，极易写错）**：目标是
`((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ)`（**不需要任何前提**，含 `lam = 0`）：

- **路线 1 `push_cast`**：`unfold barrierQ barrier; push_cast` **单独不够** ——
  它把两侧归一到 `(↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`，**不自带收尾**，
  必须**补 `ring`**（或 `rfl`）。去掉 `ring` 报
  `error: unsolved goals`。
- **路线 2 显式 `rw` 链**：`rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]`
  **自带 `rfl` 收尾**，目标已被关掉；**后面再写 `ring` 报 `error: no goals to be solved`**。
  ⇒ 这条路线**不能有尾巴战术**。
- **`Rat.cast_inj` 的 `α` 在 `apply` 下会卡住**：`apply Rat.cast_inj.mp` 报
  `typeclass instance problem is stuck, it is often due to metavariables / CharZero ?m.41`。
  必须**显式给出目标域**：`apply (Rat.cast_inj (α := ℝ)).mp`。
- 另注：`cast_pow` / `cast_ofNat` / `cast_natCast` / `cast_zero` **不需要** `[CharZero α]`；
  `mul` / `sub` / `div` / `add` / `inv` / `inj` **需要**。`cast_ofNat` 带 `[n.AtLeastTwo]`。

## 2026-09-20 — 收尾追加第 2 批：`norm_num` 的可靠域边界 — api_researcher — 它不认识 `Real.exp` 的正性

**探针**：`theories/Marcus/probes/marcus-api-cast-normnum.lean`（0 error / 0 warning）

**复核确认**（M5b `inst_I7_unphysical_rate_not_pos` 的实测偏差）：派发提示里的写法
`intro h; have := h 0; norm_num [rate, barrier] at this` **不足以收尾** ——
它把假设约简为 `Real.exp (1/4) < 0` 一类，但 `norm_num` **不认识 `Real.exp` 的正性**，
留下未解目标 `⊢ False`。

✅ **奏效写法**（四步，`PhotoLean/Marcus/Instances.lean` 已采用）：

```lean
theorem inst_I7_unphysical_rate_not_pos : ¬ (∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  have hb : barrier (-1) 0 = -(1 / 4) := by norm_num [barrier]   -- ⑴ 先算势垒值
  rw [rate, hb] at h0                                            -- ⑵ 代回 rate
  norm_num at h0                                                 -- ⑶ 归约
  linarith [Real.exp_pos (1 / 4)]                                -- ⑷ exp 正性交给 linarith
```

⇒ 已与 `decide`/`Rat` 归约条目并列，形成 **"三张可靠域表"**（见"待校准清单"G 组末尾）：
`decide`（ℚ 整数）· `norm_num`（多项式/字面量，**不含 `Real.exp`**）· `field_simp`（**仅等式**）。

`Real.exp_pos` 与本日志 A 组登记一致（`(x : ℝ) : 0 < Real.exp x`）。
同链备用工具 `mul_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a * b < 0` 已实测通过
（M4a 备用 verifier 用它证 `rate (-1) (-1) 1 1 x < 0`）。

## 2026-09-20 — 收尾追加第 2 批：D 组倒数 / 交叉相乘 / `field_simp` 失败路径 — api_researcher — 3 个名字存在，方向坑已钉住

**探针**：`theories/Marcus/probes/marcus-api-cast-normnum.lean`（0 error / 0 warning）

`#check` 原始输出：

```
one_div_le_one_div_of_le.{u_2} {α} [LinearOrderedSemifield α] {a b : α} (ha : 0 < a) (h : a ≤ b) :
  1 / b ≤ 1 / a
div_lt_div_iff₀.{u_2} {G₀} [CommGroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] [PosMulStrictMono G₀] {a b c d : G₀} (hb : 0 < b) (hd : 0 < d) :
  a / b < c / d ↔ a * d < c * b
div_lt_iff₀.{u_2} {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosStrictMono G₀] (hc : 0 < c) : b / c < a ↔ b < a * c
```

**D-3（方向坑）**：`one_div_le_one_div_of_le ha h` 的结论是 **`1 / b ≤ 1 / a`** ——
`a ≤ b` 取倒数后**翻转方向**。本日志此前未收录该名字（它只在
`theories/Marcus/probes/marcus-prover_d2-scratch.lean:38` 的 `#check` 里出现过，
是 `PhotoLean/Marcus/Reorg.lean` 的 `hgeom_of_nonoverlap` 所用），现补录。

**D-4（多分母不等式三步法）**：

- `div_lt_div_iff₀ hb hd` 的**两个参数都是"分母正性"**（`0 < b`、`0 < d`）；
  注意与 `div_lt_div_iff_of_pos_right`（**同一个**分母）区分。
- **`field_simp` 对不等式不可靠**：实测报 `error: simp made no progress`（它只对**等式**可靠）。
- **通用三步**：⑴ 需要通分时先对**等式**用 `field_simp`；⑵ 用 `div_lt_div_iff₀ hb hd`
  （或 `div_lt_iff₀ hc`）**交叉相乘**去掉分母；⑶ `nlinarith` 收尾。
  **未通分前 `nlinarith` / `gcongr` 都看不到分母符号，目标不动。**

## 2026-09-20 — 内核引理索引（`barrier`/`rate` 退化点）— api_researcher

给 M4a 备份 verifier 报告的一条索引（只登记，不新增章节）；
`Sharp.lean` 的 5 条签名经三方比对（`plan §7.1` / 语句骨架 / 交付）一致：

- **`sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False`**
  —— ⚠️ **签名里不含任何正性前提**（无 `hkB` / `hT` / `hA`）。
  机制：Lean 除零约定 `x / 0 = 0` 使 `barrier 0 x = 0`，故速率恒为 `A`，
  描述要求 `rate … 2 < rate … 1` 即 `A < A`，`lt_irrefl` 收尾。
  可编译证明体见 `theories/Marcus/probes/marcus-proof-skeletons.lean` 的 `sharp_lam_pos_of_eq`。
- 同链其它退化点引理：`barrier_at_lam`（`ring`，无前提）、`barrier_zero_lam`（`ring`，无前提）、
  `barrier_symm`（`ring_nf`，`lam ≠ 0` 未被证明使用）。

---

## 给 prover 的速查（按 M3/M5 优先级）

**M3（Sprint 3，最紧）**：

```lean
-- 势垒右支
rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]; nlinarith
-- 势垒左支（lam<0）先翻正分母
rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]; nlinarith
-- exp 层
Real.exp_lt_exp.2 h          -- h : a < b  ⇒  Real.exp a < Real.exp b
Real.exp_lt_exp.mp h         -- 反向
-- 乘法层
mul_lt_mul_of_pos_left h hA  -- h : b < c, hA : 0 < a  ⇒  a*b < a*c
pos_of_mul_pos_left h (le_of_lt (Real.exp_pos u))  -- 从 0 < A * exp u 取 0 < A
-- ≤ 版（rate_peak_at_lam 峰值）
mul_le_mul_of_nonneg_left h hA.le    -- h : b ≤ c, hA : 0 < A
div_le_div_of_nonneg_right h hkT.le  -- h : a ≤ b, hkT : 0 < kB*T
rw [Real.exp_le_exp]                 -- ≤ 版也是 iff
-- rate_ratio 的两步关键
rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]   -- 约掉 A；exp 相除 → exp 差（注意 ←）
```

**M5（Sprint 2 末）**：

```lean
-- 整数参数（含负整数）
example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) (-3) = Zone.normal := by decide
-- 含除法 / 十进制 → decide 会卡，必须 norm_num
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
-- ℚ→ℝ
Rat.cast_lt.mpr h            -- h : p < q  ⇒  (p:ℝ) < (q:ℝ)
simp only [Rat.cast_lt, Rat.cast_inj]   -- 分类器一致性的关键（不能用 rw）
-- ⚠️ cast 字面量 ≠ OfNat 字面量：((1:ℚ):ℝ) 与 (1:ℝ) 不是 defeq
--    目标含 InvertedRegion (1:ℝ) 3 时 `exact h`（h : ↑1 < ↑3）会 type mismatch
-- ⚠️ rw 不走 defeq：rw [← zoneQ_inverted_iff] 不展开 def InvertedRegion
--    用 `exact (zoneQ_inverted_iff lam x).mp h` 或先 `show (lam:ℝ) < (x:ℝ)`
-- ℚ→ℝ cast 家族（barrierQ_cast）：两条路线**尾巴规则相反**
push_cast; ring   -- 路线 1：push_cast 不自带收尾，必须补 ring
rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]  -- 路线 2：自带 rfl，**不能**再加 ring
apply (Rat.cast_inj (α := ℝ)).mp   -- ⚠️ 必须显式给 α，否则卡 CharZero ?m
-- 多分母不等式三步：field_simp 只对等式 → div_lt_div_iff₀ 交叉相乘 → nlinarith
rw [div_lt_div_iff₀ hb hd]   -- hb : 0 < b, hd : 0 < d（**两个都是分母正性**）
one_div_le_one_div_of_le ha h   -- a ≤ b ⇒ 1/b ≤ 1/a（**取倒数翻转方向**）
```

**⚠️ 工具边界（三张可靠域表，详见"待校准清单"G 组末尾）**：
`decide` 只吃 ℚ 整数；`norm_num` **不认识 `Real.exp` 的正性**（要用 `linarith [Real.exp_pos c]`）；
`field_simp` 只对**等式**可靠。

**⚠️ 术语纪律（M2 verifier 发现 A，已订正本日志）**：
"前提**未被证明使用**（unused）" ≠ "前提**可由其他前提推出**"。前者只意味着可以省；
后者是可以被后人当作**可复用推理依据**的命题。写文档时不得混用 ——
`barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁` 属于**前者**（反例 `lam=1, x₁=-5, x₂=-4` 否证后者）。

**命名（硬约束）**：Lean 4 里 `λ` 是保留 token，**不可作标识符**。统一用
`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`（见
`marcus-statement-skeleton.lean` 文件头）。

---

## 2026-09-20 — Hammond 里程碑 API 校准 (Hammond milestone API calibration) — api_researcher — 全部就绪：6 个探针 0 error / 0 warning；最高风险项（ℚ↔ℝ 七分支分类器转移）已给出可编译的两行配方

> 本节正文用英文（`AGENTS.md` 语言政策把 `proofs/API-NOTES.md` 列为 English 产物；
> 现存 `.en.md` 镜像不再扩展，故不写第二份）。标识符、`#check` 输出与报错原文照抄。

**Probe inventory — every one compiled with `proofs/scripts/lake env lean <path>`, all 0 error / 0 warning:**

| Probe | Scope | Run (from the repo root) |
|---|---|---|
| `theories/hammond/probes/hammond-api-sign-div.lean` | A: division/order signs, the `tsCoord` threshold table, negative denominator | `proofs/scripts/lake env lean theories/hammond/probes/hammond-api-sign-div.lean` |
| `theories/hammond/probes/hammond-api-field-identities.lean` | B: the five core identities + the skeleton's remaining algebraic identities (`gapProduct_eq_crossing_energy`, `gapProduct_eq_gapReactant_neg`, `tsCoord_zero`, `tsCoord_at_lam`, `lefflerSecant_symm`, sign of the secant) | same command with the file name swapped |
| `theories/hammond/probes/hammond-api-cast-classifier.lean` | C: the ℚ→ℝ transfer of the seven-branch classifier (highest risk) + `tsCoordQ_cast` | as above |
| `theories/hammond/probes/hammond-api-zone-char.lean` | D: all seven zone characterizations; G: non-vacuity witnesses; structural-regime lemmas | as above |
| `theories/hammond/probes/hammond-api-rat-compute.lean` | E: `decide` vs `norm_num` domains; ℚ-side zone characterizations; cross-link to `Marcus.Rat.zoneQ` | as above |
| `theories/hammond/probes/hammond-api-crossmodule.lean` | F: cross-module names + the definitional bridge `barrier = gapReactant` | as above |

---

### A. Division/order — sign of a quotient with a positive denominator

`#check` output (verbatim; instance-binder index suffixes joined when a signature wraps):

```
@div_pos_iff_of_pos_right : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < b → (0 < a / b ↔ 0 < a)
@div_pos_iff_of_pos_left : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < a → (0 < a / b ↔ 0 < b)
@div_lt_one : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < b → (a / b < 1 ↔ a < b)
@one_lt_div : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < b → (1 < a / b ↔ b < a)
@div_le_one : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < b → (a / b ≤ 1 ↔ a ≤ b)
@one_le_div : ∀ {α : Type u_1} [LinearOrderedSemifield α] {a b : α}, 0 < b → (1 ≤ a / b ↔ b ≤ a)
@div_lt_iff₀ : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosStrictMono G₀], 0 < c → (b / c < a ↔ b < a * c)
@lt_div_iff₀ : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosStrictMono G₀], 0 < c → (a < b / c ↔ a * c < b)
@div_le_iff₀ : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosMono G₀], 0 < c → (b / c ≤ a ↔ b ≤ a * c)
@le_div_iff₀ : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosMono G₀], 0 < c → (a ≤ b / c ↔ a * c ≤ b)
@div_lt_div_iff_of_pos_right : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [LinearOrder G₀] [ZeroLEOneClass G₀]
  {a b c : G₀} [PosMulStrictMono G₀] [MulPosStrictMono G₀], 0 < c → (a / c < b / c ↔ a < b)
@div_le_div_iff_of_pos_right : ∀ {G₀ : Type u_1} [GroupWithZero G₀] [LinearOrder G₀] [ZeroLEOneClass G₀]
  {a b c : G₀} [PosMulStrictMono G₀] [MulPosStrictMono G₀], 0 < c → (a / c ≤ b / c ↔ a ≤ b)
@div_lt_div_right_of_neg : ∀ {α : Type u_1} [LinearOrderedField α] {a b c : α}, c < 0 → (a / c < b / c ↔ b < a)
@div_le_div_right_of_neg : ∀ {α : Type u_1} [LinearOrderedField α] {a b c : α}, c < 0 → (a / c ≤ b / c ↔ b ≤ a)
@div_lt_iff_of_neg : ∀ {α : Type u_1} [LinearOrderedField α] {a b c : α}, c < 0 → (b / c < a ↔ a * c < b)
@lt_div_iff_of_neg : ∀ {α : Type u_1} [LinearOrderedField α] {a b c : α}, c < 0 → (a < b / c ↔ b < a * c)
@div_eq_iff : ∀ {G₀ : Type u_1} [GroupWithZero G₀] {a b c : G₀}, b ≠ 0 → (a / b = c ↔ a = c * b)
@eq_div_iff : ∀ {G₀ : Type u_1} [GroupWithZero G₀] {a b c : G₀}, b ≠ 0 → (c = a / b ↔ c * b = a)
@div_neg_iff : ∀ {α : Type u_1} [LinearOrderedField α] {a b : α}, a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
@div_nonpos_iff : ∀ {α : Type u_1} [LinearOrderedField α] {a b : α}, a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b
@div_neg_of_neg_of_pos : ∀ {α : Type u_1} [LinearOrderedField α] {a b : α}, a < 0 → 0 < b → a / b < 0
@sub_ne_zero : ∀ {G : Type u_1} [AddGroup G] {a b : G}, a - b ≠ 0 ↔ a ≠ b
@zero_div : ∀ {G₀ : Type u_1} [GroupWithZero G₀] (a : G₀), 0 / a = 0
@two_ne_zero : ∀ {α : Type u_1} [Zero α] [OfNat α 2] [NeZero 2], 2 ≠ 0
```

Verdicts: **all of the above exist, none is deprecated (`#check` emits no deprecation warning),
and all the `_iff₀` / `_of_pos_right` names are `↔` (usable with `rw`)**.

| Name | Verdict |
|---|---|
| `div_pos_iff_of_pos_right` | exists; `@[simp]`, `0 < b → (0 < a / b ↔ 0 < a)` |
| `div_pos_iff_of_pos_left` | exists; mirror form (`0 < a → (0 < a / b ↔ 0 < b)`) |
| `div_lt_one` / `one_lt_div` / `div_le_one` / `one_le_div` | exist; all `0 < b → (a / b ⋚ 1 ↔ a ⋚ b)` / `(1 ⋚ a / b ↔ b ⋚ a)` |
| `div_lt_iff₀` / `lt_div_iff₀` / `div_le_iff₀` / `le_div_iff₀` | exist (current names; the old `div_lt_iff` / `lt_div_iff` are deprecated — see the Ban list) |
| `div_lt_div_iff_of_pos_right` / `div_le_div_iff_of_pos_right` | exist; same-denominator comparison |
| `div_lt_div_right_of_neg` / `div_le_div_right_of_neg` | exist; `LinearOrderedField` only, right side is the *reversed* order `b < a` |
| `div_lt_iff_of_neg` / `lt_div_iff_of_neg` | exist; `LinearOrderedField` only |
| `div_eq_iff` / `eq_div_iff` | exist; note `div_eq_iff` matches `a / b = c`, `eq_div_iff` matches `c = a / b` |
| `div_neg_iff` / `div_nonpos_iff` | exist but are **general disjunctions** (`a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b`) — usable, but the `_iff₀` route is shorter |
| `div_neg_iff_of_pos_right` | **DOES NOT EXIST** (lead's finding, re-confirmed) |
| `div_neg_iff_of_pos_left`, `div_nonpos_iff_of_pos_right`, `div_le_iff_of_pos_right`, `div_lt_zero_iff`, `div_le_zero_iff` | **DO NOT EXIST** (measured this round) |

Measured errors for the non-existent names (scratch probe, verbatim):

```
error: unknown identifier 'div_neg_iff_of_pos_right'
error: unknown identifier 'div_neg_iff_of_pos_left'
error: unknown identifier 'div_nonpos_iff_of_pos_right'
error: unknown identifier 'div_le_iff_of_pos_right'
error: unknown identifier 'div_lt_zero_iff'
error: unknown identifier 'div_le_zero_iff'
```

**The gap closed — three verified routes for `(lam - x) / (2 * lam) < 0 ↔ lam < x` under `0 < lam`**
(`h2 : 0 < 2 * lam := by linarith` in each; all three compile in `hammond-api-sign-div.lean`):

1. **Shortest (recommended)** — `div_lt_iff₀` + `linarith`:
   ```lean
   unfold tsCoord
   have h2 : (0 : ℝ) < 2 * lam := by linarith
   rw [div_lt_iff₀ h2, zero_mul]
   constructor <;> intro h <;> linarith
   ```
   (the `zero_mul` step is optional; without it `linarith` still closes the goal)
2. **General disjunction** — `rw [div_neg_iff]` then kill the impossible branch:
   `rintro (⟨h, hc⟩ | ⟨h, hc⟩) <;> linarith`, and the `(⟸)` direction is
   `Or.inr ⟨by linarith, h2⟩`.
3. **Two divisions** — rewrite `0` as `0 / (2 * lam)` and use `div_lt_div_iff_of_pos_right`:
   ```lean
   rw [show (0 : ℝ) = 0 / (2 * lam) by rw [zero_div]]
   rw [div_lt_div_iff_of_pos_right h2]
   constructor <;> intro h <;> linarith
   ```
   ⚠️ `div_lt_div_right_of_neg` does **not** apply here (it needs a *negative* denominator), and
   `sub_neg` / `lt_iff_not_le` are not needed at all.

**The `≤ 0` version** is the same with `div_le_iff₀` (or `div_nonpos_iff`):
`(lam - x) / (2 * lam) ≤ 0 ↔ lam ≤ x` — verified, also `zero_mul` optional.

**Full `tsCoord` threshold table** (all verified in the probe, `hlam : 0 < lam` unless noted):

| Goal | Recipe |
|---|---|
| `0 < tsCoord lam x ↔ x < lam` | `rw [div_pos_iff_of_pos_right h2]` |
| `tsCoord lam x < 0 ↔ lam < x` | `rw [div_lt_iff₀ h2, zero_mul]` |
| `tsCoord lam x < 1 ↔ -lam < x` | `rw [div_lt_one h2]` |
| `1 < tsCoord lam x ↔ x < -lam` | `rw [one_lt_div h2]` |
| `tsCoord lam x < 1/2 ↔ 0 < x` (**ReactantLike**) | `rw [div_lt_iff₀ h2]` |
| `1/2 < tsCoord lam x ↔ x < 0` (**ProductLike**) | `rw [lt_div_iff₀ h2]` |
| `tsCoord lam x ≤ 1/2 ↔ 0 ≤ x` | `rw [div_le_iff₀ h2]` |
| `1/2 ≤ tsCoord lam x ↔ x ≤ 0` | `rw [le_div_iff₀ h2]` |
| `tsCoord lam x = 1/2 ↔ x = 0` | `rw [div_eq_iff (mul_ne_zero two_ne_zero (ne_of_gt hlam))]` |
| `tsCoord lam x₂ < tsCoord lam x₁ ↔ x₁ < x₂` | `rw [div_lt_div_iff_of_pos_right h2]` |
| `tsCoord lam x₂ ≤ tsCoord lam x₁ ↔ x₁ ≤ x₂` | `rw [div_le_div_iff_of_pos_right h2]` |
| `0 < tsCoord lam x ∧ tsCoord lam x < 1 ↔ -lam < x ∧ x < lam` | `rw [div_pos_iff_of_pos_right h2, div_lt_one h2]` |
| with `lam < 0`: `tsCoord lam x < 0 ↔ x < lam` | `rw [div_lt_iff_of_neg (by linarith : (2:ℝ) * lam < 0)]` |
| with `lam < 0`: `tsCoord lam x₁ < tsCoord lam x₂ ↔ x₁ < x₂` | `rw [div_lt_div_right_of_neg (by linarith : (2:ℝ) * lam < 0)]` |

⚠️ `eq_div_iff` **only matches `?c = ?a / ?b`**: rewriting `tsCoord lam x = 1 / 2` with it fails
(measured): `error: tactic 'rewrite' failed, did not find instance of the pattern in the target
expression ?m = ?m / (2 * lam)` — because the supplied nonzero proof fixes the implicit
denominator to `2 * lam`. Use `div_eq_iff` for that orientation.

---

### B. Field normalization on the five core identities

Verdict: **there is no "definitional field identity" among them** — bare `ring` and bare
`ring_nf` (no hypotheses) fail on all five, because `ring`/`ring_nf` never read the context.
The working pattern is `unfold … ; field_simp ; ring`, and `field_simp` **discharges the
`≠ 0` side conditions from the context itself** (`hlam`, and a `≠ 0` hypothesis for
`x₂ - x₁`), so no explicit `have h4 : (4 * lam : ℝ) ≠ 0 := …` is required.

| # | Identity (planned hypotheses) | Shortest verified recipe | Hypotheses consumed | `ring`/`ring_nf` alone? |
|---|---|---|---|---|
| B1 | `reactantSurface lam q = productSurface lam dG q ↔ q = tsCoord lam (-dG)` (`lam ≠ 0`) | `have h2 : (2*lam) ≠ 0 := mul_ne_zero two_ne_zero hlam; unfold …; rw [eq_div_iff h2]; constructor <;> intro h <;> nlinarith [h]` | `hlam` (via `h2`); **`nlinarith`, not `linarith`** (needs `(q-1)^2` expanded) | ✗; statement is false at `lam = 0` |
| B2 | `gapReactant lam (-dG) = reactantSurface lam (tsCoord lam (-dG))` (`lam ≠ 0`) | `unfold …; field_simp; ring` | `hlam` (both denominators) — no `have` needed | ✗ (`field_simp; ring` fails with no hypothesis; `ring_nf` too) |
| B3 | `lefflerSecant lam x₁ x₂ = tsCoord lam ((x₁+x₂)/2)` (`0 < lam`, `x₁ ≠ x₂`) | `have hx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr h12.symm; unfold …; field_simp; ring` | `hlam` **and** `h12` — but `h12` must be **restated as `x₂ - x₁ ≠ 0`** (`field_simp` cannot derive it from `x₁ ≠ x₂`); alternative one-liner: `field_simp [sub_ne_zero.mpr h12.symm]; ring` | ✗ |
| B4 | `tsCoord lam (-x) = 1 - tsCoord lam x` (`lam ≠ 0`) | `unfold …; field_simp; ring` | `hlam` | ✗; false at `lam = 0` |
| B5 | `gapProduct lam x - gapReactant lam x = x` (`lam ≠ 0`) | `unfold …; field_simp; ring` (alternative: insert `rw [div_sub_div_same]` first) | `hlam` | ✗; false at `lam = 0` |

Extra identities from `theories/hammond/probes/hammond-statement-skeleton.lean`, all verified:

| Identity | Recipe | Note |
|---|---|---|
| `gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG` (`lam ≠ 0`) | `unfold …; field_simp; ring` | same shape as B2 |
| `gapProduct lam x = gapReactant lam (-x)` (**no hypothesis**) | `unfold …; ring` | genuine ring identity |
| `tsCoord lam 0 = 1/2` (`lam ≠ 0`) | `unfold …; field_simp; ring` | |
| `tsCoord lam lam = 0` (**no hypothesis**) | `unfold tsCoord; rw [sub_self, zero_div]` | ⚠️ keeping the skeleton's `hlam : lam ≠ 0` here triggers `warning: unused variable 'hlam'` |
| `lefflerSecant lam (x-1) (x+1) = tsCoord lam x` (`0 < lam`) | `unfold …; field_simp; ring` | `field_simp` also discharges `(x+1)-(x-1) = 2 ≠ 0` |
| `lefflerSecant lam x₁ x₂ < 0 ↔ lam < (x₁+x₂)/2` (`0 < lam`, `x₁ ≠ x₂`) | `rw [lefflerSecant_eq_tsCoord hlam h]` then the A-route `rw [div_lt_iff₀ h2, zero_mul]` | composition pattern for `lefflerSecant_neg_iff_inverted` |

Measured failure details worth not retrying:

* B3 with `h12 : x₁ ≠ x₂` but without the restatement: `field_simp; ring` leaves
  `⊢ lam * x₁ ^ 2 * (-(lam * x₁ * 4) + lam * x₂ * 4)⁻¹ * 4 + … = lam * 2 + (-x₁ - x₂)`
  (the `lam` denominators *were* cleared; `x₂ - x₁` was not).
* B2 with no hypothesis: `field_simp` cannot discharge `lam ≠ 0` and leaves `lam⁻¹` terms.
* `unfold …; ring` / `ring_nf` with no hypothesis, e.g. B4: leftover goal
  `⊢ lam * lam⁻¹ * (1 / 2) + x * lam⁻¹ * (1 / 2) = 1 + lam * lam⁻¹ * (-1 / 2) + x * lam⁻¹ * (1 / 2)`.

---

### C. `if`-chain classifier transfer — SOLVED: `norm_cast` (this was the milestone's highest risk)

```lean
theorem hammondZoneQ_eq_hammondZone (lam x : ℚ) :
    hammondZoneQ lam x = hammondZone (lam : ℝ) (x : ℝ) := by
  unfold hammondZoneQ hammondZone
  norm_cast
```

**Two tactic lines, no hypotheses, closes all seven branches** (`hammond-api-cast-classifier.lean`).
`norm_cast` rewrites every ℝ-side test back into its ℚ-side twin — `↑x = ↑lam` → `x = lam`,
`↑x = -↑lam` → `x = -lam` (through `Rat.cast_neg`), `↑x < -↑lam`, `↑lam < ↑x`, `↑x = 0` →
`x = 0` (`Rat.cast_eq_zero`), and `0 < ↑x` (including the numeral `0`) — after which the two
`if`-chains are syntactically identical. Two equivalent formulations also compile:
`simp only [hammondZoneQ, hammondZone]; norm_cast`, and the downstream
`hammondZoneQ lam x = z ↔ hammondZone (lam : ℝ) (x : ℝ) = z` by `rw [hammondZoneQ_eq_hammondZone]`.

`#check` of the cast family used (verbatim):

```
@Rat.cast_lt : ∀ {p q : ℚ} {K : Type u_1} [LinearOrderedField K], ↑p < ↑q ↔ p < q
@Rat.cast_le : ∀ {p q : ℚ} {K : Type u_1} [LinearOrderedField K], ↑p ≤ ↑q ↔ p ≤ q
@Rat.cast_eq_zero : ∀ {α : Type u_1} [DivisionRing α] [CharZero α] {p : ℚ}, ↑p = 0 ↔ p = 0
@Rat.cast_neg : ∀ {α : Type u_1} [DivisionRing α] (q : ℚ), ↑(-q) = -↑q
@Rat.cast_inv : ∀ {α : Type u_1} [DivisionRing α] [CharZero α] (p : ℚ), ↑p⁻¹ = (↑p)⁻¹
@Rat.cast_div : ∀ {α : Type u_1} [DivisionRing α] [CharZero α] (p q : ℚ), ↑(p / q) = ↑p / ↑q
@Rat.cast_ofNat : ∀ {α : Type u_1} [DivisionRing α] (n : ℕ) [n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_zero : ∀ {α : Type u_1} [DivisionRing α], ↑0 = 0
@Rat.cast_inj : ∀ {α : Type u_1} [DivisionRing α] [CharZero α] {p q : ℚ}, ↑p = ↑q ↔ p = q
```

Verdict: all exist; `cast_lt` / `cast_le` / `cast_inj` / `cast_eq_zero` are `↔`. ⚠️ `Rat.cast_lt`
has an **implicit `K`**: `rw [← Rat.cast_lt]` alone fails with
`error: typeclass instance problem is stuck, it is often due to metavariables / LinearOrderedField ?m.99703`
— write `← (Rat.cast_lt (K := ℝ))` (same trap as `Rat.cast_inj`, which needs `(α := ℝ)`).

Measured dead ends (do not retry; recorded in the probe):

* `unfold …; push_cast; rfl` → `error: tactic 'rfl' failed, the left-hand side … is not definitionally equal to the right-hand side …` (`push_cast` has no compound cast to push; it is a no-op here).
* `simp only [hammondZoneQ, hammondZone, Rat.cast_lt, Rat.cast_inj, Rat.cast_eq_zero, ← Rat.cast_neg, ← Rat.cast_zero]` → `error: tactic 'simp' failed, nested error: maximum recursion depth has been reached` (the backward `← Rat.cast_neg` loops).
* `split_ifs with h1 … h6 <;> simp_all [Rat.cast_lt, …]` → many unsolved `⊢ False`.
* The `by_cases` transcription of the Marcus 3-branch `zoneQ_eq_zone` (`simp [h, h']` with casted counterparts) does not scale to 7 branches: it stops at nested `if`s such as
  `⊢ (if -lam = lam then HZone.atReactant else HZone.atProduct) = if -↑lam = ↑lam then HZone.atReactant else HZone.atProduct`.
* The numeric bridge `((tsCoordQ lam x : ℚ) : ℝ) = tsCoord (lam : ℝ) (x : ℝ)` is **not** closed by `push_cast` alone: `unfold tsCoordQ tsCoord; push_cast; ring` does compile, but `… ; push_cast` leaves a goal (same "tail rule" as the Marcus `barrierQ_cast`: `push_cast` needs a trailing `ring`).

---

### D. Zone-characterization recipe (one instance requested; all seven delivered)

For `hammondZone_eq_early_iff {lam x : ℝ} (hlam : 0 < lam) :
hammondZone lam x = HZone.early ↔ 0 < x ∧ x < lam` — **shortest working proof (7 lines)**:

```lean
  unfold hammondZone
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    first
      | exact iff_of_true rfl ⟨h6, lt_of_le_of_ne (le_of_not_gt h4) h1⟩
      | exact iff_of_false (by decide) (by rintro ⟨hx, hy⟩; linarith)
```

The uniform, mechanical version (28 lines, same file) writes the seven leaves out explicitly;
the `first` alternative above needs `h1 / h4 / h6`, which exist exactly in the `early` leaf.
`by decide` discharges the constructor inequality from the derived `DecidableEq`.

Why it works: `split_ifs with h1 … h6` produces exactly the seven chain leaves and hands each
one the accumulated (negated) branch tests; the `early` leaf then has `h6 : 0 < x` and needs
`x < lam`, i.e. `h4 : ¬ lam < x` plus `h1 : ¬ x = lam` through `lt_of_le_of_ne (le_of_not_gt h4) h1`.

All seven, verified `0 < lam` (`hammond-api-zone-char.lean`):

| Zone | Characterization | Extra note |
|---|---|---|
| `atReactant` | `x = lam` | **no hypothesis needed** (true at `lam = 0` as well) — the skeleton's `hlam` is unused and warns |
| `atProduct` | `x = -lam` | needs `0 < lam` (leaves 1–2 closed by `by rw [h1]; linarith`) |
| `beyondProduct` | `x < -lam` | needs `0 < lam` |
| `beyondReactant` | `lam < x` | needs `0 < lam` |
| `half` | `x = 0` | ⚠️ last leaf: use `h5` directly; `by rintro rfl; linarith` fails there because it becomes the *propositional* absurdity `¬ (0 : ℝ) < 0` (`error: linarith failed to find a contradiction`) |
| `early` | `0 < x ∧ x < lam` | as above |
| `late` | `-lam < x ∧ x < 0` | last leaf: `⟨lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2), lt_of_le_of_ne (le_of_not_gt h6) h5⟩` |

Measured dead ends: `unfold; split_ifs <;> simp_all <;> linarith` fails (`linarith` cannot
digest the `False ↔ …` shape `simp_all` leaves); `… <;> omega` fails
(`omega` supports neither `ℝ` nor `ℚ`: `error: omega could not prove the goal: No usable
constraints found …`); `simp [hammondZone]` leaves the whole chain untouched. `decide` cannot
help on the ℝ side (no computable `Decidable` for `ℝ`); on the ℚ side it cannot help either
because the characterization has free variables (see E for the closed-goal case).

The same recipe transfers verbatim to ℚ (`zoneQ_early_iff`, `zoneQ_late_iff`,
`zoneQ_atReactant_iff`, `zoneQ_beyondReactant_iff`, `zoneQ_half_iff` in
`hammond-api-rat-compute.lean`). ⚠️ The skeleton states the ℚ `late` lemma as
`x < 0 ∧ -lam < x` — the **opposite conjunct order** from the ℝ-side lemma; the
`rintro ⟨hx, -⟩` / `rintro ⟨-, hx⟩` patterns must be swapped in the corresponding leaves.

Structural-regime lemmas (verified): `tsCoord_mem_iff` via
`rw [div_pos_iff_of_pos_right h2, div_lt_one h2]`; `reactionRegion_pos`,
`not_reactionRegion_of_nonpos` and `tsCoord_lt_zero_iff_inverted` are one `unfold … at h;
linarith` / the A-route respectively.

---

### E. ℚ-side computation — `decide` vs `norm_num` (refinement of the Marcus-round rule)

| Goal | `decide` | Working recipe |
|---|---|---|
| `hammondZoneQ 1 0 = HZone.half` | ✅ | `by decide` |
| `hammondZoneQ 1 1 = HZone.atReactant` | ✅ | `by decide` |
| `hammondZoneQ 1 3 = HZone.beyondReactant` | ✅ | `by decide` |
| `hammondZoneQ 0 0 = HZone.atReactant` | ✅ | `by decide` |
| `hammondZoneQ 1 (3/4) = HZone.early` | ❌ | `by norm_num [hammondZoneQ]` |
| `hammondZoneQ 1 (-1/2) = HZone.late` | ❌ | `by norm_num [hammondZoneQ]` |
| `hammondZoneQ (6/5) (12/5) = HZone.beyondReactant` | ❌ | `by norm_num [hammondZoneQ]` |
| `tsCoordQ 1 0 = 1/2` | ❌ | `by norm_num [tsCoordQ]` |
| `tsCoordQ (6/5) (1/20) = 23/48` | ❌ | `by norm_num [tsCoordQ]` |
| `lefflerSecantQ (6/5) (3/5) (12/5) = -1/8` | ❌ | `by norm_num [lefflerSecantQ, gapReactantQ]` |

Rule: **`decide` needs the whole evaluated expression to stay division-free** — it is not only
about the literals: `tsCoordQ 1 0 = 1/2` fails although both arguments are integers, because
`tsCoordQ` itself divides. Measured `decide` error:

```
error: tactic 'decide' failed for proposition
  hammondZoneQ 1 (3 / 4) = HZone.early
since its 'Decidable' instance
  instDecidableEqHZone (hammondZoneQ 1 (3 / 4)) HZone.early
did not reduce to 'isTrue' or 'isFalse'.
```

⚠️ `norm_num` must be given **every** definition in the expression: `norm_num [lefflerSecantQ]`
fails with `error: unsolved goals ⊢ (gapReactantQ (6 / 5) (3 / 5) - gapReactantQ (6 / 5) (12 / 5)) / (9 / 5) = -(1 / 8)`.

⚠️ **`native_decide` is banned**: it does evaluate the division cases, but measured
`#print axioms native_decide_probe` → `[propext, Lean.ofReduceBool]`, and `Lean.ofReduceBool`
∉ `ALLOWED_AXIOMS` ⇒ `proofs/scripts/axioms.sh` would FAIL on any delivered theorem using it.
Use `norm_num`.

Cross-link to the Marcus decision layer (verified in `hammond-api-rat-compute.lean`):

```lean
theorem zoneQ_beyondReactant_iff_marcusInverted {lam x : ℚ} (hlam : 0 < lam) :
    hammondZoneQ lam x = HZone.beyondReactant ↔
      PhotoLean.Marcus.Rat.zoneQ lam x = PhotoLean.Marcus.Zone.inverted := by
  rw [zoneQ_beyondReactant_iff hlam, ← (Rat.cast_lt (K := ℝ)),
    PhotoLean.Marcus.Rat.zoneQ_inverted_iff]
```

---

### F. Cross-module names (Marcus → Hammond) — all exist; the bridge is `rfl`

`#check` output (verbatim, `@`-form; `def`s print their type, so argument names are from the sources):

```
Marcus.barrier : ℝ → ℝ → ℝ                                     -- PhotoLean/Marcus/Basic.lean:50
Marcus.InvertedRegion : ℝ → ℝ → Prop                           -- Basic.lean:60  (`def … := lam < x`)
Marcus.Zone : Type                                             -- Basic.lean:84  (inductive, 3 ctors)
Marcus.zone : ℝ → ℝ → Marcus.Zone                              -- Basic.lean:93
Marcus.rate : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ                            -- Basic.lean:55
Marcus.Rat.zoneQ : ℚ → ℚ → Marcus.Zone                         -- RatModel.lean:54
Marcus.Rat.barrierQ : ℚ → ℚ → ℚ                                -- RatModel.lean:60
Marcus.lamInner : ℝ → ℝ → ℝ                                    -- Reorg.lean:98
Marcus.lamOuter : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ                    -- Reorg.lean:102
@Marcus.lamInner_pos : ∀ {kk : ℝ}, 0 < kk → ∀ {dq : ℝ}, dq ≠ 0 → 0 < Marcus.lamInner kk dq
@Marcus.lam_total_pos : ∀ {lamIn lamOut : ℝ}, 0 ≤ lamIn → 0 < lamOut → 0 < lamIn + lamOut
@Marcus.hgeom_of_nonoverlap : ∀ {a1 a2 R : ℝ}, 0 < a1 → 0 < a2 → a1 + a2 ≤ R →
  1 / R < 1 / (2 * a1) + 1 / (2 * a2)
@Marcus.descriptor_sharp : ∀ {kB T : ℝ}, 0 < kB → 0 < T → ∀ (A lam : ℝ),
  (∀ (x : ℝ), 0 < Marcus.rate A lam kB T x) ∧ Marcus.InvertedDescriptor A lam kB T ↔ 0 < A ∧ 0 < lam
Marcus.Rat.zoneQ_eq_zone : ∀ (lam x : ℚ), Marcus.Rat.zoneQ lam x = Marcus.zone ↑lam ↑x
Marcus.Rat.barrierQ_cast : ∀ (lam x : ℚ), ↑(Marcus.Rat.barrierQ lam x) = Marcus.barrier ↑lam ↑x
Marcus.Rat.zoneQ_inverted_iff : ∀ (lam x : ℚ), Marcus.Rat.zoneQ lam x = Marcus.Zone.inverted ↔ ↑lam < ↑x
```

Verdict: **exists for all 13 requested names** (fully-qualified, no drift), with two import notes:

* `PhotoLean.Marcus.descriptor_sharp` lives in `PhotoLean/Marcus/Sharp.lean`, which the four
  modules in the task list do **not** import — the Hammond module citing it must
  `import PhotoLean.Marcus.Sharp` (`Basic`/`Rate`/`RatModel`/`Reorg` cover the other 12).
* The ℚ bridges `zoneQ_eq_zone`, `barrierQ_cast`, `zoneQ_inverted_iff` are reusable templates
  for the Hammond ℚ layer (C and E above).

**The `rfl` bridge** (verified, `hammond-api-crossmodule.lean`):

```lean
example (lam x : ℝ) : PhotoLean.Marcus.barrier lam x = (lam - x) ^ 2 / (4 * lam) := rfl
theorem gapReactant_eq_barrier (lam x : ℝ) : gapReactant lam x = PhotoLean.Marcus.barrier lam x := rfl
theorem barrier_eq_gapReactant (lam x : ℝ) : PhotoLean.Marcus.barrier lam x = gapReactant lam x := rfl
```

⇒ the planned `barrier_eq_gapReactant` is a **`rfl`**, not a `ring`/`field_simp` job: the two
definitions have literally the same body. Likewise `InvertedRegion lam x` **is** `lam < x` by
`rfl`, and `rate A lam kB T x` **is** `A * Real.exp (-(barrier lam x) / (kB * T))` by `rfl`.

### G. Non-vacuity witnesses (all verified)

| Witness | Proof |
|---|---|
| `∃ x : ℝ, tsCoord lam x < 1/2` (`0 < lam`) | `refine ⟨lam / 2, ?_⟩; unfold tsCoord; rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2*lam)]; linarith` |
| `∃ x : ℝ, 1/2 < tsCoord lam x` (`0 < lam`) | witness `-lam / 2`, `rw [lt_div_iff₀ …]` |
| `∃ x : ℝ, ReactionRegion lam x` / `∃ x, -lam < x ∧ x < lam` (`0 < lam`) | witness `0`; `⟨0, by constructor <;> linarith⟩` |
| `∃ x₁ x₂, x₁ < x₂ ∧ tsCoord lam x₂ < tsCoord lam x₁` (`0 < lam`) | `⟨0, 1, by norm_num, hammondDescriptor_of_pos hlam 0 1 (by norm_num)⟩` |
| `∃ x₁ x₂, x₁ < x₂ ∧ ¬ (tsCoord 0 x₂ < tsCoord 0 x₁)` | `⟨0, 1, by norm_num, ?_⟩; rw [tsCoord_zero_lam, tsCoord_zero_lam]; norm_num` |
| `¬ HammondDescriptor 0` | `intro h; have := h 0 1 (by norm_num); rw [tsCoord_zero_lam, tsCoord_zero_lam] at this; norm_num at this` |

with `tsCoord_zero_lam (x : ℝ) : tsCoord 0 x = 0 := by unfold tsCoord; norm_num` (the
division-by-zero convention, as in the Marcus `barrier_zero_lam`).

---

### 可靠域 (reliable domain): which tactic closes which goal shape

| Goal shape | Tactic that closes it | Measured counter-domain |
|---|---|---|
| `a / c ⋚ b` / `a ⋚ b / c` with `0 < c` (or `c < 0`) | `rw [div_lt_iff₀ hc]` / `div_le_iff₀` / `lt_div_iff₀` / `le_div_iff₀` (negatively: `div_lt_iff_of_neg`, `lt_div_iff_of_neg`), then `linarith` | — |
| `a / c ⋚ b / c` (same denominator) | `rw [div_lt_div_iff_of_pos_right hc]` / `div_le_div_iff_of_pos_right`, or `_of_neg` for `c < 0`, then `linarith` | the `_of_neg` versions need `LinearOrderedField`, not just a semifield |
| quotient sign with a positive denominator | `div_lt_iff₀` / `div_le_iff₀` + `linarith` (routes 1–3 in A) | `div_neg_iff_of_pos_right` & friends do not exist |
| rational-function **identity** (all five B items) | `unfold …; field_simp; ring` (context supplies the `≠ 0` conditions) | `field_simp` on **inequalities**: `error: simp made no progress` (Marcus round D-4); `ring`/`ring_nf` alone: never consume hypotheses |
| `p / q = c` vs `c = p / q` | `div_eq_iff hb` (left) / `eq_div_iff hb` (right) — orientation is exact-match | `eq_div_iff` cannot rewrite `x = 1/2` style goals |
| seven-branch `if`-chain over ℚ vs ℝ | `unfold` + **`norm_cast`** | `push_cast` (+`rfl`), `simp only [← Rat.cast_neg, …]`, `split_ifs`+`simp_all` — all fail |
| `hammondZone lam x = HZone.Z ↔ <arithmetic>` | `unfold; split_ifs with h1 … h6` + `iff_of_true rfl …` / `iff_of_false (by decide) …` + `linarith` | `simp_all`+`linarith`, `omega`, `simp [hammondZone]` — all fail |
| closed ℚ goal, no division evaluated | `by decide` | any division (literal or inside the def) breaks it |
| closed ℚ goal with rational literals / defs | `by norm_num [def₁, def₂, …]` (all defs!) | `decide` (see above); `native_decide` (axiom `Lean.ofReduceBool`) |
| `Prop` with a casted counterpart | `Rat.cast_lt.mpr` / `Rat.cast_inj.mp` / `exact_mod_cast`; the cast family needs its field explicit: `Rat.cast_lt (K := ℝ)`, `Rat.cast_inj (α := ℝ)` | bare `rw [← Rat.cast_lt]` → stuck metavariable |
| definitional bridges between modules | `rfl` (`barrier = gapReactant`, `InvertedRegion = (· < ·)`, `rate = A * exp …`) | `ring` is unnecessary here but harmless |
| `∃`-witness with a division | pick the witness, `unfold`, `rw [div_lt_iff₀ …]`, `linarith` | — |

### 禁止使用清单 / warning traps (Hammond round additions)

1. **Non-existent** (measured `unknown identifier`): `div_neg_iff_of_pos_right`,
   `div_neg_iff_of_pos_left`, `div_nonpos_iff_of_pos_right`, `div_le_iff_of_pos_right`,
   `div_lt_zero_iff`, `div_le_zero_iff`.
2. **`native_decide` is forbidden** by the axiom discipline (`Lean.ofReduceBool`).
3. **Unused-hypothesis trap** (measured, this round): `linter.unusedVariables` fires
   `warning: unused variable 'hlam'` when the proof never touches the hypothesis — even though
   the hypothesis is part of the statement. Facts:
   * hypotheses consumed only by `field_simp` / `linarith` / `positivity` do **not** warn
     (measured on B2/B3/B4/B5 and on `{lam : ℝ} (hlam : 0 < lam) : lam ≠ 0 := by linarith`);
   * in the current statement skeleton the hypothesis is **redundant** for
     **`hammondZone_eq_atReactant_iff`** (`↔ x = lam`, true for every `lam`, including `lam = 0`)
     and **`tsCoord_at_lam`** (`tsCoord lam lam = 0` via `rw [sub_self, zero_div]`); the ℚ mirror
     `hammondZoneQ_eq_atReactant_iff` is unconditional as well — keeping `hlam` there produces a
     warning, dropping it does not change the mathematics;
   * the linter can also be silenced per-file with `set_option linter.unusedVariables false`.
4. **`eq_div_iff` vs `div_eq_iff`** orientation (see A), and **`Rat.cast_lt` / `Rat.cast_inj`
   need their field argument** when rewritten/applied (see C).
5. `omega` is useless for both ℝ and ℚ goals (`Nat`/`Int` only) — this round's measurements
   extend the Marcus-round G-group table.

### Alignment check with `theories/hammond/probes/hammond-statement-skeleton.lean`

Recipes verified for the planned statements (statement text unchanged): `crossing_iff` (B1);
`gapReactant_eq_crossing_energy` (B2); `gapProduct_eq_crossing_energy` (B-extra);
`gapProduct_sub_gapReactant` (B5); `gapProduct_eq_gapReactant_neg` (`ring`);
`tsCoord_neg` (B4); `tsCoord_zero`; `tsCoord_zero_lam`; `tsCoord_at_lam` (no hypothesis needed);
`tsCoord_mem_iff`; `reactionRegion_pos`; `not_reactionRegion_of_nonpos`;
`hammondZone_eq_{early,half,late,atReactant,atProduct,beyondReactant,beyondProduct}_iff` (D);
`tsCoord_antitone` (`div_lt_div_iff_of_pos_right`); `reactantLike_iff` / `productLike_iff` (A);
`lefflerSecant_eq_midpoint` (B3); `lefflerSecant_symm`; the secant's sign via
`lefflerSecant_eq_midpoint` + the A-route (feeds `lefflerSecant_neg_iff_inverted`);
`tsCoord_lt_zero_iff_inverted` (A-route + `unfold Marcus.InvertedRegion`);
`exists_reactantLike` / `exists_productLike` / `exists_reactionRegion` (G);
`exists_direction_reversal_of_eq` (G); `barrier_eq_gapReactant` (**`rfl`**, F);
`tsCoordQ_cast`, `gapReactantQ_cast`, `lefflerSecantQ_cast`, `hammondZoneQ_eq_hammondZone`,
`hammondZoneQ_eq_{early,half,late,atReactant,beyondReactant}_iff` and
`hammondZoneQ_beyondReactant_iff_inverted` (C/E);
`hammond_descriptor_of_pos` (`div_lt_div_iff_of_pos_right` + `linarith`).

API-wise nothing further is needed for the remaining statements; they are arithmetical assembly:
`hammond_lam_pos_of_descriptor` / `hammond_sharp` / `hammond_fails_of_nonpos` (use
`tsCoord_zero_lam` for `lam = 0` and the `lam < 0` monotonicity route `div_lt_div_right_of_neg`),
`conforms_iff_zone` (assemble the seven D-lemmas plus `lt_trichotomy x 0`),
`gap_compare_iff` (B5 + `linarith`), `hammondZoneQ_eq_{atProduct,beyondProduct}_iff`,
`hammond_descriptor_of_inner` / `_of_microscopic` / `_of_nonoverlap` (Marcus `lamInner` /
`lamOuter` / `lam_total_pos` / `hgeom_of_nonoverlap`, F).

---

## 2026-09-20 — 语句订正留痕：Hammond 骨架的两条**假语句**（H1 / H2）— lead — DONE

> 规则回顾：语句改动只允许两类原因 —— **API 漂移** 或 **数学缺陷**；两类都必须在 API 日志留痕。
> 这两条属于后者（骨架初稿为假），在**任何交付之前**修正，并由 prover + verifier 双方用内核反例交叉确认。

### (1) `gapProduct_eq_crossing_energy`（H1，`PhotoLean/Hammond/Basic.lean`）

- **原因**：逆反应的势垒是**相对产物井**（能量 `dG`）度量的；原式未做井参考，RHS 恰多出 `dG`。
- **内核反例**（`prover_a` 发现；verifier 独立复核）：
  `example : gapProduct 1 1 ≠ productSurface 1 (-1) (tsCoord 1 1) := by norm_num [gapProduct, productSurface, tsCoord]`
- **订正后（交付形态）**：
  `theorem gapProduct_eq_crossing_energy {lam dG : ℝ} (hlam : lam ≠ 0) :
      gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG)) - dG`
- **正向内核核对**（`lam = 3`, `dG = 1`）：`1/3 = 4/3 - 1` 成立；旧式 `1/3 ≠ 4/3` 被推翻。

### (2) `conforms_iff_structure` → `conforms_iff_zone`（H2，`PhotoLean/Hammond/Criterion.lean`）

- **原因**：原式把判决刻化成三个**符号谓词**的析取（`ReactantLike ∨ tsCoord = 1/2 ∨ ProductLike`），
  而这是 **`<` 三分律的恒真式**（对任意 `a`：`a < 1/2 ∨ a = 1/2 ∨ 1/2 < a`），**不刻画任何东西**（lead 审计发现）。
- **内核反例**（verifier 独立复核）：旧 RHS 恒真；旧语句在 `(lam, x) = (1, 2)` 处左真右假。
- **订正后（交付形态）**：改用**分类器**刻化，并在 `0 < lam` 下陈述：
  `theorem conforms_iff_zone {lam x : ℝ} (hlam : 0 < lam) :
      HammondConforms lam x ↔ hammondZone lam x = HZone.early ∨ hammondZone lam x = HZone.half
        ∨ hammondZone lam x = HZone.late`
  （非空转证据：`(1, 1/2)` 两侧真、`(6/5, 12/5)` 左假右假 —— verifier 已给。）

### 方法论后果（已写入 `proofs/EXPERIENCE.md`）

`statement-first` 不等于"只检查看起来有风险的语句"。骨架定稿前必须做一次**带反向对照的系统审计**
（`theories/hammond/probes/hammond-lead-audit.lean`：每条非平凡语句在具体有理点上实例化，
并在"必须为假"的点上验证其为假），否则一条假语句会以"prover 报障 + 语句变更"的昂贵方式暴露。

---

## 2026-09-20 — BEP round (Bell–Evans–Polanyi) — api_researcher — 5 probes + 1 statement skeleton, **all 0 error / 0 warning**; the two Sprint-0 statement corrections are folded in; the minimax and radius rows are kernel-verified end to end

> 本节正文用英文（`AGENTS.md` 语言政策把 `proofs/API-NOTES.md` 列为 English 产物；不写第二份镜像）。
> 标识符、`#check` 输出、报错与 warning 原文照抄。

### 1. Deliverables and compile evidence

| Artifact | Declarations | Run (repo root) | Result |
|---|---|---|---|
| `theories/BEP/probes/bep-statement-skeleton.lean` | **137** (105 theorems + 18 `def` + 12 `noncomputable def` + 2 `inductive`) | `proofs/scripts/lake env lean theories/BEP/probes/bep-statement-skeleton.lean` | **exit 0, 0 error, 105 warnings — all of them `declaration uses 'sorry'` (0 other warnings)** |
| `theories/BEP/probes/bep-api-algebra.lean` | 29 named (21 theorems + 8 defs) + 6 `example` | same command, filename swapped | exit 0, 0 error / 0 warning |
| `theories/BEP/probes/bep-api-abs-sqrt.lean` | 25 named (17 theorems + 8 defs) + 3 `example` | as above | exit 0, 0 error / 0 warning |
| `theories/BEP/probes/bep-api-rat.lean` | 41 named (21 theorems + 20 defs) + 19 `example` | as above | exit 0, 0 error / 0 warning |
| `theories/BEP/probes/bep-api-minimax.lean` | 22 named (14 theorems + 8 defs) | as above | exit 0, 0 error / 0 warning |
| `theories/BEP/probes/bep-api-zone.lean` | 11 named (9 theorems + 2 defs) + 14 `example` | as above | exit 0, 0 error / 0 warning |

Skeleton declaration count per milestone block (the lead's dispatch granularity):

| Block | Declarations | Content |
|---|---|---|
| B1 `Basic.lean` — plan §4.1 | 18 | 17 definitions + the `EPZone` inductive (9 constructors, plan order, `deriving DecidableEq, Repr`) |
| B1 `Basic.lean` — plan §4.2 | 15 | the description-layer theorems, incl. the nine `epZone_eq_*_iff` |
| (AUX, ℝ helpers for the B5a casts) | 2 | `alphaObs`, `lamOfPair` |
| B2 `Criterion.lean` — plan §5 | 28 | 19 numbered rows + 9 non-vacuity witnesses |
| B3 `Sharp.lean` — plan §6.1–§6.5 | 25 | radius theorem, monotonicities, minimax pair, hypothesis-necessity witnesses |
| (AUX, literal `sSup` form of the minimax block) | 7 | `epSupError`, its `BddAbove` witness, the two second-difference identities, `sSup_eq_of_le_of_mem`, the two `sSup` sharpness forms |
| B4 `Compose.lean` — plan §7 | 13 | 12 numbered rows + the AUX `secSlope = Hammond.lefflerSecant` bridge |
| B5a `RatModel.lean` — plan §8.1 | 11 | 10 definitions + `EPQVerdict` (6 constructors) |
| B5a `RatModel.lean` — plan §8.1 theorems | 18 | 13 plan-named + `qBepLine_cast` + the two reconstruction theorems + 2 decision witnesses |
| **total** | **137** | |

**Not covered by this round**: plan §8.2 (`PhotoLean/BEP/Instances.lean`, rows I1–I11). The plan's
table gives ids and theorem *names* but no signatures; guessing them is forbidden by the engine
rules, so the skeleton stops at B5a. A follow-up API round is required once
`theories/BEP/LITERATURE.md` fixes the literature families.

Plan-internal count mismatches seen while transcribing (recorded, not silently "fixed"):
§4.2 is titled "(13)" but lists 15 rows; §5's last row is titled "20–26" but lists 9 regime
non-vacuity lemmas; §8.1 says "Theorems (13)" and names 13 (the skeleton adds 5 AUX/the plan's
reconstruction counterpart).

### 2. The two statement corrections folded in (Sprint-0 risk probe → skeleton)

#### (1) `transfer` / `reverseTransfer` are the **linear-response** bodies (plan §4.1)

```lean
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)
noncomputable def reverseTransfer (lam x : ℝ) : ℝ := 1 / 2 + x / (2 * lam)
```

Consequences, all now consistent in the skeleton and in the probes:

| Row | Statement | Note |
|---|---|---|
| `transfer_thermoneutral` (plan §5 #6) | `transfer lam 0 = 1 / 2` | **no hypothesis** (`zero_div`, `sub_zero`) |
| `transfer_zero_lam` (plan §4.2 #4) | `transfer 0 x = 1 / 2` | degenerate value is `1/2`, **not** `0` (`mul_zero`, `div_zero`) |
| `transfer_eq_tsCoord` (plan §5 #5) | `(hlam : lam ≠ 0) : transfer lam x = (lam - x) / (2 * lam)` | a **genuine theorem** now (the Leffler/Brønsted identification); `unfold; field_simp` alone closes it |
| `transfer_eq_tsCoord_bridge` (plan §7 #3) | `(hlam : lam ≠ 0) : transfer lam x = Hammond.tsCoord lam x` | cross-module form |
| `transfer_add_reverse` (plan §5 #8) | `(hlam : lam ≠ 0) : transfer lam x + reverseTransfer lam x = 1` | pure **ring** identity — `hlam` is *not* consumed (`x / 0 = 0` cancels) |
| `reverseTransfer_eq_transfer_neg` (plan §5 #9) | `reverseTransfer lam x = transfer lam (-x)` | pure ring identity, no hypothesis needed |
| `secSlope_eq_transfer_mid` (plan §5 #10) | `(hlam : lam ≠ 0) (hh : h ≠ 0) : secSlope lam x h = transfer lam (x + h / 2)` | now needs `hlam`; `field_simp; ring` |
| `transfer_at_lam` / `transfer_at_neg_lam` (plan §6.1 #3/#4) | `(hlam : 0 < lam) : transfer lam lam = 0`, `transfer lam (-lam) = 1` | `field_simp` closes the first by itself |

**⚠️ The probe-local `transfer := (lam - x) / (2 * lam)` is NOT the delivered body.** It is the
discarded transition-state body; `bep-api-algebra.lean` keeps it under the explicit name
`transferTS` in a section marked `DISCARDED body`, together with `transfer_eq_transferTS`
(`transfer lam x = transferTS lam x` for `lam ≠ 0`) so that no prover copies an old recipe against
the new definition. The statement authority (`bep-statement-skeleton.lean`) uses the linear-response
form, hence `transfer_eq_tsCoord` requires `lam ≠ 0`.

#### (2) `qLamOfPair` — numerator and the `lam ≠ 0` premise (plan §8.1)

```lean
def qLamOfPair (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))
```

Kernel counterexamples (all in `bep-api-rat.lean`, `norm_num` closed):

| Fact | Evidence |
|---|---|
| the literal numerator `x₁^2 - x₂^2` returns `-λ` | `qLamOfPairLiteral 0 (qEact 2 0) 1 (qEact 2 1) = -2` while `qLamOfPair 0 (qEact 2 0) 1 (qEact 2 1) = 2` (λ = 2 at `x = 0, 1` with barriers `1/2, 1/8`) |
| the two forms are exact negatives | `qLamOfPairLiteral x₁ ea₁ x₂ ea₂ = -qLamOfPair x₁ ea₁ x₂ ea₂` (`rw [← neg_div]; ring`) |
| `lam ≠ 0` is **necessary** | `qEact 0 0 = 0`, `qEact 0 1 = 0`, the denominator `2*(1-0) - 4*(0-0) = 2 ≠ 0`, yet `qLamOfPair 0 (qEact 0 0) 1 (qEact 0 1) = 1/2 ≠ 0` |
| `hden` cannot be dropped | at the symmetric pair `(x, -x)` the numerator and the denominator vanish together: `qLamOfPair 1 (qEact 2 1) (-1) (qEact 2 (-1)) = 0`; the data pair is blind to λ (`eact 2 1 - eact 2 (-1) = eact 5 1 - eact 5 (-1)`) |

`qLamOfPair_reconstructs` in the plan's shape (and its ℝ twin `lamOfPair_reconstructs`) is proved:
`subst h₁; subst h₂; unfold qLamOfPair; rw [div_eq_iff hden]; unfold qEact at *; field_simp; ring`.

### 3. Verified names — exact signatures (verbatim `#check` output, joined at line wraps)

**A. Division / order / field** (all exist, none deprecated unless marked):

```
@div_eq_iff : ∀ {G₀} [GroupWithZero G₀] {a b c : G₀}, b ≠ 0 → (a / b = c ↔ a = c * b)
@eq_div_iff : ∀ {G₀} [GroupWithZero G₀] {a b c : G₀}, b ≠ 0 → (c = a / b ↔ c * b = a)
@div_mul_eq_mul_div : ∀ {α} [DivisionCommMonoid α] (a b c : α), a / b * c = a * c / b
@pow_two : ∀ {M} [Monoid M] (a : M), a ^ 2 = a * a
@sq_nonneg : ∀ {α} [Semiring α] [LinearOrder α] … (a : α), 0 ≤ a ^ 2
@sq_pos_of_ne_zero : ∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2
@div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b
@div_pos : 0 < a → 0 < b → 0 < a / b
@div_pos_iff_of_pos_right : 0 < b → (0 < a / b ↔ 0 < a)
@div_ne_zero : a ≠ 0 → b ≠ 0 → a / b ≠ 0
@div_zero : ∀ {G₀} [GroupWithZero G₀] (a : G₀), a / 0 = 0
@zero_div : 0 / a = 0
@sub_ne_zero : a - b ≠ 0 ↔ a ≠ b
@mul_ne_zero : a ≠ 0 → b ≠ 0 → a * b ≠ 0
@div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a / c ≤ b / c
@div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
@div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)
@div_lt_div_iff₀ : 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)
@div_le_div_iff_of_pos_right : 0 < c → (a / c ≤ b / c ↔ a ≤ b)
@div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)
@le_div_iff₀ : 0 < c → (a ≤ b / c ↔ a * c ≤ b)
@div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)
@lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b)
@div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b)
@div_lt_one : 0 < b → (a / b < 1 ↔ a < b)
@one_le_div / @div_le_one : the `1 ≤ ·` twins
@div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0   (general disjunction)
@mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c
@mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a
@neg_div : -a / b = -(a / b)           -- orientation matters, see §4
```

**B. Absolute value / intervals**:

```
@abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
@abs_add : |a + b| ≤ |a| + |b|
@abs_mul : |a * b| = |a| * |b|
@abs_div : |a / b| = |a| / |b|
@abs_of_nonneg : 0 ≤ a → |a| = a        -- and abs_of_pos / abs_of_neg / abs_of_nonpos / abs_neg
@le_abs_self : a ≤ |a|                  @neg_le_abs : -a ≤ |a|
@sq_le_sq : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b|   -- ROOT-LEVEL name (see §4)
@Set.mem_Icc : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b
@Set.right_mem_Icc : b ∈ Set.Icc a b ↔ a ≤ b     @Set.left_mem_Icc : a ∈ Set.Icc a b ↔ a ≤ b
@Set.Icc_subset_Icc_iff : a₁ ≤ b₁ → (Set.Icc a₁ b₁ ⊆ Set.Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂)
@not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q            @not_le : ¬a ≤ b ↔ b < a
```

**C. Square roots**:

```
@Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x
@Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x
Real.sqrt_sq_eq_abs : ∀ x, √(x ^ 2) = |x|
@Real.sqrt_mul_self : 0 ≤ x → √(x * x) = x     @Real.mul_self_sqrt : 0 ≤ x → √x * √x = x
@Real.sqrt_mul : 0 ≤ x → ∀ y, √(x * y) = √x * √y
Real.sqrt_nonneg : ∀ x, 0 ≤ √x
@Real.sqrt_pos : 0 < √x ↔ 0 < x
@Real.sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
@Real.le_sqrt : 0 ≤ x → 0 ≤ y → (x ≤ √y ↔ x ^ 2 ≤ y)
@Real.le_sqrt' : 0 < x → (x ≤ √y ↔ x ^ 2 ≤ y)
@Real.sqrt_le_sqrt : x ≤ y → √x ≤ √y          (unconditional!)
@Real.sqrt_lt_sqrt : 0 ≤ x → x < y → √x < √y
@Real.lt_sqrt : 0 ≤ x → (x < √y ↔ x ^ 2 < y)
@Real.sqrt_le_sqrt_iff : 0 ≤ y → (√x ≤ √y ↔ x ≤ y)
Real.sqrt_zero / Real.sqrt_one / @Real.sqrt_eq_zero_of_nonpos
```

**D. Supremum (the minimax block)**:

```
@sSup : {α} → [SupSet α] → Set α → α
@csSup_le : s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a
@le_csSup : BddAbove s → a ∈ s → a ≤ sSup s              -- boundedness argument comes FIRST
@csSup_eq_of_forall_le_of_forall_lt_exists_gt : s.Nonempty → (∀ a ∈ s, a ≤ b) → (∀ w < b, ∃ a ∈ s, w < a) → sSup s = b
@isLUB_csSup : s.Nonempty → BddAbove s → IsLUB s (sSup s)
@bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x
Real.instConditionallyCompleteLinearOrder : ConditionallyCompleteLinearOrder ℝ
Real.sSup_def : ∀ s, sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose ⋯ else 0
```

**E. ℚ decision layer**:

```
#synth Ord ℚ                        → LinearOrder.toOrd
#synth DecidableRel (· ≤ · : ℚ → ℚ → Prop) → Rat.instDecidableLe : (a b : ℚ) → Decidable (a ≤ b)
#synth DecidableRel (· < · : ℚ → ℚ → Prop) → Rat.instDecidableLt : (a b : ℚ) → Decidable (a < b)
@instDecidableRelLe : {α} → [Ord α] → DecidableRel LE.le
@Rat.cast_div / cast_add / cast_sub / cast_mul / cast_pow / cast_neg / cast_inv / cast_lt / cast_le /
 cast_abs / cast_one / cast_zero / cast_mk   (all verified; `cast_lt`/`cast_le` are `↔`)
@decide_eq_true_iff : decide p = true ↔ p        @of_decide_eq_true
@Rat.divInt_eq_div : ∀ n d, Rat.divInt n d = ↑n / ↑d
```

**F. Tactic domains (measured, not documented)**

| Tactic | Domain measured this round |
|---|---|
| `ring` | genuine polynomial identities incl. division-as-inverse (`transfer_add_reverse`, `reverseTransfer_eq_transfer_neg`, `secSlope_eq_lefflerSecant`, `bepDefect_even` after `field_simp`) |
| `ring_nf` | same; `ring_nf` did **not** close `qAlphaObs = qTransfer` at the midpoint (the denominator normalises but does not cancel) — the working route is an explicit `hkey : ea₁ - ea₂ = (x₂-x₁)*(2*lam-x₁-x₂)/(4*lam)` then `field_simp; ring` |
| `field_simp` | clears `lam ≠ 0`, `h ≠ 0`, `x₂ - x₁ ≠ 0`, `2*lam ≠ 0`, `4*lam ≠ 0`, `8*lam ≠ 0` from the context; **sometimes closes the goal by itself** (`transfer_eq_tsCoord`, `transfer_eq_tsCoord_bridge`, `transfer_eq_transferTS`, `transfer_at_lam`, `qTransfer_at_lam`, `bepBestLine_halves`'s first conjunct) — appending `ring` then errors with `no goals to be solved` |
| `linarith` / `nlinarith` | `nlinarith` needs its nonlinear hints supplied; the parabolas' monotonicity rows are `linarith` once the quadratic normal form is rewritten in |
| `positivity` | closes `0 < 4 * lam` from `0 < lam`, `0 ≤ w ^ 2 / (8 * lam)` from `0 < lam`, `0 ≤ 2 * √(lam * tol)` |
| `by decide` | **only** kernel-reducible rationals: integer literals and `Rat.divInt` literals. It **fails** on any comparison containing a `/`-literal, and it cannot even *synthesize* `Decidable` for a `def`-wrapped predicate before `unfold` |
| `by norm_num` | the workhorse of the ℚ layer (`≤`, `<`, `≠`, `=`, `|q| = r`); it has **no `abs` support on ℚ** (`|q| ≤ r` is left unsolved) |
| `native_decide` | works, but **BANNED**: `'nativeDecideWitness' depends on axioms: [propext, Lean.ofReduceBool]` and `Lean.ofReduceBool ∉ ALLOWED_AXIOMS` → `axioms.sh` FAIL |
| `exact_mod_cast` | moves ℚ comparisons to ℝ and back (verified both directions) |
| `push_cast` | the ℚ → ℝ transfer recipe is `unfold …; push_cast; ring` (7 cast lemmas verified) |

### 4. Failures and drift (mandatory section)

**Names that do not exist** (measured this round; verbatim errors):

```
error: unknown identifier 'div_nonneg_iff_of_pos_right'
error: unknown identifier 'div_nonneg_iff_of_pos_left'
error: unknown constant 'Set.mem_Icc_iff'
error: unknown constant 'Real.sqrt_lt_iff_lt_sq'
error: unknown constant 'Real.sq_le_sq'
error: unknown constant 'Real.sqrt_four'
error: unknown identifier 'le_sqrt''          -- the bare name; it is Real.le_sqrt'
error: unknown constant 'Rat.castRat'
error: unknown constant 'Rat.decLe'
error: unknown identifier 'div_nonneg_iff_of_pos_left'
```

Consequences for the plan's own proof sketches:

| Plan sketch says | Reality | Replacement |
|---|---|---|
| §6.1 #1 suggests `div_le_iff` / `le_div_iff` | those old names are deprecated | `div_le_iff₀` / `le_div_iff₀`; for the `0 ≤` quotient the shortest route is `le_div_iff₀` + `zero_mul` (there is **no** `div_nonneg_iff_of_pos_right`) |
| §6.2 #10 suggests `abs_pow` | not `#check`ed as such; the working route is `abs_div` + `abs_of_nonneg (sq_nonneg x)` + `abs_mul` + `abs_of_nonneg` | verified in `bep-api-abs-sqrt.lean` |
| anywhere `Real.sq_le_sq` | does not exist | root-level `sq_le_sq : a^2 ≤ b^2 ↔ |a| ≤ |b|`, or `sq_le_sq' : -b ≤ a → a ≤ b → a^2 ≤ b^2` |

**Deprecated (warning only, so `#check`ing them breaks a 0-warning probe — cite as comments):**

```
warning: `div_le_div_iff` has been deprecated: use `div_le_div_iff₀` instead
warning: `div_le_div_right` has been deprecated: use `div_le_div_iff_of_pos_right` instead
warning: `div_le_div_left` has been deprecated: use `div_le_div_iff_of_pos_left` instead
warning: `pow_le_pow_left` has been deprecated: use `pow_le_pow_left₀` instead
```

**Orientation traps measured:**

* `neg_div` is `-a / b = -(a / b)`, so turning `-(a / b)` into `(-a) / b` needs `rw [← neg_div]`
  (the forward rewrite fails with `did not find instance of the pattern in the target expression:
  -?b / ?a`). `div_neg` is `a / -b = -(a / b)`.
* `field_simp` does **not** discharge a `≠ 0` fact about `x₂ - x₁` from `h : x₁ ≠ x₂` — restate it
  (`sub_ne_zero.mpr (Ne.symm h)`), the same trap as the Hammond round.
* `rw [← hval]` inside a goal that still mentions `sSup` of a set built from `hval`'s subterms
  rewrites **inside the set** and silently changes the statement (measured; the fix is the explicit
  `sSup_eq_of_le_of_mem` helper).

### 5. Kernel-verified recipes for the risky rows

| Row | Status | Recipe |
|---|---|---|
| plan §6.2 #11 `epConformsOnWindow_iff_radius` | **verified end to end** | `(→)` evaluate at `x = -w` → `w^2/(4*lam) ≤ tol` → `div_le_iff₀` → `√(w^2) ≤ √(4*lam*tol)` via `Real.sqrt_sq hw` + `Real.sqrt_le_sqrt` + `Real.sqrt_mul`; `(←)` `abs_le.mpr hx` → `x^2 ≤ w^2` (`pow_le_pow_left₀` + `sq_abs`) → `(2*√(lam*tol))^2 = 4*lam*tol` (`mul_pow` + `Real.sq_sqrt`) |
| plan §6.2 #12 `epConformsOnWindow_at_radius` | verified | one line from #11 with `le_rfl` and `0 ≤ bepRadius lam tol` by `positivity` |
| plan §6.1 #7/#8 `EPExact ↔ lam = 0`, `not_epLinearOn_of_ne_zero` | verified | three-point identity `eact_second_difference`; `(x₁-x₂)^2/(8*lam) ≠ 0` kills affinity; the `Set.univ` direction is true *only* because `eact 0 x = x^2/0 = 0` |
| plan §6.4 #18–#21 (minimax block) | **verified end to end** | `bepBestLine_error` (pointwise bound via `|x^2 - w^2/2| ≤ w^2/2`), `bep_minimax_pointwise` (equioscillation: `by_contra h; push_neg at h`, the three `abs_lt.mp` facts and `linarith`), `epBestOnWindow_holds` (one line from it), `bepLine_worst_case` (witness `x = w`), `bepBestLine_halves` (`field_simp` + `div_lt_div_iff₀` + `nlinarith`) |
| literal `sSup` layer (AUX) | verified | `csSup_le` for `≤`, `le_csSup` with the explicit `BddAbove` witness for `≥`; `epSupError_bestLine` and `epSupError_sharp` both compile |
| plan §4.2 #7–#15 (nine classifier rows) | **verified** | `unfold epZone; split_ifs with h1 … h8` → 9 leaves, each `iff_of_true rfl _` / `iff_of_false (by decide) _`; plus 9 non-vacuity witnesses and 4 negative controls |
| plan §8.1 `qLamOfPair_reconstructs` | verified | see §2 |
| plan §5 #10/#11 (`secSlope` rows) | verified | #10 = `field_simp; ring`; #11 = #10 twice |
| plan §6.3 #15/#16 | verified | `div_le_div_iff₀` + `mul_le_mul_of_nonneg_left`; `Real.sqrt_le_sqrt` + `mul_le_mul_of_nonneg_right` |

**Measured correction to the plan's risk register**: the equioscillation lower bound needs **neither
`not_forall` nor `not_or`** — the verified route is `by_contra h; push_neg at h` (the single
existential negates into a `∀` of strict bounds), then `linarith` over the three sampled errors and
the three-point identity. `prover_b` should not spend time on the pre-registered `push_neg` risk.

### 6. API-risk list per milestone (what is hardest, and where mathlib could force a statement change)

| Block | Hardest expected row | Risk / gap |
|---|---|---|
| B1 `Basic.lean` | the nine `epZone_eq_*_iff` | **already kernel-verified** in the probe; the only real risk is the *cascade shape* (a reordering of the guards invalidates several rows). Keep the plan §4.1 order verbatim |
| B2 `Criterion.lean` | `eact_antitone` (needs `nlinarith` with the expanded square) and `secSlope_midpoint_invariant` | low; all identities verified. `bepDefect_pos_iff` needs `sq_pos_iff` (not `sq_pos_of_ne_zero`) after `div_pos_iff_of_pos_right` |
| B3 `Sharp.lean` | the radius theorem (√ layer) and the minimax pair | **both verified end to end**; the remaining gap is the literal sup-norm phrasing — plan §6.4 states the ε-free `EPBestOnWindow`, and the literal `sSup` twin is available as AUX (7 declarations) if the plan wants it |
| B4 `Compose.lean` | `rate_eq_exp_neg_eact` and `epConformsOnWindow_shrinks_with_inner` | the plan's own sketches carry placeholders (`(h : Marcus.rate … = …)`, `(…)`) that the skeleton had to resolve (see §7); no mathlib gap, but the lead should confirm the resolved shapes |
| B5a `RatModel.lean` | `qLamOfPair_reconstructs` (needs `lam ≠ 0`, `hden`) and the `epQVerdict` cascade | **no mathlib gap**, but the plan's "decidable predicate decided by `decide`" is not achievable in this toolchain for `/`-literals: use `norm_num` (+ an `abs`-free normal form); `decide` only on integer/`Rat.divInt` literals; `native_decide` is banned by `ALLOWED_AXIOMS` |
| B5b `Instances.lean` | not covered | signatures for I1–I11 are not derivable from plan §8.2 (ids only) |

**No statement change was forced by mathlib** in this round: every row of plan §4.1–§8.1 that this
round covers is expressible and (for the risky ones) already proved. The only statements this round
had to *change* are the two Sprint-0 corrections of §2, both of which were mathematical defects of
the draft, not mathlib gaps.

### 7. Interpretation log — plan placeholders resolved by api_researcher (lead to confirm)

| Plan locus | Placeholder in the plan | Resolution in the skeleton | Why |
|---|---|---|---|
| §4.1 | `def epQVerdict (lam x : ℚ) : EPQVerdict := …` | 7-branch cascade: `degenerate` (`λ = 0`), `unphysical` (`λ < 0`), `boundary` (`x = ±λ`, i.e. α = 0 or 1), `conforming` (α ∈ (0,1) strictly), `superLinear` (`1 < α`, above the Evans–Polanyi band), `subLinear` (`α < 0`, below it) | makes the plan's four `epQVerdict_*_iff` rows provable; all four are kernel-verified in `bep-api-rat.lean` |
| §8.1 | `qConformsWindow_iff_radius_sq` (name only) | `qConformsWindow lam tol w ↔ ((w : ℚ) : ℝ) ≤ bepRadius (lam : ℝ) (tol : ℝ)` | the name demands the radius, and the ℚ predicate is the squared form, so the row is the binding bridge to §6.2 #11 |
| §7 #2 | `rate_eq_exp_neg_eact (h : Marcus.rate A lam kB T x = …)` | `(A lam kB T x : ℝ) : Marcus.rate A lam kB T x = A * Real.exp (-(eact lam x) / (kB * T))` | the ellipsis is the identity itself; `eact_eq_barrier` makes both sides `rfl`-equal up to `Marcus.rate`'s body |
| §6.3 #17, §7 #11 | `(…)` for the hypotheses | positivity of the curvatures (and of `tol` where the window is used) | exactly what the proofs of #15/#16 consume |
| §4.2 | "B1 theorems (13)" but 15 rows; §5's "20–26" row lists 9 lemmas | all 15 + all 9 are in the skeleton | counting only |

### 8. Tightness observations (verified; not defects, but report them as such)

1. **`bepDefect_even` needs `lam ≠ 0`.** The first draft of the probe stated it unconditionally and
   the kernel rejected it (`bepDefect 0 x = x/2`, `bepDefect 0 (-x) = -x/2`; the cancellation
   `(4*lam)*(4*lam)⁻¹ = 1` is what fails). `epConformsOnWindow_symm` is nevertheless true because
   `EPConformsOnWindow` carries `0 < lam`. **This is the one place where a plausible "obvious"
   symmetry lemma is false** — do not restate it without the premise.
2. `transfer_add_reverse` (plan §5 #8), `reverseTransfer_eq_transfer_neg` (§5 #9) and
   `transfer_complementary_microscopic` (§7 #12) are pure ring identities: their `hlam` premises are
   never consumed (`x / 0 = 0` cancels). Deliver them with the premise (plan fidelity) and the local
   `set_option linter.unusedVariables false`, as `PhotoLean/Hammond/Basic.lean` already does.
3. `bepRadius_mono` (§6.3 #16): `h0 : 0 ≤ lam₁` is not consumed; the essential premise is
   `0 ≤ tol` (with `tol < 0` the statement is false: `tol = -1`, `lam₁ = -2`, `lam₂ = -1`).
4. `bepDefect_antitone_lam` (§6.3 #15): `hx : x ≠ 0` is not consumed (at `x = 0` both sides are `0`).
5. `epZone_eq_unphysical_iff` (§4.2 #8): `hlam : lam ≠ 0` is **redundant** — the statement holds for
   every `lam` (both sides are false at `λ = 0`).
6. `bepBestLine_error` (§6.4 #18) / `epSupError_bddAbove`: the pointwise bound does not consume
   `0 ≤ w`; the attainment and `sSup` rows do (they need `0 ∈ Set.Icc (-w) w`).
7. `qLamOfPair_reconstructs` (§8.1): `hx : x₁ ≠ x₂` is not consumed by the proof — `hden` already
   carries the non-degeneracy; keep it (it is the mathematical premise of a two-point estimator).

---

## 2026-09-20 — BEP round, follow-up: plan §8.1 model-consistency block + plan §8.2 instances (I1–I12) — api_researcher — 190 declarations, 0 error, 156 placeholder warnings (all `declaration uses 'sorry'`); every instance row kernel-checked

> **Lead correction (closeout, 2026-09-20)**: the *final* authority has **191 declarations** (157
> placeholder warnings); the 190/156 figures above predate the mirrored `qReverseTransfer_cast`
> insertion. Everything else in this entry stands.

### 1. New content and compile evidence

| Block | Declarations | Evidence |
|---|---|---|
| B5a `RatModel.lean` (plan §8.1 addition) | **5**: `qSecondDividedDiff`, `qModelConsistent3`, `qSecondDividedDiff_model`, `qModelConsistent3_curvature_pos`, `qModelConsistent3_lam_eq` | kernel-checked in `theories/BEP/probes/bep-api-instances.lean` (0 error / 0 warning) |
| B5b `Instances.lean` (plan §8.2) | **48**: I1–I8 3 rows each, I9 4 rows, I10 2 rows, I11 4 rows × 4 families, I12 1 row, `inst_nonvacuous` | all 48 rows proved in the same probe with `norm_num` / `decide`-on-integers only |

Skeleton after the addition: **190 declarations** = 156 theorems + 20 `def` + 12 `noncomputable def` +
2 `inductive`; `proofs/scripts/lake env lean theories/BEP/probes/bep-statement-skeleton.lean` → exit 0,
**0 error, 156 warnings, all of them `declaration uses 'sorry'` (0 other warnings)**. Per block:
B1 definitions 18 + B1 theorems 15; AUX ℝ observation layer 2; B2 28; B3 25; AUX `sSup` block 7;
B4 13; B5a definitions 11 + B5a theorems **23**; B5b **48**.

### 2. The ℚ-side recipe for the model-consistency block (measured)

```lean
theorem qSecondDividedDiff_model {lam x₁ x₂ x₃ : ℚ} (hlam : lam ≠ 0)
    (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃) (h₁₃ : x₁ ≠ x₃) :
    qSecondDividedDiff x₁ (qEact lam x₁) x₂ (qEact lam x₂) x₃ (qEact lam x₃) = 1 / (4 * lam)
```
* pure ℚ algebra: restate the three point-inequalities as **denominator** facts
  (`x₂ - x₁ ≠ 0`, `x₃ - x₂ ≠ 0`, `x₃ - x₁ ≠ 0` via `sub_ne_zero.mpr (Ne.symm h)`), then
  `unfold qSecondDividedDiff qEact; field_simp; ring`. `field_simp` discharges `4 * lam ≠ 0` from
  `hlam`; `eq_div_iff` / `div_eq_iff` are not needed for this row but are the tools for the
  `_lam_eq` row (`field_simp` alone closes it).
* **The three pairwise-distinctness premises are necessary** (kernel-measured): at `x₁ = x₃` the outer
  denominator of the divided difference is `0`, the totalised division gives `0`, and the claimed
  `1/(4λ)` is false. The plan's §8.1 sketch hides them behind `…`; they are now explicit.
* `qModelConsistent3_curvature_pos` = rewrite the three data equalities from the predicate, apply the
  model identity, `positivity`. `qModelConsistent3_lam_eq` = the same rewrite, then `field_simp`.
* Argument order matters: `qModelConsistent3 lam x₁ x₂ x₃ e₁ e₂ e₃` takes **all abscissae first**
  (plan §8.1 verbatim), whereas `qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃` interleaves `(x, e)` pairs.
  A first draft mixed the two and failed elaboration — worth a docstring line in `Instances.lean`.

### 3. The instance block (plan §8.2): what `norm_num` can and cannot do

**Verified `norm_num` domain (all measured):**

| Row shape | Recipe |
|---|---|
| verdict rows (`Rat.epQVerdict (2:ℚ) 0 = Rat.EPQVerdict.conforming`) | `unfold epQVerdict qTransfer; norm_num` — `norm_num` reduces the whole six-branch `if`-chain of concrete rational comparisons; no `split_ifs`/`decide` case bash needed |
| value rows (`Rat.qTransfer (2:ℚ) (1/2) = 3/8`, `Rat.qBepDefect (-2:ℚ) 1 = -(1/8)`) | `unfold <def>; norm_num` |
| window rows (`Rat.qConformsWindow (2:ℚ) (1/8) 1`, and its negation) | `unfold qConformsWindow; norm_num` |
| literature rows with **decimal** literals | decimals are first-class ℚ literals: `(15.6 : ℚ) = 78/5`, `(0.3 : ℚ)`, `(7.62 : ℚ)` all normalise; `norm_num` on `qSecondDividedDiff`/`qAlphaObs`/`qLamOfPair` after `unfold` |
| falsification rows (`¬ ∃ lam : ℚ, qModelConsistent3 lam …`) | `rintro ⟨lam, hlam, h₁, h₂, h₃⟩`, then `qModelConsistent3_curvature_pos` with the three `by norm_num` distinctness facts, the computed negative value via a `show … by unfold …; norm_num` rewrite, and `norm_num at hpos` |

`by decide` remains unusable on `/`-literals and `native_decide` remains banned (see the main BEP
section); the integer-only `decide` was not needed by any row.

**Rows that could NOT be made `norm_num`-checkable (the list requested):**

1. **Family F4** (plan §8.2 I11, *Antioxidants* 2026 **Table 2 "PE"**) — `theories/BEP/LITERATURE.md`
   §R1.10.4 prints **only family aggregates** for it (mean `λ̂` = 53.4 kcal/mol, range 43.8–57.9,
   curvature −0.0046, fit `Ea = 13.7 − 0.585x`, R² = 0.952) and **no per-row `(x, Ea)` pairs**, so
   `_alphaObs` / `_lamHat` / `_curvature_negative` / `_not_model_consistent` cannot be stated for it
   without inventing numbers. The skeleton therefore carries I11 rows for **F1, F2, F3, F5 only**;
   the gap is documented in the B5b section header. If a per-row table for F4 is read first-hand in a
   later literature round, the four rows can be added by the same recipe.
2. Nothing else failed: all I1–I10 rows, the 16 I11 rows and the I12 conjunction are closed by the
   recipes above.
3. **Plan §8.2 I8 is stale on one value** (statement defect, corrected in the skeleton): the table
   still prints `α = 0` for the degenerate family `λ = 0`, which belonged to the discarded
   transition-state body. With the delivered linear-response body,
   `Rat.qTransfer (0 : ℚ) 1 = 1 / 2` (plan §4.2 #4). The skeleton states `1/2`; the plan's I-table
   cell should be updated by the lead.

### 4. Honesty notes on the literature rows (needed so no prover "improves" them)

* `Rat.qLamOfPair` is the **model's two-point solver**, not the record's per-pair `λ̂`
  (`λ̂ = (x + 2Ea) ± 2√(Ea² + x·Ea)`, irrational and not a ℚ literal). The `_lamHat` rows therefore
  state exact ℚ values at two **adjacent** printed pairs, where the model solver happens to be
  positive (F1 `9/20`, F2 `16/15`, F3 `22/5`, F5 `7958/675`) — the record's "all pairs admit
  `λ̂ > 0`" is a *different* estimator and is deliberately not restated. At a wide pair the model
  solver is negative (F1, `16(2)`&`8`: `-2079/25`), which is itself an instance of the
  wrong-sign-curvature phenomenon; the skeleton does not hide it.
* `_curvature_negative` is a statement about the **three chosen printed rows**, not about the
  record's family-level regression (R², fitted curvature) — a regression is not a ℚ identity and is
  not formalised. The λ-independent falsification (`¬ ∃ lam, qModelConsistent3 …`) is exactly the
  logical content of the chosen triple.
* `_alphaObs` uses the family's **leading documented pair as named in the family heading** (the closest
  analogue of a fitted slope); *(lead correction 2026-09-20: this line previously said "widest printed
  x-pair", which is loose — by maximal |Δx| over all printed rows the widest pairs of F1/F2/F3 are
  `19(2)`/`8`, `19(2)`/`10`, `19(2)`/`7`, and `F5`'s is `R2`/`R5`; the delivered `_alphaObs` rows use
  the pairs named in `Instances.lean`'s family headings, and the documents' separate statement about
  the "abscissa-widest pairs" is a different, explicitly labelled computation)*
  the values lie strictly inside `(0,1)`, matching the record's "the BEP side works" reading.
* Units: every Lean literal is the source's **kcal/mol** number (the sources' own first-hand value);
  the record's kJ/mol column is its own arithmetic and is deliberately never used in a statement.
  `F5` prints a classical `ΔE / V‡f`, so the docstrings carry the `ΔE`-vs-`ΔG` caveat.
* The numbers and loci are verbatim from §R1.10 (all five families `first-hand` there); nothing was
  converted, rounded or re-derived here.
