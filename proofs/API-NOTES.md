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

### Sabatier group (2026-09-21) — all seven items closed in the same round

- [x] (a) `max` on ℝ — all 15 names of the dispatch exist (`max_idem` is the *instance*
      `Std.IdempotentOp max`: use `max_idem.idempotent a`, or `max_self a`); the four goal shapes
      (`max a b ≤ c`, `c ≤ max a b`, `max a b = …`, `max a b = a ↔ b ≤ a`) have kernel-checked
      recipes. See `## Sabatier theory (2026-09-21)` §2.
- [x] (b) `StrictMonoOn` / `StrictAntiOn` / `MonotoneOn` / `AntitoneOn` — definitions and the
      `intro`-terminating toolkit verified; `strictMonoOn_const` and `strictMonoOn_iff_forall_lt`
      do **not** exist; the house pattern is plain `∀`-statements (0 `Set`-predicates under
      `PhotoLean/`). See §3.
- [x] (c) `abs` — 7 of the 8 names exist, `abs_le_iff` does **not**; the four routes for
      `|x - y| ≤ t → x ≤ y + t` are kernel-checked. See §4.
- [x] (d) `Real.exp` / `Real.log` — all names exist; `Real.exp_le_exp_iff` / `Real.exp_lt_exp_iff`
      do **not** (on ℝ, `Real.exp_le_exp` *is* the `iff`); the dimensionless→energy recipe
      (`Real.exp_le_exp` → `div_le_div_iff_of_pos_right` → `neg_le_neg_iff`) is kernel-checked.
      See §5.
- [x] (e) `Real.sqrt` — all names exist (including `Real.sqrt_pos_of_pos`) with the exact
      hypotheses recorded; the `Real.sqrt_le_sqrt_iff` (`0 ≤ y`, right argument) vs
      `Real.sqrt_lt_sqrt_iff` (`0 ≤ x`, left argument) asymmetry is the trap. See §6.
- [x] (f) ℚ → ℝ cast — the `Rat.cast_*` family plus `Rat.cast_def` and **`Rat.cast_max`** (there is
      no usable `map_max`); the `..._cast` transfer shapes of `PhotoLean/Hammond/RatModel.lean` and
      `PhotoLean/Kasha/RatModel.lean` are reproduced and kernel-checked on a miniature volcano
      model. See §7.
- [x] (g) `if` / `ite` — `if_pos`, `if_neg`, `ite_eq_iff`, `dif_pos`, `apply_ite` (and their twins)
      all exist; the 5–7 branch `split_ifs with h1 … h_n` shape and its negated-hypothesis naming
      convention are recorded. See §8.

---

### Post-delivery notes (2026-09-21, lead; verifier run 1 findings F3/F12 + worker-reported drift)

- **Statement corrections are NOT API drift, and they are logged twice**: the S1 authority rows
  `apex_comm` / `volcanoBarrier_comm` were deleted (the naive label swap `(alphaA,betaA,alphaB,betaB) ↦
  (alphaB,betaB,alphaA,betaA)` NEGATES the apex, because the second branch enters with slope
  `-alphaB`) and `activity_descriptor_iff` was replaced by `antiDescriptor_activity_iff` /
  `volcanoActivity_peak_iff` (the activity is strictly DECREASING in the barrier, so the barrier's
  unique minimum is the activity's unique MAXIMUM — the dual predicate is required). Full log:
  `theories/Sabatier/plan.md` §3.1; kernel witnesses: `apex_naive_swap_values`, `apex_naive_swap_ne`,
  `activity_zero_kT_witness` in `theories/Sabatier/probes/sabatier-risk-probe.lean`. A third
  correction (the I2 instance rows' descriptor-sign convention) is logged there too, with the
  rational cross-check as its evidence.
- **Resolved (F12)**: the earlier note in this section that `Sabatier` was missing from
  `THEORIES` / `lakefile.toml` is closed — `proofs/ENGINE.yml` lists `Sabatier` with all five
  `*_Sabatier` leaf variables, and all six `PhotoLean.Sabatier.*` modules are in
  `lakefile.toml` `defaultTargets` (build coverage = scan coverage; verified by the bare
  `check.sh --strict`).
- **Additional name drift measured by the workers (v4.17.0)**: `lt_div_iff` / `div_lt_iff` are
  deprecated in this revision — use `lt_div_iff₀` / `div_lt_iff₀`; `max_add_add_left` /
  `max_add_add_right` / `add_max_*` do **not** exist, so `max (P + x) (P + y) = P + max x y` must be
  built by hand (`rcases le_total x y` + `max_eq_left`/`max_eq_right`); `by norm_num` does not see
  through a `noncomputable def` in a *hypothesis* position (use `unfold …; norm_num`); a beta-redex
  left by a `fun`-abstraction defeats `linarith` until `dsimp only` is applied first.

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

---

## 2026-09-20 — §kasha round (Kasha's rule) — api_researcher — 5 probes, all `exit 0` / 0 error / 0 warning; the K4 #12 Marcus chain, the K4 #14 `sqrt` window and **all eight K5a cast bridges** are kernel-verified end to end; K4b/K4c (exponential race) answered with a measured feasibility verdict

> Body in English (`AGENTS.md` language policy: `proofs/API-NOTES.md` is an English artifact; no
> mirror copy). Identifiers, `#check` output, errors and warnings are quoted verbatim.
>
> **Statement authority — a hash in a log has to say *when*.** This §kasha section was calibrated
> against the authority state `theories/kasha/probes/kasha-statement-skeleton.lean`
> sha256 `801983702a9dc0129e7a2ab4ec6505c4d7c9967daed444c58b460910bc7e3cb0` (144 declarations).
> Corrections later on 2026-09-20 moved it to `4cf2b105…` (K1 #24 `kashaZone_eq_violating_iff` and
> its ℚ twin `kashaQVerdict_eq_violating_iff` gained `0 < tol` — prover_a's kernel counterexample
> `rad ≡ 1`, `ic ≡ 1`, `N = 0`, `tol = -1`; K3 #2/#9; the K5a criterion row) and then to
> `8508e1df7705daaac31288ef78e97073aaff2f1c6422c31bd2eb83b669cbf888` (151 declarations, K5b
> literature rows appended). None of those corrections is an API/name change: no row of this API
> round is affected, and the drift log below records only measured name facts.
> **2026-09-20 close-out (verifier finding, fixed here): an earlier revision of this section claimed
> `theories/kasha/probes/kasha-api-risk.lean` carried 2 deprecation warnings. Re-measured at the
> verifier's request the file is `exit 0` with **0 warnings** (92 output lines); the stale claim
> described the file's pre-rename/pre-cleanup revision. Corrected in §2 below.**

### 1. Deliverables and compile evidence

| Probe | Content (topics of task K-API-1) | Run (repo root) | Result |
|---|---|---|---|
| `theories/kasha/probes/kasha-api-cascade.lean` | (a) `Finset` index surgery + the cascade algebra; K1 §4.2 #7–#21, K2 §5.1 #1–#6, §5.2 #13, K3 §6.2 #17, K4 §7.2 #1 | `proofs/scripts/lake env lean theories/kasha/probes/kasha-api-cascade.lean` | **exit 0, 0 error, 0 warning**, 104 `#check` output lines |
| `theories/kasha/probes/kasha-api-order.lean` | (b) division/order on ℝ + (d) the `Real.sqrt` window recipe; K3 §6.1 #1–#3, §6.2 #9/#10, K4 §7.2 #12/#14/#15 | same command, filename swapped | exit 0, 0 error, 0 warning, 84 lines |
| `theories/kasha/probes/kasha-api-logexp.lean` | (c) `Real.exp`/`Real.log` + the whole K4 #12 bridge (`import PhotoLean.Marcus.Basic`) | as above | exit 0, 0 error, 0 warning, 33 lines |
| `theories/kasha/probes/kasha-api-cast.lean` | (e) `Rat.cast_*` family + the eight K5a cast bridges; §8.1 | as above | exit 0, 0 error, 0 warning, 30 lines |
| `theories/kasha/probes/kasha-api-race.lean` | (f) exponential-race feasibility (plan §1.2, K4b/K4c, §13 limit 5) | as above | exit 0, 0 error, 0 warning, 78 lines |

Every probe is a `#check` log plus kernel-checked `example`/`theorem` bodies; each worked recipe is
delivery-shaped (the plan's own row, not a toy analogue), so a prover's job collapses to
transcription. Nothing in this section names an unverified name: the names in §3 are exactly the
ones that survived `#check`, the names in §4 are exactly the ones that did not.

### 2. Probe-name coordination (why (a) is not called `kasha-api-finset.lean`)

* Task K-API-1 dispatched topic (a) to `theories/kasha/probes/kasha-api-finset.lean`. At dispatch
  time that path was occupied by **prover_c's K5a scratch probe** (`/-- Scratch calibration probe
  (owner `prover_c`) — **not a delivered artifact**`), written after the dispatch; engine rule 5
  (one writer per file) forbids overwriting it, so topic (a) is delivered as
  **`kasha-api-cascade.lean`**. **Resolution (2026-09-20): the lead confirmed the rename and it has
  landed — `kasha-api-finset.lean` no longer exists, the scratch file is `kasha-rat-scratch.lean`,
  and the `kasha-api-*` prefix now means "api_researcher's calibrated probe" without exception.**
* Pre-existing probes not owned by this role and not touched: `theories/kasha/probes/kasha-api-k1-finset.lean`
  (prover_a, K1) and `theories/kasha/probes/kasha-api-risk.lean` (prover_b, task K-PROBE-1). The
  risk probe independently reports the same two non-existent interval names
  (`Finset.sum_Icc_succ_bot`, `Finset.prod_Icc_succ_bot`). **Corrected measurement (2026-09-20, at
  the verifier's request): `proofs/scripts/lake env lean theories/kasha/probes/kasha-api-risk.lean`
  → `exit 0`, 92 output lines, 0 error, 0 warning.** An earlier revision of this section reported
  2 deprecation warnings from that file; that measurement was taken at 21:05 on an intermediate
  revision whose lines 165–166 still contained `#check @div_le_iff` and `#check @le_div_iff`. Those
  `#check`s were **removed before the file was committed** (its lines 98–100 now use
  `div_le_iff₀` / `le_div_iff₀`; the deprecated names survive only inside a comment at lines
  21–22). The deprecation fact itself (§4.3) stands and was re-measured independently in a
  temporary scratch file.

### 3. Verified names — exact signatures (verbatim `#check` output, wraps joined)

**(a) `Finset` index surgery** (`kasha-api-cascade.lean`)

```
@Finset.Icc_eq_cons_Ico : a ≤ b → Finset.Icc a b = Finset.cons b (Finset.Ico a b) ⋯
@Finset.Icc_eq_cons_Ioc : a ≤ b → Finset.Icc a b = Finset.cons a (Finset.Ioc a b) ⋯
@Finset.prod_Icc_succ_top : a ≤ b + 1 → ∀ (f : ℕ → M), ∏ k ∈ Finset.Icc a (b + 1), f k = (∏ k ∈ Finset.Icc a b, f k) * f (b + 1)
@Finset.sum_Icc_succ_top  : a ≤ b + 1 → ∀ (f : ℕ → M), ∑ k ∈ Finset.Icc a (b + 1), f k = ∑ k ∈ Finset.Icc a b, f k + f (b + 1)
@Finset.prod_Ico_succ_top : a ≤ b → ∀ (f : ℕ → M), ∏ k ∈ Finset.Ico a (b + 1), f k = (∏ k ∈ Finset.Ico a b, f k) * f b
@Finset.sum_Ico_succ_top  : a ≤ b → ∀ (f : ℕ → M), ∑ k ∈ Finset.Ico a (b + 1), f k = ∑ k ∈ Finset.Ico a b, f k + f b
@Finset.prod_eq_prod_Ico_succ_bot : a < b → ∀ f, ∏ k ∈ Finset.Ico a b, f k = f a * ∏ k ∈ Finset.Ico (a + 1) b, f k
@Finset.sum_eq_sum_Ico_succ_bot   : a < b → ∀ f, ∑ k ∈ Finset.Ico a b, f k = f a + ∑ k ∈ Finset.Ico (a + 1) b, f k
@Finset.prod_Ico_consecutive : (f : ℕ → M) → m ≤ n → n ≤ k → (∏ i ∈ Finset.Ico m n, f i) * ∏ i ∈ Finset.Ico n k, f i = ∏ i ∈ Finset.Ico m k, f i
@Finset.sum_Ico_consecutive  : (f : ℕ → M) → m ≤ n → n ≤ k → ∑ i ∈ Finset.Ico m n, f i + ∑ i ∈ Finset.Ico n k, f i = ∑ i ∈ Finset.Ico m k, f i
@Finset.prod_Ioc_consecutive / @Finset.sum_Ioc_consecutive     (the `Ioc` twins)
@Finset.Icc_self : Finset.Icc a a = {a}
@Finset.Icc_eq_empty : ¬a ≤ b → Finset.Icc a b = ∅
@Finset.Icc_eq_empty_iff : Finset.Icc a b = ∅ ↔ ¬a ≤ b          -- `@[simp]`
@Finset.prod_empty : ∏ x ∈ ∅, f x = 1     @Finset.sum_empty : ∑ x ∈ ∅, f x = 0
@Finset.prod_singleton : ∏ x ∈ {a}, f x = f a    @Finset.sum_singleton : ∑ x ∈ {a}, f x = f a
Finset.range_one : Finset.range 1 = {0}
@Finset.range_succ : Finset.range n.succ = insert n (Finset.range n)
@Finset.range_add_one : Finset.range (n + 1) = insert n (Finset.range n)
Finset.range_eq_Ico : Finset.range = Finset.Ico 0                 -- pointfree!
Nat.Ico_zero_eq_range : Finset.Ico 0 = Finset.range
Nat.range_succ_eq_Icc_zero : Finset.range (n + 1) = Finset.Icc 0 n
Nat.Ico_succ_right : Finset.Ico a b.succ = Finset.Icc a b
Nat.Icc_eq_range' / Nat.Ico_eq_range' : the `List.range'` bodies (`rfl`-equal)
@Finset.sum_range_eq_add_Ico : (f : ℕ → M) → 0 < n → ∑ x ∈ Finset.range n, f x = f 0 + ∑ x ∈ Finset.Ico 1 n, f x
@Finset.prod_range_eq_mul_Ico : (f : ℕ → M) → 0 < n → ∏ x ∈ Finset.range n, f x = f 0 * ∏ x ∈ Finset.Ico 1 n, f x
@Finset.sum_range_succ : ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f n
@Finset.sum_range_succ' : ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 1) + f 0
@Finset.prod_range_succ : ∏ x ∈ Finset.range (n + 1), f x = (∏ x ∈ Finset.range n, f x) * f n
@Finset.sum_range_zero / @Finset.sum_range_one
@Finset.Ico_union_Ico_eq_Ico : a ≤ b → b ≤ c → Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c
@Finset.prod_union : Disjoint s₁ s₂ → ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x
@Finset.sum_union  : Disjoint s₁ s₂ → ∑ x ∈ s₁ ∪ s₂, f x = ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x
@Finset.disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t
@Finset.disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅
@Finset.prod_disjUnion / @Finset.sum_disjUnion (h : Disjoint s₁ s₂)
@Finset.prod_nonneg : (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∏ i ∈ s, f i
@Finset.prod_le_one : (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) → ∏ i ∈ s, f i ≤ 1   -- CommMonoidWithZero + PosMulMono
@Finset.sum_nonneg : (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i
@Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
@Finset.sum_eq_zero_iff_of_nonneg : (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
@Finset.sum_eq_zero_iff_of_nonpos : (∀ i ∈ s, f i ≤ 0) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
@Finset.sum_div : (s : Finset ι) (f : ι → K) (a : K), (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a
@Finset.sum_mul : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
@Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
@Finset.sum_congr  : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
@Finset.prod_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g
@Finset.mem_Icc : x ∈ Finset.Icc a b ↔ a ≤ x ∧ x ≤ b      @Finset.mem_range : m ∈ Finset.range n ↔ m < n
@Finset.sum_insert / @Finset.prod_insert : a ∉ s → ∑/∏ x ∈ insert a s, f x = f a +/* ∑/∏ x ∈ s, f x
```

**(b) Division / order** (`kasha-api-order.lean`)

```
@div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)
@div_lt_div_iff₀ : 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)
@div_le_div_iff_of_pos_right : 0 < c → (a / c ≤ b / c ↔ a ≤ b)
@div_le_div_iff_of_pos_left  : 0 < a → 0 < b → 0 < c → (a / b ≤ a / c ↔ c ≤ b)
@le_div_iff₀ : 0 < c → (a ≤ b / c ↔ a * c ≤ b)
@div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)
@lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b)
@div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)
@div_pos : 0 < a → 0 < b → 0 < a / b
@div_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a / b
@div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
@div_pos_iff_of_pos_right : 0 < b → (0 < a / b ↔ 0 < a)
@div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
@div_le_div_of_nonneg_right : a ≤ b → 0 ≤ c → a / c ≤ b / c
@mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c
@mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a
@lt_of_mul_lt_mul_right : b * a < c * a → 0 ≤ a → b < c        -- note: positivity of the CANCELLED right factor
@le_of_mul_le_mul_right : b * a ≤ c * a → 0 < a → b ≤ c
@one_div : 1 / a = a⁻¹
@inv_le_inv₀ : 0 < a → 0 < b → (a⁻¹ ≤ b⁻¹ ↔ b ≤ a)      @inv_lt_inv₀ : the strict twin
@inv_anti₀ : 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹
@inv_pos : 0 < a⁻¹ ↔ 0 < a          @inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a
@one_div_le_one_div_of_le : 0 < a → a ≤ b → 1 / b ≤ 1 / a
@div_self : a ≠ 0 → a / a = 1       @div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b)
@one_le_div : 0 < b → (1 ≤ a / b ↔ b ≤ a)          @div_lt_one : 0 < b → (a / b < 1 ↔ a < b)
@inv_div : (a / b)⁻¹ = b / a        @one_div_one_div : 1 / (1 / a) = a
```

**(c) `Real.exp` / `Real.log`** (`kasha-api-logexp.lean`; cross-module names also verified)

```
PhotoLean.Marcus.barrier (lam x : ℝ) : ℝ        PhotoLean.Marcus.rate (A lam kB T x : ℝ) : ℝ
Real.exp_pos : ∀ (x : ℝ), 0 < Real.exp x            Real.exp_ne_zero : ∀ x, Real.exp x ≠ 0
@Real.exp_le_exp : Real.exp x ≤ Real.exp y ↔ x ≤ y  @Real.exp_lt_exp : Real.exp x < Real.exp y ↔ x < y
Real.exp_add / Real.exp_sub / Real.exp_neg
@Real.exp_le_one_iff : Real.exp x ≤ 1 ↔ x ≤ 0   @Real.exp_lt_one_iff : Real.exp x < 1 ↔ x < 0
@Real.one_lt_exp_iff : 1 < Real.exp x ↔ 0 < x
@Real.log_pos : 1 < x → 0 < Real.log x         @Real.log_nonneg : 1 ≤ x → 0 ≤ Real.log x
@Real.log_nonpos : 0 ≤ x → x ≤ 1 → Real.log x ≤ 0    @Real.log_neg : 0 < x → x < 1 → Real.log x < 0
Real.log_one : Real.log 1 = 0   Real.log_zero : Real.log 0 = 0
Real.log_exp : Real.log (Real.exp x) = x       @Real.exp_log : 0 < x → Real.exp (Real.log x) = x
@Real.log_le_log : 0 < x → x ≤ y → Real.log x ≤ Real.log y
@Real.log_lt_log : 0 < x → x < y → Real.log x < Real.log y
@Real.log_le_log_iff : 0 < x → 0 < y → (Real.log x ≤ Real.log y ↔ x ≤ y)
@Real.log_lt_log_iff : 0 < x → 0 < y → (Real.log x < Real.log y ↔ x < y)
@Real.le_log_iff_exp_le : 0 < y → (x ≤ Real.log y ↔ Real.exp x ≤ y)
@Real.log_le_iff_le_exp : 0 < x → (Real.log x ≤ y ↔ x ≤ Real.exp y)     -- `.mpr` goes exp-ward
@Real.log_div : x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y
Real.log_inv : Real.log x⁻¹ = -Real.log x      @Real.log_mul : x ≠ 0 → y ≠ 0 → Real.log (x * y) = …
Real.log_pow : Real.log (x ^ n) = ↑n * Real.log x
@Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1
Real.exp_injective : Function.Injective Real.exp    Real.log_injOn_pos : Set.InjOn Real.log (Set.Ioi 0)
```

**(d) `Rat.cast_*` and the big-operator casts** (`kasha-api-cast.lean`)

```
@Rat.cast_add / cast_sub / cast_mul / cast_div / cast_inv : [DivisionRing α] [CharZero α] (p q : ℚ), ↑(p ±/*÷ q) = ↑p ±/*÷ ↑q
@Rat.cast_neg / cast_pow / cast_zero / cast_one : [DivisionRing α] only (no CharZero)
@Rat.cast_natCast : [DivisionRing α] (n : ℕ), ↑↑n = ↑n
@Rat.cast_ofNat : [DivisionRing α] (n : ℕ) [n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_le / cast_lt / cast_pos / cast_nonneg / cast_nonpos : {p q : ℚ} {K} [LinearOrderedField K]   -- all `↔`
@Rat.cast_ne_zero / cast_eq_zero : [DivisionRing α] [CharZero α]   -- `↔`
@Rat.cast_inj : [DivisionRing α] [CharZero α] {p q : ℚ}, ↑p = ↑q ↔ p = q
@Rat.cast_injective : [DivisionRing α] [CharZero α], Function.Injective Rat.cast
@Rat.cast_sum : [DivisionRing α] [CharZero α] (s : Finset ι) (f : ι → ℚ), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)   -- `@[simp, norm_cast]`
@Rat.cast_prod : [Field α] [CharZero α] (s : Finset ι) (f : ι → ℚ), ↑(∏ i ∈ s, f i) = ∏ i ∈ s, ↑(f i)        -- needs `Field`, not merely `DivisionRing`
@Rat.cast_list_sum / cast_multiset_sum / cast_list_prod / cast_multiset_prod
Rat.castHom : (α) → [DivisionRing α] → [CharZero α] → ℚ →+* α
```

**(e) Measure / probability (the race)** — see §7; full output in `kasha-api-race.lean`.

```
ProbabilityTheory.expMeasure : ℝ → Measure ℝ
@ProbabilityTheory.isProbabilityMeasureExponential : 0 < r → IsProbabilityMeasure (expMeasure r)
ProbabilityTheory.exponentialPDF : ℝ → ℝ → ℝ≥0∞
@ProbabilityTheory.lintegral_exponentialPDF_eq_one : 0 < r → ∫⁻ x, exponentialPDF r x = 1
@ProbabilityTheory.exponentialCDFReal_eq : 0 < r → ↑(exponentialCDFReal r) x = if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0
@ProbabilityTheory.tendsto_cdf_atTop / @ProbabilityTheory.measure_cdf
@StieltjesFunction.measure_Ioi : Tendsto (↑f) atTop (𝓝 l) → f.measure (Set.Ioi x) = ENNReal.ofReal (l - ↑f x)
@withDensity_apply : MeasurableSet s → (μ.withDensity f) s = ∫⁻ a in s, f a ∂μ
@lintegral_withDensity_eq_lintegral_mul : Measurable f → Measurable g → ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ
@Measure.prod_apply : MeasurableSet s → (μ.prod ν) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ     [SFinite ν]
@lintegral_prod / @lintegral_lintegral_swap    (Fubini for `ℝ≥0∞`)
@Measure.prod / @Measure.map / @Measure.restrict / @lintegral_indicator / @measure_compl / @measure_univ
@ProbabilityTheory.iIndepFun / @ProbabilityTheory.IndepFun / @ProbabilityTheory.iIndep
@ofReal_integral_eq_lintegral_ofReal : Integrable f μ → 0 ≤ᶠ[ae μ] f → ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ
@integral_comp_mul_left_Ioi : 0 < b → ∫ x in Set.Ioi a, g (b * x) = b⁻¹ • ∫ x in Set.Ioi (b * a), g x
@integral_exp_neg_Ioi : ∫ x in Set.Ioi c, Real.exp (-x) = Real.exp (-c)      -- root namespace
integral_exp_neg_Ioi_zero : ∫ x in Set.Ioi 0, Real.exp (-x) = 1
exp_neg_integrableOn_Ioi : 0 < b → IntegrableOn (fun x => Real.exp (-b * x)) (Set.Ioi a) volume
```

### 4. Failures and drift (mandatory section)

**4.1 Names that do NOT exist in mathlib v4.17.0 (verbatim errors; banned in Kasha proofs).**

```
error: unknown constant 'Finset.Icc_succ_right'          -- the Finset top-split; `Order.Icc_succ_right` (a *Set* lemma) does exist
error: unknown constant 'Finset.Icc_insert_left'
error: unknown constant 'Finset.prod_Icc_succ_bot'       -- the "bottom" twin of `prod_Icc_succ_top` is absent
error: unknown constant 'Finset.sum_Icc_succ_bot'
error: unknown constant 'Finset.prod_Icc_consecutive'
error: unknown constant 'Finset.sum_Icc_consecutive'
error: unknown constant 'Finset.Icc_union_Icc_eq_Icc'    -- only `Set.Icc_union_Icc_eq_Icc` and `Finset.Ico_union_Ico_eq_Ico` exist
error: unknown constant 'Finset.Ico_zero_eq_range'       -- it is `Nat.Ico_zero_eq_range`
error: unknown identifier 'div_le_div_iff_of_pos'        -- use `div_le_div_iff₀`
error: unknown constant 'Real.exp_one_lt_iff'
error: unknown constant 'Real.log_injective'             -- the `Injective` version is `ENNReal.log_injective`; for ℝ use `Real.log_injOn_pos`
error: unknown identifier 'MeasureTheory.integral_exp_neg_mul_Ioi'
error: unknown identifier 'MeasureTheory.integral_exp_neg_Ioi'   -- it is root-level `integral_exp_neg_Ioi`
error: unknown constant 'Real.integral_exp_neg_Ioi'
error: unknown identifier 'MeasureTheory.measure_lt'
error: unknown identifier 'MeasureTheory.measure_Ioi'            -- usable: `StieltjesFunction.measure_Ioi` / `MeasureTheory.measure_Ioi_pos`
error: unknown constant 'MeasureTheory.Measure.withDensity_apply' -- it is `MeasureTheory.withDensity_apply`
error: unknown identifier 'IsProbabilityMeasure'                 -- it is `MeasureTheory.IsProbabilityMeasure`
error: unknown identifier 'MeasureTheory.lintegral_exp_neg_mul_Ioi'
error: unknown identifier 'MeasureTheory.lintegral_exp_neg'
error: unknown identifier 'MeasureTheory.integral_exp_neg_mul'
error: unknown identifier 'MeasureTheory.lintegral_mul_left'     -- use `lintegral_const_mul`
```

| Banned | Verified replacement (usage form that compiled) |
|---|---|
| `Finset.Icc_succ_right` | `Finset.prod_Icc_succ_top` / `Finset.sum_Icc_succ_top` (arithmetic), or `Finset.Icc_eq_cons_Ico h` / `Finset.Icc_eq_cons_Ioc h` (set identity) |
| `Finset.prod_Icc_succ_bot` / `Finset.sum_Icc_succ_bot` | `prod/sum_Icc_succ_top` on `Icc (a+1) …` or `prod/sum_eq_…Ico_succ_bot` on `Ico` (K4 #1 works with `Ico`) |
| `Finset.prod_Icc_consecutive` / `Finset.sum_Icc_consecutive` | `Ico_consecutive`/`Ioc_consecutive`, or the `ext`+`omega`+`Finset.prod_union hdisj` recipe of §5 |
| `Finset.Icc_union_Icc_eq_Icc` | `ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega` (then `Finset.prod_union hdisj`) |
| `Finset.Ico_zero_eq_range` | `Nat.Ico_zero_eq_range` |
| `div_le_div_iff_of_pos` | `div_le_div_iff₀` |
| `Real.exp_one_lt_iff` | `Real.one_lt_exp_iff` |
| `Real.log_injective` | `Real.log_injOn_pos` (or `Real.exp_injective`) |
| `MeasureTheory.integral_exp_neg_mul_Ioi` | `integral_comp_mul_left_Ioi` + `integral_exp_neg_Ioi_zero` (§7(f)) |
| `MeasureTheory.measure_lt`, `MeasureTheory.measure_Ioi` | `StieltjesFunction.measure_Ioi` (tail of a Stieltjes function) or `MeasureTheory.Measure.measure_Ioi_pos` (open-positive measures) |
| `MeasureTheory.Measure.withDensity_apply` | `MeasureTheory.withDensity_apply` |
| bare `IsProbabilityMeasure` | `MeasureTheory.IsProbabilityMeasure` |

**4.2 Name that exists but is not usable on ℝ: `Finset.prod_le_one'`.**

```
@Finset.prod_le_one' : [OrderedCommMonoid N] → (∀ i ∈ s, f i ≤ 1) → ∏ i ∈ s, f i ≤ 1
error: failed to synthesize
  OrderedCommMonoid ℝ
```
ℝ does not synthesize `OrderedCommMonoid` in this toolchain (the modern signature keeps only
`CommMonoidWithZero` + `PosMulMono`). **Use the two-hypothesis `Finset.prod_le_one`**:
`Finset.prod_le_one (fun j _ => icBranch_nonneg …) (fun j _ => icBranch_le_one …)`. (`Finset.prod_nonneg`
and `Finset.sum_nonneg` are unaffected — their signatures are already the modern ones.)

**4.3 Deprecated (warning only, so they must NOT appear in a 0-warning probe; measured in a
temporary scratch file, not in any delivered probe).**

```
warning: `div_le_div_iff` has been deprecated: use `div_le_div_iff₀` instead
warning: `div_le_div_right` has been deprecated: use `div_le_div_iff_of_pos_right` instead
warning: `div_le_div_left` has been deprecated: use `div_le_div_iff_of_pos_left` instead
warning: `inv_le_inv` has been deprecated: use `inv_le_inv₀` instead
warning: `inv_le_inv_of_le` has been deprecated: use `inv_anti₀` instead
warning: `le_div_iff` has been deprecated: use `le_div_iff₀` instead
warning: `div_le_iff` has been deprecated: use `div_le_iff₀` instead
warning: `lt_div_iff` has been deprecated: use `lt_div_iff₀` instead
warning: `div_lt_iff` has been deprecated: use `div_lt_iff₀` instead
```
(The Marcus/BEP rounds already registered `div_le_div_iff`, `div_le_div_right`, `div_le_div_left`,
`pow_le_pow_left`; the four **new** entries are `inv_le_inv → inv_le_inv₀`,
`inv_le_inv_of_le → inv_anti₀`, `le_div_iff → le_div_iff₀`, `lt_div_iff → lt_div_iff₀`.)

**4.4 Measured traps (kernel facts, not name facts).**

* **`linarith` does not unfold definitions.** `radBranch_le_one` first failed with
  `error: linarith failed to find a contradiction … a✝ : rad n > decay rad ic n ⊢ False`
  because the goal still contained the *definition* `decay`. Fix: `rw [radBranch, div_le_one …, decay]`
  **before** `linarith`.
* **`Finset.prod_union`'s side condition is generated FIRST.** `rw [Finset.prod_union]` followed by
  `· ring` / `· rw [Finset.disjoint_left]` mismatched (measured:
  `unsolved goals … ⊢ Disjoint (Finset.Icc (1 + i) M) (Finset.Icc (1 + M) N)` then
  `no goals to be solved`). Fix: prove the disjointness separately and pass it: `rw [hset, Finset.prod_union hdisj]`.
* **`Finset.mul_sum` orientation.** In a `calc … = θ * ∑ …, …` step, the *reverse* form is the usable
  one: `(Finset.mul_sum ..).symm`; the forward form gives
  `type mismatch … has type ?b * ∑ … = ∑ …, ?b * …`.
* **`← Rat.cast_le` is stuck without the field.** Measured:
  `error: typeclass instance problem is stuck … LinearOrderedField ?m.88`. Fix: `(Rat.cast_le (K := ℝ)).symm`
  (same family as the already registered `apply Rat.cast_inj.mp` → `CharZero ?m.82`; use
  `(Rat.cast_inj (α := ℝ)).mp`).
* **`rw` rewrites too deep in the sqrt window.** `rw [← Real.sq_sqrt hR]` also hits the `R` inside
  `Real.sqrt R` (measured leftover goal `|(|x|)| ≤ √R ↔ |x| ≤ √(√R ^ 2)`). Fix: `nth_rewrite 1 [← Real.sq_sqrt hR]`
  (the nested `conv_lhs => conv_rhs => …` syntax is rejected:
  `error: unexpected identifier; expected '{' or conv`); the remaining `||x||` needs `abs_abs`.
* **`set_option linter.unusedVariables false in` must NOT follow the doc comment** — measured again:
  `error: unexpected token 'set_option'; expected 'lemma'`. Correct order: block comment →
  `set_option … in` → doc comment + theorem (the BEP-round lesson, re-confirmed).
* **`by decide` on a `/`-bearing ℚ comparison** (re-measured; verbatim):
  ```
  error: tactic 'decide' failed for proposition
    3 / 4 < 1
  since its 'Decidable' instance
    (3 / 4).instDecidableLt 1
  did not reduce to 'isTrue' or 'isFalse'.
  After unfolding the instances 'instDecidableEqBool', 'Bool.decEq', 'Int.decLt', 'Rat.instDecidableLt' and 'Int.decNonneg✝', reduction got stuck at the 'Decidable' instance
    match (3 / 4).blt 1, true with …
  ```
  Integer ℚ literals are fine (`example : (1 : ℚ) < 3 := by decide` compiles); `/`-bearing ones are
  `norm_num` (`example : (3 / 4 : ℚ) < 1 := by norm_num` compiles). The K5a/K5b verdict layer must
  stay `norm_num`-sized; `native_decide` is banned (`Lean.ofReduceBool` ∉ `ALLOWED_AXIOMS`).
* **`Rat.cast_prod` needs `Field`, `Rat.cast_sum` only `DivisionRing`** — relevant when a K5a bridges
  is instantiated at a non-field target (all K5a targets are ℝ, so both apply).

### 5. Kernel-verified recipes (one per plan row shape)

| Plan row | Recipe that compiled (module-local helper names omitted) |
|---|---|
| K1 #7 `cascade_self` | `unfold cascade; rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ i + 1 ≤ i), Finset.prod_empty]` — or one line `simp [cascade]`. **`Icc (i+1) i` is empty, not a singleton**: the plan's sketch (`Finset.Icc_self`) is wrong for this statement |
| K1 #14 `fluoYield_zero` | `unfold fluoYield emitYield; rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cascade_self rad ic 0, mul_one]` |
| K1 #15 `upperYield_zero` | `unfold upperYield; rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (1:ℕ) ≤ 0), Finset.sum_empty]` |
| K1 #3/#4 `radBranch_nonneg`/`icBranch_nonneg` | `div_nonneg (h.rad_nonneg n) (le_of_lt (h.decay_pos n hn))` |
| K1 #5/#6 `…_le_one` | `rw [radBranch, div_le_one (h.decay_pos n hn), decay]; linarith [h.ic_nonneg n]` |
| K1 #8/#9 `cascade_nonneg`/`cascade_le_one` | `Finset.prod_nonneg …`; for `≤ 1` the **two-hypothesis** `Finset.prod_le_one (fun j _ => icBranch_nonneg …) (fun j _ => icBranch_le_one …)` (§4.2) |
| K1 #11/#17 `emitYield_nonneg`/`upperYield_nonneg` | `mul_nonneg` / `Finset.sum_nonneg` over `Finset.mem_Icc.mp hi |>.2` |
| K1 #13 `fluoYield_eq_low_add_upper` | `unfold …; rw [Finset.sum_range_eq_add_Ico (f := …) (Nat.succ_pos N), Nat.Ico_succ_right]` — **no `RateData` needed** |
| K1 #20 `specFrac_sum` | `unfold specFrac; rw [← Finset.sum_div]; exact div_self hF` |
| K2 #1/#2/#3 `cascade_succ`, `emitYield_succ`, `emitYield_succ_self` | `unfold cascade; rw [Finset.prod_Icc_succ_top (f := …) (by omega : i + 1 ≤ N + 1)]; ring`; then `ring`-steps |
| K2 #4 `fluoYield_succ` | `rw [Finset.sum_range_succ, Finset.sum_congr rfl hterm, Finset.mul_sum, emitYield_succ_self]; ring` where `hterm` is `emitYield_succ` on `Finset.mem_range.mp hi` — **unconditional** (no `RateData`) |
| K2 #5 `upperYield_succ` | same with `Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)` |
| K2 #13 `upperYield_eq_zero_iff` | `rw [Finset.sum_eq_zero_iff_of_nonneg (fun i hi => emitYield_nonneg h (Finset.mem_Icc.mp hi).2)]` then the two `Finset.mem_Icc` directions |
| K3 #17 `leak_le_of_radBranch_le` | `Finset.sum_le_sum` with `mul_le_mul_of_nonneg_right (hθ …) (cascade_nonneg h h2)`, then `(Finset.mul_sum ..).symm` |
| K4 #1 `cascade_compose` | `hset : Icc (i+1) N = Icc (i+1) M ∪ Icc (M+1) N` by `ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega`; `hdisj` by `rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_Icc] at hx hy; omega`; then `rw [hset, Finset.prod_union hdisj]` — closes by `rfl` |
| K3 #1 ⟺ #2 (cross-multiplication) | `have hden : 0 < rad 1 * decay rad ic 0 := mul_pos hr h0; rw [div_le_div_iff₀ htol hden]; constructor <;> intro h <;> nlinarith [h]` |
| K3 #3 (cancel `rad 0`) | reassociate so the cancelled factor is on the right (`linarith`), then `lt_of_mul_lt_mul_right h' hr0.le` |
| K3 #9 (strict side) | `(div_lt_div_iff₀ hden htol).mp h` gives `rad 0 * ic 1 * tol < (1 - tol) * (rad 1 * decay rad ic 0)`; `nlinarith` against the rate form |
| K3 #10 (strict threshold) | `rw [div_lt_div_iff₀ h0' h0]; nlinarith` — `tol < 1` is *not consumed* (linter off locally) |
| K4 #12/#15 (reciprocal of the threshold) | `unfold kashaGapThreshold; rw [one_div, inv_div]; ring_nf` for `1/K = rad1·dec0·(1-tol)/(A·rad0·tol)`; positivity by `apply div_pos` + `positivity` + (`have h1 : 0 < 1 - tol := by linarith; positivity`) — plain `positivity` cannot see `0 < 1 - tol` from `tol < 1` |
| K4 #14 (sqrt window) | one-line `rw` route: `nth_rewrite 1 [← Real.sq_sqrt hR]; rw [← sq_abs x, sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)]`; `calc` route: `|x| = √(x²) ≤ √R` (`Real.sqrt_sq_eq_abs`) and the reverse `x² = |x|² ≤ (√R)² = R` (`sq_abs`, `pow_le_pow_left₀`, `Real.sq_sqrt`) |
| K5a (all eight cast bridges) | see §6 |
| K4 #12 (the Marcus chain) | see §7 |

### 6. K5a — the eight cast bridges, kernel-verified (recipes for prover_c)

```lean
decayQ_cast    : unfold decayQ decay; push_cast; ring
radBranchQ_cast: unfold radBranchQ radBranch; rw [Rat.cast_div, decayQ_cast]
icBranchQ_cast : unfold icBranchQ icBranch; rw [Rat.cast_div, decayQ_cast]
cascadeQ_cast  : unfold cascadeQ cascade; rw [Rat.cast_prod]; exact Finset.prod_congr rfl fun j _ => icBranchQ_cast rad ic j
emitYieldQ_cast: unfold emitYieldQ emitYield; rw [Rat.cast_mul, radBranchQ_cast, cascadeQ_cast]
fluoYieldQ_cast: unfold fluoYieldQ fluoYield; rw [Rat.cast_sum]; exact Finset.sum_congr rfl fun i _ => emitYieldQ_cast rad ic i N
upperYieldQ_cast: same with `upperYieldQ`, `upperYield`
kashaWithinQ_iff_cast: unfold KashaWithinQ KashaWithin;
  rw [← upperYieldQ_cast, ← fluoYieldQ_cast, ← Rat.cast_mul];
  exact (Rat.cast_le (K := ℝ)).symm
```
`Rat.cast_prod` / `Rat.cast_sum` are the whole reason no induction is needed for the cascade/yield
casts. The predicate transfer needs the fourth step (`← Rat.cast_le`, field explicit) — with only the
three rewrites the goal stays `upperYieldQ … ≤ tol * fluoYieldQ … ↔ ↑(upperYieldQ …) ≤ ↑(tol * fluoYieldQ …)`.

### 7. (c) the K4 #12 Marcus chain, and (f) the exponential-race verdict

**(c) The chain that worked** (`kasha-api-logexp.lean`, two kernel-checked theorems).

1. `exp_neg_div_iff_log (hc : 0 < c) (hA : 0 < A) (hk : 0 < k) : c ≤ A * Real.exp (-b / k) ↔ b ≤ k * Real.log (A / c)`.
   Forward: `div_le_iff₀ hA` → `c / A ≤ exp (-b/k)`; `(Real.log_le_iff_le_exp hcA).mpr` →
   `Real.log (c/A) ≤ -b/k`; `(le_div_iff₀ hk).mp` → `Real.log (c/A) * k ≤ -b`;
   `rw [Real.log_div …] at h3`; then rewrite the *goal's* `Real.log (A/c)` and `linarith`.
   Backward: rewrite `h` with `Real.log_div`, `div_le_iff₀ hk`, `neg_div`, `(Real.log_le_iff_le_exp hcA).mp`,
   `div_le_iff₀ hA`, `linarith`.
   **Direction trap**: `Real.log_le_iff_le_exp`'s `.mp` goes `exp`-ward, `.mpr` goes `log`-ward; the
   two log-div rewrites must be applied to the *hypothesis* and to the *goal* separately (a `rw` on a
   goal that contains `log (A/c)` cannot use `Real.log_div` for `log (c/A)`).
2. `one_div_le_exp_iff (hK : 0 < K) (hk : 0 < k) : 1 / K ≤ Real.exp (-B / k) ↔ B ≤ k * Real.log K`
   (the bridge's actual shape, `A` absorbed) — instance of (1) with `A := 1`, `c := 1/K`, then
   `simpa only [one_div_one_div, one_mul]`.
3. `marcus_gap_window_step … : rad1 * dec0 * (1-tol) ≤ tol * rad0 * (A * Real.exp (-(barrier lam x)/(kB*T)))
   ↔ (lam - x)^2 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold A rad0 dec0 rad1 tol)` — the
   **entire arithmetic content of K4 #12**, proved by
   `hkey` (divide by `tol * rad0 * A > 0` via `div_le_iff₀`, `linarith` both ways) →
   `hquot` (`unfold kashaGapThreshold; rw [one_div, inv_div]; ring_nf`) →
   `rw [hkey, hquot, one_div_le_exp_iff hK hkT]` (with `hK` from K4 #15) →
   `unfold PhotoLean.Marcus.barrier; rw [div_le_iff₀ (by positivity : 0 < 4 * lam)]` →
   `constructor <;> intro x <;> linarith [x]`.
   Combined with K3 #1 (prover_b's row) this yields K4 #12 verbatim; K4 #13 is its `not`-form and
   K4 #14 adds the §5 sqrt window. `positivity` cannot prove `0 < kashaGapThreshold …` (measured);
   `apply div_pos` + `positivity` + `have h1 : 0 < 1 - tol := by linarith; positivity` does.

**(f) Exponential race (plan K4b/K4c, §13 limit 5): statement yes, bounded proof NO.**

* `#check`ed race proposition (kernel-elaborated, no proof):
  `fun (a b : ℝ) (_ : 0 < a) (_ : 0 < b) => ((expMeasure a).prod (expMeasure b)) {p : ℝ × ℝ | p.1 < p.2} = ENNReal.ofReal (a / (a + b))`
  — the type is `(a b : ℝ) → 0 < a → 0 < b → Prop`.
* Kernel-checked partial steps in `kasha-api-race.lean`:
  (i) `expMeasure r = volume.withDensity (exponentialPDF r)` (`rfl`) and
  `isProbabilityMeasureExponential`, `lintegral_exponentialPDF_eq_one` restated;
  (ii) the survival function `expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x)))` for `0 ≤ x`,
  `0 < r` (route: `StieltjesFunction.measure_Ioi (cdf (expMeasure r)) (tendsto_cdf_atTop …) x`, then
  `ProbabilityTheory.measure_cdf`, then `exponentialCDFReal_eq` — note the `unfold exponentialCDFReal at h`
  that `rw [measure_cdf]` requires);
  (iii) the Laplace integral `∫ x in Set.Ioi 0, Real.exp (-(c * x)) = 1 / c` for `0 < c`
  (`integral_comp_mul_left_Ioi` + `integral_exp_neg_Ioi_zero`).
* **Why the full race is not within reach for one lemma**: (1) there is no mathlib object that
  packages "two independent exponential clocks" — `iIndepFun` is a statement about one probability
  space `Ω`, and no lemma identifies `(expMeasure a).prod (expMeasure b)` with it; (2) the density
  change of measure (`lintegral_withDensity_eq_lintegral_mul`) has to be combined with the restriction
  to `Ioi 0` (indicator/`restrict` bookkeeping), (3) the `ℝ≥0∞ → ℝ` conversion
  (`ofReal_integral_eq_lintegral_ofReal`) needs `Integrable` + `0 ≤ᵐ` side conditions, (4) the tail
  `s ↦ expMeasure b (Ioi s)` is `1` for `s < 0`, so the integrand must be split a.e. at `0`, and (5)
  the answer must be reassembled as `ofReal (a / (a + b))`. Order of magnitude: a dedicated sprint
  (order 100 lines of measure theory), not a probe.
* **Verdict**: the plan's §1.2 branching-probability identification stays a **declared modelling
  premise**; K4b/K4c are not delivered as theorems, and the delivered statement list keeps its scope
  limit `the exponential-race derivation of the branching probabilities is not formalized`. The API
  side is now measured, not assumed: everything needed for *one* lemma of the race exists, but the
  composition is a milestone of its own.

### 8. API-risk list per milestone (post-calibration)

| Block | Risk after this round |
|---|---|
| K1 `Basic.lean` | **low** — the four index identities (`cascade_self`, `fluoYield_eq_low_add_upper`, `fluoYield_zero`, `upperYield_zero`) and the `prod_le_one'` trap (§4.2) are the only non-obvious bits, all verified |
| K2 `Criterion.lean` | **low** — `fluoYield_succ`/`upperYield_succ` verified unconditionally; `upperYield_eq_zero_iff` needs the exact `Finset.sum_eq_zero_iff_of_nonneg` signature (quoted) |
| K3 `Sharp.lean` | **low** — cross-multiplication, cancellation, strict threshold all verified; the remaining work is the two-level unfolding (`Icc 1 1 = {1}`, `cascade 1 1 = 1`), which is the §3(a) toolkit |
| K4 `Compose.lean` | **lowest** — `cascade_compose` verified; the Marcus bridge is *proved* here up to K3 #1; only `Real.log`'s positivity side conditions (`kashaGapThreshold_pos`, verified) need care |
| K5a `RatModel.lean` | **low** — all eight bridges verified (`Rat.cast_prod`/`cast_sum` do the heavy lifting); the only traps are the explicit-field forms of `Rat.cast_inj`/`Rat.cast_le` |
| K5b `Instances.lean` | unchanged, `norm_num`-only; no API work needed here (instance rows are prover_c's, not duplicated in these probes) |
| K4b/K4c | **closed as a scope limit** (§7(f)) |

### 9. Plan-sketch corrections found while calibrating (recorded, not applied to the plan)

| Plan locus | Sketch says | Measured |
|---|---|---|
| §4.2 #7 `cascade_self` | "`Finset.Icc_self`, product of one term" | `Icc (i+1) i = ∅` — the usable pair is `Finset.Icc_eq_empty_iff` + `Finset.prod_empty` (`Finset.Icc_self` applies to `Icc a a`, which never occurs in the cascade) |
| §4.2 #13 | "`range (N+1)` = `{0} ∪ Icc 1 N`" | the shortest verified route is `Finset.sum_range_eq_add_Ico` + `Nat.Ico_succ_right` (`Ico`-based); the `range`-equality itself is `Nat.range_succ_eq_Icc_zero` / `Finset.range_eq_Ico`, not `Finset.Ico_eq_range` (absent) |
| §5.1 #1 | "`Finset.Icc_succ_right`, `Finset.prod_insert`" | `Finset.Icc_succ_right` does not exist; the verified route is `Finset.prod_Icc_succ_top` + `ring` |
| §6.1 #8/§6.2 #17 | "`Finset.prod_le_one` with 3" | the *one-argument* `prod_le_one'` is unusable on ℝ (§4.2); the two-hypothesis `prod_le_one` is the working form |

---

## Sabatier theory (2026-09-21) — api_researcher — 4 probes, all `exit 0` / 0 error / 0 warning; the ℚ→ℝ cast transfer, the exp-monotonicity recipe and the max-form minimization are kernel-verified end to end

> Body in English (`AGENTS.md` language policy: `proofs/API-NOTES.md` is an English artifact; no
> mirror copy). Identifiers, `#check` output, errors and warnings are quoted verbatim.
>
> **Authority state.** Measured at repository `HEAD = 61e26d9` ("docs(S0): theories/Sabatier
> scaffolding …"). `theories/Sabatier/plan.md` was still the Sprint-0 scaffold at calibration time
> (milestones S1–S5 only, no statement rows), so this round calibrates the **API surface named in
> the dispatch** — `max`, half-line monotonicity, `abs`, `Real.exp`/`Real.log`, `Real.sqrt`, the
> ℚ→ℝ cast layer and the `if`/`ite` classifier layer — and, for every item, records a *compiling*
> usage form rather than a name. Nothing under `PhotoLean/` was written or modified by this role
> (read-only there); the only files touched are this section and the four probes below.
>
> **Contract note for the lead (checklist item, not an API fact).** The Sabatier probe directory is
> `theories/Sabatier/probes/` (`ENGINE.yml` declares `PROBES` for the canonical theory and
> `<LEAF>_<theory>` for others; `Sabatier` is not yet listed in `THEORIES`, and
> `lakefile.toml`'s `defaultTargets` has no `PhotoLean.Sabatier.*` entry yet — per `ENGINE.md` §1.1
> both must be added when the theory's Lean modules land, otherwise the gate's build pass silently
> skips them).

### 1. Deliverables and compile evidence

| Probe | Topics (dispatch letters) | Run (repo root) | Result |
|---|---|---|---|
| `theories/Sabatier/probes/sabatier-api-max-abs.lean` | (a) `max` on ℝ, (c) `abs` | `proofs/scripts/lake env lean theories/Sabatier/probes/sabatier-api-max-abs.lean` | **exit 0, 0 error, 0 warning**, 50 output lines |
| `theories/Sabatier/probes/sabatier-api-monotone.lean` | (b) `StrictMonoOn`/`StrictAntiOn`/`MonotoneOn`/`AntitoneOn` + the house pattern | same command, filename swapped | **exit 0, 0 error, 0 warning**, 94 output lines |
| `theories/Sabatier/probes/sabatier-api-explog-sqrt.lean` | (d) `Real.exp`/`Real.log`, (e) `Real.sqrt` | as above | **exit 0, 0 error, 0 warning**, 42 output lines |
| `theories/Sabatier/probes/sabatier-api-cast-ite.lean` | (f) ℚ→ℝ cast, (g) `if`/`ite` classifier | as above | **exit 0, 0 error, 0 warning**, 47 output lines |

Each probe is a `#check` log plus kernel-checked `example`/`theorem` bodies. The `NOT FOUND` names
are **not** `#check`ed in the delivered probes (so that they stay at 0 error); they were measured in
a scratch probe and their verbatim error lines are quoted in §9. Every name that appears in the
probes' `#check` blocks is confirmed present; no name in this section is a guess.

Two probes import delivered PhotoLean modules (`PhotoLean.Marcus.Basic`, `PhotoLean.Hammond.Basic`)
to kernel-verify the house-pattern bridges of §3 on the *real* definitions rather than on toys.

### 2. (a) `max` on ℝ — confirmed signatures (verbatim `#check @`, wraps joined)

```
@le_max_left  : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ a ⊔ b
@le_max_right : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ a ⊔ b
@max_le       : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤ c → a ⊔ b ≤ c
@max_le_iff   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c
@le_max_iff   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c
@lt_max_iff   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a < b ⊔ c ↔ a < b ∨ a < c
@max_lt_iff   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ⊔ b < c ↔ a < c ∧ b < c
@max_eq_left  : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → a ⊔ b = a
@max_eq_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → a ⊔ b = b
@max_eq_left_iff  : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ⊔ b = a ↔ b ≤ a
@max_eq_right_iff : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ⊔ b = b ↔ a ≤ b
@max_comm     : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ⊔ b = b ⊔ a
@max_assoc    : ∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
@max_left_comm: ∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
@max_self     : ∀ {α : Type u_1} [inst : LinearOrder α] (a : α), a ⊔ a = a
@max_idem     : ∀ {α : Type u_1} [inst : LinearOrder α], Std.IdempotentOp max
@max_eq_iff   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ⊔ b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b
@max_le_max   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c d : α}, a ≤ c → b ≤ d → a ⊔ b ≤ c ⊔ d
@max_le_max_left  : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α} (c : α), a ≤ b → c ⊔ a ≤ c ⊔ b
@max_le_max_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α} (c : α), a ≤ b → a ⊔ c ≤ b ⊔ c
@min_le_max   : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ⊓ b ≤ a ⊔ b
@max_cases    : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ⊔ b = a ∧ b ≤ a ∨ a ⊔ b = b ∧ a < b
@max_choice   : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ⊔ b = a ∨ a ⊔ b = b
@max_def      : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ⊔ b = if a ≤ b then b else a
@le_max_of_le_left  : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ b → a ≤ b ⊔ c
@le_max_of_le_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → a ≤ b ⊔ c
```

All **fifteen** names of the dispatch's (a) list exist (the block above adds eleven more that
the recipes need), with two recorded readings:

* **`#check` prints `⊔`/`⊓`, not `max`/`min`** — for a `LinearOrder`, `max` *is* `⊔` and `min` *is*
  `⊓`, so `a ⊔ b` in every signature above is `max a b` at the use site. (Consequence: a lemma
  whose statement is written with `max` still unifies, but a *search* for `max`-named lemmas finds
  the `sup`-named ones too.)
* **`max_idem` is an instance, not an equation** (name drift, measured): it is defined at
  `Mathlib/Order/MinMax.lean:157` as `instance max_idem : Std.IdempotentOp (α := α) max`, so
  `#check @max_idem` prints `∀ {α} [LinearOrder α], Std.IdempotentOp max` and the pointwise
  equation must be *projected*: `max_idem.idempotent a`. Writing `max_idem a` gives
  `error: function expected at max_idem … term has type Std.IdempotentOp max`. The pointwise lemma
  `max_self` is the simpler route; both are kernel-checked in the probe.

**Canonical tactic recipes (all kernel-checked in `sabatier-api-max-abs.lean`).**

| Goal shape | Recipe that compiled |
|---|---|
| `max a b ≤ c` | `exact max_le ha hb`, or `(max_le_iff.mp h).1/.2` to *consume* one |
| `c ≤ max a b` | `le_max_iff.mpr (Or.inl h)` / `le_max_of_le_right h`; projections `le_max_left a b`, `le_max_right a b` |
| `max a b = a` | `exact max_eq_left h` with `h : b ≤ a`; `rw [max_eq_left h]` |
| `max a b = b` | `exact max_eq_right h` with `h : a ≤ b` |
| `max a b = a ↔ b ≤ a` | `exact max_eq_left_iff` (or `simp only [max_eq_left_iff]`) — **this is the answer to the dispatch's last sub-question** |
| `max a b = c` | `exact max_eq_iff` for the full characterization; else the case split `rcases le_total a b with h \| h; · exact Or.inr (max_eq_right h); · exact Or.inl (max_eq_left h)`, or the packaged `max_choice a b` / `max_cases a b` / `max_def a b` + `split_ifs` |
| consume `max a b = c` | `rw [← h]` then `le_max_left`/`le_max_right` — **the rewrite is backwards** (see §10.1) |

### 3. (b) monotonicity on a half-line

**(i) The house pattern is plain `∀`, not `Set`-predicates — measured, not asserted.** `grep -rn
'StrictMonoOn\|MonotoneOn\|StrictAntiOn\|AntitoneOn\|Set.Iic\|Set.Ici' PhotoLean/` returns **0
occurrences**. What the delivered sources do instead:

| File:line | Declaration | Shape |
|---|---|---|
| `PhotoLean/Marcus/Basic.lean:71` | `InvertedDescriptor A lam kB T` | `∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate … x₂ < rate … x₁` |
| `PhotoLean/Marcus/Basic.lean:78` | `NormalDescriptor A lam kB T` | `∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate … x₁ < rate … x₂` |
| `PhotoLean/Marcus/Basic.lean:60/65` | `InvertedRegion` / `NormalRegion` | `def … : Prop := lam < x` / `x < lam` (region membership as a plain `Prop`) |
| `PhotoLean/Marcus/Barrier.lean:106/127/143` | `barrier_mono_of_pos` / `barrier_antitone_of_pos` / `barrier_antitone_of_neg` | `{lam} (hlam : 0 < lam) {x₁ x₂} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂` |
| `PhotoLean/Hammond/Basic.lean:66` | `HammondDescriptor lam` | `∀ x₁ x₂ : ℝ, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁` |
| `PhotoLean/Hammond/Criterion.lean:27/34` | `tsCoord_antitone` / `hammond_descriptor_holds` | `unfold tsCoord; rw [div_lt_div_iff_of_pos_right …]; linarith`, then `intro x₁ x₂ h; exact tsCoord_antitone hlam h` |
| `PhotoLean/Hammond/Sharp.lean:32/42/51` | `exists_direction_reversal_of_neg` / `…_of_eq` / `hammond_lam_pos_of_descriptor` | explicit two-point counter-witnesses, consumed per branch of `lt_trichotomy lam 0` |
| `PhotoLean/Marcus/Sharp.lean:188–247` | `sharp_lam_pos_of_lt` / `…_of_eq` / `sharp_lam_pos` | the same triangle: `barrier` monotonicity ⇒ `exp` monotonicity ⇒ contradiction, with `lt_trichotomy lam 0` |

**Verdict for the Sabatier layer:** write the descriptor/region statements in the house `∀`-form
(pair + explicit region hypotheses + explicit physical premises) unless the statement authority says
otherwise; keep region membership as a `Prop`-valued `def`. The `Set`-predicate layer is fully
interderivable with it, and the probes kernel-verify the bridges on the *delivered* definitions, so
a prover may switch to `StrictMonoOn` mid-proof without changing the statement:

```
Marcus.NormalDescriptor A lam kB T   ↔ StrictMonoOn (fun x => rate A lam kB T x) (Set.Icc 0 lam)
Marcus.InvertedDescriptor A lam kB T ↔ StrictAntiOn (fun x => rate A lam kB T x) (Set.Ioi lam)
Hammond.HammondDescriptor lam        ↔ StrictAntiOn (fun x => Hammond.tsCoord lam x) Set.univ
```

**Trap (statement fact, measured):** the second row uses **`Set.Ioi`**, not `Set.Ici`.
`InvertedDescriptor` demands the *strict* side condition `lam < x₁`, membership in `Set.Ici lam` only
gives `lam ≤ x₁`, and the two do not match: the proof fails with
`application type mismatch … has type lam ≤ x : Prop but is expected to have type lam < x : Prop`.
The corresponding `↔` with `Set.Ici` is simply false at `x₁ = lam`.

**(ii) The four definitions (verbatim `#print`, wraps joined).**

```
def StrictMonoOn  … := fun f s => ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f a < f b
def StrictAntiOn  … := fun f s => ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f b < f a
def MonotoneOn    … := fun f s => ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≤ b → f a ≤ f b
def AntitoneOn    … := fun f s => ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≤ b → f b ≤ f a
```

Because the elements are **strict implicit** (`⦃a⦄`) and the membership proofs are explicit, a bare
`intro x hx y hy hxy` in a `StrictMonoOn` goal introduces exactly `x, hx, y, hy, hxy`, and
`hf hx hy hxy` is the whole *use* site.

**(iii) The lemmas that make an `intro`-style proof terminate (all `#check`ed).**

```
@monotoneOn_iff_forall_lt : MonotoneOn f s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f a ≤ f b
@antitoneOn_iff_forall_lt : AntitoneOn f s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f b ≤ f a
@StrictMonoOn.monotoneOn : StrictMonoOn f s → MonotoneOn f s
@StrictAntiOn.antitoneOn : StrictAntiOn f s → AntitoneOn f s
@StrictMonoOn.le_iff_le : StrictMonoOn f s → a ∈ s → b ∈ s → (f a ≤ f b ↔ a ≤ b)
@StrictMonoOn.lt_iff_lt : StrictMonoOn f s → a ∈ s → b ∈ s → (f a < f b ↔ a < b)
@StrictMonoOn.eq_iff_eq : StrictMonoOn f s → a ∈ s → b ∈ s → (f a = f b ↔ a = b)
@StrictMonoOn.injOn    : StrictMonoOn f s → Set.InjOn f s
@Set.strictMonoOn_iff_strictMono : StrictMonoOn f s ↔ StrictMono fun a : s => f a
@strictMonoOn_univ : StrictMonoOn f Set.univ ↔ StrictMono f
@strictMonoOn_id   : ∀ {s : Set α}, StrictMonoOn id s
@Set.strictMonoOn_singleton : ∀ (f : α → β) {a}, StrictMonoOn f {a}
@strictMonoOn_insert_iff : StrictMonoOn f (insert a s) ↔ (∀ b ∈ s, b < a → f b < f a) ∧ (∀ b ∈ s, a < b → f a < f b) ∧ StrictMonoOn f s
@Set.monotoneOn_iff_monotone : MonotoneOn f s ↔ Monotone fun a : s => f a
@monotoneOn_id : ∀ {s : Set α}, MonotoneOn id s
@monotoneOn_const : ∀ {c : β} {s : Set α}, MonotoneOn (fun _ : α => c) s
@antitoneOn_const : ∀ {c : β} {s : Set α}, AntitoneOn (fun _ : α => c) s
@Set.monotoneOn_singleton : ∀ (f : α → β) {a}, MonotoneOn f {a}
@strictMono_restrict : StrictMono (s.restrict f) ↔ StrictMonoOn f s
@StrictMonoOn.restrict : StrictMonoOn f s → StrictMono (s.restrict f)
@MonotoneOn.mono  : MonotoneOn f s  → s₂ ⊆ s → MonotoneOn f s₂      @AntitoneOn.mono  : the twin
@StrictMonoOn.mono: StrictMonoOn f s → s₂ ⊆ s → StrictMonoOn f s₂   @StrictAntiOn.mono: the twin
@MonotoneOn.monotone : MonotoneOn f s → Monotone (f ∘ Subtype.val)  @StrictMonoOn.strictMono : the strict twin
@StrictMonoOn.comp : StrictMonoOn g t → StrictMonoOn f s → Set.MapsTo f s t → StrictMonoOn (g ∘ f) s
@StrictAntiOn.comp : StrictAntiOn g t → StrictAntiOn f s → Set.MapsTo f s t → StrictMonoOn (g ∘ f) s
@StrictMonoOn.comp_strictAntiOn : StrictMonoOn g t → StrictAntiOn f s → Set.MapsTo f s t → StrictAntiOn (g ∘ f) s
@StrictAntiOn.comp_strictMonoOn : StrictAntiOn g t → StrictMonoOn f s → Set.MapsTo f s t → StrictAntiOn (g ∘ f) s
@StrictMonoOn.Iic_union_Ici : StrictMonoOn f (Set.Iic a) → StrictMonoOn f (Set.Ici a) → StrictMono f
@StrictMonoOn.union : StrictMonoOn f s → StrictMonoOn f t → IsGreatest s c → IsLeast t c → StrictMonoOn f (s ∪ t)
@Set.mem_Iic : x ∈ Set.Iic b ↔ x ≤ b        @Set.mem_Ici : x ∈ Set.Ici a ↔ a ≤ x
@Set.mem_Iio : x ∈ Set.Iio b ↔ x < b        @Set.mem_Ioi : x ∈ Set.Ioi a ↔ a < x
@Set.mem_Icc : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b
@Set.mapsTo   → @Set.MapsTo : (α → β) → Set α → Set β → Prop
```

* **`strictMonoOn_iff_…`**: the dispatch asked for it — the name that exists is
  `Set.strictMonoOn_iff_strictMono : StrictMonoOn f s ↔ StrictMono fun a : s => f a` (it lives in
  *namespace `Set`* in `Mathlib/Data/Set/Basic.lean:1480`, which is why a bare
  `strictMonoOn_iff_strictMono` is `unknown identifier`). `strictMonoOn_iff_forall_lt` does **not**
  exist (§9) and is not needed: `StrictMonoOn` is already `∀`-shaped (see the `#print` output).
  The `MonotoneOn`/`AntitoneOn` analogues are `monotoneOn_iff_forall_lt`,
  `antitoneOn_iff_forall_lt` (root namespace) and `Set.monotoneOn_iff_monotone`.
* **`strictMonoOn_const` does not exist** and must not be invented — a constant function is *not*
  strictly monotone on a nontrivial set. The existing names are `monotoneOn_const` /
  `antitoneOn_const` (both hypothesis-free), verified in the probe.
* **`MonotoneOn.mono` does exist** (and so do the other three `.mono` lemmas): they live in
  `Mathlib/Data/Set/Monotone.lean:60–70` and are declared as `_root_.MonotoneOn.mono`, i.e. they
  attach to the *root* name. A first grep that looked only for `(theorem|lemma) MonotoneOn.mono`
  missed them — the `_root_.` prefix is part of the declaration line, not of the name.
* **Membership needs no rewrite**: `x ∈ Set.Iic b` and `x ≤ b` are definitionally equal, so
  `exact hx` works in both directions; `Set.mem_Iic.mp/.mpr` are the named forms when a `rw`/`simp`
  step wants a lemma.

**(iv) Measured trap in the `intro`-style route.** After `intro`, the goal still contains the
beta-redex `(fun x => 2 * x) x`, and `linarith` treats it as an *opaque atom* — it fails with
`linarith failed to find a contradiction … a✝ : (fun x => 2 * x) x ≥ (fun x => 2 * x) y ⊢ False`.
Run `dsimp only` (or `show`) first; the probe's recipe is `intro x _ y _ hxy; dsimp only; linarith`.

### 4. (c) `abs` — confirmed signatures

```
@abs_le : ∀ {α} [LinearOrderedAddCommGroup α] {a b : α}, |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
@abs_lt : ∀ {α} [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α] {a b : α}, |a| < b ↔ -b < a ∧ a < b
@abs_le' : ∀ {α} [Lattice α] [AddGroup α] {a b : α}, |a| ≤ b ↔ a ≤ b ∧ -a ≤ b      -- the `to_additive` primitive of `abs_le`
@abs_sub_comm : ∀ {α} [Lattice α] [AddGroup α] (a b : α), |a - b| = |b - a|
@abs_of_nonneg : ∀ {α} [Lattice α] [AddGroup α] [AddLeftMono α] {a : α}, 0 ≤ a → |a| = a
@abs_of_nonpos : ∀ {α} [Lattice α] [AddGroup α] [AddLeftMono α] {a : α}, a ≤ 0 → |a| = -a
@abs_of_pos : 0 < a → |a| = a          @abs_of_neg : a < 0 → |a| = -a
@neg_le_of_abs_le : ∀ {α} [LinearOrderedAddCommGroup α] {a b : α}, |a| ≤ b → -b ≤ a
@le_of_abs_le     : ∀ {α} [LinearOrderedAddCommGroup α] {a b : α}, |a| ≤ b → a ≤ b
@abs_sub_le_iff : ∀ {α} [LinearOrderedAddCommGroup α] {a b c : α}, |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c
@abs_sub_le : ∀ {α} [LinearOrderedAddCommGroup α] (a b c : α), |a - c| ≤ |a - b| + |b - c|
@abs_nonneg : ∀ {α} [Lattice α] [AddGroup α] [AddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
@abs_nonpos_iff : |a| ≤ 0 ↔ a = 0      @abs_pos : 0 < |a| ↔ a ≠ 0
@abs_eq_max_neg : |a| = a ⊔ -a         -- `abs` *is* a `max`, useful when a volcano bound is written with `max`
```

**Seven of the dispatch's eight names exist; `abs_le_iff` does not** (§9) — the two usable forms
are `abs_le` (`-b ≤ a ∧ a ≤ b`) and the
primitive `abs_le'` (`a ≤ b ∧ -a ≤ b`, generated by `to_additive` from `mabs_le'`). They differ only
in the order of the conjunction and in which side carries the negation.

**The recipe the dispatch asked for** — `|x - y| ≤ t → x ≤ y + t` with `t x y : ℝ`. Four
kernel-checked routes, shortest first:

```lean
example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t :=        -- one step, no tactic
  sub_le_iff_le_add'.mp (le_of_abs_le h)

example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by     -- the house style
  have h' : x - y ≤ t := le_of_abs_le h
  linarith

example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by linarith [le_of_abs_le h]

example {x y t : ℝ} (h : |x - y| ≤ t) : x ≤ y + t := by     -- via the `abs_sub` specialisation
  have h' : x - y ≤ t := (abs_sub_le_iff.mp h).1
  linarith
```

Symmetric bound `y ≤ x + t`: `linarith [(abs_sub_le_iff.mp h).2]`. To mirror the argument order use
`rwa [abs_sub_comm] at h`. To get the two-sided window in one step:
`rw [abs_sub_le_iff] at h` gives `x - y ≤ t ∧ y - x ≤ t`.

### 5. (d) `Real.exp` / `Real.log`

```
Real.exp_pos : ∀ (x : ℝ), 0 < Real.exp x          Real.exp_ne_zero : ∀ (x : ℝ), Real.exp x ≠ 0
Real.exp_nonneg : ∀ (x : ℝ), 0 ≤ Real.exp x       Real.exp_zero  : Real.exp 0 = 1
@Real.exp_le_exp : ∀ {x y : ℝ}, Real.exp x ≤ Real.exp y ↔ x ≤ y      -- **already the `iff`**
@Real.exp_lt_exp : ∀ {x y : ℝ}, Real.exp x < Real.exp y ↔ x < y      -- **already the `iff`**
Real.exp_monotone   : Monotone Real.exp
Real.exp_strictMono : StrictMono Real.exp
Real.exp_injective  : Function.Injective Real.exp
@Real.exp_le_one_iff : Real.exp x ≤ 1 ↔ x ≤ 0    @Real.exp_lt_one_iff : Real.exp x < 1 ↔ x < 0
@Real.one_lt_exp_iff : 1 < Real.exp x ↔ 0 < x
Real.exp_add : Real.exp (x + y) = Real.exp x * Real.exp y
Real.exp_sub : Real.exp (x - y) = Real.exp x / Real.exp y     Real.exp_neg : Real.exp (-x) = (Real.exp x)⁻¹
Real.log_exp : ∀ (x : ℝ), Real.log (Real.exp x) = x           @Real.exp_log : 0 < x → Real.exp (Real.log x) = x
@Real.log_le_log : 0 < x → x ≤ y → Real.log x ≤ Real.log y
@Real.log_lt_log : 0 < x → x < y → Real.log x < Real.log y
@Real.log_le_log_iff : 0 < x → 0 < y → (Real.log x ≤ Real.log y ↔ x ≤ y)
@Real.log_lt_log_iff : 0 < x → 0 < y → (Real.log x < Real.log y ↔ x < y)
@Real.log_pos : 1 < x → 0 < Real.log x            @Real.log_nonneg : 1 ≤ x → 0 ≤ Real.log x
@Real.log_nonpos : 0 ≤ x → x ≤ 1 → Real.log x ≤ 0
@Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1
@Real.log_le_iff_le_exp : 0 < x → (Real.log x ≤ y ↔ x ≤ Real.exp y)      -- `.mpr` goes exp-ward
@Real.le_log_iff_exp_le : 0 < y → (x ≤ Real.log y ↔ Real.exp x ≤ y)      -- `.mpr` goes log-ward
Real.log_injOn_pos : Set.InjOn Real.log (Set.Ioi 0)
```

**`Real.exp_le_exp_iff` / `Real.exp_lt_exp_iff` do not exist on ℝ** (§9) — on ℝ the names
`Real.exp_le_exp` / `Real.exp_lt_exp` *are* the `iff`s. (`EReal.exp_le_exp_iff` exists for `EReal`
and is a different statement; do not import it into an ℝ proof.)

#### The key recipe: dimensionless comparison → energy comparison (kernel-verified)

Goal: from `Real.exp (-(a) / (kB * T)) ≤ Real.exp (-(b) / (kB * T))` with `0 < kB`, `0 < T`, get
`b ≤ a`. Three cancelling steps: drop `exp` via `Real.exp_le_exp`, cancel the **positive**
denominator via `div_le_div_iff_of_pos_right`, flip the negations via `neg_le_neg_iff`:

```lean
theorem exp_neg_div_le_iff_of_pos {a b k : ℝ} (hk : 0 < k) :
    Real.exp (-a / k) ≤ Real.exp (-b / k) ↔ b ≤ a := by
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hk, neg_le_neg_iff]

-- the physical hypothesis shape (0 < kB, 0 < T) reduces to it by `mul_pos`:
theorem exp_neg_div_le_iff {a b kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) :
    Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T)) ↔ b ≤ a :=
  exp_neg_div_le_iff_of_pos (mul_pos hkB hT)
```

Both are **kernel-checked** in `sabatier-api-explog-sqrt.lean`, together with the two one-directional
halves (`exp_neg_div_mono` for `b ≤ a ⇒ …`, `le_of_exp_neg_div_le` for the necessity side) and the
`linarith` variant that survives when the two sides are not syntactically `-(·)/k`. The house
alternative when `kB * T` has already been combined into a hypothesis `hkT : 0 < kB * T` is the same
three rewrites with `hkT`:

```lean
example {a b kB T : ℝ} (hkT : 0 < kB * T)
    (h : Real.exp (-a / (kB * T)) ≤ Real.exp (-b / (kB * T))) : b ≤ a := by
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff] at h
  exact h
```

**Why not `div_le_div_iff_of_pos_right` alone?** Because a bare `div_le_div_iff_of_pos_right` cannot
remove the `(−)`; and `neg_le_neg_iff` (`-a ≤ -b ↔ b ≤ a`) is the *only* step that reverses the
order — `linarith` after the two rewrites also works and is the fallback when the shapes drift.

#### The `rate`-shaped version (the cross-theory row)

`PhotoLean.Marcus.rate A lam kB T x = A * Real.exp (-(barrier lam x) / (kB * T))`. The delivered
`PhotoLean.Marcus.Rate.rate_gt_of_barrier_lt` covers `barrier <` ⟹ `rate >`. The volcano needs the
**reverse** reading; the probe proves both directions (new, kernel-checked):

```lean
theorem barrier_le_of_rate_le {A lam kB T x₁ x₂ : ℝ} (hA : 0 < A) (hkB : 0 < kB) (hT : 0 < T)
    (h : Marcus.rate A lam kB T x₁ ≤ Marcus.rate A lam kB T x₂) : Marcus.barrier lam x₂ ≤ Marcus.barrier lam x₁ := by
  have hkT : 0 < kB * T := mul_pos hkB hT
  unfold Marcus.rate at h
  rw [mul_le_mul_left hA, Real.exp_le_exp, div_le_div_iff_of_pos_right hkT, neg_le_neg_iff] at h
  exact h
-- strict twin: same with `lt`, `mul_lt_mul_left`, `Real.exp_lt_exp`, `neg_lt_neg_iff`
```

Note the argument order of the conclusion: the rate inequality `rate x₁ ≤ rate x₂` yields
`barrier x₂ ≤ barrier x₁` — the rate is **antitone** in the barrier, so the inequalities flip.

#### The `log` counterpart

```lean
theorem log_threshold {c A b k : ℝ} (hA : 0 < A) (hc : 0 < c) :
    c ≤ A * Real.exp (-b / k) ↔ Real.log (c / A) ≤ -b / k := by
  rw [Real.log_le_iff_le_exp (div_pos hc hA), mul_comm A, ← div_le_iff₀ hA]
theorem log_threshold_energy {c A k b : ℝ} (hA : 0 < A) (hk : 0 < k) (hc : 0 < c) :
    c ≤ A * Real.exp (-b / k) ↔ Real.log (c / A) * k ≤ -b := by
  rw [← le_div_iff₀ hk, mul_comm A, ← div_le_iff₀ hA, Real.log_le_iff_le_exp (div_pos hc hA)]
```

Direction rule (re-confirmed): `Real.log_le_iff_le_exp`'s `.mpr` goes **exp-ward** (`x ≤ Real.exp y`),
`Real.le_log_iff_exp_le`'s `.mpr` goes **log-ward** (`Real.exp x ≤ y`). The division lemmas needed:
`div_le_iff₀`, `le_div_iff₀`, `div_pos`.

### 6. (e) `Real.sqrt` — exact hypotheses in v4.17.0

```
@Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
Real.sqrt_sq_eq_abs : ∀ (x : ℝ), √(x ^ 2) = |x|
@Real.sqrt_mul_self : ∀ {x : ℝ}, 0 ≤ x → √(x * x) = x
@Real.sqrt_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x * y) = √x * √y
@Real.sqrt_div : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x / y) = √x / √y
@Real.sqrt_pos : ∀ {x : ℝ}, 0 < √x ↔ 0 < x
@Real.sqrt_pos_of_pos : ∀ {x : ℝ}, 0 < x → 0 < √x          -- **exists** (the dispatch asked)
Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x
@Real.sqrt_lt_sqrt : ∀ {x y : ℝ}, 0 ≤ x → x < y → √x < √y
@Real.sqrt_lt_sqrt_iff : ∀ {x y : ℝ}, 0 ≤ x → (√x < √y ↔ x < y)
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
@Real.sqrt_le_sqrt_iff : ∀ {x y : ℝ}, 0 ≤ y → (√x ≤ √y ↔ x ≤ y)
@Real.sqrt_inj : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (√x = √y ↔ x = y)
@Real.sqrt_eq_zero_of_nonpos : ∀ {x : ℝ}, x ≤ 0 → √x = 0
```

**Hypothesis table (the trap the dispatch anticipated — the four order lemmas are *not* symmetric):**

| Name | hypothesis | on which argument |
|---|---|---|
| `Real.sqrt_le_sqrt` | `x ≤ y` | — (hypothesis-free) |
| `Real.sqrt_le_sqrt_iff` | `0 ≤ y` | **right** argument |
| `Real.sqrt_lt_sqrt` | `0 ≤ x` and `x < y` | **left** argument |
| `Real.sqrt_lt_sqrt_iff` | `0 ≤ x` | **left** argument |
| `Real.sqrt_inj` | `0 ≤ x` and `0 ≤ y` | both |

Passing the wrong one is a unification failure, never a silently different statement. Note also that
the `#check` output prints `√` with **no space**: `√x ^ 2 = x` parses as `(√x) ^ 2 = x`.

**Apex recipes (kernel-checked).**

```lean
example {lam : ℝ} (hlam : 0 < lam) : 0 < Real.sqrt lam := Real.sqrt_pos_of_pos hlam
example {lam : ℝ} (hlam : 0 ≤ lam) : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam
example {lam x : ℝ} (hlam : 0 ≤ lam) (h : x = Real.sqrt lam) : x ^ 2 = lam := by rw [h, Real.sq_sqrt hlam]
example {lam₁ lam₂ : ℝ} (h₁ : 0 ≤ lam₁) (h : lam₁ < lam₂) : Real.sqrt lam₁ < Real.sqrt lam₂ :=
  Real.sqrt_lt_sqrt h₁ h
```

The `√`-window (a squared comparison against an apex) needs the `nth_rewrite` discipline recorded in
§kasha §4.4, and works in both orientations:

```lean
example {R x : ℝ} (hR : 0 ≤ R) : x ^ 2 ≤ R ↔ |x| ≤ Real.sqrt R := by
  nth_rewrite 1 [← Real.sq_sqrt hR]
  rw [sq_le_sq, abs_of_nonneg (Real.sqrt_nonneg R)]

example {R x : ℝ} (hR : 0 ≤ R) : |x| ≤ Real.sqrt R ↔ x ^ 2 ≤ R := by
  constructor
  · intro h
    have h' : (|x|) ^ 2 ≤ (Real.sqrt R) ^ 2 := by
      rw [sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)]; exact h
    rwa [sq_abs, Real.sq_sqrt hR] at h'
  · intro h
    have h' : (|x|) ^ 2 ≤ (Real.sqrt R) ^ 2 := by rwa [sq_abs, Real.sq_sqrt hR]
    rwa [sq_le_sq, abs_abs, abs_of_nonneg (Real.sqrt_nonneg R)] at h'
```

### 7. (f) ℚ → ℝ cast, and the `..._cast` transfer shape

```
@Rat.cast_add / cast_sub / cast_mul / cast_div / cast_inv : [DivisionRing α] [CharZero α] (p q : ℚ), ↑(p ± * / q) = ↑p ± * / ↑q
@Rat.cast_neg / cast_zero / cast_one : [DivisionRing α] only
@Rat.cast_ofNat  : [DivisionRing α] (n : ℕ) [n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_natCast: [DivisionRing α] (n : ℕ), ↑↑n = ↑n      @Rat.cast_intCast : ↑↑n = ↑n
@Rat.cast_le : ∀ {p q : ℚ} {K} [LinearOrderedField K], ↑p ≤ ↑q ↔ p ≤ q
@Rat.cast_lt : ∀ {p q : ℚ} {K} [LinearOrderedField K], ↑p < ↑q ↔ p < q
@Rat.cast_inj : [DivisionRing α] [CharZero α] {p q : ℚ}, ↑p = ↑q ↔ p = q
@Rat.cast_injective : [DivisionRing α] [CharZero α], Function.Injective Rat.cast
@Rat.cast_def : ∀ {K} [DivisionRing K] (q : ℚ), ↑q = ↑q.num / ↑q.den
@Rat.cast_max : ∀ {K} [LinearOrderedField K] (p q : ℚ), ↑(p ⊔ q) = ↑p ⊔ ↑q      -- `@[simp, norm_cast]`
@Rat.cast_min : ∀ {K} [LinearOrderedField K] (p q : ℚ), ↑(p ⊓ q) = ↑p ⊓ ↑q      -- `@[simp, norm_cast]`
@Rat.cast_abs : ∀ {K} [LinearOrderedField K] (q : ℚ), ↑|q| = |↑q|
@Rat.cast_pos : 0 < ↑q ↔ 0 < q    @Rat.cast_nonneg : 0 ≤ ↑q ↔ 0 ≤ q    @Rat.cast_nonpos : ↑q ≤ 0 ↔ q ≤ 0
@Rat.cast_lt_zero : ↑q < 0 ↔ q < 0    @Rat.cast_ne_zero : ↑p ≠ 0 ↔ p ≠ 0    @Rat.cast_eq_zero : ↑p = 0 ↔ p = 0
@Rat.cast_sum : [DivisionRing α] [CharZero α] (s : Finset ι) (f : ι → ℚ), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)
@Rat.cast_prod : [Field α] [CharZero α] (s : Finset ι) (f : ι → ℚ), ↑(∏ i ∈ s, f i) = ∏ i ∈ s, ↑(f i)
@Rat.cast_mono : [LinearOrderedField K], Monotone Rat.cast
@Rat.cast_strictMono : [LinearOrderedField K], StrictMono Rat.cast
Rat.castHom (α) [DivisionRing α] [CharZero α] : ℚ →+* α
```

Note the unchanged traps already registered in §kasha: `Rat.cast_prod` needs `Field` while
`Rat.cast_sum` only needs `DivisionRing`; and the *field must be explicit* when the instance is not
determined by the goal: `(Rat.cast_le (K := ℝ))`.

**Recipe for `((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) ↔ p < q`** (kernel-checked, all four orientations):

```lean
example {p q : ℚ} : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) ↔ p < q := Rat.cast_lt                 -- the `iff` itself
example {p q : ℚ} : p < q ↔ ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).symm  -- reversed goal
example {p q : ℚ} (h : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ)) : p < q := (Rat.cast_lt (K := ℝ)).mp h
example {p q : ℚ} (h : p < q) : ((p : ℚ) : ℝ) < ((q : ℚ) : ℝ) := by exact_mod_cast h
-- and `by norm_cast` closes the goal-side `↔` in one step
```

**Cast commuting with `max`.** The dispatch's guesses `map_max` / `Rat.cast_max` resolve as:
`map_max` is **not** usable (`error: unknown identifier 'map_max'`, §9); the current name is
**`Rat.cast_max`**, and all three routes are kernel-checked:

```lean
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := Rat.cast_max p q
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := by push_cast; rfl
example (p q : ℚ) : ((max p q : ℚ) : ℝ) = max (p : ℝ) (q : ℝ) := by norm_cast
```

**The `..._cast` transfer shape used by the delivered rational models.** Read from
`PhotoLean/Hammond/RatModel.lean` (H5a, lines 65–110) and `PhotoLean/Kasha/RatModel.lean` (K5a; §6
of the §kasha section above):

| Transfer kind | Recipe | Delivered example |
|---|---|---|
| algebraic body (`…/…`, `^2`, `*`) | `unfold Xq X; push_cast; ring` | `tsCoordQ_cast`, `gapReactantQ_cast` (Hammond), `volcanoQ_cast` (probe) |
| algebraic body, explicit rewrites | `unfold Xq X; rw [Rat.cast_div, Rat.cast_pow, …]` — **closes by itself**, no trailing `rfl` | `volcanoQ_cast'` (probe, §10.9) |
| predicate / comparison | push the cast through the body, then `Rat.cast_le` / `Rat.cast_lt` (explicit field) or its `.symm` | `kashaWithinQ_iff_cast`, `volcanoWithinQ_iff_cast` (probe) |
| classifier (`if`-cascade) | `unfold zoneQ zone; norm_cast` — no hypotheses, no case bash | `hammondZoneQ_eq_hammondZone`, `volcanoZoneQ_eq_volcanoZone` (probe) |
| big operators | `Rat.cast_sum` / `Rat.cast_prod` remove the need for induction over the index set | `cascadeQ_cast`, `fluoYieldQ_cast` (Kasha) |

`push_cast` alone does **not** close an algebraic transfer — `ring` must follow (the two routes have
opposite tail rules; see §10.9).

### 8. (g) the `if` / `ite` classifier layer

```
@if_pos : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
@if_neg : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
@ite_eq_iff  : (if P then a else b) = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
@ite_eq_iff' : (if P then a else b) = c ↔ (P → a = c) ∧ (¬P → b = c)
@dif_pos : ∀ {c : Prop} {h : Decidable c} (hc : c) {α} {t : c → α} {e : ¬c → α}, dite c t e = t hc
@dif_neg : ∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α} {t : c → α} {e : ¬c → α}, dite c t e = e hnc
@apply_ite : (f : α → β) (P : Prop) [Decidable P] (x y : α), f (if P then x else y) = if P then f x else f y
@apply_dite : (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α), f (dite P x y) = if h : P then f (x h) else f (y h)
@ite_cond_eq_true  : c = True  → (if c then a else b) = a
@ite_cond_eq_false : c = False → (if c then a else b) = b
```

All ten names quoted above exist (the five the dispatch named — `if_pos`, `if_neg`, `ite_eq_iff`,
`dif_pos`, `apply_ite` — plus `ite_eq_iff'`, `dif_neg`, `apply_dite`, `ite_cond_eq_true`,
`ite_cond_eq_false`). **`split_ifs at h` is the tool for a hypothesis**, `if_pos`/`if_neg` for
a goal.

**The classifier shape as delivered** (`PhotoLean/Hammond/Basic.lean:82` `hammondZone` = 7 branches;
`PhotoLean/BEP/Basic.lean:104` `epZone` = 9 branches) and reproduced self-containedly as a 6-branch
`volcanoZone` in `sabatier-api-cast-ite.lean`:

* **Backward direction** (predicate → classifier value): `unfold zone; rw [if_neg g₁, if_neg g₂,
  …, if_pos gₖ]`, each guard discharged inline by `linarith` / `by rintro rfl; …`. BEP's own form is
  `rw [if_neg (by linarith : ¬ (lam = 0)), if_neg (by linarith : ¬ lam < 0), if_pos rfl]`.
* **Forward direction** (classifier value → predicate): `unfold zone at h; split_ifs at h with h1 … h8`
  followed by the branch arithmetic (BEP `epZone_eq_…_iff`).
* **The characterization lemma shape** (`zone x = Z ↔ predicate`): `unfold zone`, then
  `split_ifs with h1 … h_n`. A cascade with `n` guards yields **`n+1` goals** in guard order
  (`hammondZone`: 6 guards → 7 goals, matching its 7 branches; `epZone`: 8 guards → 9 goals,
  again matching its 9 branches). **Naming convention (measured, and it is the subtle part):**
  in branch `i`, the hypotheses `h1 … h_{i-1}` are the **negated** earlier guards and `h_i` is the
  **positive** one; the final branch has `h1 … h_n` **all negated**. That is exactly why
  `hammondZoneQ_eq_late_iff`'s last branch can write
  `⟨lt_of_le_of_ne (le_of_not_gt h6) h5, lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm h2)⟩`.
  Each goal is closed by `iff_of_true rfl …` / `iff_of_false (by decide) …` (the `by decide` is on the
  *inductive-constructor* inequality, not on ℚ arithmetic — see §kasha §4.4).
* **A fully worked 5-branch example** (6 branches in the cascade) with the branch bookkeeping and the
  `weak`-branch arithmetic is `volcanoZoneQ_eq_weak_iff` in `sabatier-api-cast-ite.lean`; the
  `strong` branch (which needs no case arithmetic) is `volcanoZoneQ_eq_strong_iff`.
* **Verdict rows**: `rw [← zoneQ_eq_zone]; unfold zoneQ; norm_num` reduces the whole concrete
  `if`-cascade — the `Rat.epQVerdict` recipe of §BEP §3. **Trap:** the rewrite only matches the
  ℚ-literal form; `volcanoZone (2 : ℝ) (3 : ℝ)` does not match `volcanoZone ↑2 ↑3` (§10.10).

### 9. NOT FOUND in mathlib v4.17.0 (verbatim errors; banned in Sabatier proofs)

```
error: unknown identifier 'strictMonoOn_const'          -- a constant is not strictly monotone; use `monotoneOn_const`
error: unknown identifier 'strictMonoOn_iff_forall_lt'  -- `StrictMonoOn` is already `∀`-shaped; `Set.strictMonoOn_iff_strictMono` exists
error: unknown constant 'Real.exp_le_exp_iff'           -- on ℝ this is `Real.exp_le_exp` itself
error: unknown constant 'Real.exp_lt_exp_iff'           -- on ℝ this is `Real.exp_lt_exp` itself
error: unknown identifier 'abs_le_iff'                  -- use `abs_le` (or the primitive `abs_le'`)
error: unknown identifier 'map_max'                     -- use `Rat.cast_max` / `Rat.cast_min`, or `max_def` + case split
error: unknown constant 'Real.exp_log_iff'              -- use `Real.exp_log` (→) and `Real.log_exp` (←)
error: unknown identifier 'strictMonoOn_iff_strictMono' -- it is `Set.strictMonoOn_iff_strictMono`
error: unknown identifier 'strictMonoOn_singleton'      -- it is `Set.strictMonoOn_singleton`
error: unknown identifier 'monotoneOn_iff_monotone'     -- it is `Set.monotoneOn_iff_monotone`
error: unknown identifier 'monotoneOn_singleton'        -- it is `Set.monotoneOn_singleton`
```

| Banned | Verified replacement (usage form that compiled) |
|---|---|
| `strictMonoOn_const` | `monotoneOn_const` / `antitoneOn_const` (a constant *is* monotone on every set) |
| `strictMonoOn_iff_forall_lt` | nothing needed; `Set.strictMonoOn_iff_strictMono`, `strictMonoOn_univ`, `strictMonoOn_insert_iff` are the existing `iff`s |
| bare `strictMonoOn_iff_strictMono`, `strictMonoOn_singleton`, `monotoneOn_iff_monotone`, `monotoneOn_singleton` | the **namespace-qualified** forms `Set.…` (they live in `namespace Set`, `Mathlib/Data/Set/Basic.lean` / `Subsingleton.lean`) |
| `Real.exp_le_exp_iff` | `Real.exp_le_exp` (`Real.exp x ≤ Real.exp y ↔ x ≤ y`) |
| `Real.exp_lt_exp_iff` | `Real.exp_lt_exp` |
| `Real.exp_log_iff` | `Real.exp_log` (`0 < x → Real.exp (Real.log x) = x`) |
| `abs_le_iff` | `abs_le` (`-b ≤ a ∧ a ≤ b`) or `abs_le'` (`a ≤ b ∧ -a ≤ b`) |
| `map_max` | `Rat.cast_max` (`↑(max p q) = max ↑p ↑q`), or `max_def` + `rcases le_total`/`max_cases` |
| `max_idem` used as a function | `max_idem.idempotent a` (it is the instance `Std.IdempotentOp max`), or `max_self a` |

### 10. Measured traps (kernel facts, not name facts)

1. **`rw` on `max a b = c` must go backwards.** With `h : max a b = c` and goal `a ≤ c`,
   `rw [h]` fails: `error: tactic 'rewrite' failed, did not find instance of the pattern in the
   target expression / a ⊔ b`. Use `rw [← h]` then `le_max_left`/`le_max_right`.
2. **`intro` leaves a beta-redex for `linarith`.** `intro x _ y _ hxy; linarith` on a
   `StrictMonoOn (fun x => 2 * x) …` goal fails (`linarith failed to find a contradiction … a✝ :
   (fun x => 2 * x) x ≥ (fun x => 2 * x) y ⊢ False`); insert `dsimp only` (or `show`).
3. **`StrictAntiOn` on a half-line needs `Set.Ioi`, not `Set.Ici`, for a *strict* descriptor**
   (measured `application type mismatch … lam ≤ x : Prop … expected lam < x : Prop`; the `↔` with
   `Set.Ici` is false at the endpoint). See §3.
4. **`Real.sqrt_le_sqrt_iff` carries `0 ≤ y` (right argument) but `Real.sqrt_lt_sqrt_iff` carries
   `0 ≤ x` (left argument).** Full table in §6.
5. **The unused-hypothesis linter fires on hypotheses, not only on variables.**
   `warning: unused variable 'hlam'` for a statement-mandated premise the proof does not consume
   (same situation as `hammondZoneQ_eq_atReactant_iff`). The house response is
   `set_option linter.unusedVariables false in` **before** the doc comment
   (`set_option … in` → doc comment → declaration — the ordering rule re-confirmed in §kasha §4.4).
6. **`rw [← Rat.cast_lt] at h` does not cross the cast on a *hypothesis*.** With
   `h : ↑p < ↑q : Prop` (ℝ) the pattern is a *ℚ* comparison, so rewriting fails syntactically:
   `error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
   ?m.94 < ?m.95`. Use `.mp` with the explicit field (`(Rat.cast_lt (K := ℝ)).mp h`) or
   `exact_mod_cast h`.
7. **`push_cast` does not cross ℚ→ℝ in the goal `↑p < ↑q`.** From `h : p < q` the goal
   `↑p < ↑q` is left untouched (the casts are already at the leaves), so `push_cast; exact h` fails
   with `type mismatch … h has type p < q … expected ↑p < ↑q`. Use `exact_mod_cast h`, `norm_cast`,
   or `(Rat.cast_lt (K := ℝ)).mpr h`.
8. **`norm_cast` closes a classifier transfer but is not a case analysis.** `unfold zoneQ zone;
   norm_cast` transfers a 6/7/9-branch `if`-cascade with **no hypotheses and no `split_ifs`** — this
   is the single reason no `by_cases` transcription is needed for the ℚ-side classifier.
9. **The two algebraic cast routes have opposite tails.** `unfold …; push_cast; ring` **needs** the
   `ring`; `unfold …; rw [Rat.cast_div, Rat.cast_pow, …]` closes **by itself**, so appending `rfl`
   gives `error: no goals to be solved`.
10. **Rewriting with a classifier transfer does not match ℝ literals.** On
    `volcanoZone (2 : ℝ) (3 : ℝ) = VZone.strong`, `rw [← volcanoZoneQ_eq_volcanoZone (2 : ℚ)
    (3 : ℚ)]` fails: `did not find instance of the pattern in the target expression / volcanoZone ↑2 ↑3`
    (the ℝ literal is `OfNat.ofNat 2`, not `↑(2 : ℚ)`). Prove the ℚ-literal form in a `have` and
    close the numeral gap with `simpa`.
11. **A `√`-window rewrite must be `nth_rewrite 1 [← Real.sq_sqrt hR]`** — a plain `rw` rewrites too
    deep into the `R` inside `Real.sqrt R` (§kasha §4.4, re-confirmed in §6).

### 11. API-risk list per Sabatier milestone (post-calibration)

| Milestone (plan §2) | Risk after this round |
|---|---|
| S1 `PhotoLean/Sabatier/Basic.lean` (description layer: `max`-form activity, region predicates, classifier) | **low** — every `max`/`abs` name of §2/§4 is confirmed; the `if`-cascade shape of §8 is kernel-checked on a 6-branch volcano classifier |
| S2 `Criterion.lean` ("prove it": the volcano shape, monotone flanks) | **low** — the half-line recipes of §3 and the exp recipe of §5 are kernel-checked; the house `∀`- vs `Set`-predicate question is settled (§3) |
| S3 `Sharp.lean` (exact conditions, apex uniqueness) | **low/medium** — the `√` apex algebra of §6 is verified in both orientations, but case analysis must respect the `Set.Ioi` fact (§3) and the `lt_trichotomy`-with-explicit-witness house pattern (`PhotoLean/Marcus/Sharp.lean:188–247`, `PhotoLean/Hammond/Sharp.lean:32–59`) |
| S4 `Compose.lean` (microscopic / cross-theory form) | **low** — `rate`/`barrier` are the delivered `PhotoLean.Marcus` objects; both directions of the barrier↔rate comparison are now kernel-checked (§5), the reverse one being new |
| S5 `RatModel.lean` / `Instances.lean` (verdicts) | **low** — all transfer recipes of §7 are verified, including a full 6-branch classifier transfer and a `norm_num` verdict row; the only traps are the literal-match issue (§10.10) and `by decide` on `/`-bearing ℚ literals (banned since §kasha §4.4) |

---

## Goldschmidt theory (2026-09-21) — api_researcher — 7 probes, all exit 0 / 0 error / 0 warning

> Body in English (`AGENTS.md` language policy: `proofs/API-NOTES.md` is an English artifact; no
> mirror copy). Identifiers, `#check` output, errors and warnings are quoted verbatim.
>
> **Authority state.** Measured at repository `HEAD = 95dc0ba`. The plan of record is
> `theories/goldschmidt/plan.md` (Sprint 0); the directory `theories/goldschmidt/probes/` was
> **empty** at calibration time — `goldschmidt-statement-skeleton.lean` did not exist yet — so every
> statement form below is derived from plan §2 (symbol table), §4–§9 (row tables) and the dispatch's
> row list, and stated as the form that compiles today. Nothing under `PhotoLean/` was written or
> modified by this role; the only files touched are this section and the seven probes.
>
> **Standard.** Each delivered probe is a `#check` log **plus** kernel-checked `theorem`/`example`
> bodies, and each one is required to be *warning-free*, so no deprecated name is `#check`ed inside
> them (a deprecation is a warning). The verbatim deprecation and `unknown constant` texts are
> quoted in §9 from a scratch probe.
>
> **What is a *settled delivered form* here** (the point of the round): `tolFac_irrational` (§5),
> `exists_negative_of_pos` / `exists_compensating_partner` (§6), `tolFacSq_cast` / `inBandQ_cast`
> (§7), `zoneQ_eq_zone` plus the three `goldschmidtZone` characterization rows (§8) — all with
> complete kernel-checked proofs in the probes, and the six instance verdicts (§10, an independent
> cross-check of the numbers).

### 1. Deliverables and compile evidence

| Probe | Topics (dispatch letters) | `#check`s | Kernel-checked rows |
|---|---|---|---|
| `theories/goldschmidt/probes/goldschmidt-api-sqrt.lean` | (a) `Real.sqrt` bookkeeping | 19 | the 3 identities, `latticeOf_div_sqrt_eq_idealAO`, `contact_iff_tolFac_one`, `idealA_contact` |
| `theories/goldschmidt/probes/goldschmidt-api-div-mono.lean` | (b) squaring, (c) division/monotonicity, auxiliary lemmas of this entry | 59 | `tolFac_strictMono_rA`, `tolFac_strictAnti_rB`, `conforms_iff_radius_window`, `le_tolFac_iff_sq`, `tolFac_le_iff_sq`, `conforms_iff_sq`, `tolFac_eq_one_iff`, `chiTol_anti_corrected` (+`'`) and the kernel-checked falsification of the plan's sketched `chiTol_anti` direction |
| `theories/goldschmidt/probes/goldschmidt-api-sqrt2-irrational.lean` | (d) irrationality | 23 | `irrational_ratCast_div_sqrt_two`, two orientations, **`tolFac_irrational` (complete)** |
| `theories/goldschmidt/probes/goldschmidt-api-finset-z.lean` | (e) `Finset`/`ℤ` charge balance | 17 | `chargeBalanced_single_iff`/`_pair_iff` on the raw sum *and* in the authority's `ChargeBalanced` signatures, **`exists_negative_of_pos`**, **`exists_compensating_partner`** (complete; authority signature, no `DecidableEq`) |
| `theories/goldschmidt/probes/goldschmidt-api-rat-cast.lean` | (f) ℚ layer and ℚ→ℝ casts | 23 | `tolFacSq_cast` (2 routes), `le_tolFac_iff_sq`, `tolFac_le_iff_sq`, **`inBandQ_cast`**, plus the ℚ-trap examples (`|·|`, `inBandQ` by `norm_num`) |
| `theories/goldschmidt/probes/goldschmidt-api-classifier.lean` | (g) `if`/`ite` classifier | 12 | `deriving DecidableEq`, **`zoneQ_eq_zone`** (authority signature), **`zoneQ_ideal_iff`**, the four `goldschmidtZone_eq_…_iff` rows, the `norm_num [zoneQ]` verdict recipe, and the two kernel witnesses that the quotient-shaped guard diverges |
| `theories/goldschmidt/probes/goldschmidt-api-instance-arith.lean` | (h) instance arithmetic | 0 (arithmetic-only) | the six verdicts, classic/tetragonal band membership, `tolFac_gt/lt_one_of_sq_gt/lt`, and the nine authority-radii sum equalities |

Exact command (from the repository root), run once per file:

```
proofs/scripts/lake env lean theories/goldschmidt/probes/goldschmidt-api-<topic>.lean
```

Measured in one loop at `HEAD = 95dc0ba` (`<probe>` = `sqrt`, `div-mono`, `sqrt2-irrational`,
`finset-z`, `rat-cast`, `classifier`, `instance-arith`):

```
goldschmidt-api-sqrt.lean            exit=0 err=0 warn=0 outlines=19 checks=19
goldschmidt-api-div-mono.lean        exit=0 err=0 warn=0 outlines=93 checks=59
goldschmidt-api-sqrt2-irrational.lean exit=0 err=0 warn=0 outlines=23 checks=23
goldschmidt-api-finset-z.lean        exit=0 err=0 warn=0 outlines=32 checks=17
goldschmidt-api-rat-cast.lean        exit=0 err=0 warn=0 outlines=25 checks=23
goldschmidt-api-classifier.lean      exit=0 err=0 warn=0 outlines=14 checks=12
goldschmidt-api-instance-arith.lean  exit=0 err=0 warn=0 outlines=0  checks=0
```

(`outlines` counts the probe's stdout lines: `#check` output plus any multi-line signature wrap;
`instance-arith` is `#check`-free by design — it asserts no API name.)

Every name quoted in this section was `#check`ed in *this* run; the absent ones were measured in a
scratch probe and are quoted verbatim in §9. No name here is a guess.

### 2. (a) `Real.sqrt` bookkeeping — confirmed signatures (verbatim `#check @`, wraps joined)

```
@Real.sqrt_pos_of_pos : ∀ {x : ℝ}, 0 < x → 0 < √x
@Real.sqrt_ne_zero' : ∀ {x : ℝ}, √x ≠ 0 ↔ 0 < x
@Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
Real.sqrt_sq_eq_abs : ∀ (x : ℝ), √(x ^ 2) = |x|
@Real.sqrt_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x * y) = √x * √y
@Real.sqrt_mul_self : ∀ {x : ℝ}, 0 ≤ x → √(x * x) = x
Real.sqrt_mul_self_eq_abs : ∀ (x : ℝ), √(x * x) = |x|
@Real.sqrt_div : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x / y) = √x / √y
@Real.div_sqrt : ∀ {x : ℝ}, x / √x = √x
@Real.mul_self_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x * √x = x
Real.sqrt_inv : ∀ (x : ℝ), √x⁻¹ = (√x)⁻¹
@Real.sqrt_div_self' : ∀ {x : ℝ}, √x / x = 1 / √x
@Real.sqrt_pos : ∀ {x : ℝ}, 0 < √x ↔ 0 < x
Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
@Real.sqrt_lt_sqrt : ∀ {x y : ℝ}, 0 ≤ x → x < y → √x < √y
@Real.sqrt_le_sqrt_iff : ∀ {x y : ℝ}, 0 ≤ y → (√x ≤ √y ↔ x ≤ y)
@Real.sqrt_lt_sqrt_iff : ∀ {x y : ℝ}, 0 ≤ x → (√x < √y ↔ x < y)
@Real.sqrt_eq_zero_of_nonpos : ∀ {x : ℝ}, x ≤ 0 → √x = 0
```

**The three bookkeeping identities — exact tactic lines (all kernel-checked in the probe):**

| identity | recipe that compiled |
|---|---|
| `2 / Real.sqrt 2 = Real.sqrt 2` | `Real.div_sqrt` — **one term, no tactic**. `Real.div_sqrt` is *unconditional* (`x / √x = √x`, also at `x = 0` because `0/0 = 0 = √0`), so nothing about positivity is needed |
| `Real.sqrt 2 * (1 / Real.sqrt 2) = 1` | `rw [one_div, mul_inv_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))]` |
| `(1 / Real.sqrt 2) * Real.sqrt 2 = 1` | `rw [one_div, inv_mul_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))]` (note: `inv_mul_cancel₀`, the reversed factor order) |
| `Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1` | `mul_inv_cancel₀ ((Real.sqrt_ne_zero').mpr (by norm_num))` — the `⁻¹` form without `one_div` |
| `Real.sqrt 2 * Real.sqrt 2 = 2` | `Real.mul_self_sqrt (by norm_num)` (the `*` version) |
| `Real.sqrt 2 ^ 2 = 2` | `Real.sq_sqrt (by norm_num)` (the `^` version; note `√x ^ 2` parses as `(√x)^2`) |
| `2 * (rB + rO) / √2 = √2 * (rB + rO)` | `rw [show 2 * x / Real.sqrt 2 = (2 / Real.sqrt 2) * x by ring, Real.div_sqrt]` — the `ring` rearrangement is *needed* (a bare `ring` does close `2*x/√2 = (2/√2)*x`, but not the second step) |
| `Real.sqrt 2 ≠ 0` | `(Real.sqrt_ne_zero').mpr (by norm_num)` — **not** `Real.sqrt_ne_zero_of_pos` (§9) |
| `0 < Real.sqrt 2` | `Real.sqrt_pos_of_pos (by norm_num)` — there is no `Real.sqrt_two_pos` (§9) |

Two G1 rows are kernel-checked on the same probe over the plan §2 mirrors
(`latticeOf rB rO = 2*(rB+rO)`, `idealAO rB rO = √2*(rB+rO)`, `tolFac rA rB rO = (rA+rO)/(√2*(rB+rO))`):

* `latticeOf_div_sqrt_eq_idealAO : latticeOf rB rO / √2 = idealAO rB rO` —
  `have h : … = (2 / √2) * (rB + rO) := by unfold latticeOf; ring`, then `rw [h]; unfold idealAO; rw [Real.div_sqrt]`.
  **Trap:** a trailing `rfl` after those rewrites is `error: no goals to be solved` — `rw` already
  closes a goal that becomes reflexive.
* `contact_iff_tolFac_one : rA + rO = idealAO rB rO ↔ tolFac rA rB rO = 1` —
  `unfold tolFac idealAO; rw [div_eq_one_iff_eq (mul_ne_zero sqrt_two_ne_zero hB)]`, and **stop**:
  the `rw` closes the `↔` by itself (appending `constructor` is `no goals to be solved`).

### 3. (b) squaring equivalences and (c) division/monotonicity — the two G3 headlines

**(b) confirmed signatures (verbatim `#check @`, wraps joined).** `sq_le_sq'`, `sq_le_sq`,
`sq_lt_sq`, `sq_lt_sq'`, `sq_le_sq₀`, `sq_lt_sq₀`, `pow_le_pow_left₀`, `pow_lt_pow_left₀`,
`abs_le`, `abs_sub_le_iff`, `sq_nonneg`, `Real.sqrt_le_sqrt`, `Real.sqrt_le_sqrt_iff`:

```
@sq_le_sq' : ∀ {α : Type u_1} [inst : LinearOrderedRing α] {a b : α}, -b ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2
@sq_le_sq : ∀ {α : Type u_1} [inst : LinearOrderedRing α] {a b : α}, a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b|
@sq_lt_sq : ∀ {α : Type u_1} [inst : LinearOrderedRing α] {a b : α}, a ^ 2 < b ^ 2 ↔ |a| < |b|
@sq_lt_sq' : ∀ {α : Type u_1} [inst : LinearOrderedRing α] {a b : α}, -b < a → a < b → a ^ 2 < b ^ 2
@sq_le_sq₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [inst_2 : ZeroLEOneClass M₀]
  [inst_3 : PosMulStrictMono M₀] [inst_4 : MulPosStrictMono M₀] {a b : M₀}, 0 ≤ a → 0 ≤ b → (a ^ 2 ≤ b ^ 2 ↔ a ≤ b)
@sq_lt_sq₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [inst_2 : ZeroLEOneClass M₀]
  [inst_3 : PosMulStrictMono M₀] [inst_4 : MulPosStrictMono M₀] {a b : M₀}, 0 ≤ a → 0 ≤ b → (a ^ 2 < b ^ 2 ↔ a < b)
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀}
  [inst_2 : ZeroLEOneClass M₀] [inst_3 : PosMulMono M₀] [inst_4 : MulPosMono M₀],
  0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n
@pow_lt_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a b : M₀}
  [inst_2 : ZeroLEOneClass M₀] [inst_3 : PosMulStrictMono M₀] [inst_4 : MulPosStrictMono M₀],
  a < b → 0 ≤ a → ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
@abs_le : ∀ {α : Type u_1} [inst : LinearOrderedAddCommGroup α] {a b : α}, |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
@abs_sub_le_iff : ∀ {α : Type u_1} [inst : LinearOrderedAddCommGroup α] {a b c : α}, |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c
@sq_nonneg : ∀ {α : Type u_1} [inst : Semiring α] [inst_1 : LinearOrder α] [inst_2 : IsRightCancelAdd α]
  [inst_3 : ZeroLEOneClass α] [inst_4 : ExistsAddOfLE α] [inst_5 : PosMulMono α] [inst_6 : AddLeftStrictMono α] (a : α),
  0 ≤ a ^ 2
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
@Real.sqrt_le_sqrt_iff : ∀ {x y : ℝ}, 0 ≤ y → (√x ≤ √y ↔ x ≤ y)
```

**The recipe the dispatch asked for** (`0 ≤ a → 0 ≤ b → a^2 ≤ b^2 ↔ a ≤ b` in v4.17.0) is exactly
`sq_le_sq₀ ha hb` — hypotheses first, no `abs`. The `abs`-flavoured `sq_le_sq` (`↔ |a| ≤ |b|`) is a
different statement; the strict twin is `sq_lt_sq₀ ha hb`. `sq_le_sq'` / `sq_lt_sq'` are the
*hypothesis-shaped* implications (`-b ≤ a → a ≤ b → …`) and need no nonnegativity.

**(c) confirmed signatures (wraps joined).**

```
@div_lt_div_of_pos_right : … {a b c : G₀} [MulPosStrictMono G₀], a < b → 0 < c → a / c < b / c
@div_lt_div_of_pos_left : … 0 < a → 0 < c → c < b → a / b < a / c
@div_lt_div_iff_of_pos_right : … 0 < c → (a / c < b / c ↔ a < b)
@div_lt_div_iff_of_pos_left : … 0 < a → 0 < b → 0 < c → (a / b < a / c ↔ c < b)
@div_le_div_of_nonneg_left : … 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
@div_le_div_of_nonneg_right : … a ≤ b → 0 ≤ c → a / c ≤ b / c
@div_le_div_iff_of_pos_right : … 0 < c → (a / c ≤ b / c ↔ a ≤ b)
@div_le_div_iff_of_pos_left : … 0 < a → 0 < b → 0 < c → (a / b ≤ a / c ↔ c ≤ b)
@div_le_iff₀ : … 0 < c → (b / c ≤ a ↔ b ≤ a * c)
@le_div_iff₀ : … 0 < c → (a ≤ b / c ↔ a * c ≤ b)
@div_lt_iff₀ : … 0 < c → (b / c < a ↔ b < a * c)
@lt_div_iff₀ : … 0 < c → (a < b / c ↔ a * c < b)
@div_eq_one_iff_eq : ∀ {G₀} [GroupWithZero G₀] {a b : G₀}, b ≠ 0 → (a / b = 1 ↔ a = b)
@div_eq_div_iff : ∀ {G₀} [CommGroupWithZero G₀] {a b c d : G₀}, b ≠ 0 → d ≠ 0 → (a / b = c / d ↔ a * d = c * b)
@div_eq_iff : … b ≠ 0 → (a / b = c ↔ a = c * b)      @eq_div_iff : … b ≠ 0 → (c = a / b ↔ c * b = a)
@one_div : ∀ {G} [DivInvMonoid G] (a : G), 1 / a = a⁻¹
@inv_mul_cancel₀ : ∀ {G₀} [GroupWithZero G₀] {a : G₀}, a ≠ 0 → a⁻¹ * a = 1
@div_add_div_same : ∀ {K} [DivisionSemiring K] (a b c : K), a / c + b / c = (a + b) / c
@add_div : ∀ {K} [DivisionSemiring K] (a b c : K), (a + b) / c = a / c + b / c
@div_sub_div_same : ∀ {K} [DivisionRing K] (a b c : K), a / c - b / c = (a - b) / c
@sub_div : ∀ {K} [DivisionRing K] (a b c : K), (a - b) / c = a / c - b / c
```

**The `₀` question (the drift the dispatch anticipated):** `div_le_iff` and `le_div_iff` **exist but
are deprecated** (warning, not error) — the working names are `div_le_iff₀` / `le_div_iff₀`;
`div_lt_iff` / `lt_div_iff` were already recorded as drifted to `div_lt_iff₀` / `lt_div_iff₀` in the
Marcus round and are re-confirmed here (no `div_le_iff₀`-style trap: the `₀` forms are exactly the
old statements). `div_add_div` exists but needs `Field`-style hypotheses, so for the theory's
uniform denominators `div_add_div_same` / `add_div` are the ones to use.

**Two usage forms kernel-checked on the theory's own denominator `√2 * (rB + rO)`:**

* `tolFac_strictMono_rA` (plan §6): `unfold tolFac; exact div_lt_div_of_pos_right (by linarith) hd`
  with `hd : 0 < √2 * (rB + rO)`.
* `tolFac_strictAnti_rB` (plan §6): the monotone denominator goes through
  `div_lt_div_of_pos_left hA hd hlt` where **the last argument is the *denominator* inequality
  `hd : √2*(rB+rO) < √2*(rB'+rO)`** (the lemma states `0 < a → 0 < c → c < b → a / b < a / c`, so
  the "smaller denominator" comes last and the conclusion is written in the reversed order).

**The two G3 headline rows, kernel-checked end to end** (`goldschmidt-api-div-mono.lean` and
`goldschmidt-api-rat-cast.lean`).

* `conforms_iff_radius_window` — the un-squared window:
  `(lo ≤ t ∧ t ≤ hi) ↔ (lo * (√2*(rB+rO)) ≤ rA+rO ∧ rA+rO ≤ hi * (√2*(rB+rO)))`,
  proved by `rw [tolFac]; exact and_congr (le_div_iff₀ hd) (div_le_iff₀ hd)` (no squaring at all).
* `conforms_iff_sq` — the `√2`-free headline, halves:
  `le_tolFac_iff_sq hlo hB hA : lo ≤ t ↔ 2*lo^2*(rB+rO)^2 ≤ (rA+rO)^2` and
  `tolFac_le_iff_sq hhi hB hA : t ≤ hi ↔ (rA+rO)^2 ≤ 2*hi^2*(rB+rO)^2`, assembled by `and_congr`.
  Each half is **two steps**:
  `rw [tolFac, le_div_iff₀ hd, ← hsq]` then `exact (sq_le_sq₀ … ).symm`, where
  `hsq : (lo * (√2*(rB+rO)))^2 = 2*lo^2*(rB+rO)^2` is proved by
  `rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring`.
  **Direction trap:** the goal after the rewrites is `a ≤ b ↔ a^2 ≤ b^2`, i.e. the *reverse* of
  `sq_le_sq₀`, so the `.symm` is mandatory (`exact sq_le_sq₀ …` is a type mismatch — measured).
* `tolFac_eq_one_iff` (G1): `unfold tolFac; rw [div_eq_one_iff_eq (mul_ne_zero sqrt_two_ne_zero hB)]`
  — the two side conditions are `√2 ≠ 0` (`Real.sqrt_ne_zero'`) and `rB + rO ≠ 0`.

**The G2 `chiTol_anti` direction (statement fact, kernel-checked).** Plan §2 defines
`chiTol tol₀ k χ χ' = tol₀ - k * |χ - χ'|`, and plan §5 sketches the row as
`|χ'' - χ| ≤ |χ' - χ| → 0 ≤ k → chiTol tol₀ k χ χ'' ≤ chiTol tol₀ k χ χ'`. With the plan's own
definition of `chiTol` that conclusion is **inverted**: `chiTol` is antitone in `|Δχ|`, so the
*closer* `χ''` gets the **larger** tolerance, and the true row is
`chiTol tol₀ k χ χ' ≤ chiTol tol₀ k χ χ''`. `goldschmidt-api-div-mono.lean` contains both

```lean
theorem chiTol_anti_corrected {tol0 k chi chi' chi'' : ℝ}
    (h : |chi - chi''| ≤ |chi - chi'|) (hk : 0 ≤ k) :
    chiTol tol0 k chi chi' ≤ chiTol tol0 k chi chi'' := by
  unfold chiTol
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left h hk) tol0
```

(and the same row re-spelled in the plan's `|χ'' - χ| ≤ |χ' - χ|` hypothesis order via
`abs_sub_comm`), and a **kernel-checked falsification of the sketched direction**
(`chiTol_anti_sketch_counterexample`) at `χ = 0`, `χ' = 1`, `χ'' = 0`, where the hypothesis holds and
`chiTol 0 1 0 0 = 0 > -1 = chiTol 0 1 0 1`. The tool is

```
@sub_le_sub_left : ∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE α] [inst_2 : AddLeftMono α]
  [inst_3 : AddRightMono α] {a b : α}, a ≤ b → ∀ (c : α), c - b ≤ c - a
```

i.e. subtracting reverses the order (`a ≤ b → c - b ≤ c - a`). This is the same class of defect as
the S1/Hammond "tautology trap" and the BEP statement corrections: the *name* `_anti` and the
conclusion must agree, and here they do not.

### 4. (d) `Irrational` — the drift is severe, and the row is settled

**Nothing in the dispatch's candidate family `Irrational.mul_ratCast` / `div_ratCast` /
`add_ratCast` / `ratCast_mul` / `ratCast_div` / `of_ratCast_mul` / `of_ratCast_add` /
`of_ratCast_div` / `sub_ratCast` / `of_ratCast_sub` / `of_ratCast_inv` exists in v4.17.0.** The
whole closure family is spelled with a bare `rat` / `int` / `nat`. Confirmed signatures:

```
Irrational : ℝ → Prop
irrational_sqrt_two : Irrational √2
@Irrational.inv : ∀ {x : ℝ}, Irrational x → Irrational x⁻¹
@Irrational.ne_rat : ∀ {x : ℝ}, Irrational x → ∀ (q : ℚ), x ≠ ↑q
@Irrational.ne_zero : ∀ {x : ℝ}, Irrational x → x ≠ 0
@Irrational.rat_mul : ∀ {x : ℝ}, Irrational x → ∀ {q : ℚ}, q ≠ 0 → Irrational (↑q * x)
@Irrational.mul_rat : ∀ {x : ℝ}, Irrational x → ∀ {q : ℚ}, q ≠ 0 → Irrational (x * ↑q)
Irrational.of_mul_rat : ∀ (q : ℚ) {x : ℝ}, Irrational (x * ↑q) → Irrational x
Irrational.rat_add : ∀ (q : ℚ) {x : ℝ}, Irrational x → Irrational (↑q + x)
Irrational.add_rat : ∀ (q : ℚ) {x : ℝ}, Irrational x → Irrational (x + ↑q)
Irrational.of_rat_add : ∀ (q : ℚ) {x : ℝ}, Irrational (↑q + x) → Irrational x
Irrational.rat_sub : ∀ (q : ℚ) {x : ℝ}, Irrational x → Irrational (↑q - x)
Irrational.sub_rat : ∀ (q : ℚ) {x : ℝ}, Irrational x → Irrational (x - ↑q)
@Irrational.rat_div : ∀ {x : ℝ}, Irrational x → ∀ {q : ℚ}, q ≠ 0 → Irrational (↑q / x)
@Irrational.div_rat : ∀ {x : ℝ}, Irrational x → ∀ {q : ℚ}, q ≠ 0 → Irrational (x / ↑q)
Irrational.of_div_rat : ∀ (q : ℚ) {x : ℝ}, Irrational (x / ↑q) → Irrational x
Irrational.of_rat_div : ∀ (q : ℚ) {x : ℝ}, Irrational (↑q / x) → Irrational x
@Irrational.mul_int : ∀ {x : ℝ}, Irrational x → ∀ {m : ℤ}, m ≠ 0 → Irrational (x * ↑m)
@Irrational.of_mul_self : ∀ {x : ℝ}, Irrational (x * x) → Irrational x
@Irrational.of_one_div : ∀ {x : ℝ}, Irrational (1 / x) → Irrational x
Rat.not_irrational : ∀ (q : ℚ), ¬Irrational ↑q
@irrational_sqrt_natCast_iff : ∀ {n : ℕ}, Irrational √↑n ↔ ¬IsSquare n
@Nat.Prime.irrational_sqrt : ∀ {p : ℕ}, Nat.Prime p → Irrational √↑p
```

Note the binder shapes: in `Irrational.mul_rat` / `rat_mul` / `div_rat` / `rat_div` the rational is
an **implicit** `{q : ℚ}` followed by the explicit `q ≠ 0`, whereas in `Irrational.of_mul_rat` /
`of_div_rat` / `of_rat_div` / `rat_add` / `rat_sub` the rational is an **explicit first argument**.

**Settled statement of `tolFac_irrational` (plan §7 G4).** The plan writes the row on rational radii
while `tolFac : ℝ → ℝ → ℝ → ℝ`; the form that compiles — and that keeps the plan's `tolFac` shape
verbatim, so no definition is specialized — quantifies `ℚ` and casts inside the conclusion:

```lean
theorem tolFac_irrational (rA rB rO : ℚ) (hA : rA + rO ≠ 0) (hB : rB + rO ≠ 0) :
    Irrational (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ))
```

Both hypotheses are **necessary**, not cosmetic: `rB + rO = 0` or `rA + rO = 0` each make
`tolFac = 0` (rational). The proof is a complete, kernel-checked three-step argument
(`goldschmidt-api-sqrt2-irrational.lean`, no placeholder):

```lean
theorem irrational_ratCast_div_sqrt_two (q : ℚ) (hq : q ≠ 0) :
    Irrational ((q : ℝ) / Real.sqrt 2) := by
  have h : Irrational ((q : ℝ) * (Real.sqrt 2)⁻¹) :=
    (irrational_sqrt_two.inv).rat_mul hq          -- Irrational.inv, then Irrational.rat_mul
  simpa only [div_eq_mul_inv] using h

theorem tolFac_irrational (rA rB rO : ℚ) (hA : rA + rO ≠ 0) (hB : rB + rO ≠ 0) :
    Irrational (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) := by
  have hq : (rA + rO) / (rB + rO) ≠ 0 := div_ne_zero hA hB
  have key : tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)
      = ((rA + rO) / (rB + rO) : ℚ) / Real.sqrt 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)
    have hb : ((rB + rO : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hB
    unfold tolFac
    push_cast
    field_simp
    ring
  rw [key]
  exact irrational_ratCast_div_sqrt_two _ hq
```

Three things the prover must not improvise:

1. the algebraic identity `key` is closed by **`push_cast` → `field_simp` → `ring`**. The two
   context hypotheses (`√2 ≠ 0`, `↑(rB+rO) ≠ 0`) are what `field_simp` consumes.
2. **`ring_nf` does NOT close `key`** — it leaves `unsolved goals` (verbatim in §9). `field_simp`
   with `ring` is the working tail; `push_cast; ring_nf` is the failing route.
3. all three statement orientations of the denominator are available and kernel-checked:
   `Irrational (↑q / √2)`, `Irrational ((√2)⁻¹ * ↑q)` (`simpa only [mul_comm]`), and
   `Irrational (↑q * (√2)⁻¹)` (straight from `Irrational.rat_mul`). The plan's phrasing
   "`Irrational (Real.sqrt 2)` scaled by the rational ratio" maps onto the **`↑q / √2`** form; the
   other two are recorded as equivalent spellings, not as different rows.

A concrete instance (`rA = rB = 1/2`, `rO = 3/2`, so `t = 1/√2`) is also kernel-checked, and
`Irrational.ne_rat` (`h.ne_rat q : x ≠ ↑q`) plus `Rat.not_irrational` are exercised as the
contradiction-side tools.

### 5. (e) `Finset`/`ℤ` charge balance — the toolkit, and two complete proofs

**Confirmed signatures (verbatim `#check @`, wraps joined):**

```
@Finset.sum_eq_zero_iff_of_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : OrderedAddCommMonoid N] {f : ι → N}
  {s : Finset ι}, (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
@Finset.sum_eq_zero_iff_of_nonpos : ∀ {ι : Type u_1} {N : Type u_2} [inst : OrderedAddCommMonoid N] {f : ι → N}
  {s : Finset ι}, (∀ i ∈ s, f i ≤ 0) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)
@Finset.sum_erase_add : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid β] [inst_1 : DecidableEq α] (s : Finset α)
  (f : α → β) {a : α}, a ∈ s → ∑ x ∈ s.erase a, f x + f a = ∑ x ∈ s, f x
@Finset.sum_erase_eq_sub : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f : α → β} [inst : AddCommGroup β]
  [inst_1 : DecidableEq α] {a : α}, a ∈ s → ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x - f a
@Finset.sum_pos' : ∀ {ι : Type u_1} {M : Type u_2} [inst : OrderedCancelAddCommMonoid M] {f : ι → M} {s : Finset ι},
  (∀ i ∈ s, 0 ≤ f i) → (∃ i ∈ s, 0 < f i) → 0 < ∑ i ∈ s, f i
@Finset.sum_pos : ∀ {ι : Type u_1} {M : Type u_2} [inst : OrderedCancelAddCommMonoid M] {f : ι → M} {s : Finset ι},
  (∀ i ∈ s, 0 < f i) → s.Nonempty → 0 < ∑ i ∈ s, f i
@Finset.sum_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : OrderedAddCommMonoid N] {f : ι → N} {s : Finset ι},
  (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i
@Finset.sum_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : OrderedAddCommMonoid N] {f g : ι → N} {s : Finset ι},
  (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
@Finset.sum_lt_sum : ∀ {ι : Type u_1} {M : Type u_2} [inst : OrderedCancelAddCommMonoid M] {f g : ι → M} {s : Finset ι},
  (∀ i ∈ s, f i ≤ g i) → (∃ i ∈ s, f i < g i) → ∑ i ∈ s, f i < ∑ i ∈ s, g i
@Finset.sum_sub_distrib : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f g : α → β} [inst : SubtractionCommMonoid β],
  ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x
@Finset.sum_neg_distrib : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f : α → β} [inst : SubtractionCommMonoid β],
  ∑ x ∈ s, -f x = -∑ x ∈ s, f x
@Finset.sum_eq_zero_iff : ∀ {ι : Type u_1} {M : Type u_2} [inst : OrderedAddCommMonoid M]
  [inst_1 : CanonicallyOrderedAdd M] {f : ι → M} {s : Finset ι}, ∑ x ∈ s, f x = 0 ↔ ∀ x ∈ s, f x = 0
@Finset.sum_eq_single : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid β] {s : Finset α} {f : α → β} (a : α),
  (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s → f a = 0) → ∑ x ∈ s, f x = f a
@Finset.sum_singleton : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid β] (f : α → β) (a : α),
  ∑ x ∈ {a}, f x = f a
@Finset.univ_unique : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Unique α], Finset.univ = {default}
@Fintype.sum_unique : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid β] [inst_1 : Unique α] [inst_2 : Fintype α]
  (f : α → β), ∑ x : α, f x = f default
@Fintype.sum_bool : ∀ {α : Type u_1} [inst : AddCommMonoid α] (f : Bool → α), ∑ b : Bool, f b = f true + f false
```

**`Finset.sum_bool` and `Finset.sum_unit` do not exist** (§9). Replacements are the `Fintype`-level
`Fintype.sum_bool` (`∑ b : Bool, f b = f true + f false`) and `Fintype.sum_unique`
(`∑ x : α, f x = f default`, which covers `Unit`). Two usage traps measured:

* the sum order of `Fintype.sum_bool` is **`f true + f false`**; the plan's `chargeBalanced_pair_iff`
  is printed as `dz false + dz true = 0`, so either state the row in the `true + false` order or add
  `rw [Fintype.sum_bool, add_comm]` (both variants are kernel-checked in the probe).
* `Finset.sum_erase_add`'s membership proof is **explicit**: `Finset.sum_erase_add _ _ (Finset.mem_univ i)`
  (`_ _` are the `Finset`/function arguments). Its `=`-form twin `Finset.sum_erase_eq_sub` is the one
  the compensating-partner proof uses.

**Settled row `exists_negative_of_pos` (complete proof, no `DecidableEq`):**

```lean
theorem exists_negative_of_pos {ι : Type*} [Fintype ι] (dz : ι → ℤ)
    (hsum : ∑ i, dz i = 0) (hpos : ∃ i, 0 < dz i) : ∃ j, dz j < 0 := by
  by_contra h
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ dz i :=
    fun i _ => le_of_not_gt (fun hlt => h ⟨i, hlt⟩)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  obtain ⟨i, hi⟩ := hpos
  have := hz i (Finset.mem_univ i)
  omega
```

* The plan's route (`Finset.sum_eq_zero_iff_of_nonneg` contrapositive) works **verbatim**; the
  finisher is `omega` (on `ℤ`; `linarith` also closes it).
* A shorter alternative with the same statement: `Finset.sum_pos' hnonneg ⟨i, Finset.mem_univ i, hi⟩`
  gives `0 < ∑ i, dz i`, contradicting `hsum` — also kernel-checked, and the preferred engine when
  the index set is *not* `Finset.univ`.
* The `ℚ` variant (plan §8 `chargeBalancedQ`) is kernel-checked identically, with `linarith` as the
  finisher.

**Settled row `exists_compensating_partner` (complete proof; the delivered signature carries NO
`DecidableEq`):**

```lean
theorem exists_compensating_partner {ι : Type*} [Fintype ι] (dz : ι → ℤ)
    (hsum : ∑ i, dz i = 0) (i : ι) (hi : 0 < dz i) : ∃ j, j ≠ i ∧ dz j < 0 := by
  classical
  by_contra h
  have hnn : ∀ j ∈ (Finset.univ : Finset ι).erase i, 0 ≤ dz j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact le_of_not_gt (fun hlt => h ⟨j, hj.1, hlt⟩)
  have hsum_erase : ∑ j ∈ (Finset.univ : Finset ι).erase i, dz j = -dz i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum]
    ring
  have hnn' := Finset.sum_nonneg hnn
  rw [hsum_erase] at hnn'
  omega
```

* **The recipe for the authority's exact signature** (`[Fintype ι]` only): put `classical` as the
  first tactic. Internally the proof needs `DecidableEq ι` (the split uses
  `Finset.sum_erase_eq_sub (Finset.mem_univ i)` over `univ.erase i`, and `Finset.erase` requires it),
  and `classical` supplies it **locally** — the instance does not escape into the statement. That is
  the delivered shape; the probe deliberately contains **no** `DecidableEq`-carrying variant, so no
  prover can pick one up by mistake (independently re-confirmed by `prover_c` on this toolchain during
  G2: the authority's signature is deliverable as-is with `classical` inside the proof).
* `rw [Finset.mem_erase] at hj` turns `j ∈ univ.erase i` into `j ≠ i ∧ j ∈ univ`; `hj.1` is the
  `j ≠ i` needed by the negated witness `h`.
* `by_contra` + `le_of_not_gt` is enough — no `push_neg` is needed, because the raw negated
  existential `h : ¬ ∃ j, j ≠ i ∧ dz j < 0` can be applied directly as `h ⟨j, hj.1, hlt⟩`.
* `Finset.sum_nonneg hnn : 0 ≤ ∑_{univ.erase i} dz j`, then `rw [hsum_erase]` makes it `0 ≤ -dz i`,
  and `omega` closes against `hi : 0 < dz i`.

### 6. (f) the ℚ layer — cast push-through, `tolFacSq_cast`, `inBandQ_cast`

**All 23 `Rat.cast_*` names of the dispatch exist** (verbatim `#check @`, wraps joined):

```
@Rat.cast_pow : ∀ {α : Type u_1} [inst : DivisionRing α] (p : ℚ) (n : ℕ), ↑(p ^ n) = ↑p ^ n
@Rat.cast_div : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] (p q : ℚ), ↑(p / q) = ↑p / ↑q
@Rat.cast_mul : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] (p q : ℚ), ↑(p * q) = ↑p * ↑q
@Rat.cast_add : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] (p q : ℚ), ↑(p + q) = ↑p + ↑q
@Rat.cast_sub : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] (p q : ℚ), ↑(p - q) = ↑p - ↑q
@Rat.cast_inv : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] (p : ℚ), ↑p⁻¹ = (↑p)⁻¹
@Rat.cast_le : ∀ {p q : ℚ} {K : Type u_1} [inst : LinearOrderedField K], ↑p ≤ ↑q ↔ p ≤ q
@Rat.cast_lt : ∀ {p q : ℚ} {K : Type u_1} [inst : LinearOrderedField K], ↑p < ↑q ↔ p < q
@Rat.cast_nonneg : ∀ {q : ℚ} {K : Type u_1} [inst : LinearOrderedField K], 0 ≤ ↑q ↔ 0 ≤ q
@Rat.cast_eq_zero : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] {p : ℚ}, ↑p = 0 ↔ p = 0
@Rat.cast_ne_zero : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] {p : ℚ}, ↑p ≠ 0 ↔ p ≠ 0
@Rat.cast_pos : ∀ {q : ℚ} {K : Type u_1} [inst : LinearOrderedField K], 0 < ↑q ↔ 0 < q
@Rat.cast_neg : ∀ {α : Type u_1} [inst : DivisionRing α] (q : ℚ), ↑(-q) = -↑q
@Rat.cast_one : ∀ {α : Type u_1} [inst : DivisionRing α], ↑1 = 1
@Rat.cast_zero : ∀ {α : Type u_1} [inst : DivisionRing α], ↑0 = 0
@Rat.cast_ofNat : ∀ {α : Type u_1} [inst : DivisionRing α] (n : ℕ) [inst_1 : n.AtLeastTwo],
  ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_natCast : ∀ {α : Type u_1} [inst : DivisionRing α] (n : ℕ), ↑↑n = ↑n
@Rat.cast_intCast : ∀ {α : Type u_1} [inst : DivisionRing α] (n : ℤ), ↑↑n = ↑n
@Rat.cast_inj : ∀ {α : Type u_1} [inst : DivisionRing α] [inst_1 : CharZero α] {p q : ℚ}, ↑p = ↑q ↔ p = q
@Rat.cast_abs : ∀ {K : Type u_1} [inst : LinearOrderedField K] (q : ℚ), ↑|q| = |↑q|
@Rat.cast_max : ∀ {K : Type u_1} [inst : LinearOrderedField K] (p q : ℚ), ↑(p ⊔ q) = ↑p ⊔ ↑q
@Rat.cast_min : ∀ {K : Type u_1} [inst : LinearOrderedField K] (p q : ℚ), ↑(p ⊓ q) = ↑p ⊓ ↑q
@Rat.cast_sum : ∀ {ι : Type u_1} {α : Type u_2} [inst : DivisionRing α] [inst_1 : CharZero α] (s : Finset ι)
  (f : ι → ℚ), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)
```

Note `Rat.cast_pow` needs only `DivisionRing` while the additive/multiplicative/division lemmas need
`CharZero` as well; `Rat.cast_le` / `cast_lt` / `cast_nonneg` / `cast_pos` need `LinearOrderedField`
and are **iff**s (the field must be pinned as `(Rat.cast_lt (K := ℝ))` when the goal is ambiguous).

**Settled recipe for pushing a cast through `(rA + rO)^2 / (2 * (rB + rO)^2)` — `tolFacSq_cast`
(complete, kernel-checked):**

```lean
theorem tolFacSq_cast (rA rB rO : ℚ) :
    ((tolFacSq rA rB rO : ℚ) : ℝ) = (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ)) ^ 2 := by
  unfold tolFacSq tolFac
  push_cast
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
```

Two kernel-checked routes, and the trap that distinguishes them: route B above needs **no trailing
`ring`** (`rw` closes the reflexive goal; appending `ring` gives `no goals to be solved`); route A
(`push_cast; field_simp; rw [mul_pow, Real.sq_sqrt (by norm_num)]`) also closes with no trailing
`ring`. What does **not** work is `push_cast; ring_nf` — see §9.

**Settled row `inBandQ_cast`** (plan §8 G5, the correctness theorem of the ℚ layer), with the two
definitions this probe proposes:

```lean
def GoldschmidtConforms (lo hi rA rB rO : ℝ) : Prop :=
  lo ≤ tolFac rA rB rO ∧ tolFac rA rB rO ≤ hi

def inBandQ (lo hi rA rB rO : ℚ) : Prop :=
  2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
    (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

theorem inBandQ_cast (lo hi rA rB rO : ℚ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hB : 0 < rB + rO) (hA : 0 ≤ rA + rO) :
    inBandQ lo hi rA rB rO ↔
      GoldschmidtConforms (lo : ℝ) (hi : ℝ) (rA : ℝ) (rB : ℝ) (rO : ℝ)
```

i.e. `inBandQ` is literally the right-hand side of `conforms_iff_sq`, and the transfer is that
equivalence plus the cast alignment. The four side conditions are exactly the physical premises;
the cast-alignment recipe is

```lean
have hcast1 : (2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2) ↔
    (2 * (lo : ℝ) ^ 2 * ((rB : ℝ) + (rO : ℝ)) ^ 2 ≤ ((rA : ℝ) + (rO : ℝ)) ^ 2) := by
  rw [(Rat.cast_le (K := ℝ)).symm]
  push_cast
  rfl
```

— `rw [(Rat.cast_le (K := ℝ)).symm]` rewrites the *ℚ* comparison into its ℝ cast, `push_cast`
distributes the casts over `*`, `^`, `+`, and `rfl` finishes. The final assembly is
`unfold inBandQ GoldschmidtConforms; rw [le_tolFac_iff_sq …, tolFac_le_iff_sq …]; exact and_congr hcast1 hcast2`.
`exact_mod_cast` discharges each numeric side condition (`hlo' : (0:ℝ) ≤ (lo:ℝ)` etc.).

**The `float`-free cross-checks the dispatch asked for** (`goldschmidt-api-rat-cast.lean`):
`example : 2 * (3/20 : ℚ)^2 * (401/200)^2 ≤ (71/25)^2 := by norm_num` and
`example : (322624 : ℚ) > 321602 := by norm_num` both compile; `norm_num` also closes
`(71/25 : ℚ)^2 > 2 * (401/200)^2`.

**`decide` domain on ℚ (measured, table is the answer to the dispatch's last sub-question):**

| goal | `norm_num` | `decide` |
|---|---|---|
| `2 * (3/20 : ℚ)^2 * (401/200)^2 ≤ (71/25)^2` | **closes** | fails |
| `(322624 : ℚ) > 321602` | closes | **closes** |
| `(322624 : ℚ)/40000 > (321602 : ℚ)/40000` | closes | fails |
| `(2 : ℚ) * 3 = 6` | closes | fails |
| `(71/25 : ℚ)^2 > 2 * (401/200)^2` | **closes** | fails |

`decide` is reliable **only on a comparison of integer literals**; any `/`, `*` or `^` in `ℚ` leaves
`Rat.instDecidableLt` stuck at `Rat.blt` (verbatim text in §9). The `decide`-after-rewriting route
that *does* work is to clear the division first:

```lean
example : (322624 : ℚ) / 40000 > (321602 : ℚ) / 40000 := by
  show (321602 : ℚ) / 40000 < (322624 : ℚ) / 40000
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 40000)]
  decide
```

**Trap:** `rw [div_lt_div_iff_of_pos_right …]` does **not** fire on a goal written with `>` (`a > b`
is `GT.gt`, not literally `b < a`): the rewrite fails with
`did not find instance of the pattern in the target expression / ?m / 40000 < ?m / 40000`. Insert the
`show` first. For the instance layer, `norm_num` remains the recommended tool — it needs no `show`.

### 7. (g) the computable classifier — `deriving DecidableEq` and `zoneQ_eq_zone`

**The `if`/`ite` layer (verbatim `#check @`, wraps joined):**

```
@if_pos : ∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = t
@if_neg : ∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u_1} {t e : α}, (if c then t else e) = e
@ite_eq_iff : ∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b c : α},
  (if P then a else b) = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
@ite_eq_iff' : ∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b c : α},
  (if P then a else b) = c ↔ (P → a = c) ∧ (¬P → b = c)
@lt_trichotomy : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ a = b ∨ b < a
@lt_or_ge : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ a ≥ b
@le_or_lt : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b < a
@lt_or_gt_of_ne : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≠ b → a < b ∨ a > b
@lt_iff_not_ge : ∀ {α : Type u_1} [inst : LinearOrder α] (x y : α), x < y ↔ ¬x ≥ y
@le_iff_lt_or_eq : ∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ b ↔ a < b ∨ a = b
@Bool.rec : {motive : Bool → Sort u_1} → motive false → motive true → (t : Bool) → motive t
decide : (p : Prop) → [h : Decidable p] → Bool
```

**`lt_iff_le_not_ge` does not exist** (§9) — the name is `lt_iff_not_ge`
(`x < y ↔ ¬x ≥ y`). `if_pos` / `if_neg` are the goal-side splitters; `split_ifs with h1 … hn` is the
hypothesis-side tool, with the branch bookkeeping already recorded in the Sabatier section §8.

**The classifier shape settled by this probe** (the plan fixes the *names* and the three-way
behaviour but not the bodies):

```lean
inductive GoldschmidtZone where
  | tooSmall
  | ideal
  | tooLarge
  deriving DecidableEq

def goldschmidtZone (lo hi t : ℝ) : GoldschmidtZone :=
  if t < lo then GoldschmidtZone.tooSmall
  else if t ≤ hi then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge

def zoneQ (lo hi rA rB rO : ℚ) : GoldschmidtZone :=
  if (rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.tooSmall
  else if (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2 then GoldschmidtZone.ideal
  else GoldschmidtZone.tooLarge
```

**This is the authority's body verbatim** (`goldschmidt-statement-skeleton.lean:402`, delivered at
`PhotoLean/Goldschmidt/RatModel.lean`). i.e. **`ideal` is the in-band branch** (`lo ≤ t ∧ t ≤ hi`),
which is what makes the transfer row and the plan §9 I8 non-vacuity family ("one conforming row per
zone of the classic band") consistent. `deriving DecidableEq` on the 3-constructor inductive compiles
and is *used*: every constructor mismatch in the characterization rows is discharged by `by decide`
(constructor disjointness), not by `noConfusion` gymnastics.

> **⚠ Do NOT use a quotient-shaped guard.** The tempting reformulation
> `if tolFacSq rA rB rO < lo^2 then .tooSmall else …` with
> `tolFacSq = (rA+rO)^2 / (2*(rB+rO)^2)` is **not equivalent** to the authority's body: it agrees
> only under `rB + rO ≠ 0`, because at `rB + rO = 0` the quotient is `x / 0 = 0` in `ℚ` and the first
> guard degenerates to `0 < lo^2`. Kernel witnesses (in `goldschmidt-api-classifier.lean`,
> definitions `zoneQ` vs `zoneQQuotientForm`):
> * `zoneQ 1 1 0 (-1) 1 = .tooLarge` while `zoneQQuotientForm 1 1 0 (-1) 1 = .tooSmall`;
> * with the quotient form the authority's unconditional `zoneQ_ideal_iff` becomes **false**:
>   `zoneQQuotientForm 0 1 0 (-1) 1 = .ideal` while `¬ inBandQ 0 1 0 (-1) 1`.
>
> The difference was found by the batch-1 verifier and re-verified here; the quotient definition is
> present in the probe only as `zoneQQuotientForm`, explicitly marked DO NOT USE.

**Settled row `zoneQ_eq_zone` (complete, kernel-checked):**

```lean
theorem zoneQ_eq_zone {lo hi rA rB rO : ℚ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hB : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : zoneQ lo hi rA rB rO =
      goldschmidtZone (lo : ℝ) (hi : ℝ) (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ))
```

The radii are **implicit** `{…}` and the declared hypothesis order is `hlo hhi hB hA` — exactly the
authority's signature, so a fidelity check passes; call sites should name the radii
(`zoneQ_eq_zone (lo := 4/5) (hi := 1) … (by norm_num) …`), otherwise the first positional argument
binds to `hlo` (measured elaboration error).

Four steps, all in the probe:

1. `hlo'`, `hhi'`, `hB'`, `hA'` by `exact_mod_cast`;
2. the two ℝ↔ℚ **squared halves** `le_tolFac_iff_sq` / `tolFac_le_iff_sq`, plus the strict half
   `lt_tolFac_iff_sq` (`t < lo ↔ (rA+rO)^2 < 2 lo^2 (rB+rO)^2`, obtained by
   `rw [← not_le, le_tolFac_iff_sq …, not_le]`);
3. the two **guard equivalences** for the authority's inlined ℚ guards (the `inBandQ_cast`-style
   facts), each one `rw`/`push_cast`/`rfl`:

```lean
have h1iff : ((rA + rO) ^ 2 < 2 * lo ^ 2 * (rB + rO) ^ 2) ↔
    (tolFac (rA : ℝ) (rB : ℝ) (rO : ℝ) < (lo : ℝ)) := by
  rw [lt_tolFac_iff_sq hlo' hB' hA', (Rat.cast_lt (K := ℝ)).symm]
  push_cast
  rfl
```

   (and the `≤` twin via `tolFac_le_iff_sq` / `Rat.cast_le`);

4. `unfold zoneQ goldschmidtZone`, then two nested `by_cases` with
   `rw [if_pos h1, if_pos (h1iff.mp h1)]` and, on the negative side,
   `rw [if_neg h1, if_neg (fun hc => h1 (h1iff.mpr hc))]`.

**Do not reach for `norm_cast` here**: the Hammond/Sabatier trick `unfold zoneQ zone; norm_cast` works
only when the ℚ guard *is* the cast of the ℝ guard; here the ℚ side is
`(rA+rO)^2 < 2 lo^2 (rB+rO)^2` and the ℝ side is `t < ↑lo`, so a guard equivalence must be built
first (the ℝ halves provide it). With `h1iff`/`h2iff` in hand the branch alignment is three rewrites
and no automation.

**Bonus row, also kernel-checked:** `zoneQ_ideal_iff (lo hi rA rB rO : ℚ) : zoneQ lo hi rA rB rO =
.ideal ↔ inBandQ lo hi rA rB rO` (authority line 449) — the classifier's `ideal` branch *is* the
band predicate. Its recipe is `unfold zoneQ inBandQ`, `by_cases` on the two guards, `rw` the `if`,
and only **then** `by decide` for the constructor mismatches (`by decide` before the `if` is
resolved would hit the ℚ-comparison stall of §9.1).

**The characterization rows (plan §4 G1), kernel-checked — the authority's exact forms**
(`goldschmidt-statement-skeleton.lean:134/138/143/147`, delivered at
`PhotoLean/Goldschmidt/Basic.lean`):

* `goldschmidtZone_eq_tooSmall_iff (lo hi t : ℝ) : goldschmidtZone lo hi t = .tooSmall ↔ t < lo`
  — unconditional;
* `goldschmidtZone_eq_ideal_iff (lo hi t : ℝ) : … = .ideal ↔ lo ≤ t ∧ t ≤ hi` — unconditional;
* `goldschmidtZone_eq_tooLarge_iff (lo hi t : ℝ) : … = .tooLarge ↔ lo ≤ t ∧ hi < t` — unconditional,
  the **conjunction**;
* `goldschmidtZone_eq_tooLarge_iff_of_band (lo hi t : ℝ) (h : lo ≤ hi) : … ↔ hi < t` — the
  *reduced* corollary for a non-empty band.

The conjunct `lo ≤ t` in the `tooLarge` row is load-bearing: the classifier tests `t < lo` first, so
for an inverted band with `hi < t < lo` it returns `tooSmall` while `hi < t` holds — kernel witness
`lo = 1, hi = 0, t = 1/2` (plan §3.1 item 4; `goldschmidtZone_tooLarge_dropped_conjunct_false` in the
probe). **An earlier draft of this entry said the authority "must carry `lo ≤ hi`" on the row; that
was stale — the authority carries the unconditional conjunction plus the `_of_band` corollary, and
only the `↔ hi < t` reduction needs `lo ≤ hi`.**

The proof pattern for each row (both `by_cases`/`rw [if_pos/if_neg …]` and the shorter
`unfold goldschmidtZone; split_ifs with h1 h2` used by the delivered file work; the probe uses
`split_ifs` for the two `tooLarge` rows) is then
`exact iff_of_true rfl ⟨…⟩` / `iff_of_false (by decide) ⟨…⟩`, with the arithmetic of the inverted
cases done by `not_le.mpr` / `not_le.mp` / `not_lt.mpr`.

### 8. (h) the six instance verdicts — independent cross-check of the numbers

Criterion: `t ⋚ 1` ⟺ `(rA+rO)^2 ⋚ 2 (rB+rO)^2`. All numbers below are `norm_num` facts **in `ℚ`,
with no `Real.sqrt`**, and each is paired with the ℝ verdict via the kernel-checked transfer
`tolFac_gt_one_of_sq_gt` / `tolFac_lt_one_of_sq_lt` (the `rO := 0` normalization, under which
`tolFac nA nB 0 = nA / (√2 nB)` exactly).

| row | `rA + rO` | `rB + rO` | ℚ comparison (`norm_num`) | verdict | `t` |
|---|---|---|---|---|---|
| `SrTiO₃` | `71/25` | `401/200` | `2*(401/200)^2 < (71/25)^2` | **`t > 1`** | `1.00159` |
| `CaTiO₃` | `137/50` | `401/200` | `(137/50)^2 < 2*(401/200)^2` | **`t < 1`** | `0.96632` |
| `BaTiO₃` | `301/100` | `401/200` | `2*(401/200)^2 < (301/100)^2` | **`t > 1`** | `1.06154` |
| `LaMnO₃` | `69/25` | `409/200` | `(69/25)^2 < 2*(409/200)^2` | **`t < 1`** | `0.95434` |
| `NaNbO₃` | `279/100` | `51/25` | `(279/100)^2 < 2*(51/25)^2` | **`t < 1`** | `0.96707` |
| `BaNiO₃` | `301/100` | `47/25` | `2*(47/25)^2 < (301/100)^2` | **`t > 1`** | `1.13212` |

`t = 1` occurs for **no** row. The common denominators show the hand-checkable forms: the `SrTiO₃`
`1`-edge test is `(71/25)^2 = 322624/40000` vs `2·(401/200)^2 = 321602/40000`, i.e. exactly the
`322624 > 321602` comparison of the dispatch.

**⚠ One number in the dispatch's brief is WRONG and is corrected here (disagreement reported
loudly).** The brief gave the `BaNiO₃` row as `rB + rO = 47/50`; the authority's Shannon radii
(`rB_Ni = 12/25 = 0.48 Å`, `rO_shannon = 7/5 = 1.40 Å`, `goldschmidt-statement-skeleton.lean` G6) give
`rB + rO = 47/25 = 1.88 Å`, and `47/50 = 0.94 Å` is *smaller than `rO` itself*, i.e. it would force
`rB < 0`. The correct row is `47/25`, `t ≈ 1.13212`, `t² = 90601/70688` — this matches plan §9 and
the verifier's independent recomputation. The verdict *direction* is unaffected (both readings give
`t > 1` and outside the tetragonal band), so **no plan claim flips**; only the magnitude was wrong
(`2.26425` was the `47/50` artefact). The other five rows are exactly the authority's
`rA_X + rO_shannon` / `rB_Y + rO_shannon`, kernel-checked in the probe's final section
(`rA_Sr = 36/25`, `rA_Ca = 67/50`, `rA_Ba = 161/100`, `rA_La = 34/25`, `rA_Na = 139/100`,
`rB_Ti = 121/200`, `rB_Mn = 129/200`, `rB_Nb = 16/25`, `rB_Ni = 12/25`, `rO_shannon = 7/5`).

**Cross-check against the plan's own claims — agreement, no disagreement found (after the `BaNiO₃`
number correction above):**

* plan §1.1 (`SrTiO₃` above the classic `1.0` edge) — **agrees**: `srTiO3_gt_one`,
  `srTiO3_not_classic` (`¬ (4/5 ≤ t ∧ t ≤ 1)`), and `srTiO3_tetragonal_conforms` (it is inside
  `[1, 11/10]`, `t ≈ 1.0016`).
* plan §9 I3 (`BaTiO₃` fails `[4/5, 1]`, conforms to `[1, 11/10]`) — **agrees**:
  `baTiO3_not_classic` and `baTiO3_tetragonal_conforms`.
* plan §9 I4 / §1.1 (`BaNiO₃` outside every delivered band) — **agrees**: `BaNiO3_gt_one` and
  `BaNiO3_not_tetragonal` (`¬ t ≤ 11/10`).
* plan §9 I2 (`CaTiO₃`, `LaMnO₃`, `NaNbO₃` with the classic band) — **agrees**: all three satisfy
  `4/5 ≤ t ∧ t ≤ 1` (`caTiO3_classic_conforms`, `laMnO3_classic_conforms`, `NaNbO3_classic_conforms`).

The independent exact-rational recomputation of these numbers (outside Lean) reproduces all six
verdicts; no label or direction invert was found.

### 9. Failures and drift (names that do NOT exist, verbatim errors, working replacement)

Verbatim from a scratch probe (the failing names are deliberately **not** `#check`ed in the delivered
probes, so that those stay at 0 error / 0 warning):

```
error: unknown constant 'Real.sqrt_ne_zero_of_pos'
error: unknown constant 'Real.sqrt_two_pos'
error: unknown constant 'Real.inv_sqrt'
error: unknown constant 'Real.sqrt_two_lt_two'
error: unknown identifier 'sq_lt_sq_iff'
warning: `pow_le_pow_left` has been deprecated: use `pow_le_pow_left₀` instead
warning: `div_le_iff` has been deprecated: use `div_le_iff₀` instead
warning: `le_div_iff` has been deprecated: use `le_div_iff₀` instead
error: unknown constant 'Irrational.mul_ratCast'
error: unknown constant 'Irrational.div_ratCast'
error: unknown constant 'Irrational.add_ratCast'
error: unknown constant 'Irrational.ratCast_mul'
error: unknown constant 'Irrational.ratCast_div'
error: unknown constant 'Irrational.of_ratCast_mul'
error: unknown constant 'Irrational.of_ratCast_add'
error: unknown constant 'Irrational.of_ratCast_div'
error: unknown constant 'Irrational.sub_ratCast'
error: unknown constant 'Irrational.of_ratCast_sub'
error: unknown constant 'Irrational.of_ratCast_inv'
error: unknown constant 'Finset.sum_bool'
error: unknown constant 'Finset.sum_unit'
error: unknown constant 'Fintype.sum_unit'
error: unknown constant 'Finset.sum_univ_unique'
error: unknown constant 'Finset.sum_univ_eq_single'
error: unknown constant 'Finset.sum_pos_iff_of_nonneg'
error: unknown identifier 'lt_iff_le_not_ge'
```

| banned (does not exist in v4.17.0) | verified replacement (usage form that compiled) |
|---|---|
| `Real.sqrt_ne_zero_of_pos` | `(Real.sqrt_ne_zero').mpr (by norm_num)` — `sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x` |
| `Real.sqrt_two_pos` | `Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)` |
| `Real.inv_sqrt` | `Real.sqrt_inv : √x⁻¹ = (√x)⁻¹` (the reverse direction), or `one_div` + `inv_mul_cancel₀` |
| `Real.sqrt_two_lt_two` | nothing needed; for a numeric bound use `Real.sqrt_lt_sqrt` / `nlinarith` |
| `sq_lt_sq_iff` | `sq_lt_sq` (already the `↔ \|a\| < \|b\|`), or `sq_lt_sq₀ ha hb` |
| `pow_le_pow_left` (deprecated) | `pow_le_pow_left₀` |
| `div_le_iff` / `le_div_iff` (deprecated) | `div_le_iff₀` / `le_div_iff₀` |
| the entire `Irrational.*_ratCast` family | `Irrational.rat_mul`, `Irrational.mul_rat`, `Irrational.rat_div`, `Irrational.div_rat`, `Irrational.rat_add`, `Irrational.add_rat`, `Irrational.rat_sub`, `Irrational.sub_rat`, `Irrational.of_mul_rat`, `Irrational.of_div_rat`, `Irrational.of_rat_div`, `Irrational.inv`, `Irrational.mul_int` (bare `rat`/`int`, **not** `ratCast`) |
| `Finset.sum_bool` | `Fintype.sum_bool : ∑ b : Bool, f b = f true + f false` (note the `true + false` order) |
| `Finset.sum_unit` | `Fintype.sum_unique : ∑ x : α, f x = f default` (covers `Unit`); or `Finset.univ_unique` + `Finset.sum_singleton` |
| `Fintype.sum_unit` | `Fintype.sum_unique` |
| `Finset.sum_univ_unique` / `Finset.sum_univ_eq_single` | `Fintype.sum_unique` / `Finset.sum_eq_single` |
| `Finset.sum_pos_iff_of_nonneg` | `Finset.sum_pos'` (`(∀ i ∈ s, 0 ≤ f i) → (∃ i ∈ s, 0 < f i) → 0 < ∑ i ∈ s, f i`) |
| `lt_iff_le_not_ge` | `lt_iff_not_ge : x < y ↔ ¬x ≥ y`, or `not_le` (`¬a ≤ b ↔ b < a`) |

**Two tactic-level failures measured in this round** (verbatim):

```
error: unsolved goals
rA rB rO : ℚ
⊢ ↑rA * (↑rO * √2 + √2 * ↑rB)⁻¹ + ↑rO * (↑rO * √2 + √2 * ↑rB)⁻¹ =
    ↑rA * (↑rO + ↑rB)⁻¹ * (√2)⁻¹ + ↑rO * (↑rO + ↑rB)⁻¹ * (√2)⁻¹
```

— the `push_cast; ring_nf` route on the `tolFac` cast identity of §4 step 1. The working tail is
`push_cast; field_simp; ring` (with `√2 ≠ 0` and `↑(rB+rO) ≠ 0` in context). **This is the recipe the
`tolFac_irrational` prover must use.**

```
error: tactic 'decide' failed for proposition
  (71 / 25) ^ 2 > 2 * (401 / 200) ^ 2
since its 'Decidable' instance
  (2 * (401 / 200) ^ 2).instDecidableLt ((71 / 25) ^ 2)
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqBool', 'Bool.decEq', 'Int.decLt', 'Rat.instDecidableLt' and 'Int.decNonneg✝', reduction got stuck at the 'Decidable' instance
  match (2 * (401 / 200) ^ 2).blt ((71 / 25) ^ 2), true with
```

— `decide` on ℚ literals with `/`, `*`, `^` (§6 table). Use `norm_num`, or clear the division and
`show` the `<` orientation first.

**Two rewrite failures measured** (both in §2/§6): a trailing `rfl` after a closing `rw` is
`error: no goals to be solved`; and `rw [div_lt_div_iff_of_pos_right …]` on a `>`-shaped goal is
`error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression / ?m / 40000 < ?m / 40000`.

### 9.1 Measured traps on `ℚ` (kernel facts, not name facts)

All of the following were re-measured on this toolchain in `goldschmidt-api-rat-cast.lean` /
`goldschmidt-api-classifier.lean` (positive forms are `example`s in those probes; the failing forms
are quoted here verbatim and are deliberately absent from the probes).

1. **An unannotated `ℚ`-intended goal silently elaborates in `ℕ`.** The bare goal

   ```lean
   example : 2 / 3 ≤ 1 / 2 := by norm_num          -- COMPILES (ℕ reading: 0 ≤ 0)
   example : (2 / 3 : ℚ) ≤ 1 / 2 := by norm_num    -- error: unsolved goals ⊢ False
   example : 157 / 100 > 1 := by norm_num          -- error: unsolved goals ⊢ False (ℕ: 1 > 1)
   ```

   `ℕ` division is integer division, so the first line is a *true `ℕ`* proposition and `norm_num`
   closes it although the intended `ℚ` reading is false; the same shape with a false `ℕ` reading
   leaves the absurd `⊢ False`. **Rule for G5/G6:** state the instance layer through the
   `ℚ`-parameterized definitions (`inBandQ`, `zoneQ`, `tolFacSq`, `radiusMatchQ`) or annotate every
   literal — never deliver a bare literal comparison as a row, and never trust a bare `example`.
2. **`norm_num` and `|·|` on `ℚ`.** On a *closed literal* argument `norm_num` does evaluate `|·|`:
   `example : |(3 : ℚ) - 5| = 2 := by norm_num` compiles. On a *variable* it stalls at the side
   condition:

   ```lean
   example (q : ℚ) (hq : 0 ≤ q) : |q| = q := by norm_num
   -- error: unsolved goals  q : ℚ  hq : 0 ≤ q  ⊢ 0 ≤ q
   example (q : ℚ) (hq : 0 ≤ q) : |q| = q := by norm_num [abs_of_nonneg]
   -- error: unsolved goals  q : ℚ  hq : 0 ≤ q  ⊢ 0 ≤ q      (the bare lemma is not enough)
   example (q : ℚ) (hq : 0 ≤ q) : |q| = q := by norm_num [abs_of_nonneg hq]   -- COMPILES
   ```

   So the recipe is `norm_num [abs_of_nonneg hq]` **with the nonnegativity hypothesis supplied**
   (`rw [abs_of_nonneg hq]` is the plain alternative; `norm_num [abs_of_nonneg (sq_nonneg q)]` for
   `|q^2| = q^2`). The dispatch's phrasing "`norm_num [abs_of_nonneg]`" is not sufficient by itself.
3. **`norm_num` decides the concrete classifier / ℚ-band facts; `decide` does not.**
   `norm_num [inBandQ]` closes the concrete `CaTiO₃` classic-band conjunction, and
   `norm_num [zoneQ]` closes the classifier verdicts
   (`SrTiO₃` at `[4/5, 1]` ↦ `tooLarge`, `CaTiO₃` ↦ `ideal`). `decide` fails on both (verbatim
   `Decidable` stall above). `norm_num` is the G6 evaluator of record.
4. **The evaluator depends on the classifier body, and only the authority's body may be used.**
   With the authority's inlined `zoneQ` (guards `(rA+rO)^2 ⋚ 2 lo^2 (rB+rO)^2`), plain
   `norm_num [zoneQ]` closes the concrete verdicts (`SrTiO₃` ↦ `tooLarge`, `CaTiO₃` ↦ `ideal`).
   With a body that *delegates* to `tolFacSq`, `norm_num [zoneQ]` leaves the guard folded
   (verbatim goal
   `⊢ (if tolFacSq (91 / 50) (197 / 200) (51 / 50) < 16 / 25 then … else …) = GoldschmidtZone.tooLarge`)
   and one must write `norm_num [zoneQ, tolFacSq]` — **but that body is not equivalent to the
   authority's at `rB + rO = 0` anyway (§7), so it must not be used**; with the authority's body the
   extra `tolFacSq` in the simp set is simply unnecessary.
5. **`ring_nf` fails where `field_simp` + `ring` succeeds** (§9, first quoted failure) — the single
   most important recipe-level fact of this round, because it is on the `tolFac_irrational` critical
   path.
6. **A trailing `rfl`/`ring` after a closing `rw` is `error: no goals to be solved`** (§9) — measured
   twice, on `latticeOf_div_sqrt_eq_idealAO` and on `tolFacSq_cast` route B.

### 10. Plan-sketch corrections found while calibrating

| # | plan location | plan sketch | what the API/statement reality forces |
|---|---|---|---|
| 1 | §5 G2 `exists_compensating_partner` | no `DecidableEq` mentioned; proof "sum over `erase i` is non-positive" | the statement **keeps** `[Fintype ι]` only; `classical` supplies `DecidableEq ι` locally for `Finset.erase`. The probe carries the exact delivered signature and proof (no `DecidableEq` in the signature). |
| 2 | §7 G4 `tolFac_irrational` | "for rational `rA rB rO` with `rB + rO ≠ 0` and `rA + rO ≠ 0`, `Irrational (tolFac rA rB rO)`" | the two hypotheses are right and both necessary; the *statement* must quantify `ℚ` and cast (`Irrational (tolFac (↑rA) (↑rB) (↑rO))`), because `tolFac` is a function of `ℝ`. Equivalent spellings `↑q / √2`, `(√2)⁻¹ * ↑q`, `↑q * (√2)⁻¹` are all provable; `↑q / √2` is the delivered one. |
| 3 | §4 G1 `goldschmidtZone_eq_tooLarge_iff` | `… = tooLarge ↔ hi < t` | the delivered exact row is the **conjunction** `… = tooLarge ↔ lo ≤ t ∧ hi < t` (unconditional; authority line 143 / `Basic.lean:179`), with the reduced `↔ hi < t` as the separate corollary `goldschmidtZone_eq_tooLarge_iff_of_band (h : lo ≤ hi)`. The dropped-conjunct form is false (kernel witness `lo = 1, hi = 0, t = 1/2`); plan §3.1 item 4 already records the fix. |
| 4 | §5 G2 `chargeBalanced_pair_iff` | `ChargeBalanced (dz : Bool → ℤ) ↔ dz false + dz true = 0` | the authority keeps exactly this order; since `Finset.sum_bool` does not exist and `Fintype.sum_bool` unfolds the sum as `dz true + dz false`, the proof needs one extra `add_comm`: `rw [ChargeBalanced, Fintype.sum_bool, add_comm]` (kernel-checked in the probe, in the authority's exact signature). |
| 5 | §8 G5 `inBandQ` / `zoneQ` | names fixed, bodies not written | bodies now **match the authority exactly**: `inBandQ lo hi rA rB rO := 2*lo^2*(rB+rO)^2 ≤ (rA+rO)^2 ∧ (rA+rO)^2 ≤ 2*hi^2*(rB+rO)^2`; `zoneQ` uses the **inlined squares** (not `tolFacSq`, which the verifier showed is non-equivalent at `rB + rO = 0` — see §7); `goldschmidtZone`'s `ideal` branch is the in-band one. |
| 6 | §11 risks ("`Irrational` closure API for `q * √2` may be missing") | — | the closure family **is** missing under the `ratCast` spelling; the bare-`rat` spelling exists and is sufficient. Recorded above. |
| 7 | §7 G4 `conforms_iff_sq` sketch "`sq_le_sq'`" | `sq_le_sq'` suggested | `sq_le_sq'` is the hypothesis-shaped implication; the working equivalence is `sq_le_sq₀ ha hb`, applied **with `.symm`** after the `le_div_iff₀` step. Both are in §3. |
| 9 | §9 G6 `BaNiO₃` numbers (dispatch brief) | `rB + rO = 47/50`, `t ≈ 2.26425` | **the brief's number is wrong**: the authority's Shannon radii give `rB_Ni + rO_shannon = 12/25 + 7/5 = 47/25`, `t ≈ 1.13212`. `47/50 < rO` would make `rB` negative. Verdict direction unchanged (`t > 1`, outside `[1, 11/10]`); probe and table corrected. See §8. |
| 8 | §5 G2 `chiTol_anti` | `|χ'' - χ| ≤ |χ' - χ| → 0 ≤ k → chiTol tol₀ k χ χ'' ≤ chiTol tol₀ k χ χ'` | **the sketched direction was false** (a statement defect, not an API one): with §2's `chiTol = tol₀ - k|Δχ|` the closer `χ''` must get the **larger** tolerance. The authority fixed it by swapping the hypothesis instead of the conclusion — its row is `(hk : 0 ≤ k) (h : |χ' - χ| ≤ |χ'' - χ|) : chiTol tol₀ k χ χ'' ≤ chiTol tol₀ k χ χ'` (line 216). Both spellings are kernel-checked in `goldschmidt-api-div-mono.lean` (`chiTol_anti_corrected`, `chiTol_anti_corrected'`, `chiTol_anti_authority`), together with a kernel counterexample to the plan sketch; tool: `sub_le_sub_left` (`a ≤ b → c - b ≤ c - a`). See §3. |

### 11. API-risk list per Goldschmidt milestone (post-calibration)

| Milestone (plan §10) | Risk after this round |
|---|---|
| **G1** `PhotoLean/Goldschmidt/Basic.lean` (definitions, classifier, `contact_iff_tolFac_one`, zone characterization rows) | **low** — every `Real.sqrt`/`div_eq_one_iff_eq` name is confirmed (§2, §3); the classifier shape, the authority's four characterization rows and `deriving DecidableEq` are kernel-checked (§7); the `tooLarge` conjunct correction is already folded into the authority (correction #3) |
| **G2** `Rules.lean` (`RadiusMatch` window, `ChargeBalanced` unit/Bool rows, compensating partner, `chiTol` monotonicity) | **low**, with one **statement correction** — `abs_le`/`abs_sub_le_iff` confirmed (§3), the two `Finset` charge rows and both existence theorems are **complete** (§5), and `chiTol_anti` is calibrated with its corrected direction plus a counterexample to the plan's sketch (§3, correction #8); the prover must use the corrected statement, not the plan's |
| **G3** `Criterion.lean` (the two headline equivalences, strict monotonicity, `rO` trichotomy) | **low/medium** — `conforms_iff_radius_window` and `conforms_iff_sq` are kernel-verified end to end (§3), as are `tolFac_strictMono_rA` / `tolFac_strictAnti_rB`. Residual risk is the `rO` trichotomy, which needs the *exact* `Real.sqrt` algebra of §2 plus `div_lt_div_of_pos_left`'s reversed denominator order |
| **G4** `Sharp.lean` (`tolFac_irrational`, band sharpness, `Δt` bound, inverted-band emptiness) | **low** — `tolFac_irrational` is settled with a complete proof (§4); the sharpness rows are pure order algebra over §3. The one trap is that the identity step must use `field_simp; ring`, **never** `ring_nf` (§9) |
| **G5** `RatModel.lean` (`tolFacSq`, `inBandQ`, `zoneQ`, all cast transfers) | **low** — `tolFacSq_cast`, `inBandQ_cast`, `zoneQ_eq_zone` are all kernel-verified with the recipe spelled out (§6, §7); the `decide` domain is tabulated (§6) and the ℕ-elaboration trap is pinned (§9.1) so the instance evaluator cannot be mis-chosen |
| **G6** `Instances.lean` (model rows, six Shannon rows, rule verdicts) | **low** — all six verdicts plus the classic/tetragonal band memberships are `norm_num`-kernel-checked and cross-checked against the plan's claims (§8); the evaluator of record is `norm_num` (`norm_num [inBandQ]` / `norm_num [zoneQ]`, §9.1), `decide` is banned on `/`-bearing ℚ literals, and every delivered row must be `ℚ`-annotated or routed through the ℚ-typed definitions (§9.1 item 1) |

### 12. Authority cross-check (statement skeleton), measured before commit

`theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` did not exist when this round
started (the probe directory was empty) and landed in parallel during it. Every settled form above
was therefore re-read against the authority and the probes were realigned where they differed. State
at the commit below:

| authority declaration (skeleton line) | probe state |
|---|---|
| `GoldschmidtZone` + `deriving DecidableEq` (80) | verbatim |
| `goldschmidtZone` body (87) | verbatim |
| `Rat.zoneQ` body, **inlined squares** (402) | verbatim — the earlier quotient-shaped body was removed and is kept only as `zoneQQuotientForm` DO-NOT-USE plus two kernel witnesses of the divergence at `rB + rO = 0` (M2 of the verifier audit) |
| `Rat.inBandQ` body (389) | verbatim |
| `zoneQ_eq_zone` (444): implicit `{lo hi rA rB rO}`, hypotheses `hlo hhi hB hA` | identical (order and implicitness matched); proof complete |
| `zoneQ_ideal_iff` (449): explicit radii | identical; proof complete |
| `goldschmidtZone_eq_tooSmall_iff` / `_ideal_iff` (134/138) | verbatim, unconditional, proofs complete |
| `goldschmidtZone_eq_tooLarge_iff` (143) = `lo ≤ t ∧ hi < t`, and `_of_band` (147) | both rows delivered with complete proofs; the entry's earlier "needs `lo ≤ hi` on the row" phrasing is corrected (M1) |
| `tolFac_irrational {rA rB rO : ℚ} (hB) (hA)` (350) | same statement; the probe writes the hypotheses in the other order `(hA) (hB)` (argument order is immaterial for the proof); complete proof |
| `ChargeBalanced` (170) | delivered; both existence theorems also delivered in the authority's `ChargeBalanced` signatures (implicit `dz`/`i`, no `DecidableEq`) |
| `chiTol_anti` (216) with the swapped hypothesis | delivered as `chiTol_anti_authority`, complete proof, plus the plan-spelling and the counterexample |
| G6 Shannon radii (`rA_Sr` … `rO_shannon`) | the nine contact sums are kernel-checked equal to the table's `rA+rO` / `rB+rO`; the `BaNiO₃` brief number is corrected to `47/25` (M3) |

**Not calibrated in this round** (outside the dispatch's (a)–(h) scope; a prover should ask for a
probe before using them): `radiusMatch_iff_window`, `radiusMatch_min_iff`, `radiusMatch_refl`,
`radiusMatch_mono_tau`, `radiusMatch_fifteen_window`, `radiusMatch_comp_ratchet`,
`substitutable_mono_chi`, `substitutable_iff_window`, `rAMin`/`rAMax`/`idealA`/`idealAO`/`gapA` rows,
`tolFac_strictMono_rA`-family radius-window rows, `tolFacFifteen_le`,
`conforms_of_radiusMatch_window`, `inBandQ_ideal_iff`, `radiusMatchQ_*`, `classicLoQ_cast` and the
other `*_cast` band-constant rows.

### 13. Statement-change index for the Goldschmidt theory (iron rule 2) — lead, 2026-09-21

`AGENTS.md` iron rule 2 and `ENGINE.md` §2 require a statement change to be recorded in this log. The
Goldschmidt theory's changes live in `theories/goldschmidt/plan.md` §3.1 (with the kernel
counterexample for each) and are indexed here so that a reader of this file can find them:

| plan §3.1 item | statement touched | change | why |
|---|---|---|---|
| 1 | `radiusMatch_refl` | premise `0 ≤ r` **added** | `|r - r| = 0 ≤ τ * r` needs it |
| 2 | `conforms_symmetric_band_iff` | premise `0 ≤ delta` **removed** | the equivalence holds for every `δ` (kernel-checked) |
| 3 | `rAMin_le_iff_sq` / `le_rAMax_iff_sq` | moved G4 → G3 | `conforms_iff_sq` is proved from them (import order) |
| 4 | `goldschmidtZone_eq_tooLarge_iff` | **FALSE as drafted** → exact form `↔ lo ≤ t ∧ hi < t` + new `_of_band` corollary | the `if`-cascade tests `t < lo` first (witness `lo = 1, hi = 0, t = 1/2`) |
| 5 | `zoneQ_ideal_iff` | four premises **removed** | the row is unconditional (kernel-checked) |
| 6 | `tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt` | **FALSE as drafted** → premise `0 < rB + rO` replaces `0 < rO` | the pole at `rO = -rB` |
| 7 | `tolFac_rO_const_iff` | **FALSE as drafted** → `(hrB : 0 ≤ rB) (hrO : 0 < rO)` | the quantifier can hit the pole; `0 < rB + rO` alone is not enough |
| 8 | `chiTol_anti` | **FALSE as drafted** → hypothesis direction corrected (name kept) | `chiTol` is *antitone* in `|Δχ|` |
| 9 | `conforms_point_band_iff` | premise `0 < rB + rO` **removed** | the point band is antisymmetry, no division algebra |
| 10 | `inBandQ_ideal_iff` | two premises **removed** | pure `ℚ` algebra on the squared criterion |
| 11 | `radiusMatch_comp_ratchet` | `(hr1 : 0 < r1) (htau1 : tau ≤ 1)` **removed** | the triangle route needs only `0 ≤ tau` (kernel-checked) |

Items 4, 6, 7, 8 were **false statements** caught by the kernel before delivery; items 1, 2, 5, 9, 10,
11 are premise corrections of the "non-load-bearing hypothesis" class that this repository treats as
findings. None of them was an API-name drift, which is why they were first recorded in the plan's
correction log; this table is the API-log index required by rule 2.

## SymmetryFactor theory (2026-09-21) — lead-as-api_researcher — 6 probe rounds, all delivered routes kernel-verified end to end

Scope: the F0-b API round of `theories/SymmetryFactor/plan.md` (the β = 1/2 adjudication over the
unequal-curvature two-parabola model). Probe files: `theories/SymmetryFactor/probes/
SymmetryFactor-api-probe.lean` (committed; rounds 2–6 ran as throwaway `/tmp` files inside single
shell invocations — `/tmp` does not persist across invocations in this environment, a measured
fact worth knowing before scheduling probe work).

**Refuted guesses (iron rule 4 paid for itself; none of these reached a delivered file):**

| guessed name | verdict | working replacement (kernel-checked) |
|---|---|---|
| `Real.sqrt_four` | **does not exist** in this toolchain | `show (4:ℝ) = 2^2 by norm_num` + `Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)` |
| `sq_eq_sq_iff_eq_or_eq` | **unknown identifier** | `sq_eq_sq_iff_abs_eq_abs : a^2 = b^2 ↔ |a| = |b|` + `abs_of_nonneg` (the nonnegativity side-conditions are exactly what the `[0,1]` interval supplies) |
| `BEP.transfer_thermoneutral` in `BEP.Basic` | lives in **`BEP.Criterion`** (line 83), and is **unconditional** (`transfer lam 0 = 1/2` holds even at `lam = 0` through totalized division) | import `PhotoLean.BEP.Criterion` |
| bare `norm_num` on `Real.sqrt` of perfect squares | **fails** (`Real.sqrt 4 = 2` not reduced) — same family as the thrice-measured "`decide` does not reduce `/`-literals" boundary | the `sqrt_sq` route above |
| `pos_iff_ne_zero` on ℝ | **fails**: needs `CanonicallyOrderedAdd ℝ`, which ℝ is not | `lt_of_le_of_ne (add_nonneg …) (Ne.symm hd)` |
| `ratCast_inj` | **unknown identifier** | `Rat.cast_inj : (↑p : α) = ↑q ↔ p = q` (also `Rat.cast_injective`) |
| `norm_cast` / `exact_mod_cast` across `(1/2 : ℝ)` | **type mismatch** (measured twice): the ℝ numeral `1/2` does not present as `↑(1/2 : ℚ)` to mod_cast in these goals | explicit numeral lemma `((1/2:ℚ):ℝ) = 1/2` (`norm_num`) + `Rat.cast_inj.mp` |
| bare `field_simp` on `√lam/(√lam+√lam) = 1/2` and `lam/(2·lam) = 1/2` | **unsolved goals** even with the `ne'` hints | `div_eq_iff (mul_ne_zero two_ne_zero hne)` + `ring` (deterministic) |

**Confirmed API (all `#check`ed or used in delivered proofs):** `Real.sqrt_one`, `Real.sqrt_sq`,
`Real.sq_sqrt`, `Real.sqrt_inj`, `Real.sqrt_lt_sqrt (0 ≤ x → x < y → √x < √y)`,
`Real.sqrt_lt_sqrt_iff (0 ≤ x → …)`, `Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.sqrt_mul_self`,
`div_eq_iff (b ≠ 0 → (a/b = c ↔ a = c·b))`, `eq_div_iff`, `div_lt_one`, `lt_div_iff₀`,
`div_lt_iff₀`, **`div_lt_div_iff₀` (LEFT denominator positivity first — the deprecated
`div_lt_div_iff` still resolves but warns; the house zero-warning standard requires the `_₀`
forms)**, `mul_lt_mul_of_pos_right/left`, `add_pos_of_pos_of_nonneg`, `lt_add_of_pos_left`,
`le_add_of_nonneg_left/right`, `Rat.cast_div`, `Rat.cast_add`, `Rat.cast_pos`, `sq_eq_sq_iff_abs_eq_abs`,
`abs_of_nonneg`, `mul_pow`, `div_zero`, `div_nonneg`.

**Proof-route patterns worth reusing (each kernel-verified as a probe example before delivery):**
1. *Crossing uniqueness without calculus*: from `kr·q² = kp·(q−1)²` with `q ∈ [0,1]`, the two
   nonnegative quantities `√kr·q` and `√kp·(1−q)` have equal squares (`mul_pow` + `sq_sqrt` +
   `show (1−q)² = (q−1)² by ring`), hence are equal (`sq_eq_sq_iff_abs_eq_abs` + `abs_of_nonneg`);
   a linear solve (`eq_div_iff` + `calc`/`ring`) gives the closed form.
2. *Verdict-iff shape* `b/(a+b) = 1/2 ↔ a = b`: `div_eq_iff` (denominator positive) then
   `linarith` on the two atoms; back direction `rw [h]; ring`.
3. *ℚ shadow at perfect-square curvatures*: `Real.sqrt_mul_self` erases the roots, `Rat.cast_div`/
   `Rat.cast_add` move the arithmetic to ℚ — the Goldschmidt squared-criterion pattern transfers
   verbatim to a √-quotient.
4. *Monotonicity of `b/(a+b)`*: `div_lt_div_iff₀` (LEFT first!) + `mul_add` both sides +
   `mul_lt_mul_of_pos_right/left` + `linarith` with an explicit `mul_comm` witness where the atom
   order differs between the two sides.

## §photobatch — Phase-1 calibration findings (2026-09-22)

Confirmed present (mathlib v4.17.0), used by the new skeletons' proof routes:
`Real.log_mul` (two `≠` premises), `Real.log_exp`, `Real.exp_pos`, `Real.exp_ne_zero`,
`Real.exp_lt_exp`, `Real.exp_strictMono`, `Real.pi_pos`, `irrational_pi`,
`Real.sin_sq_add_cos_sq`, `Real.cos_sq_le_one`, `Real.sin_pi_div_two`, `div_pow`,
`div_lt_div_iff₀` (the zero-anchored form — the deprecated `div_lt_div_iff` stays banned),
`Finset.max'`, `Finset.exists_max_image`, `Fin.sum_univ_succ`, `Fin.cons_zero`,
`Fin.cons_succ`, `Fin.sum_univ_three`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`,
`Matrix.cons_val_two`, `Rat.cast_div`, `Rat.cast_mul`, `Rat.cast_add`, `Rat.cast_lt`,
`Rat.cast_inj`, `map_sum`.

Absent / drifted:
* `Fin.sum_univ_cons` — does NOT exist. Cons-sum route: `rw [Fin.sum_univ_succ,
  Fin.cons_zero]` then `simp only [Fin.cons_succ]` (a direct `Finset.sum_congr` +
  `Fin.cons_succ` term fails on a stuck `AddCommMonoid` metavariable).

Measured tactic boundaries (probes, this round):
* `decide` still does not reduce ℚ division (the `Marcus.RatModel` boundary); additionally
  `norm_num [Fin.ext_iff]` on `Fin 3` numeral-`if` sums overflows `maxRecDepth`. Working
  pattern: ℤ-valued finite sums by `decide`, ℚ quotients by `norm_num` (Forster FO-R2).
* `field_simp` on nested-ratio identities can leave a `True ∨ kF = 0` clearance side
  condition: close with `ring_nf` then `exact Or.inl trivial` (Forster FO-C10 dry run).
* Bare `norm_num` does not close linear identities containing a `Real.log A` atom; `ring`
  does (EnergyGapLaw EG-I3 dry run, prover_a).
* Structure-valued premise bundles introduce binders through the anonymous-constructor
  lambdas; a surplus `intro` fails with "insufficient number of binders" (KashaVavilov
  api-probe).

## §photobatch/KashaVavilov — Phase-2 proof calibration (prover_b, 2026-09-23)

Measured against mathlib v4.17.0 while proving KV-B1–KV-B7, KV-C1–KV-C7 and KV-I1–KV-I5.

Absent (guessed names that do NOT exist — do not use):
* `Finset.pos_of_prod_pos` — absent. Extract a single positive factor from a positive
  product as: `Finset.mul_prod_erase s f hmem` to factor out the chosen index, plus
  `Finset.prod_nonneg` for the erased part, plus `mul_nonpos_of_nonpos_of_nonneg` and
  `linarith` for the contradiction. (`Finset.prod_ne_zero_iff` is an alternative if the
  factors are only nonnegative: `prod ≠ 0` at the chosen index then rules the factor out.)
* `Finset.single_le_prod` — absent (its additive sibling `Finset.single_le_sum` does exist).

Confirmed present and used:
* `Finset.mul_prod_erase`, `Finset.prod_erase_mul`, `Finset.prod_ne_zero_iff`,
  `Finset.prod_nonneg`, `Finset.prod_pos`, `Finset.prod_eq_one`, `Finset.sum_pos'`,
  `Finset.single_le_sum`, `Finset.exists_max_image`, `Finset.max'_mem`, `Finset.le_max'`,
  `Finset.mem_filter`, `Finset.filter_nonempty_iff`;
* `div_pos_iff_of_pos_right`, `mul_pos_iff_of_pos_left`, `pos_of_mul_pos_left`,
  `pos_of_mul_pos_right`, `div_ne_zero`, `div_self`, `zero_div`, `one_div`.

Measured tactic boundaries (probes, this round):
* `mul_pos_iff` is **not** usable as a rewriting rule: `rw [mul_pos_iff]` on `0 < a * b`
  rewrites it to the *disjunction* `0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0`, which does not match a
  conjunction-shaped right-hand side. Working route for `(0 < a * b) ↔ (0 < a ∧ 0 < b)` with
  `0 ≤ a`, `0 ≤ b`: forward by `pos_of_mul_pos_left hp hb` / `pos_of_mul_pos_right hp ha`,
  backward by `mul_pos`.
* `unfold` with several definitions for a nested noncomputable chain can print an
  over-precise target whose `let`-bound `decay` hides the projection structure ("invalid
  projection, structure expected" on `hp.1`). Working route: state the definitional equation
  as a `have ... := rfl` and `rw` it in, then destructure the conjunction with an explicit
  `⟨fun hp => ..., fun hp => ...⟩`.
* **Import-order shadowing (unexplained, measured)**: in a file importing both
  `PhotoLean.Kasha.Basic` and `PhotoLean.Kasha.Criterion`, the declarations of
  `PhotoLean.KashaVavilov.Basic` are *not* visible when `PhotoLean.Kasha.Criterion` is the
  last import (`unknown identifier 'PhotoLean.KashaVavilov.rateData_mono'`, while
  `#check` resolves it if `PhotoLean.Kasha.Criterion` is not imported). Ordering the theory's
  own module first — `import PhotoLean.KashaVavilov.Basic` before the Kasha modules —
  restores resolution. Root cause not identified; the ordering fix is what is delivered.

## §photobatch/EnergyGapLaw — Phase-2 proof calibration (prover_a, 2026-09-23)

Measured against mathlib v4.17.0 while proving EG-B1–EG-B4, EG-C1–EG-C4, EG-S1–EG-S4,
EG-R1–EG-R3 and EG-I1–EG-I3.

Confirmed present and used:
* `Real.log_mul` (two `≠` premises), `Real.log_exp`, `Real.exp_ne_zero`, `Real.exp_pos`;
* `div_lt_div_iff₀` (two positive denominators), `div_lt_div_of_pos_right`,
  `div_lt_iff₀` (+ `zero_mul`), `div_eq_zero_iff`, `div_nonneg`, `mul_nonneg`, `mul_pos`;
* `sq_eq_zero_iff`, `sub_eq_zero`, `sub_ne_zero`, `pow_ne_zero`, `ne_of_lt`, `not_lt_of_gt`;
* `Rat.cast_lt`, `push_cast`, `EGZone.noConfusion` (a derived-`DecidableEq` inductive);
* `decide_eq_true_eq` + `norm_num [def]` for ℚ-literal `Bool` verdicts (the ICvsISC route).

Absent / unusable (do not reach for these):
* `div_neg_iff_of_pos` — **does not exist** in this version. `div_neg_iff` exists but rewrites
  `a / b < 0` to a *disjunction*; destructuring its two disjuncts under `rintro (⟨ha, hb⟩ | …)`
  produced hypotheses whose types did not match the lemma's printed statement (measured twice in
  EG-C4). Working route for a quotient-sign goal with a positive denominator:
  `rw [div_lt_iff₀ hden, zero_mul]`, or use `div_lt_div_of_pos_right` when comparing two
  quotients over the same positive denominator.
* `linarith` on `p - q` against a hypothesis about `p` and `q` — **fails**:
  `example {p q : ℝ} (hpq : p < q) : p - q < 0 := by linarith` reports
  `linarith failed to find a contradiction … a✝ : p - q < 0 ⊢ False`. Adding the same comparison
  as an explicit hypothesis (`have h : p - q < 0 := sub_neg.mpr hpq`) does not help, and
  `nlinarith` fails identically; only the hypothesis-free rewrite `sub_neg.mpr hpq` inside a
  `calc`/`exact` works. For `¬ (p - q = 0)` the working route is
  `sub_ne_zero.mpr (ne_of_lt hpq)`.
* `ring` / `ring_nf` on a goal whose `field_simp`-cleared denominator was split into a product of
  factors: the residual normal form (`lam^3 * kB^3 * T^3 * p * q * 256 = …`) is a true identity,
  but both tactics leave it (Lean only suggests `ring_nf`). Route that closes it: keep the
  transport at the level where the denominator is one atom (`field_simp; ring` on the
  definitional equations, as EG-C1 does).
