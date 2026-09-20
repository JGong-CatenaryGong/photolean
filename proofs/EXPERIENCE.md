# 经验库（Experience Bank）

> 本文件是**引擎的自反思记忆**。`TASKS.md` 记录"做完了什么"，本文件记录
> **"试过什么、为什么失败、什么最终奏效"** —— 后者才是可跨轮复用的资产。

## 为什么存在

形式化迭代里最贵的浪费是**重复死路**：同一类目标（例如"实数的严格单调性
在 `1/x` 复合下"）换一个 lemma 又要重新踩一遍战术组合。引擎的迭代循环
（`workflow` 扇出 / `ralph` fresh 轮）本身不带记忆 —— 共享工作区才是长期
记忆载体，而本文件就是那个载体。

对应 Hyra-1.0 的 **Experience Bank**：Proposal Agent 每轮把"灵感"回写，
下一轮从历史经验出发而不是从零出发。Lean 场景下的一个简化是：
**评估器就是内核**（`lake build` + `check.sh --strict`），不存在
αEvolve/Hyra 里"评估器被 reward hacking 所以要共进化"的问题，
所以只需要单层经验积累。

## 写法（强制格式）

每个条目一个 `##` 标题，四段固定：`目标` / `试过且失败` / `奏效` / `可复用模式`。
**失败路径必须记录** —— 只记成功的经验库没有价值。

```markdown
## YYYY-MM-DD — <lemma 或目标类> — <role> — <结果>
- 目标：<精确语句或目标形态>
- 试过且失败：<战术/引理 + 报错要点>（逐条）
- 奏效：<最终证明骨架 + commit>
- 可复用模式：<一句话，能迁移到别的 lemma 的判据>
```

---

## 2026-09-20 — 验收门自身的行为验证（脚手架） — lead — DONE

- 目标：确认 `check.sh --strict` + `axioms.sh` 能真正拦住三类作弊，而不是只写在文档里。
- 试过且失败：无（这是对门的验证，不是对被门拦住的证明的验证）。
- 奏效（四个样本，实测结果）：

  | 样本 | `lake build` | `check.sh --strict` | `axioms.sh` |
  |---|---|---|---|
  | 干净树 | EXIT 0 | **PASS** | PASS |
  | 证明体写 `sorry` | **EXIT 0** ⚠️ | FAIL | FAIL (sorryAx) |
  | 自定义 `axiom` | **EXIT 0** ⚠️ | FAIL | FAIL |
  | 定理体隐藏 `sorry`（语句干净）| **EXIT 0** ⚠️ | FAIL | FAIL (sorryAx) |

- **可复用模式（最重要的一条）**：`lake build` 成功 **不能**证明定理为真 ——
  `sorry` 与自定义 `axiom` 都只产生 warning，`build` 照样返回 0。
  因此"构建通过"绝不构成验收；必须叠加 (1) 源码扫描 + (2) `#print axioms`。
  三层里任何单独一层都可被绕过：自定义 axiom 无 `sorry` 关键字（靠扫描行首 `axiom` 抓），
  行内 `sorry` 可能被注释规则误放过（靠 `#print axioms` 的 `sorryAx` 抓）。
  **引擎的验收门必须三层齐备，且由不写证明的角色执行。**

## 2026-09-20 — Marcus 规划落盘 + 语句骨架（S0） — lead — DONE

- 目标：把"Marcus 反转区"三部分需求（形式化描述 / 证明与成立条件 / 实例判定）
  转成 M1–M5 的精确 Lean 语句，并让骨架编译通过（statement-first 门）。
- 试过且失败（三条，全部是工具链硬事实）：
  1. 用希腊字母 `λ` 作 Lean 标识符（`noncomputable def barrier (λ x : ℝ) ...`）→
     整个骨架 30+ 处报错 `unexpected token 'λ'; expected '_' or identifier`。
     **`λ` 在 Lean 4 里是 lambda 关键字，不是合法标识符字符**。
  2. `by decide` 判 `zoneQ (1 : ℚ) (3/4) = Zone.normal` → 失败：
     `its 'Decidable' instance ... did not reduce to 'isTrue' or 'isFalse'`；
     归约卡在 `Rat.instDecidableLt` → `Int.decNonneg` 的 gcd/除法路径上。
     **`decide` 对 ℚ 只在整数归约路径上可靠**（`zoneQ 1 3`、`zoneQ 1 1` 反而通过）。
  3. 把语句骨架直接写进 `PhotoLean/` → 会被 `check.sh --strict` 的 sorry 扫描命中
     （源码树零容忍），导致"先写语句后补证明"在纪律上不可执行。
- 奏效：
  1. Lean 侧标识符全部 ASCII：`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` /
     `a1` / `a2`（物理记号只留在文档里）；
  2. 含除法的有理判定改用 `norm_num [zoneQ]`；纯整数参数保留 `decide`；
  3. 骨架放 `proofs/probes/marcus-statement-skeleton.lean`（**不在 `SOURCE_DIRS`**）→
     31 处 sorry warning、**0 error**；末尾 4 个风险探针（`decide`、`Real.exp_lt_exp.mpr`、
     `positivity`、`nlinarith` + `div_lt_div_of_pos_right`）**全部真通过**，即 M2 的
     关键目标形态已有一条可用内核。
- 可复用模式：
  - **statement-first 的骨架必须落在源码扫描范围之外**，否则该门在纪律上不可执行；
  - **Lean 标识符禁用记号字符**（`λ` / `∀` / `→` / `∑`）：物理量命名先做一次 ASCII 化，
    能省掉一整轮 rename；
  - `decide` 的可靠域是**纯 Nat/Int 归约**；字面量一旦含除法或取模，换 `norm_num`
    （它给证明项，不依赖内核归约）。

## 2026-09-20 — 规划期发现：描述的正性前提不可去（物理侧，本项目的核心） — lead — DONE

- 目标：确定"反转区描述"的**锐利成立条件**（人类需求的第二部分）。
- 试过且失败：把描述写成
  `InvertedDescriptor A lam kB T := ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁`
  并猜想 `InvertedDescriptor ⟺ 0 < lam ∧ 0 < kB*T ∧ 0 < A` —— **这个猜想是错的**。
- 反例（规划时手算发现，已写成 M4a 的拉伸定理去钉住）：取 `A < 0 ∧ lam < 0 ∧ 0 < kB*T`：
  `lam < 0` 使 `barrier lam ·` 在反转区内**递减**，于是 `exp(-Φ/(kBT))` 递增、
  再乘负的 `A` 得**严格递减** —— 描述成立，但速率是**负的**（非物理）。
  （另一条非物理分支：`lam = 0` 时 Lean 的除零约定使 `barrier 0 x = 0`，速率恒为 `A`，严格性失败。）
- 奏效（写进 `plan.md` §7.1 的修正语句）：把"速率处处为正"并入刻画：
  `((∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ⟺ 0 < A ∧ 0 < lam`
  （在物理前提 `0 < kB`、`0 < T` 下）；必要性分 `lam = 0` 与 `lam < 0` 两支，
  两支都只需 M2 的现成引理。
- 可复用模式：
  - **"某描述成立"这类谓词命题，必须与"物理量有物理意义"（正性）捆在一起做锐利刻画**，
    否则纯代数变形会给出"形式上成立、物理上荒谬"的解；
  - 把非物理分支**保留成一条定理**（`inverted_descriptor_holds_of_neg`）比删掉它更有价值 ——
    它正是"正性前提不可去"的可检查证据；
  - 定义里凡有除法，都要先问一句 **"分母为零时 Lean 取什么值"**：`/0 = 0` 的约定会
    悄悄制造出额外的退化分支，锐利性证明必须显式覆盖它。

## 2026-09-20 — M1 描述层：`zone` 三分类的正确性（4 条定理） — prover_a — DONE

- 目标：`PhotoLean/Marcus/Basic.lean` 的
  `zone_eq_normal_iff` / `zone_eq_barrierless_iff` / `zone_eq_inverted_iff` / `zone_trichotomy`
  （`zone lam x := if x < lam then .normal else if x = lam then .barrierless else .inverted`）。
- 试过且失败（四条，全部实测报错，探针 `proofs/probes/marcus-prover_a-scratch.lean` 留档）：
  1. `iff_of_false (by decide) (ne_of_lt h).symm` →
     `application type mismatch: Ne.symm (ne_of_lt h) has type lam ≠ x but is expected to have type ¬x = lam`。
     **`ne_of_lt h : a ≠ b` 的方向已经是证明所需的 `¬(a = b)`，多套一层 `Ne.symm` 反而把方向拧反**。
  2. 备选 A `cases h : zone lam x <;> simp` → 能过（三支都自动收），但依赖 `simp` 对
     `Or` 与构造子相等的归约；**不如 `by_cases` + `if_pos` 显式分支稳**（见下）。
  3. 备选 B 单层 `by_cases h : x < lam` 后 `simp [zone, NormalRegion, h]` → 第二分支
     `unsolved goals ⊢ ¬(if x = lam then Zone.barrierless else Zone.inverted) = Zone.normal`：
     `simp` 先把 `a ↔ False` 归约成 `¬a`，此时内层 `if` 缺 `x = lam` 的判据，**必须再补一层 `by_cases h2`**。
  4. 备选 C 用 `lt_trichotomy` 三分后把 `h : lam < x` 直接塞进 `simp` →
     `unsolved goals ⊢ (if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted) = Zone.inverted`：
     **`simp` 不能用 `h` 反向简化 `x < lam`**（`lam < x` 不是 `x < lam` 的重写规则），
     必须显式给否命题 `not_lt.mpr (le_of_lt h)` / `ne_of_gt h`。
- 奏效（逐条 commit：`3644a82` 定义 / `f3d2055` / `ac80776` / `c98c85d` / `1376f8e`）：
  ```lean
  unfold zone NormalRegion            -- 或 zone / zone InvertedRegion
  by_cases h : x < lam
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; exact iff_of_false (by decide) h
    · rw [if_neg h2]; exact iff_of_false (by decide) h
  ```
  `zone_trichotomy` 用同一分支树直接给 witness：`Or.inl rfl` / `Or.inr (Or.inl rfl)` / `Or.inr (Or.inr rfl)`。
- 实测确认可用的名字（`#check` 输出见探针；供 API-NOTES 归档）：
  `@if_pos : ∀ {c} {h : Decidable c}, c → ∀ {α} {t e}, (if c then t else e) = t`（`if_neg` 同形对偶）、
  `@iff_of_true : ∀ {a b : Prop}, a → b → (a ↔ b)`、`@iff_of_false : ∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)`、
  `@le_of_not_gt`、`@le_of_lt`、`@ne_of_lt`、`@lt_of_le_of_ne`、`@Ne.symm`、`@lt_irrefl`、`@not_lt`。
- 可复用模式：
  - **`if` 分类器的 ⟺ 引理用"两层 `by_cases` + `if_pos`/`if_neg` + `iff_of_true`/`iff_of_false`"
    是零 `simp` 依赖的最短路径**；`simp` 路线需要把两层判据**全部**喂给它，否则内层 `if` 不动；
  - **`Zone`（deriving `DecidableEq`）的构造子互异可以直接 `by decide`** ——
    不需要 `noConfusion` / `reduceCtorEq` 之类需要猜的名字；
  - ⚠️ **`check.sh --strict` 的扫描包含块注释**：文件头的 `/- ... -/` 里写出
    被扫描的两个关键字字面量会造成误报 FAIL（实测：头注释里写了一次即 `verdict: FAIL`）。
    交付文件里讨论纪律时**改写措辞**（本次改为"零占位证明、无自定义公理声明"）。
    这是 prover 侧必须知道的坑（脚本注释里只提到"由 verifier 人工复核"，实际 `--strict` 直接 FAIL）。

## 2026-09-20 — M4b 微观重组能正性（`Marcus/Reorg.lean`，零依赖支线） — prover_d — DONE

- 目标：`PhotoLean/Marcus/Reorg.lean`（只 `import Mathlib`）的 2 个定义 + 4 条定理；
  签名必须与 `proofs/probes/marcus-statement-skeleton.lean` 的 M4b 段**逐字一致**
  （已用脚本抽取两侧语句做 diff 验证：6/6 VERBATIM MATCH）。
- 试过且失败（3 条，全部可迁移）：
  1. **`plan.md` §7.2 的证明提示在 API 层是错的**：照抄提示写 `sq_pos_of_ne_zero dq hdq`
     → `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`。
     v4.17 实测签名为 `∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2`
     —— **`a` 是隐式参数**，正确写法 `sq_pos_of_ne_zero hdq`。
     结论：规划文件里的证明提示是"意图"，不是 API 事实。
  2. `set_option linter.unusedVariables false in` **不能紧跟在文档注释 `/-- ... -/` 之后**
     → `error: unexpected token 'set_option'; expected 'lemma'`（doc comment 后只接受声明命令）。
     修法：说明写成普通块注释 `/- ... -/` → 再 `set_option ... in` → 最后文档注释 + 定理。
  3. 探针里手算几何因子口算错误：`R = 1/2, a1 = a2 = 1` 时
     `1/(2a₁) + 1/(2a₂) − 1/R = −1 < 0`（要 `R > 1` 几何因子才可能为正）
     → `norm_num` 报 unsolved goals，**由机器替口算兜底**（写非空真例证时别信心算）。
- 奏效（证明骨架，一次通过）：
  - `lamInner_nonneg`：`unfold lamInner; positivity`（`positivity` 直接读假设 `0 ≤ kk`）；
  - `lamInner_pos`：`have hsq : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq` → `unfold lamInner; positivity`；
  - `lamOuter_pos`：`linarith` 把 `hgeom` / `hPekar` 分别转成两因子正性 →
    `positivity` 得 `0 < dE ^ 2` → `mul_pos (mul_pos hdE2 hgeom') hPekar'`；
  - `lam_total_pos`：`linarith`。
  - 提交（每 lemma 一个 commit）：`2d4e296` 定义 / `723034d` / `acc5e8e` / `fcb7589` / `de63c09`。
  - 证据：`check.sh --strict PhotoLean.Marcus.Reorg` verdict PASS；4 条定理 `axioms.sh` 全部
    `depends on axioms: [propext, Classical.choice, Quot.sound]` → PASS。
- 可复用模式：
  - **`linarith` 是"不等式前提 → 因子正性"的最佳转换器**：目标形如 `0 < A + B - C` 时，
    直接 `have : 0 < A + B - C := by linarith`，再交给 `mul_pos` 组合；
    比让 `positivity` 独自啃"带括号的多因子乘积"更稳、报错也更可读。
  - **`positivity` 会读上下文里的正性假设**，故 `unfold <def>; positivity` 是
    "定义 = 显式乘积/除法"类目标的默认收尾 —— 但严格性前提（如 `dq ≠ 0`）
    必须自己先补成 `have hsq : 0 < dq ^ 2`。
  - **签名里有"物理定义域前提"但证明用不到时，不要为此改签名**（plan §7.2 明确要求
    这些前提在签名里可见）。做法：普通块注释写清"哪些前提是定义域、哪些被证明真正使用"，
    再用**局部** `set_option linter.unusedVariables false in` 消警告 —— 只作用于该定理，
    语句与骨架仍逐字一致（比留一排 warning 更便于 verifier 判读）。
  - **交付前跑一次"语句 vs 骨架"的脚本 diff**（正则抽 `theorem/def ... :=` 前缀再规范化空白），
    比人工比对可靠，且能作为 statement-first 的机器证据。
  - `experience.md` 是并发写热点：追加时用**唯一锚点**做局部替换，若报
    "file changed since it was read" 就重读再试（本次实测被 prover_a 的并发追加拦下一次）。

<!-- 条目从这里继续往下追加 -->
