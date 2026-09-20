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
  3. 骨架放 `theories/Marcus/probes/marcus-statement-skeleton.lean`（**不在 `SOURCE_DIRS`**）→
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
- 奏效（写进 `theories/Marcus/plan.md` §7.1 的修正语句）：把"速率处处为正"并入刻画：
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
- 试过且失败（四条，全部实测报错，探针 `theories/Marcus/probes/marcus-prover_a-scratch.lean` 留档）：
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
  签名必须与 `theories/Marcus/probes/marcus-statement-skeleton.lean` 的 M4b 段**逐字一致**
  （已用脚本抽取两侧语句做 diff 验证：6/6 VERBATIM MATCH）。
- 试过且失败（3 条，全部可迁移）：
  1. **`theories/Marcus/plan.md` §7.2 的证明提示在 API 层是错的**：照抄提示写 `sq_pos_of_ne_zero dq hdq`
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

## 2026-09-20 — ⚠️ lead 的并发提交事故：`git add -A` 吞掉工人的中间产物 — lead — FAIL→已修正

- 目标：把 `theories/Marcus/plan.md` §8.3 的文献参数回填与任务板状态更新提交。
- 试过且失败：提交时用了 `git add -A`（图省事）。当时有三个工人在并发写自己的工作文件，
  于是：
  - `e53d562`（本应是"任务板 + lakefile"）里混进了 `theories/Marcus/LITERATURE.md` 的 453 行初稿、
    `api_researcher` 的两个探针、`prover_b` 的 scratch 探针，以及 **`marcus-lemma-skeletons.lean` 的删除**；
  - `c000996`（本应是"plan 文档更新"）里混进了 **`PhotoLean/Marcus/Barrier.lean` 的 WIP** 与两个 scratch 探针。
  后果：**`barrier_nonneg`（M2 第一条）失去了自己的 per-lemma 提交** —— 内容落在一个
  标题为 `docs(plan): ...` 的提交里，审计轨迹被污染。
- 奏效（修正）：
  1. **规则写进任务板**：lead 只用 `git add <显式路径>`（`theories/Marcus/plan.md`/`theories/Marcus/TASKS.md`/`proofs/EXPERIENCE.md`/`lakefile.toml`），
     **永不 `git add -A`/`git add .`**；工人的对应规则是"只 add 自己的属主文件"；
  2. 把偏差**如实记在任务板** `barrier_nonneg` 行（不伪造一个"补提交"来回填审计轨迹 —— 那比偏差本身更糟）；
  3. 通知受影响工人：不要重试已被吸收的提交，继续按 lemma 提交余下部分。
- 可复用模式：**多写者共享一个 git 仓库时，`git add -A` 是并发事故的头号来源**。
  正确姿势是"属主即提交边界"：谁拥有文件谁 add，lead 只 add 叶子文档。
  另外一条：**事故本身要写进经验库而不是抹掉** —— 抹掉会让下一轮的 fresh agent 再犯同样的错，
  而记录它能让"规则"变成可核查的任务板条目。
- 未受影响（重要）：交付定理 M1 四条、M4b 五条各自都有正确的 `feat(M1)/feat(M4b)` per-lemma 提交。

## 2026-09-20 — 验收门自身的竞态 bug：固定探针路径导致"问 A 答 B" — prover_b 报障 / lead 修 — FIXED

- 目标：让 `axioms.sh` 在多工人并发验收时给出**可信的证据**。
- 试过且失败（**门本身的问题，不是证明的问题**）：原实现把探针写在固定路径
  `.lake/tmp/AxiomsProbe.lean`。prover_b 串行循环三条定理时实测到：
  ```
  问 PhotoLean.Marcus.rate_pos          → 打印 'PhotoLean.Marcus.Rat.zoneQ_eq_zone' depends ...
  问 PhotoLean.Marcus.rate_ratio        → 打印 'PhotoLean.Marcus.barrier_at_lam' depends ...
  ```
  即同刻运行的另一个 prover 覆盖了探针文件。**危害不是假 PASS（打印的公理集仍来自某个真定理），
  而是张冠李戴的假证据**：verifier 会拿 A 的公理报告去证明 B 干净 —— 审计轨迹被污染，比直接报错更危险。
- 奏效：把探针路径改为**每次唯一**（`AxiomsProbe.$$.$RANDOM.lean`）+ `trap 'rm -f' EXIT` 清理；
  并发隔离实测：4 个不同定理同时跑，每条各自打印自己的名字、全部
  `verdict: PASS (only mathlib infrastructure axioms)`。**判定标准未变，只消除竞态。**
- 可复用模式：
  1. **验收门自己也要被验证**（本项目 Sprint 0 已验证过一次"门能拦作弊"），
     但那次的验证是**串行**的；**并发**是另一类失效模式（竞态），必须在多人并行时单独验一次；
  2. 任何"写临时文件再读回"的脚本，临时文件名**必须含 PID 或随机段**；固定临时名 = 定时炸弹；
  3. 报障者（prover_b）除了报 bug 还给了**隔离复核**（自己起唯一路径的探针重跑一遍并保留输出）——
     这是"证据被污染时的正确应对"：不是放弃，而是换一条不可能被污染的路径重取证据。

## 2026-09-20 — M2 势垒代数（9 条，含 μ/λ 两支方向反转） — prover_a — DONE

- 目标：`PhotoLean/Marcus/Barrier.lean`（只 `import PhotoLean.Marcus.Basic`，**不新建任何定义**）的 9 条定理，
  签名须与 `theories/Marcus/probes/marcus-statement-skeleton.lean` 的 M2 段**逐字一致**：
  `barrier_nonneg` / `barrier_at_lam` / `barrier_symm` / `barrier_min_at_lam` / `barrier_mono_of_pos` /
  `barrier_antitone_of_pos` / `barrier_antitone_of_neg` / `barrier_zero_lam` / `barrier_mono_cases`
  （后三者是"方向反转"与退化支：`lam < 0` 时反转区内势垒**递减**、`lam = 0` 时恒零）。
- 试过且失败（4 条，前 3 条可迁移）：
  1. **`nlinarith` 不能直接吃除法目标**。在 `(lam-x₁)^2/(4*lam) < (lam-x₂)^2/(4*lam)` 这种形态上直接
     `nlinarith` 收不了（它既不替你清分母，也不引入分母正性）→ 必须先把分母的**符号**建成显式 `have`，
     把目标降维到"分母无关"的纯平方比较：
     `have h4 : (0:ℝ) < 4*lam := by positivity`、
     `have hsq : (lam-x₁)^2 < (lam-x₂)^2 := by nlinarith`、再 `div_lt_div_of_pos_right hsq h4`。
     **负分母支更危险**：`lam < 0` 时不能用 `div_lt_div_of_pos_right`；而
     `div_lt_div_of_neg_right` **不存在**（`#check` 直接 unknown）。可用的是
     `div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)` —— 它是 **iff，且 RHS 顺序反转**
     （右边是 `b < a`），第一次极易写反方向。正确收尾：
     `have h4 : 4 * lam < 0 := by linarith` → `unfold barrier` → `exact (div_lt_div_right_of_neg h4).mpr hsq`，
     其中 `hsq : (lam - x₁)^2 < (lam - x₂)^2`（注意与直觉的左右顺序相反）。
  2. **探针设计坑：探针不能引用"它正要验证的交付文件"里的定理**。我在只
     `import PhotoLean.Marcus.Basic` 的探针里写 `rw [barrier_at_lam]` →
     `error: unknown identifier 'barrier_at_lam'`（该定理属于 M2 待建文件，Basic 里没有）。
     正确做法：探针里先声明**局部**同名引理（`theorem scratch_at_lam (lam : ℝ) : barrier lam lam = 0 := by simp [barrier]`）
     再复用它。**探针能验证的只是"战术内核"，不是"交付文件的定理存在性"** —— 后者的证据只能来自
     真交付文件上的 `check.sh --strict` / `axioms.sh`。
  3. **流程失败（并发 git）**：`git add -A` 会把并发写者的 WIP 卷进提交（lead 的 `c000996` 事故：把当时
     只写了 1 条定理的 `Barrier.lean` 吞进一个 `docs(plan): ...` 提交）→ `barrier_nonneg` 失去自己的
     per-lemma 审计轨迹（按 lead 指示**不补空提交、不改动该条**，偏差如实记在任务板）。
     工人侧正确姿势是 **pathspec 限定提交**：
     `git commit -q -m "feat(M2): <lemma>" -- PhotoLean/Marcus/Barrier.lean`
     —— 只取该路径的工作树内容，**不会**把别人已经 `git add` 进 index 的内容并进提交
     （比 `git add <file>` + `git commit` 更抗污染：后者在 index 里有他人已 stage 内容时会一起提交）。
     提交后用 `git show --name-only <hash>` 自查"这个 commit 只碰了我的属主文件"。
  4. 初版担心"前提写了但用不到"的 linter warning 会污染验收输出（`barrier_symm` 的 `hlam : lam ≠ 0`、
     `barrier_antitone_of_pos` 的 `h₁ : 0 ≤ x₁` 证明里**真的都没用到**）；一度想改签名去掉，被纪律否决。
- 奏效：
  - 文件结构：`import PhotoLean.Marcus.Basic` → 顶层 `set_option linter.unusedVariables false`
    （**无 `in`，作用于整个文件**；`... in` 形式只作用于紧随其后的一个声明）→ `namespace PhotoLean.Marcus` → 9 条。
  - 两条骨架（lead 风险探针未覆盖，本次补齐）：
    ```lean
    theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
        barrier lam x = barrier lam (2 * lam - x) := by
      unfold barrier; congr 1; ring     -- congr 1 把目标降到 (lam-x)^2 = (lam-(2*lam-x))^2

    theorem barrier_mono_cases (lam : ℝ) : (…四元合取…) :=
      ⟨fun h x₁ x₂ h₁ h₂ => barrier_mono_of_pos h h₁ h₂,
       fun h x₁ x₂ h₁ h₂ h₃ => barrier_antitone_of_pos h h₁ h₂ h₃,
       fun h x₁ x₂ h₁ h₂ => barrier_antitone_of_neg h h₁ h₂,
       fun h x => by subst h; exact barrier_zero_lam x⟩   -- lam=0 支：subst 后目标即 barrier 0 x = 0
    ```
  - 其余条目统一内核（关键：**不需要 `unfold barrier`** —— `exact` 默认透明度即可把 `barrier lam x`
    与 `(lam-x)^2/(4*lam)` 判等）：
    `have h4 : (0:ℝ) < 4*lam := by positivity` → `have hsq : … := by nlinarith` → `exact div_lt_div_of_pos_right hsq h4`；
    `barrier_nonneg` / `barrier_min_at_lam` 用 `unfold barrier; positivity`（后者先 `rw [barrier_at_lam]`）；
    `barrier_at_lam` / `barrier_zero_lam` 直接 `simp [barrier]`。
  - 实测确认的名字（v4.17.0，探针 `theories/Marcus/probes/marcus-prover_a2-scratch.lean` 留 `#check` 原文）：
    `@div_lt_div_of_pos_right : a < b → 0 < c → a / c < b / c`；
    `@div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)`；
    `@div_lt_div_iff_of_pos_right : 0 < c → (a / c < b / c ↔ a < b)`；
    `@div_le_div_iff_of_pos_right : 0 < c → (a / c ≤ b / c ↔ a ≤ b)`；`@sq_nonneg`、`@mul_self_lt_mul_self`。
  - 两层机器证据：脚本抽签名比对 skeleton → **mismatches: 0**（9/9 逐字一致）；
    `check.sh --strict PhotoLean.Marcus.Barrier` → 扫描 `clean` + `verdict: PASS`；
    `axioms.sh` 逐条 → `[propext, Classical.choice, Quot.sound]` + `verdict: PASS (only mathlib infrastructure axioms)` ×9。
  - 每 lemma 一个 commit（pathspec 限定）：`8d9c2ff` / `03c740f` / `169a0c7` / `3dc2fcc` / `4ab7259` /
    `4561931` / `ae1276e` / `f0d79ee`。
- 可复用模式：
  1. **含除法的有序比较三步走**：① 建分母符号的 `have`；② 把目标降维成分母无关的比较（`nlinarith` 擅长）；
     ③ 用 `div_lt_div_*` 类引理合回去。口诀：**正分母保号（`div_lt_div_of_pos_right`）；
     负分母是 iff 且 RHS 反转（`div_lt_div_right_of_neg`）；负分母没有 `_of_neg_right` 版**。
  2. **`nlinarith` 的可靠域是"清完分母之后"的子目标**：把它放进 `have hsq`，别直接对准带 `/` 的 goal。
  3. **物理定义域前提即使数学冗余也保留**（statement-first；前提本身是文档）：
     在文件头块注释里写明"哪条是定义域、哪条被证明真正使用"，用**顶层**
     `set_option linter.unusedVariables false` 消噪。本次两条冗余前提：`hlam : lam ≠ 0` 与 `h₁ : 0 ≤ x₁`；
     我另验了**去掉 `hlam` 的 `barrier_symm` 语句仍可编译通过**（除零约定使 `lam = 0` 时两端同为 0）——
     "前提冗余"的实测证据比猜测更有价值。
  4. **探针只证战术、不证定理存在**：探针里若需要待建文件的引理，就写局部同名副本；
     交付定理的证据永远来自 `check.sh --strict` + `axioms.sh`（三层：构建 ≠ 验收）。
  5. **共享仓库的提交边界 = 文件属主**：`git commit -m "..." -- <自己的文件>`（pathspec 限定），
     提交后 `git show --name-only` 自查；任何一次 `git add -A` 都可能把别人的 WIP 变成"你的提交内容"。

## 2026-09-20 — 并发写入期间"全量门 FAIL"是瞬时现象，不是缺陷信号 — lead — 已确认

- 目标：判断 `proofs/scripts/check.sh --strict`（裸跑，构建 `defaultTargets` 全部模块）在多人并发时是否可信。
- 试过且失败：观察到一次裸跑全量门 `verdict: FAIL`（`build: FAILED`）。若直接据此判"有人交付坏了"，
  就是误判 —— 当时 `Rate.lean` / `Sharp.lean` 正被两个工人**写在中途**（半成品还在工作树里）。
- 奏效：**逐模块复核**已交付且已验收的四个模块（`Basic` / `Barrier` / `Reorg` / `RatModel`）→ 全部 OK；
  几秒后（写者完成当前编辑）再跑全量门 → `verdict: PASS`。即在**冻结提交**上门的判定稳定。
- 可复用模式：
  1. **门的判定必须绑定"冻结的提交/文件 blob"**：`verdict: PASS` 只在"你跑门的那一刻，被验文件没有人在写"
     时才有意义。写最终结论前，先确认 `git status` 干净或明确记录 blob 哈希。
  2. **看到全量门 FAIL 时的第一动作是"逐模块复核 + 看 `git status`"**，而不是立刻报障或回滚 ——
     并发窗口会制造瞬时 FAIL，也会制造瞬时 PASS（后者更危险：半成品恰好通过）。
  3. 这也是 `defaultTargets` 那个漏洞的**反面价值**：逐模块跑门（`check.sh --strict <Module>`）
     不受别人 WIP 影响，是并发环境下的**稳定验收通道**；裸跑全量门只适合做"最终冻结检查"。

## 2026-09-20 — 文献 vs 形式化：锐利刻画的"信息量守恒" — literature_researcher + lead — 双向纠错

- 目标：给"反转区描述"写一条**充要**的成立条件（人类需求第二部分）。
- 试过且失败（**三方各自踩过同一个坑，值得记录**）：
  - 规划期（lead）猜 `InvertedDescriptor ⟺ 0<lam ∧ 0<kB*T ∧ 0<A` —— 错。反例 `A<0 ∧ lam<0 ∧ kB*T>0`：
    `lam<0` 使势垒在反转区**递减** ⇒ 速率递增 ⇒ 乘负的 `A` 后**严格递减** ⇒ 描述成立但速率为负。
  - 文献分支独立推出的 `desc ⟺ 0<λ ∧ 0<τ ∧ 0<A` —— 同一个错（`desc` 单独不蕴含 `A>0`）。
  - lead 给文献的"修正版" `(∀x,0<rate) ∧ desc ⟺ 0<A ∧ 0<λ ∧ 0<τ` —— **也不通用**：
    反例 `λ=-3/2, τ=-1, A=1`（`λτ>0, A>0` ⇒ 描述成立且速率处处正，但 `0<λ`、`0<τ` 都不成立）。
- 奏效：文献分支用**穷举数值复核**（λ,τ,A 各取 −2…2 全组合，0 反例）定出真正的等价式：
  `desc ⟺ 0 < A·λ/τ`（等价 `0 < A·λ·τ`）；`(∀x, 0<rate) ∧ desc ⟺ 0 < A ∧ 0 < λ·τ`。
  而 `theories/Marcus/plan.md` §7.1 的 `descriptor_sharp` **恰好规避了全部陷阱**：它把 `0<kB`、`0<T` 放**前提**
  （⇒ `0<τ`），于是 `⟺` 退化为 `0<A ∧ 0<lam` —— **计划写法无需修改**，已由 M4a 交付并过门。
- 可复用模式（文献分支自己总结的，值得推广）：
  **"锐利刻画的 `⟺` 右边必须与左边的合取项一一对应。"**
  `desc` 的信息量只有 `sign(A·λ/τ)`（**一个乘积**），想从它反推三个参数**各自的符号**是不可能的；
  要反推就必须把"速率正性"这类额外信息**并入左边**。**先数左边的信息量，再写右边。**
- 副产品（诚实性）：文献用逐化合物数据算出经典公式在反转区**下降过快约 3.6 个数量级**
  （预言 5.1 个数量级 vs 实测 1.46 个数量级）⇒ 已写进 `theories/Marcus/plan.md` §8.3，
  限定实例层文案**只能**声称"经典模型满足描述"，**不能**声称预测实测速率。

## 2026-09-20 — M3 速率层（6 条，两批）+ M5a 判定层 — prover_b / prover_c — DONE

- 目标：把势垒的单调性推到速率上（M3），并让"实例判定"能在内核里算（M5a）。
- 试过且失败：
  - **`rate_ratio`**：想用 `rw [neg_div, neg_div, neg_sub_neg, sub_neg_eq_add, ← neg_sub]` 手工搬指数里的负号
    → `tactic 'rewrite' failed, did not find instance of the pattern ?a - -?b`。
  - **`by decide` 判 ℚ**：`zoneQ (1:ℚ) (3/4) = Zone.normal` 失败，报
    `'Decidable' instance did not reduce to 'isTrue' or 'isFalse'` —— 卡点在 `Rat.instDecidableLt` → `Int.decNonneg`
    的 **gcd/除法归约**上（不是 Eq 那条链）。同理 `(4:ℚ)/4 = 1`、`(0.75:ℚ) < 1` 都卡。
  - **`rw [← Rat.zoneQ_eq_zone]` 写反**：`←` 的模式是 `zone ↑?lam ↑?x`，与假设 `h : Rat.zoneQ 1 3 = ...` 对不上。
  - **cast 字面量 ≠ `OfNat` 字面量**：ℝ 侧写 `InvertedRegion (1:ℝ) 3` 与引理结论 `↑1 < ↑3` type mismatch。
  - **`rw` 不展开 `def`**：`rw [← Rat.zoneQ_inverted_iff]` 在 `¬ InvertedRegion ↑1 ↑(3/4)` 上失败（语法上无 `<` 模式）。
- 奏效：
  - `rate_ratio` 的最短路径：`unfold rate` → `rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]` → `congr 1` →
    `field_simp` → `ring`（**先 `field_simp` 让 `ring` 收尾，别手工搬负号**）。
  - M3 三条速率定理 = "势垒单调性 + `rate_gt_of_barrier_lt`" 两行复合；注意核心引理的方向约定
    （`Φx < Φy ⇒ rate y < rate x`）：正常区取 `y := x₁`、反转区取 `y := x₂`；`lam < x₁` 需 `le_of_lt` 弱化为 `lam ≤ x₁`。
  - ℚ 判定规范：**整数/无除法字面量用 `decide`；含除法或十进制一律 `norm_num [zoneQ]`**。
  - ℝ 侧一律把参数写成 `((n : ℚ) : ℝ)`（与引理结论逐字对齐），用 `norm_num` 显式桥接十进制字面量；
    否定形态先 `show` 出展开式再 `rw`；正反两个改写方向取决于式子里出现的是 `zoneQ`（正向）还是 `zone ↑↑`（反向）。
- 可复用模式：
  1. **`decide` 的可靠域是"内核能归约到底"的路径**（Nat/Int 比较）；一旦涉及 `Rat` 的 gcd/除法或十进制字面量，
     换 `norm_num`（它给证明项，不依赖内核归约）。
  2. **转移引理是"可计算判定"与"不可计算理论层"之间唯一的桥**；桥的两端字面量类型不同（`Rat.cast` vs `OfNat`），
     必须用显式 `norm_num` 等式搭，不能指望 coercion 自动统一。
  3. `rw` 是**语法模式匹配**、不走 defeq：改写前先问"式子里现在是哪个符号、规则 LHS 是什么"，
     方向由模式决定，不由直觉决定。

## 2026-09-20 — M4c 复合定理 + M4b 几何引理（`hgeom` 从假设变推导） — prover_d — DONE

- 目标：把"微观正性 ⇒ 反转区描述成立"合成一条定理（M4c），并把外层重组能的**几何因子正性**
  从"假设"降级为"由两球不重叠推出"（`a1 + a2 ≤ R ⇒ 1/R < 1/(2a1) + 1/(2a2)`）。
- 试过且失败：
  - 对三分母目标直接 `nlinarith` / `gcongr` ✗（未通分前看不到分母符号）；对**不等式**用 `field_simp` ✗
    （`simp made no progress` —— 它只对**等式**可靠）。
  - Lean 4 **混用位置参数与具名参数**（`f a b (h := …) c`）会**静默少绑一个参数**，
    报 `type mismatch … but is expected to have type …`（实为部分应用），极难一眼看出。
  - `#check` 复合定理必须 `import PhotoLean.Marcus.Compose`；只 import `Sharp`+`Reorg` 会报
    `unknown identifier`（**定义所在模块 ≠ 文件里 import 的模块**）。
  - `git commit -- <path>` 对**全新未跟踪**文件报 `pathspec … did not match any file(s) known to git`
    ⇒ 新文件必须先 `git add -- <path>`（限定路径，仍不得用 `-A`）。
- 奏效骨架（`hgeom_of_nonoverlap`）：
  `have hpos : 0 < a1 + a2 := by linarith` → `one_div_le_one_div_of_le hpos hRge` →
  `field_simp; ring` 得**通分等式** `1/(2a1)+1/(2a2) = (a1+a2)/(2a1a2)` →
  `div_lt_div_iff₀ hpos hden` 交叉相乘 → `nlinarith`。
  核心等价式：`2a1a2 < (a1+a2)² ⟺ 0 < a1² + a2²`。
  复合定理本体是一行组合：`inverted_descriptor_holds hA (lam_total_pos (lamInner_nonneg hkk dq) (lamOuter_pos …)) (mul_pos hkB hT)`。
- 可复用模式：
  1. **"先通分（对等式用 `field_simp`）→ 再交叉相乘（`div_lt_div_iff₀`）→ 最后 `nlinarith`"**
     是处理多分母不等式的通用三步；直接对不等式用 `field_simp` 一定失败。
  2. **参数的绑定方式要统一**（全位置或全具名）—— 混用会静默产生部分应用，报错信息毫无指向性。
  3. 非空性取证要**主动做**：`a1=a2=1, R=3, kk=0, nSq=1, epsS=2` 让两条复合定理落地为
     `InvertedDescriptor 1 (1/3) 1 1`，证明前提集可满足（`kk = 0` 恰好演示必须走 `lamInner_nonneg` 而非 `_pos`）。

## 2026-09-20 — M5b 实例判定（两批共 31 条） — prover_c — DONE

- 目标：把实例代进形式化理论并**判定**是否符合反转区描述（人类需求第三部分）。
- 试过且失败：
  1. **lead 派发提示里的一段写法不成立（实测打脸）**：证明"速率非正"时写
     `intro h; have := h 0; norm_num [rate, barrier] at this` —— `norm_num` 会把假设约简为
     `h0 : Real.exp (1/4) < 0`，但**它不认识 `Real.exp` 的正性**，于是留下未解目标
     `unsolved goals … h0 : Real.exp (1/4) < 0 ⊢ False`。
     奏效：先把势垒值算出来再用 `Real.exp_pos` 反驳：
     `have hb : barrier (-1) 0 = -(1/4) := by norm_num [barrier]; rw [rate, hb] at h0;
      norm_num at h0; linarith [Real.exp_pos (1/4)]`。
  2. 在 `Instances.lean` 追加第二批时忘了**重开命名空间**（批 1 末尾已有 `end PhotoLean.Marcus`）
     ⇒ `InvertedDescriptor`/`rate` 全报 `unknown identifier`。
  3. 判定证据链的三个坑（第一批已记录，这里再确认其**必要性**）：`rw [← Rat.zoneQ_eq_zone]` 方向取决于
     式子里出现的是 `zoneQ` 还是 `zone ↑↑`；ℝ 十进制字面量与 ℚ 分数 cast **定义层不等**，必须显式
     `norm_num` 桥接；`rw` 不展开 `InvertedRegion` 这类 `def`（先 `show`）。
- 奏效：
  - 13 条新定理**全部**由已过门的上游定理**实例化**得到（`descriptor_sharp` 的 (⟸) 用于"可采纳"判定、
    `inverted_rate_decreases` 用于速率比较、`descriptor_fails_of_nonpos_lam` 用于反例判定），
    **没有引入任何新的实分析步骤** —— 这是"实例层只是实例化"的结构性证据。
  - `kBT` 写成定理的**全称变量**（前提 `0 < kBT`），使"判定与温度无关"成为**语句的一部分**而非注释声称。
- 可复用模式：
  1. **`norm_num` 不是万能的**：它能算数值，但**不认识超越函数的性质**（`Real.exp_pos` 等）。
     涉及 `exp`/`log` 的反驳，必须显式提供正性引理（`linarith [Real.exp_pos x]`）。
  2. **一个文件的每一段追加都要自成命名空间上下文**（`namespace … end`），并发/分段编辑时极易漏。
  3. **实例层的正确姿势是"实例化"而不是"重新证明"**：新定理的证明体应当只调用已过门的上游定理
     + `norm_num` 定界；若发现自己在实例里重写实分析论证，说明抽象层没抽干净。

## 2026-09-20 — M4a 锐利刻画（9 条，主定理 `descriptor_sharp`） — prover_a — DONE

- 目标：证明"反转区描述成立"的**充要条件**：`(速率处处正 ∧ 描述) ⟺ 0 < A ∧ 0 < lam`（在 `0<kB`、`0<T` 前提下）。
- 试过且失败：
  1. `#check` / `#print` **不能紧跟文档注释** `/-- … -/` → `unexpected token '#check'; expected 'lemma'`；
     要用 `--` 行注释或空行隔开（与 API-NOTES 记的 `set_option` 同类坑）。
  2. `git commit -- <path>` 对**全新未跟踪文件**报 `pathspec … did not match any file(s) known to git`；
     新文件必须先 `git add -- <path>`（显式路径，仍**不得**用 `-A`），再 `commit -- <path>`。
  3. 隐式参数不显式写出会触发 `unused variable` 警告：`fun x₁ x₂ h₁ h₂ => rate_gt_of_barrier_lt hA hkT …` 里
     `x₁`/`x₂` 只被合一推断使用。改成 `rate_gt_of_barrier_lt (x := x₁) (y := x₂) …` 后 0 warning。
  4. `rate_gt_of_barrier_lt` 的 `{x y}` **方向在两支里相反**：其结论是 `rate y < rate x`。
     反转区要 `rate x₂ < rate x₁` ⇒ 取 `x := x₁, y := x₂`；正常区要 `rate x₁ < rate x₂` ⇒ 取 `x := x₂, y := x₁`。写反内核立刻报 type mismatch。
- 奏效（分支覆盖的"结构证据"）：
  - 必要性按**机制**拆三条内核而不是一条引理套两种情形：
    `sharp_lam_pos_of_eq` 的签名**不含任何正性前提**（只依赖除零约定 ⇒ 速率恒为 `A` ⇒ `A < A`），
    因此**结构上不可能**被 `lam < 0` 支吸收；`sharp_lam_pos` 用 `rcases lt_trichotomy lam 0` 三分支组装。
  - 用 `#print` 打印证明项确认三支都出现（`Or.casesOn` 嵌套），比只读源码强。
- 可复用模式：
  1. **"锐利性"的必要性要按机制拆分支**，每一支的签名要能**自证不被别支吞掉**（例如让某支不带另一支才需要的前提）。
  2. **验证分支覆盖的最强手段是打印证明项**（`#print` + `pp.proofs`），而不是读战术脚本。
  3. 复合引理的方向参数（`{x y}` 这类）在"单调递增/递减"两支里往往**相反** —— 每处调用都要重新对一次方向。

## 2026-09-20 — M5a 追加：`barrierQ` 的 ℚ→ℝ 数值桥（补结构审计发现的"未被约束定义"） — prover_c — DONE

- 目标：`barrierQ`（ℚ 侧势垒）原本**没有任何伴随定理**（结构审计与 M3+M5a verifier 各自独立发现），
  补 `barrierQ_cast : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam:ℝ) (x:ℝ)` 让 ℚ 侧数值有资格作 ℝ 层证据。
- 试过且失败：
  1. `unfold barrierQ barrier; push_cast` **单独不够** → 留 `X = X` 的 `unsolved goals`，必须补 `ring`；
     而显式 `rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]` **自带 rfl 收尾**，
     后面再写 `ring` 报 `no goals to be solved` —— **两条路线的"尾巴规则相反"**。
  2. `apply Rat.cast_inj.mp` 报 `typeclass instance problem is stuck … CharZero ?m`
     → 必须显式写 **`(Rat.cast_inj (α := ℝ))`**。
  3. `↑(0:ℚ)` 与 `(0:ℝ)` **不是 defeq**（API-NOTES 已记的 cast 字面量坑再次复现）。
- 奏效：`unfold barrierQ barrier; push_cast; ring`（一条），退化点用 `(Rat.cast_inj (α := ℝ)).mp` + `rw [barrierQ_cast]` + `simp [barrier]`。
- 可复用模式：
  1. **"未被任何定理约束的定义"是一种结构性坏味道** —— 它意味着该定义可以任意改动而无人察觉。
     交付后做一次"定义 → 引用计数"审计能直接发现它（本项目的唯一一处就是 `barrierQ`）。
  2. `push_cast` 与显式 `rw [Rat.cast_*]` 是两条**收尾规则相反**的路线：前者不给 rfl 需要 `ring`，后者自带 rfl。
  3. 若某条更短的路线需要给文件**新增 import**（破坏"只依赖 M1"的约定），**宁可写长一点**也不破坏依赖边界。

## 2026-09-20 — The gate silently skipped newly added theories (variable pass vs directory pass) — lead — FIXED

- Goal: with three theories in the repository (`theories/Marcus`, `theories/BEP`, `theories/hammond`), make the
  acceptance gate validate **every** theory's leaf data plane, not just the canonical one.
- Tried and failed (a gate that passes when it should fail):
  the contract's existing multi-theory mechanism declared per-theory leaves as `<LEAF>_<theory>` variables
  (`PLAN_Marcus`, `TASKS_BEP`, …) and `check.sh` looped over `THEORIES` checking `"${!var}"`. But the guard is
  `[ -z "$leaf" ] && continue` — so **any theory whose variables are not declared is silently skipped**. Before the
  declarations existed the whole loop was a no-op, and the contract's own comment still claimed
  "a missing leaf = FAIL". Measured directly: a freshly created theory directory was not reported at all.
- What worked:
  1. a second, **directory-sweeping** pass in `check.sh`: for every `"$THEORIES_DIR"/*/`, require the five items
     `plan.md / TASKS.md / LITERATURE.md / RESULTS.md / probes/`; report `OK <dir> (5/5)` or
     `MISSING <dir>: <items>` and set the shared `LEAF_FAIL` (so `--strict` exits 1);
  2. the theories root is read from the contract (`THEORIES_DIR`, added to `ENGINE.yml`), with a derivation
     fallback from any `<LEAF>_<theory>` path — the script still hard-codes no project path;
  3. the variable pass is **kept** (it serves projects with non-standard layouts); the two passes coexist.
- Reverse-validated (the house rule: a checker that cannot fail is worthless): creating
  `theories/_gate_probe/plan.md` made the gate print
  `MISSING theories/_gate_probe: TASKS.md LITERATURE.md RESULTS.md probes` and exit 1 under `--strict`;
  in non-strict mode it reports and continues; after removing the probe directory the tree is back to PASS.
- Reusable patterns:
  1. **A guard like `[ -z "$x" ] && continue` turns a validator into a no-op.** Any check driven by
     *optional declarations* must have a *discovery* mechanism (here: glob the directory) behind it,
     otherwise the thing you forgot to declare is exactly the thing that goes unchecked.
  2. Prefer **discovery over declaration** for coverage, and keep declarations for exceptions.
  3. When you extend a gate, immediately **construct the failing case** and watch it fail — the same
     discipline this project used on Sprint 0's gate and on every checker added since.

<!-- 条目从这里继续往下追加 -->

## 2026-09-20 — H1 description layer (13 definitions + 19 theorems): a **false** skeleton statement + `split_ifs` auto-discharge — prover_a — DONE

- Goal: `PhotoLean/Hammond/Basic.lean` (`import Mathlib` only), 20 `feat(H1)` commits; signatures
  verbatim against the skeleton (fidelity script: 32/32 VERBATIM MATCH), `axioms.sh` PASS for all 19.
- Tried and failed (5 items; the first three are transferable):
  1. **The skeleton statement `gapProduct_eq_crossing_energy` is false** (not API drift). Original:
     `gapProduct lam (-dG) = productSurface lam dG (tsCoord lam (-dG))`: LHS `= (lam-dG)²/(4lam)`,
     RHS `= (lam-dG)²/(4lam) + dG` (the product surface at the crossing point is the **absolute**
     energy, while the reverse barrier is referenced to the **product well**, whose energy is `dG`).
     The leftover goal after `field_simp; ring` exposes it: `... - lam^3*dG*8 ... = ... + lam^3*dG*8 ...`.
     Kernel counterexample (compiles):
     `example : gapProduct 1 1 ≠ productSurface 1 (-1) (tsCoord 1 1) := by norm_num [...]`.
     **Lesson: when `field_simp` + `ring` fails and the leftover goal differs only by one signed term,
     suspect the statement's physical convention before the tactic** — reported to the lead, who adopted
     fix (a) (add `- dG`); re-proved in one shot afterwards. The lead's own audit then found the same class
     of defect in `conforms_iff_structure` (a three-way disjunction, i.e. a tautology with no content).
  2. **`split_ifs at h with h1 … h6` discharges the contradictory branches itself.** Writing all 7 branches
     as 7 bullets reports `no goals to be solved`; only the branch that really produces the constructor
     survives (carrying its 6 guards), the others being killed by constructor injectivity on
     `h : Ctor₁ = Ctor₂`. Correct shape: `split_ifs at h with h1 … h6` followed by **one** proof.
  3. **After `constructor` on a `↔`, each branch goal is one-directional**: the backward goal is an
     **equality** (not an `↔`), so `unfold <def>; rw [if_neg …, if_pos …]` closes it by `rfl`; adding
     `exact iff_of_true …` then reports `no goals to be solved`. Also, `exact iff_of_true h …` with the
     anonymous constructor `⟨h1,h2⟩` reports `expected type must be an inductive type ?m` (the implicit
     argument is not fixed yet) — use `And.intro h1 h2` or a `have` first.
  4. **Self-swallowing commit driver**: `python3 emit.py k > PhotoLean/Hammond/Basic.lean` where `emit.py`
     *reads* the same path → the shell truncates the input before the script reads it (`segments:` empty).
     Fix: **emit to a temp file, then `cp`** (or have the script read a master copy). The driver must also
     always generate step k from the **master snapshot**, since after step k-1 the working tree no longer
     contains the later theorems and an `assert` fires immediately.
  5. Tool-surface trap: the `write` tool reported success for `/tmp/*.sh` but the file did not exist
     (`bash: /tmp/…: No such file or directory`); create `/tmp` scripts/probes with a bash heredoc and use
     `write`/`edit` for workspace files only.
- Worked (reusable recipes):
  - **`set_option linter.unusedVariables false in` must precede the docstring**:
    `set_option … in` → `/-- doc -/` → `theorem …` (measured; the reverse order reports `unexpected token`).
    H1 has 4 declarations with a physical premise the proof does not consume (`tsCoord_at_lam` because of
    Lean's `x / 0 = 0` convention; three zone lemmas because their branch guards already force the signs) —
    **keep the premise, disable the linter locally**, never touch the statement (signature fidelity is a hard
    constraint).
  - Shortest two-way path for `if`-classifier `iff` lemmas: forward
    `unfold <def> at h; split_ifs at h with …` (auto-discharge, one goal left); backward
    `unfold <def>; rw [if_neg …, if_pos …]` (closed by `rfl`). Supply the guard facts directly with
    `ne_of_lt h2` / `not_lt.mpr (le_of_lt h2)` / `by linarith`, never relying on `simp`.
  - One submission driver ran all 20 steps (build + `check.sh --strict` + `axioms.sh` + `git commit -- <path>`
    per theorem), log kept at `/tmp/h1-gate-log.txt`; `git commit -m … -- <path>` guarantees that concurrent
    writers' files are not swallowed.

## 2026-09-20 — H5a 判定层（`Hammond/RatModel.lean`：4 定义 + 12 定理，含 7 分支分类器转移） — prover_c — DONE

(This entry is in English per the language policy; the earlier entries in this file predate it.)

- Goal: the ℚ-side classifier and transfer lemmas, so that a kernel-computed zone verdict is
  binding for the ℝ theory (`ℚ` order/equality are decidable, `ℝ`'s are not). Highest-risk item:
  the seven-branch `hammondZoneQ` vs `hammondZone` transfer. 13 commits, one declaration each.
- Tried and FAILED (4 items):
  1. **Copying branch closers across an order change.** The API probe proves the ℝ-side `late`
     characterization for the conjunction `-lam < x ∧ x < 0`; the skeleton states the ℚ-side one as
     `x < 0 ∧ -lam < x`. I copied `rintro ⟨hx, -⟩; linarith` into the `x = -lam` and `x < -lam`
     leaves, where the *first* conjunct is TRUE and the second is the false one. Measured error:
     `linarith failed to find a contradiction … h2 : x = -lam, hx : x < 0 ⊢ False`.
     Fix: leaves 1/4/5/6 need `⟨hx, -⟩`, leaves 2/3 need `⟨-, hy⟩`.
     **Lesson: the statement's conjunction order decides which component each leaf must destroy;
     re-derive it per leaf instead of transplanting branch closers.**
  2. `set_option linter.unusedVariables false in` written AFTER the doc comment →
     `error: unexpected token 'set_option'; expected 'lemma'`. The `in` form must precede the doc
     comment (same lesson `prover_a` recorded above, independently hit here). Works: `set_option … in`
     → `/-- doc -/` → `theorem …`.
  3. Chasing the wrapped `#print axioms` output with printer options: `pp.width` is not a Lean 4
     option (`unknown option 'pp.width'`); the real option `format.width` (file-level **and** the
     `… in` form) and `lean -Dformat.width=400` all leave the message rendering unchanged. The wrap
     cannot be fixed from the theorem side.
  4. Transcribing Marcus's three-branch `by_cases` ladder to seven branches: does not scale
     (independently measured by `api_researcher`: 31 lines and still fragile). Not attempted after
     reading that measurement — recorded here as the rejected path.
- Worked (reusable recipes):
  - **The seven-branch transfer is two lines**: `unfold hammondZoneQ hammondZone` then `norm_cast`.
    No hypotheses (the degenerate `lam = 0` branch transfers too), no case bash: `norm_cast` moves
    all six ℝ-side tests back to ℚ, including the literal `0` and `-↑lam` via `Rat.cast_neg`.
  - All seven ℚ-side characterizations: `unfold hammondZoneQ; split_ifs with h1 … h6` (exactly the
    seven leaves, each with the accumulated negated tests), then per leaf one of
    `exact iff_of_true rfl …` / `exact iff_of_false (by decide) …` with `linarith` on the arithmetic
    side. `early` compacts to 7 lines with `<;> first | … | …`.
  - The Marcus cross-link is pure composition, no new arithmetic:
    `rw [hammondZoneQ_eq_beyondReactant_iff hlam, Marcus.Rat.zoneQ_inverted_iff, Rat.cast_lt]`
    (the last rewrite returns the ℝ comparison to ℚ and `rw` closes the goal by `rfl`).
  - Algebraic casts: `unfold …; push_cast; ring` (coordinate, barrier) and
    `unfold …; push_cast; rw [gapReactantQ_cast, gapReactantQ_cast]` (secant; the skeleton-mandated
    `h : x₁ ≠ x₂` is kept but is **not used** — `Rat.cast_div` commutes the cast with division
    unconditionally, so both sides collapse to `0` at `x₁ = x₂`; linter switched off for that
    declaration only, doc comment says "not used by the proof" — never "implied by the others").
  - Workflow: develop the **whole** file in a probe importing the same two upstream modules, verify
    fidelity (script: all 16 declarations byte-identical to the skeleton) and 0 warnings there,
    then deliver one declaration per commit with build + `check.sh --strict` + `axioms.sh`.
- ⚠️ **Gate defect found (engine-level, script-owned)**: `axioms.sh` parses `#print axioms` with
  `sed -n 's/.*\[\(.*\)\].*/\1/p' | head -1`, which is **line-based**. `hammondZoneQ…
  _beyondReactant_iff_inverted` has a 62-character name ⇒ the message
  `'NAME' depends on axioms: [propext, Classical.choice, Quot.sound]` (124 chars) is wrapped by the
  ~120-column layout into three lines ⇒ LIST empty ⇒ **false** `verdict: FAIL (could not parse axiom
  list from output)`. Raw output and a line-joined parse show exactly
  `[propext, Classical.choice, Quot.sound]`. Fix belongs in the script (`tr '\n' ' '` before `sed`),
  reported to the lead. **Lesson: a gate is code too — a FAIL from a long name can be a parser
  artifact, so verify the raw output before touching the statement.**

## 2026-09-20 — H2 Hammond criterion (15 theorems, `Hammond/Criterion.lean`) — prover_a — DONE

- Goal: `PhotoLean/Hammond/Criterion.lean` (imports `PhotoLean.Hammond.Basic` + `PhotoLean.Marcus.Basic`),
  15 theorems verbatim against the corrected skeleton (15/15 VERBATIM MATCH), one `feat(H2)` commit each,
  `check.sh --strict` PASS, `axioms.sh` PASS for all 15.
- Tried and failed (4 items):
  1. `conforms_iff_zone`, backward direction: `exact (hammondZone_eq_early_iff hlam).mp h` →
     `type mismatch: 0 < x ∧ x < lam` vs expected `ReactionRegion lam x`. `ReactionRegion lam x` unfolds to
     `-lam < x ∧ x < lam`: the **right** conjunct matches, the **left** one does not (`0 < x` vs `-lam < x`),
     and they are only equivalent through `0 < lam`, not definitionally. Same trap in the `late` branch
     (whose conjunction has the reverse order). Fix: `unfold ReactionRegion` first, then
     `obtain ⟨hx0, hxlam⟩ := …mp h; exact ⟨by linarith, hxlam⟩` / `exact ⟨hnlam, by linarith⟩`.
     **Lesson: a conjunction proved by a lemma with a reordered/weaker left component never closes by
     `exact`; unfold the target predicate and re-assemble the pair explicitly.**
  2. `lefflerSecant_eq_midpoint`: `positivity` supplies `(4*lam) ≠ 0` and `(2*lam) ≠ 0`, but `field_simp`
     additionally needs the secant denominator — had to add
     `have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)`. `field_simp` consumes **every** denominator's
     nonzero fact explicitly; a missing one is not inferred from `h : x₁ ≠ x₂`.
  3. Almost guessed that `barrier_eq_gapReactant` needs unfolding; it is `rfl` directly, because
     `Marcus.barrier` and `gapReactant` have literally the same body `(lam - x)^2 / (4*lam)` — checked in the
     source (`PhotoLean/Marcus/Basic.lean` line 50) **before** guessing any API name.
  4. No unused-premise problem here: unlike H1 (4 declarations with a proof-redundant physical premise,
     needing `set_option linter.unusedVariables false in`), every H2 premise (`0 < lam`, `x₁ ≠ x₂`) is consumed.
- Worked (reusable recipes):
  - `reactantLike_iff` / `productLike_iff`: after `unfold <pred> tsCoord`, one `rw [div_lt_iff₀ h2]`
    (or `lt_div_iff₀ h2`) with `h2 : 0 < 2*lam` by `linarith`, then `constructor <;> intro h <;> linarith`.
  - `tsCoord_antitone`: `unfold tsCoord; rw [div_lt_div_iff_of_pos_right (by linarith : (0:ℝ) < 2*lam)]; linarith`.
  - `lefflerSecant_mem_iff` / `lefflerSecant_neg_iff_inverted`: `rw [lefflerSecant_eq_midpoint hlam h]`
    then `exact tsCoord_mem_iff hlam` / `exact tsCoord_lt_zero_iff_inverted hlam` — chaining the identity lemma
    with the H1 characterization is the shortest path (no recomputation).
  - `tsCoord_lt_zero_iff_inverted`: `unfold tsCoord Marcus.InvertedRegion; rw [div_lt_iff₀ h2]`, then
    `constructor <;> intro h <;> linarith` (avoids the nonexistent `div_neg_iff_pos_right` route).
  - Submission driver reused from H1: `python3 emit.py k > /tmp/snap.lean && cp /tmp/snap.lean <file>`
    (never redirect the emitter into its own input), then build + `check.sh --strict` + `axioms.sh` +
    `git commit -m … -- <path>` per theorem; logs at `/tmp/h2-gate-log.txt`.

## 2026-09-20 — H4 microscopic composition (4 theorems, `Hammond/Compose.lean`) — prover_a — DONE

- Goal: `PhotoLean/Hammond/Compose.lean` (imports `PhotoLean.Hammond.Criterion` +
  `PhotoLean.Marcus.Reorg`), 4 theorems verbatim against the skeleton H4 section (4/4 VERBATIM MATCH),
  one `feat(H4)` commit each, `check.sh --strict` PASS, `axioms.sh` PASS for all 4.
  Whole file compiled on the first attempt with 0 warnings.
- Tried and failed / traps avoided (3 items):
  1. **Implicit-argument drift in `Marcus.lamInner_pos`**: the source signature is
     `lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) : 0 < lamInner kk dq` — `dq` is
     **implicit**, so the call is `Marcus.lamInner_pos hkk hdq` (no explicit `dq`). The plan's sketch and
     the printed line in `Reorg.lean` both hide this (the printed line starts mid-signature). Read the
     signature from source before writing the call — same class of failure as the M4b `sq_pos_of_ne_zero`
     incident recorded above, which is why it did **not** become an error this time.
  2. `Marcus.lam_total_pos` needs `0 ≤ lamIn` (not `0 <`): in `exists_reactionRegion_of_microscopic` the
     strict `lamInner_pos` must be pushed through `le_of_lt`, while the microscopic (non-strict `hkk`)
     version uses `lamInner_nonneg hkk dq`. Two different producers for the same `0 ≤` slot.
  3. `hammond_descriptor_of_nonoverlap` has **no** `hR : 0 < R` hypothesis (only `hRge : a1 + a2 ≤ R`):
     `lamOuter_pos` still wants `0 < R`, so it must be derived — `(by linarith)` from `ha1`, `ha2`, `hRge`.
     The stretch target replaces only the geometric premise, via
     `Marcus.hgeom_of_nonoverlap ha1 ha2 hRge`.
- Worked (reusable recipes):
  - The whole H4 layer is **term mode, one line per theorem**:
    `hammond_descriptor_holds (Marcus.lam_total_pos (Marcus.lamInner_nonneg hkk dq) (Marcus.lamOuter_pos …))`.
    Composition lemmas whose only content is "positivity transports through a definitional wrapper" need no
    tactics at all.
  - **Scope note that belongs in the artifact, not only in the report**: this composition carries no
    `A`/`kB`/`T` premise (it is a structural statement), unlike the Marcus rate-level counterpart
    `Marcus.descriptor_holds_of_microscopic`. Written into the file header so a reader cannot mistake the
    weaker premise set for an omission.
  - Submission driver reused unchanged from H1/H2 (emit → build → strict scan → `axioms.sh` → commit -- path);
    logs at `/tmp/h4-gate-log.txt`. Reusing one driver for three milestones cost nothing and kept the evidence
    format identical across H1/H2/H4.

## 2026-09-20 — H3 sharp conditions (6 theorems, `Hammond/Sharp.lean`) — prover_d — DONE

- Goal: `0 < lam` as the **exact** validity condition of `HammondDescriptor` (`hammond_sharp`), with
  explicit two-point counter-witnesses for `lam < 0` and `lam = 0` instead of a negated quantifier.
  6 theorems, one `feat(H3)` commit each; `check.sh --strict` PASS and `axioms.sh` PASS for all six.
- Tried and failed (3 items):
  1. **Forward reference to the witnesses in the skeleton's declaration order is impossible** — the
     authority lists `hammond_lam_pos_of_descriptor` first and the two witnesses after it, and Lean has
     no forward references. Delivering in proof order (witnesses first, necessity kernel consuming them)
     is the fix sanctioned by the plan; the fidelity script is dict-based and order-insensitive, so the
     reordering produced **0 signature differences**. Record the deviation in the file header.
  2. `subst hzero` in the `lam = 0` branch rewrites the **goal** `0 < lam` to `0 < 0`, so
     `exact hnot (h x₁ x₂ hlt)` (type `False`) fails: `type mismatch: False` vs `0 < 0 : Prop`. Fix:
     `exact absurd (h x₁ x₂ hlt) hnot`. **Lesson: after `subst`, the contradiction proof has type
     `False` while the goal is the rewritten proposition — use `absurd`/`False.elim`.**
  3. Two **self-inflicted diagnosis errors** while collecting the "witnesses are genuine" evidence
     (worth recording because both looked like workspace faults):
     a. A probe containing `example : tsCoord (-3) 0 < tsCoord (-3) 1 := …` failed with
        `function expected at tsCoord`, `term has type ?m.4` and `unknown identifier
        'hammond_fails_of_nonpos'` **because the probe never opened `namespace PhotoLean.Hammond`**:
        an unqualified name that is not in scope is auto-bound as an implicit variable inside an
        `example`, so the error message points at the use, not at the missing namespace. Wrapping the
        probe in the two namespaces (or fully qualifying every name) makes the identical file compile
        with 0 error. **Lesson: in a probe file, `term has type ?m.N` on a known identifier means
        "not in scope", not "import broken".**
     b. Chasing (a) I concluded that a concurrent build was deleting the oleans, because
        `ls .lake/build/lib/lean/PhotoLean/Hammond/` returned `No such file or directory` while other
        runs still worked. The real cause: in this project Lake writes
        `.lake/build/lib/PhotoLean/Hammond/` (there is **no** `lean/` path component) — the wrong path
        gives ENOENT forever, which mimics a churning build tree exactly. Verify the build-dir layout
        once with `find .lake/build -name '*.olean'` instead of assuming the upstream Lake layout.
        **Lesson: a path-shaped error is evidence about your path guess before it is evidence about
        the workspace; and in a multi-prover workspace, reproduce an isolated failure once more before
        reporting it as interference.**
- Worked (reusable recipes):
  - `exists_direction_reversal_of_neg`: `refine ⟨0, 1, by norm_num, ?_⟩; unfold tsCoord;
    rw [div_lt_div_right_of_neg (by linarith : (2 : ℝ) * lam < 0)]; linarith`. Note this rewrite's RHS is
    `b < a` (numerator order flips) — the exact reverse of H2's `tsCoord_antitone` route.
  - `exists_direction_reversal_of_eq`: `refine ⟨0, 1, by norm_num, ?_⟩;
    rw [tsCoord_zero_lam, tsCoord_zero_lam]; norm_num` — two `rw`s instantiate the two different `x`s.
  - `hammond_lam_pos_of_descriptor`: `rcases lt_trichotomy lam 0 with hneg | hzero | hpos`; the negative
    branch contradicts the descriptor at the witness pair (`linarith`), the zero branch by `absurd`, the
    third branch is the conclusion itself. `set_option pp.proofs true in #print` shows both witness
    lemmas, `lt_trichotomy`, `absurd` and `Or.casesOn` ×2 in the proof term (2 nested `casesOn` = the
    3 branches), i.e. the witness → necessity dependency is kernel-enforced, not a code-reading claim.
  - `hammond_sharp`: one line, `⟨hammond_lam_pos_of_descriptor, hammond_descriptor_holds⟩` (H2's
    sufficiency) — no new arithmetic. `hammond_fails_of_nonpos`:
    `linarith [hammond_lam_pos_of_descriptor h]`. `conforms_requires_pos`: `h.1`. No linter suppression
    needed: every premise of the six signatures is used.
- Reusable pattern: **make the necessity direction consume the witness theorems rather than inlining the
  same two points twice** — the counterexamples then cannot drift from the branch that uses them, and
  "the witnesses are genuine" becomes a proof dependency. Corollary: when the statement authority fixes a
  declaration order that is not the proof order, deliver in proof order, verify fidelity (order-insensitive),
  and record the deviation in the file header and the hand-off report.

## 2026-09-20 — H5b 实例判定层（`Hammond/Instances.lean`：29 条，I1–I10） — prover_c — DONE

(This entry is in English per the language policy; earlier entries predate it.)

- Goal: the 29 instance verdicts of the skeleton's H5b section, one commit per theorem, with the
  plan §13 wording rule ("outside the domain of applicability of the model's description", never
  "the molecule violates Hammond"). Delivered: 29/29 signatures verbatim, 29 commits, all gates
  green on the first run of the incremental driver.
- Tried and FAILED (3 items, all in the literal-bridge plumbing):
  1. **Writing the ℚ-side literal bridge in a different surface syntax than the statement
     authority.** The instance literal is `-(1 / 2)`; I bridged with
     `(((-(1 : ℚ) / 2 : ℚ)) : ℝ) = (-(1 / 2) : ℝ)`. `-(1:ℚ)/2` parses as `(-1)/2`, while the
     skeleton's `-(1/2)` parses as `-(1/2)` — *equal but not syntactically equal*, so the final
     `rw [inst_I3_endergonic_zone]` failed with
     `did not find instance of the pattern … Rat.hammondZoneQ 1 (-1 / 2) = HZone.late`.
     Fix: write the ℚ literal with the skeleton's own surface syntax
     (`((-(1 / 2) : ℚ) : ℝ) = (-(1 / 2) : ℝ)`).
  2. **Ordering two literal bridges wrongly.** In `hammondZone (1) (-(1/2))` the bridge for `1`
     ran first, which also rewrote the `1` inside `-(1/2)`, so the second bridge's pattern no
     longer matched: `did not find instance … ⊢ hammondZone (↑1) (-(↑1 / 2)) = HZone.late`.
     Fix: rewrite the compound literal first, the atomic one second.
  3. `rw [Rat.hammondZoneQ_eq_early_iff]` without the hypothesis: the hypothesis is an unassigned
     metavariable → `unsolved goals ⊢ 0 < ?m`. It must be given explicitly, e.g.
     `rw [Rat.hammondZoneQ_eq_early_iff (by norm_num : (0 : ℚ) < 6 / 5)]`.
- Worked (reusable recipes):
  - **The binding chain, per verdict**: build the ℝ-side classifier value from the ℚ computation
    by `rw [← (bridge_c), ← (bridge_d), ← Rat.hammondZoneQ_eq_hammondZone, inst_…_zone]`, then
    `(conforms_iff_zone h).mpr (Or.inl hz)` for a positive verdict, or
    `intro hc; have hd := (conforms_iff_zone h).mp hc; rw [hz] at hd;
    rcases hd with h | h | h <;> exact absurd h (by decide)` for a negative one. The literal
    bridges are `by norm_num : (((c : ℚ)) : ℝ) = (c : ℝ)`.
  - **Marcus cross-link on a real instance**: `Rat.hammondZoneQ_beyondReactant_iff_inverted` (H5a)
    → `Marcus.Rat.zoneQ … = Marcus.Zone.inverted` → `Marcus.Rat.zoneQ_inverted_iff` → `lam < x`;
    close with `unfold Marcus.InvertedRegion; norm_num at hlt ⊢`.
  - Pure instantiations (no arithmetic): `hammond_fails_of_nonpos (by norm_num : … ≤ 0)` (I8),
    `tsCoord_antitone` (I9), `hammond_descriptor_holds` (I4), `reactantLike_iff` / `productLike_iff`
    (I2/I3/I10), `not_reactionRegion_of_nonpos` (I8).
  - **Master-copy + emitter delivery**: keep the whole file (with `-- @DECL: <name>` markers) in the
    scratch probe, and have the driver emit "header + first k declarations + footer" (stripping
    `-- @` dev lines) into a temp file, `cp` it over the delivered path, run
    build + `check.sh --strict` + `axioms.sh` + `git commit -- <path>` — 29 commits in ~3 minutes,
    full log at `/tmp/h5b-gate-log.txt`. The emitter **reads the master and writes a temp file**
    (never the path it reads), which avoids prover_a's self-truncating-emitter bug.
  - Corollary for the verifier: "all 29 verdicts are kernel-checked" is backed by 58
    `verdict: PASS` lines (one strict-check plus one axioms line per step) and no
    `FAIL|error|warning` line in the driver log.

## 2026-09-20 — Hammond Sprint 0: two FALSE statements in the first skeleton draft — lead — DONE (caught before delivery)

- Goal: turn the Hammond plan into a compiled statement skeleton (statement-first gate) and a lead risk probe.
- Tried and failed:
  1. The lead's risk probe covered only the statements that *looked* risky (crossing uniqueness, monotonicity,
     sharpness branches, the Leffler identity). Two statements that looked routine were false:
     - `gapProduct_eq_crossing_energy`: the reverse barrier is measured from the **product well** (energy `dG`),
       so the un-referenced form `gapProduct lam (-dG) = productSurface lam dG (tsCoord …)` is off by exactly `dG`.
       Found by `prover_a` with a kernel counterexample (`example : gapProduct 1 1 ≠ productSurface 1 (-1) (tsCoord 1 1)`).
     - `conforms_iff_structure`: the intended "verdict = early ∨ half ∨ late" disjunction of sign predicates is a
       **tautology of trichotomy** (`a < 1/2 ∨ a = 1/2 ∨ 1/2 < a` holds for every `a`), so it characterizes nothing.
       Found by the lead's audit pass.
- Worked:
  1. Fix the statements in the skeleton (and plan/board) *before* delivery, and record the correction in the
     experience bank + the plan (documenting *why* the well-referenced form is the right one).
  2. **Systematic audit instead of risk-based spot checks**: `theories/hammond/probes/hammond-lead-audit.lean`
     instantiates *every* non-definitional skeleton statement at concrete rationals **and adds negative controls**
     (`¬` forms at points where the statement must fail), so a tautology or an off-by-a-term identity cannot pass.
  3. Recipe for classifier evaluations (also reused by the provers and by the H5a layer):
     `unfold <classifier>; split_ifs <;> first | rfl | decide | norm_num at *`
     (`norm_num at *` kills contradictory branch hypotheses; `decide` closes constructor-disjointness goals).
- Reusable pattern: **statement-first does not mean "only the risky statements are checked".** A skeleton needs a
  *falsification pass with negative controls* before any prover is dispatched; a false statement costs a blocked
  prover plus a statement change (the expensive kind of churn), while the audit probe costs minutes.

## 2026-09-20 — Engine: `axioms.sh` false FAIL on long theorem names — prover_c (reported) / lead (fixed) — DONE

- Goal: run the third acceptance layer (`#print axioms`) on a 62-character fully-qualified theorem name.
- Tried and failed:
  1. `LIST="$(printf '%s' "$OUT" | sed -n 's/.*\[\(.*\)\].*/\1/p' | head -1)"` parses the output **line-wise**;
     `#print axioms` wraps at the Format width (~100 chars), so a long name splits `[propext, Classical.choice,
     Quot.sound]` across three lines → `LIST` empty → `verdict: FAIL (could not parse axiom list)` while the raw
     output contains *exactly* the three allowed axioms. A false negative on a correct theorem.
  2. `set_option format.width 400` (file-level and `in`) and `lean -Dformat.width=400` — all ineffective.
- Worked: `LIST="$(printf '%s' "$OUT" | tr '\n' ' ' | sed -n 's/.*\[\(.*\)\].*/\1/p' | head -1)"` — join the lines
  before parsing. Re-ran the previously failing theorem: `verdict: PASS (only mathlib infrastructure axioms)`.
- Reusable pattern: **when a gate parses tool output, it must normalize the tool's formatting first** — a gate that
  reports FAIL on correct input is as costly as one that misses a defect (here it nearly became a "blocked"
  milestone). Keep the failure reproducible and record it in the API/gate log.

## 2026-09-20 — Engine: adding a second theory to the contract (Hammond) — lead — DONE

- Goal: host a second theory without breaking the Marcus data plane or the acceptance gate.
- Worked (additive design):
  1. `proofs/ENGINE.yml`: keep the canonical single-theory keys (`PLAN`, `TASKS`, …) untouched and add
     `THEORIES="Marcus hammond"` plus `<LEAF>_<theory>` keys (`PLAN_hammond`, `TASKS_hammond`,
     `LITERATURE_hammond`, `PROBES_hammond`, `RESULT_hammond`).
  2. `proofs/scripts/check.sh`: a generic loop over `THEORIES` that checks `<LEAF>_<theory>` existence
     (`${!var:-}` indirect expansion, skipped when the variable is unset) — so a new theory's leaves are
     actually gated, and old projects are unaffected.
  3. `SOURCE_DIRS` stays global: the new theory's Lean sources go to `PhotoLean/Hammond/` (the human confirmed
     this layout explicitly) and `lakefile.toml`'s `defaultTargets` gains one line per delivered module.
- Reusable pattern: **extend the data plane additively; never re-point the canonical keys.** A second theory must
  not silently un-gate the first one's leaves, and a bare full-tree run must build what the scan can see.

## 2026-09-20 — Hammond: submitted theory is weaker than the sharpest provable form in 4 places — prover_b (audit) — DONE (documented, not changed)

- Goal: adversarially audit the delivered H1/H5a statements (hypothesis necessity, boundary, non-vacuity,
  classifier integrity, independence) — 99 kernel checks in `theories/hammond/probes/hammond-audit-b.lean`.
- Result: **no false statement, no vacuous hypothesis**; 41 `#print axioms` clean. Tightness observations:
  1. `tsCoord_mem_iff`'s `0 < lam` is not sharp: for `lam = 0` the equivalence holds for every `x`; the sharp
     hypothesis is `0 ≤ lam`. (`reactionRegion_pos` is nevertheless forced: `(∃ x, ReactionRegion lam x) ↔ 0 < lam`.)
  2. The seven zone-characterization lemmas split into three classes: `early`/`late`/`atReactant` hold for arbitrary
     `lam` and `x` (their `0 < lam` is redundant), `atProduct` needs only `lam ≠ 0`, and only
     `half`/`beyondReactant`/`beyondProduct` genuinely need the sign hypothesis.
  3. The `lam ≠ 0` hypotheses of the two crossing-energy identities and of `tsCoord_at_lam` are redundant at `lam = 0`.
- Reusable pattern: **a redundant hypothesis is not a defect, but it must be reported as "unused / a sharp form is
  available", never as "derivable from the others".** Keep the delivered signature stable (statement stability is
  worth more than tightness here) and record the sharp form + the kernel counterexamples for the next revision.

## 2026-09-20 — BEP Sprint-0 risk probe: `Real.sqrt` tolerance radius + equioscillation minimax (7 handed forms; one of them FALSE) — prover_d — DONE

- 目标：before B3 (`PhotoLean/BEP/Sharp.lean`) is dispatched, prove the riskiest statement forms of
  `theories/BEP/plan.md` §6 in a standalone probe (`theories/BEP/probes/bep-risk-probe.lean`,
  18 declarations, no `sorry`, no custom `axiom`, 8.6 s wall for the whole file) so that the §11
  fallbacks are chosen on kernel evidence. Handed forms: defect expansion (1), secant/midpoint
  identity (2), tolerance radius `w ≤ 2√(λ·tol)` (3), best-line error (4), minimax lower bound (5),
  halving (6), two-point λ solver (7).
- 试过且失败：
  1. **Handed form 7 is false, not merely hard.** `lam = (x₁²-x₂²)/(2(x₂-x₁) - 4(y₁-y₂))` pairs a
     numerator and a denominator of opposite sign, so the right-hand side equals `-λ`. Kernel
     counterexample with every handed hypothesis satisfiable (`risk_pair_solver_literal_refuted`):
     `λ=2, x₁=0, x₂=1, y₁=1/2, y₂=1/8` → denominator `= 1/2 ≠ 0`, `x₁ ≠ x₂`, RHS `= -2 ≠ 2 = λ`.
     The same defect is in plan §8.1 line 372 (`qLamOfPair`) and would have reached B5a's
     `qLamOfPair_reconstructs`. Corrected forms (`risk_pair_solver`, `risk_pair_solver_alt`) are proved.
  2. **The handed form also lacks `lam ≠ 0`**, which `x₁ ≠ x₂` + nonvanishing denominator do *not*
     imply (at `λ=0` the barrier map `(λ-x)²/(4λ)` degenerates to the constant `0`, while
     `2(x₂-x₁) ≠ 0`): kernel witness `risk_pair_solver_needs_lam_ne_zero` (`λ=0, x₁=0, x₂=1`, RHS `1/2`).
     Further, for model data the denominator equals `(x₂²-x₁²)/λ` (`risk_pair_denominator_eq`), so it
     also vanishes at `x₁ = -x₂`: the nondegeneracy premise is a genuinely separate hypothesis.
  3. Auto-bound variables default to `ℕ` when the statement does not force `ℝ`:
     `theorem … (hw : 0 ≤ w) (hx : x ∈ Set.Icc (-w) w) : x^2 ≤ w^2` silently elaborated over `ℕ`
     (Nat division!) and the call from an `ℝ` context failed with a metavariable type mismatch; the
     same trap made `risk_best_line_halves` elaborate as `lam w : ℕ`. Fix: annotate **every** binder
     (`(lam w : ℝ)`), even when a later hypothesis looks like it pins the type.
  4. `field_simp` does not always discharge its own denominator side goals; carrying explicit
     `(4:ℝ)*lam ≠ 0` / `(8:ℝ)*lam ≠ 0` (or `by positivity` when a `0 <` hypothesis is present) makes
     `field_simp; ring` work every time in this file.
  5. Guessed-but-unresolved names (verbatim `unknown constant` from the API sweep):
     `Real.sqrt_lt_iff_lt_sq`, `Real.sq_le_sq` (the real name is the root-level `sq_le_sq`),
     `Set.mem_Icc_iff`. Deprecated (warning, not error) in mathlib v4.17:
     `div_le_div_iff` → use `div_le_div_iff₀`, `div_le_div_right` → `div_le_div_iff_of_pos_right`,
     `div_le_div_left` → `div_le_div_iff_of_pos_left`.
- 奏效：
  1. Form 3 (radius) — **two independent green routes**: (a) `div_le_iff₀ h4` to `w^2 ≤ tol*(4*lam)`,
     rewrite with `Real.sq_sqrt` to `(2*Real.sqrt (lam*tol))^2`, then `sq_le_sq` + `abs_of_nonneg`;
     (b) canonical `rw [bepRadius, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), div_le_iff₀ …, Real.le_sqrt hw h4nonneg]; ring_nf`
     (with `norm_num` closing `√4 = 2`). The `∀`-direction is tested at `x = w`
     (`Set.right_mem_Icc.mpr`); the window direction uses `abs_le.mpr` + `sq_le_sq` +
     `div_le_div_of_nonneg_right` + `le_trans`.
  2. Form 5 (equioscillation) delivered in the **requested `∃ x ∈ Set.Icc (-w) w` form** — the
     pre-registered disjunction fallback was not needed. Recipe: `set A/B/C`, second difference
     `A + C - 2*B = w^2/(2*lam)` by `field_simp; ring`, helper
     `A + B - 2*C ≤ |A| + |B| + 2*|C|` from `le_abs_self` + `abs_add` + `abs_neg` + `abs_mul`, then
     `by_contra h; rw [not_or] at h` (twice) + `rw [not_le] at h1 h2 h3` — **`push_neg` not needed** —
     and one `linarith` against `w^2/(8λ) + w^2/(8λ) + 2*(w^2/(8λ)) = w^2/(2λ)` (`field_simp; ring`).
  3. Form 7 corrected: `field_simp; ring` for `4λ(y₁-y₂) = 2λ(x₂-x₁) + (x₁²-x₂²)`, `nlinarith [hdiff]`
     for `λ*(…)`, then `rw [eq_div_iff hden]`. The sign defect is exactly one overall sign, so both
     conventions are provable (`risk_pair_solver`, `risk_pair_solver_alt`).
  4. Evidence practice: `#print axioms` *inside* the probe (18 lines, all
     `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) — the file prints its own kernel
     footprint, which is the no-`sorry` evidence for a file that lives outside `SOURCE_DIRS` and is
     therefore invisible to `check.sh --strict`.
- 可复用模式：**probe the statement, not only the proof.** A Sprint-0 probe that asks only "can I prove
  this?" misses the failure mode "the statement is false as written (sign/convention) or is missing a
  non-derivable premise"; put a *refutation* theorem (`∃ …, hypotheses hold ∧ conclusion fails`) next to
  every corrected form and a hypothesis-necessity witness next to every added premise. For `Real.sqrt`
  radius goals the recipe is `div_le_iff₀` + `Real.sq_sqrt` (+ `sq_le_sq`, `abs_of_nonneg`), with
  `Real.le_sqrt` + `Real.sqrt_mul` as an equally short canonical alternative; for equioscillation /
  minimax lower bounds it is `set` the residuals, prove the exact second difference, bound it with
  `le_abs_self` + `abs_add`, kill the negated disjunction with `not_or`/`not_le`, finish with `linarith`.

## 2026-09-20 — BEP round-1b: literature data table judged against the model (5 first-hand families; all fail the constant-λ curvature test) — literature_researcher — DONE

- Goal: fill the B5b data-table leaf of `theories/BEP/LITERATURE.md` (≥ 4 families × ≥ 2 `(driving force,
  barrier)` pairs in kJ/mol with provenance) **and** answer the lead's added question: is each pair
  *model-consistent* (does it admit a finite positive λ̂)? Result appended as §R1.10–§R1.12 (file now 848 lines).
- Worked (mirrors + API routes that actually served content when publishers 403'd): **Europe PMC REST
  `…/fullTextXML`** for OA tables (`PMC13405240`, `PMC5950756`) when the HTML table page is behind
  reCAPTCHA; **eScholarship / Edinburgh Pure** mirrors for the IUPAC glossary VoR (iupac.org + De Gruyter +
  goldbook = 403/empty); **Nobel Foundation PDF** for Marcus 1992; **CaltechAUTHORS** records for the 1968
  abstracts; **`api.crossref.org` + `api.unpaywall.org`** to prove `is_oa=false` before declaring `not-accessed`.
- Finding that changes the theory's reading: 5 first-hand families (*Antioxidants* **15**(7):840 (2026) Tables 1–2
  — 31/34 pairs, water vs pentyl ethanoate; *Chem. Sci.* **6**:5866 (2015) Table 1 CCSD(T) row — 5 sites).
  **All five admit per-pair λ̂ > 0** (water 61.5, PE 50.3, `•OOCH₃` 59.4/53.4, CCSD(T) 37.5 kcal/mol), **but every
  family's fitted curvature is negative** — and the model requires `d²Ea/dx² = 1/(2λ) > 0` for *every* λ > 0.
  So no positive λ reproduces any family's shape, while the *linear* BEP fit is excellent where the record
  reports it (R² = 0.934 / 0.548 / 0.934 / 0.952 for F1/F2/F3/F4 — F2 is the printed exception and F5 is
  not reported; three of the five families have a good linear fit)
  of five). Report this as a finding; **never** "fix" it by reporting a λ̂ as a measured reorganization energy.
  Also: the same substrates in a different solvent give a different λ̂ (Δλ ≈ 11 kcal/mol) ⇒ the family must be
  indexed by solvent too; and the per-pair λ is only identified up to the spurious small root.
- 试过且失败（记录以免下一轮重踩）：
  1. **A prior round of this role had already written the leaf** (round 1, §R1–§R1.9). My first two `write`
     calls were rejected ("file has not been read"), and two `edit` calls failed with "file changed since it was
     read" because that round's writer was still appending. Recovery: `cp` the file to `/tmp`, write the new
     sections to a scratch file, `cat >>` them onto the leaf with a `---` separator. **Pattern: when a leaf is
     co-authored across rounds, append; never rewrite, and always re-read before an `edit`.**
  2. **Option (b) of the dispatch (reuse the sibling records' MCC / reaction-centre numbers) is NOT viable as
     data**: those `x` values are *fit-derived inside the model* (λ = 1.20 eV from a figure annotation), so
     converting them to kJ/mol would pass model outputs off as measurements. Recorded as `not-accessed` for the
     pair table together with five other families that lack either the barrier or the driving force side.
  3. `archive.org` / HathiTrust / Google Books / `books.google.com` all time out from this sandbox (kills
     Semenov 1935/1958 and any Faraday Soc. 34 scan); `pubs.rsc.org`, `royalsocietypublishing.org`, `science.org`,
     `goldbook.iupac.org`, `degruyter.com`, `onlinelibrary.wiley.com/doi/pdfdirect`, `orbit.dtu.dk/files` are
     403/202 for both `curl` and the fetch tool ⇒ Evans–Polanyi 1938/1936, Bell 1936, Leffler 1953 bodies stay
     `not-accessed`. Search hits included libgen/sci-hub mirrors of them; **deliberately not used**.
  4. Semantic Scholar's API hangs (>300 s) in this sandbox and its Graph call timed out — use Crossref/Unpaywall/
     Europe PMC instead, and wrap every `curl` in `timeout` (a hung call also resets the bash session's cwd).
- Reusable pattern: **a literature data table is only a deliverable if every row carries a verdict** — here,
  per family: pairs + units + locus + `first-hand`, *plus* a model-consistency test with the test's own algebra
  printed. Report negative curvature as evidence, not as an error; and treat "is this number the model's input
  or its output?" as the first question for any candidate family (it disqualified three otherwise attractive ones).

## 2026-09-20 — BEP: API round on the dispatched statement list vs. the plan that landed mid-round — api_researcher — DONE

- Goal: furnish `theories/BEP/probes/bep-statement-skeleton.lean` (statement authority) plus `#check`
  probes for every name the BEP proofs need, and calibrate the risky rows before the provers start.
- Tried and failed (kept as banned names in the API log): `Real.sq_le_sq`, `Real.sqrt_lt_iff_lt_sq`,
  `Real.sqrt_four`, `Rat.castRat`, `Rat.decLe`, `Set.mem_Icc_iff`, `div_nonneg_iff_of_pos_right`
  (the strict `div_pos_iff_of_pos_right` exists, the `≤` version does not), bare `le_sqrt'`
  (it is `Real.le_sqrt'`); `div_le_div_iff` / `div_le_div_right` / `div_le_div_left` /
  `pow_le_pow_left` are deprecated (warning-only, so they must not appear in a 0-warning probe).
  Two tactic assumptions also failed: `by decide` on ℚ comparisons containing `/`
  (`Int.decNonneg✝` is not kernel-reducible, so `Rat.blt` never reduces) and `by norm_num` on
  `|q| ≤ r` over ℚ (no `abs` support). `native_decide` works but adds `Lean.ofReduceBool`, which is
  outside `ALLOWED_AXIOMS` — banned. `field_simp` sometimes closes a BEP field identity by itself,
  so the habitual `field_simp; ring` then errors with `no goals to be solved` (4 measured cases).
- Worked (and is now recorded with kernel evidence): the radius theorem
  `EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol`, the whole minimax block
  (`bepBestLine_error`, the equioscillation bound `bep_minimax_pointwise`, `epBestOnWindow_holds`,
  `bepLine_worst_case`, `bepBestLine_halves`), the exactness pair
  `not_epLinearOn_of_ne_zero` / `EPExact ↔ lam = 0`, all nine `epZone_eq_*_iff` rows, the ℚ
  reconstruction theorem, and the literal `sSup` sharpness form (with the explicit `BddAbove`
  witness `le_csSup` needs — `sSup` of an unbounded set is `0` in ℝ, so a missing boundedness proof
  silently falsifies the statement). One genuine formula defect was caught and corrected:
  `bepDefect_even` is **false** without `lam ≠ 0` (the draft probe stated it unconditionally and the
  kernel rejected it), while `epConformsOnWindow_symm` survives because it carries `0 < lam`.
- Reusable pattern 1 — **the dispatch text is not the statement authority.** Mid-round the lead's
  `theories/BEP/plan.md` landed with a richer spec (9-constructor `EPZone`, linear-response
  `transfer`, `qLamOfPair`, `EPQVerdict`) than the original dispatch list. The right move was to
  regenerate the skeleton plan-aligned rather than to deliver a second, conflicting authority, and to
  keep the old dispatch's names only where the plan is silent (the `sSup`/second-difference AUX
  block). A skeleton that disagrees with the plan costs every prover a round trip.
- Reusable pattern 2 — **calibrate the *definition bodies* first, then the theorems.** The
  `transfer` body change (TS-coordinate → linear-response) inverted the direction of several rows:
  a `rfl` bridge became a theorem needing `lam ≠ 0`, and a solver's numerator sign flipped the
  meaning of the whole ℚ layer (`x₁² - x₂²` returns `-λ`). Kernel counterexamples at concrete
  rationals (`norm_num`-closed `example`s) are the cheapest way to pin this down: they are one line
  each, they are re-checked on every toolchain bump, and they make the drift entry in the API log
  unarguable.
- Reusable pattern 3 — **the API probe should state the *risky rows verbatim*, not a toy analogue.**
  Where a probe proves the actual delivery-shaped statement (radius theorem, minimax optimality,
  nine classifier rows), the prover's job collapses to transcription; where it proves a weaker toy
  version, the prover re-derives the hard part and the probe's evidence does not transfer.

## 2026-09-20 — BEP round-1c: the quadratic barrier law is **Marcus 1968 eq. (2) p. 891**, *not* Marcus 1956; and Cohen & Marcus's strict range clause `|A| < λ` — literature_researcher — DONE (record §R1.13)

- Goal: independently verify a delegated claim that Marcus 1956 (the two-parabola paper) contains **no**
  quadratic barrier formula, and pin the printed equation numbers of the coefficient formula.
- Verified first-hand, reproducibly: `pdftotext` plain / `-layout` / `-raw` on
  `theories/Marcus/literature/Marcus1956_ET_theory_I.pdf`, whitespace collapsed, case-insensitive —
  `parabola` 0, `intersect` 0, `quadratic` 0, `slope` 0, `alpha` 0, `Bronsted` 0, `Polanyi` 0, `Bell` 0,
  `Semenov` 0; `Evans` 1 (footnote 9(b) = Eley & Evans, *TFS* **34**, 1093 — a *solvent* paper on p. 1093 of
  the same volume, not the BEP paper on p. 11); the only `(1 + …` strings are dielectric (`E*(r) = E_t*(r)/(1+4πa…)`).
  ⇒ 1956 has the barrier derivation (Eq. (38), p. 974) but **neither the quadratic law nor its slope**.
  The law's home is **Marcus 1968 Eq. (2), printed p. 891**: `ΔF* = w_r + λ(1 + ΔF⁰'/λ)²/4`.
- ★ The most useful new locus of the whole survey: **Cohen & Marcus 1968, Eqs. (5a)–(5c), printed p. 4250**
  (full issue scan `lib3.dss.go.th/.../j.of_physical_1968_v72_n12.pdf`, 60 MB, HTTP 200; `printed = PDF + 3938`):
  `a = ½[1 + (A/λ)] (|A| < λ)` (5a), `a = 0 (A < −λ)` (5b), `a = 1 (A > λ)` (5c), with `A = ΔF°' + RT ln(s_r/s_p)`
  (their eq. (2), p. 4249) and footnote 9's "we have excluded work and steric terms".
  Consequences: (i) the affine coefficient's range clause is a **strict inequality** and is printed;
  (ii) the **endpoint values 0 and 1 are the outside-range behaviour**, so the model's `(0,1) ⟺ |x| < λ`
  is a statement about *where the linearization is being used*, not a law about families (reinforces §R1.11);
  (iii) the model's `x` corresponds to `−A`, residual work terms excluded exactly as the model does.
- 试过且失败 / 教训：
  1. **A "verified (sibling record)" status does not survive a new question.** The sibling record had already
     noted "1956 contains no slope/α/Brønsted/inverted", but the *new* question — "does 1956 contain the
     quadratic barrier?" — still produced a mis-citation candidate in the plan, and needed its own grep set
     (`parabola`, `intersect`, `quadratic`, plus a whitespace-tolerant pattern for `(1 +`). **Extend the
     negative grep whenever a formula is attributed, not only when a name is.**
  2. Ranked greps hide hits: a first pass for `parabola` missed `parabolas`; the decisive Appendix II
     sentence is plural. Use case-insensitive **substring** counts, not word matches.
  3. `pdftotext` on a 60 MB whole-issue scan works, but extract with `-f/-l` page windows and verify the
     page map from running heads before quoting a page number (here `printed = PDF + 3938`; the earlier
     §n3 scan used `+766`) — **the offset differs per volume/issue**.
- Reusable pattern: **when a formula is attributed to a classic paper, grep the formula's *shape* (and its
  OCR variants) in the full text before trusting the attribution**; and prefer the paper's own *body*
  equation over its abstract rewriting (the abstract of Cohen & Marcus normalizes by `ΔF₀* = λ/4`, while
  eq. (5a) prints the strict range clause that the formalization actually needs).

## 2026-09-20 — BEP round-1d: `β = 1/2` has a published disclaimer; Denisov 2012 rows are model-derived and circular — literature_researcher — DONE (record §R1.14)

- Goal: verify a delegated new source that bears on the plan's `α(0) = 1/2` claim, and rule on whether a
  newly offered data family may enter the instance layer.
- Verified first-hand: Ooka, Huang & Exner, *Front. Energy Res.* **9**, 654460 (2021), DOI
  `10.3389/fenrg.2021.654460`, gold-OA PDF (HTTP 200), **page map exact** — the running footers print the
  Frontiers pagination, so printed page = PDF page for all 20 pages. Printed **p. 10**: "β = 0.5 is a
  frequent assumption, **although there is no physical basis for why β should be 0.5 or why it should be
  independent of the material**", "no basis for why β should be **constant throughout the various
  elementary steps**", and "**a negative BEP coefficient, which is a direct contradiction to the
  assumption of 0 < β < 1**"; printed **p. 9**: the BEP relationship "is in **direct contradiction to the
  Marcus theory of electron transfer**"; printed **p. 7**, their eq. (2): `ΔG‡_RI = (λ + ΔG_RI)²/(4λ)` —
  verbatim the model's law with `ΔG_RI = −x`.
- Anti-circularity ruling: the `(ΔH, Ee)` table of Denisov et al. 2012 (`Russ. Chem. Rev.` **81**, 1117,
  Table 6, pp. 1125–1126) is **computed from that review's own intersecting-parabola equations (23)–(24)**;
  any two-point slope computed from it (delegated: ≈ +0.50…+0.56 saturated, ≈ −0.74 across to allylic C–H)
  measures **the same functional form that produced the table** ⇒ **must not enter the instance layer as
  `provenance: literature` data**, only as an algebra self-consistency check. The F1–F5 families of §R1.10 are
  unaffected (their barriers come from DFT/CCSD(T), a different theory from the parabola law).
- 试过且失败 / 教训：**"first-hand numbers" is not the same as "independent measurements".** Three candidate
  families looked attractive on a citation basis and had to be rejected for three different reasons — MCC/RC
  (`x` is *fit-derived inside the model*), Denisov (`Ee` is *computed by the same parabola model*), npj-HER
  (only *fitted parameters*, points in a figure). Before adding any row to a data-validation table, ask:
  **is the printed quantity an input to, an output of, or independent of the law being tested?**
- Reusable pattern: for any "is this constant universal?" claim in a plan, the decisive literature citation
  is usually a sentence of the form "X is a frequent assumption, although there is no physical basis for …".
  Grep for `no physical basis` / `no basis for` / `frequent assumption` inside OA reviews of the field, and
  record the page — that sentence pattern is what turns a model convenience into a documented convention.

## 2026-09-20 — BEP round-1e: the `α ∉ (0,1)` outliers now have printed pages; `α` is a *partial* function of the family — literature_researcher — DONE (record §R1.15)

- Goal: settle verdict (ii) (`0 ≤ α ≤ 1`) with page-level counterexamples, and check whether the "family"
  premise needs strengthening.
- Verified first-hand:
  1. **Pogorelyi & Vishnyakova, *Russ. Chem. Rev.* 53(12):1154–1167 (1984), DOI
     `10.1070/rc1984v053n12abeh003145`, printed p. 1160** (free PDF `russchemrev.org/RCR3145pdf`, HTTP 200;
     the page header inside the text layer prints "1160 Russian Chemical Reviews, 53(12), 1984" — a *printed*
     page, not a PDF offset): "Anomalous values of the Brønsted coefficient (α < 0 and α > 1) are most
     characteristic of CH acids containing the nitro-group"; "α = −0.7 and β = 1.7 are anomalous";
     "α = 1.67, 1.61, 1.42, and 1.56 … for nitroalkanes R(CH₃)₂NO₂, ArCH₂CH(CH₃)NO₂, ArCH(CH₃)NO₂, ArCH₂NO₂";
     and the **new premise**: "**all systems with α > 1 included a fixed base. If the base is varied for the
     same nitroalkane, then the Brønsted coefficient returns to … 0 < α < 1**" ⇒ a substituent series and a
     base series are *different objects*; "family" must vary **exactly one parameter**.
  2. **Mayr & Ofial, *Isr. J. Chem.* 63:e202300054 (2023), printed pp. 7–8** (LMU repository copy 200; Wiley
     watermark gives the page range): "nitroalkanes have α values around 1.5 … **α is not limited to the range
     0 < α < 1**, and therefore cannot be an indicator of the position of the transition state"; and
     "**in identity reactions … δΔG_r° = 0 with the consequence that α = δΔG‡/0 = ∞**" ⇒ the empirical
     coefficient is a **partial function**: any "coefficient read off a family" needs an explicit
     non-degeneracy hypothesis (the analogue of the repo's existing `h : x₁ ≠ x₂`).
- 试过且失败 / 教训：**`russchemrev.org/RCR<nnnn>pdf` and LMU `epub.ub.uni-muenchen.de` served content where
  the publishers did not** (RSC/ACS/Wiley/De Gruyter all 403/202 here) — but the LMU path must be taken from
  the Unpaywall `oa_locations` record verbatim; a hand-guessed filename 404'd. Also: a repository copy of a
  Wiley article can carry a **watermark with the printed page range**, which is the cheapest reliable page
  locus for an article-number-style citation (here pp. 7–8 for `e202300054`).
- Reusable pattern: when a plan asserts a **bound** on a physical coefficient, hunt for (a) one source printing
  values *outside* the bound, (b) one source stating *when* the bound fails, and (c) one source printing the
  bound itself with its domain. Here (a)+(b) came from the same page of a 1984 review, and (c) turned out to be
  electrochemical (Inzelt p. 36) — i.e. **the bound's name migrated between subfields, which is exactly the
  kind of naming import a formalization record must flag rather than inherit.**

## 2026-09-20 — BEP follow-up: plan §8.1 model-consistency block + §8.2 instance table (I1–I12) — api_researcher — DONE

- Goal: extend the frozen statement skeleton with the second divided difference / three-point
  consistency block and the whole instance table, every row kernel-checked before the provers see it.
- Tried and failed: a first draft of the falsification rows interleaved the data arguments
  (`qModelConsistent3 lam x₁ e₁ x₂ e₂ x₃ e₃`) although plan §8.1 defines `qModelConsistent3 lam x₁ x₂ x₃
  e₁ e₂ e₃` (all abscissae first) while `qSecondDividedDiff x₁ e₁ x₂ e₂ x₃ e₃` interleaves `(x, e)`
  pairs — two sibling signatures with opposite conventions in the same plan section. Also: the plan's
  §8.2 I8 row still prints `α = 0`, a leftover of the discarded transition-state body (the delivered
  body gives `1/2`), and F4 (Table 2 "PE") has no per-row data in `LITERATURE.md` §R1.10 at all.
- Worked: `len 4` recipes, all `norm_num`-closed — the verdict rows need only
  `unfold epQVerdict qTransfer; norm_num` (norm_num reduces the six-branch `if`-chain of concrete
  rational comparisons on its own), the literature rows use **decimal** ℚ literals verbatim from the
  source (`(15.6 : ℚ)`, `(0.3 : ℚ)`), and the falsification rows are
  `rintro` + `qModelConsistent3_curvature_pos` + a `show … by unfold …; norm_num` negative value +
  `norm_num at hpos`.
- Reusable pattern 1 — **the same plan section can mix argument conventions.** When two signatures are
  transcribed from one section, check each call site against the definition, not against the
  neighbouring theorem; the kernel only reports the mismatch three arguments later (our failure showed
  up as `0.9 ≠ 15.7` inside a distinctness side goal).
- Reusable pattern 2 — **a corrected body invalidates the *values* of older instance tables.** The
  `transfer` body change silently made the I8 "α = 0" cell false; the instance round is where such
  stale cells surface, so grep the instance table for every quantity whose definition changed, and fix
  the statement rather than adding a hypothesis that hides it.
- Reusable pattern 3 — **state exactly the data you have.** For a family whose source prints only
  aggregates (F4), the honest output is "no statement", reported with the reason; a `norm_num`-checkable
  statement can always be manufactured, and it would have been worthless.

## 2026-09-20 — BEP round-1f: a **bimodal (broken) EP line with non-constant λ** is now the record's violation family — literature_researcher — DONE (record §R1.16)

- Goal: close the last two gaps — a *documented* (not model-constructed) violation family, and a family whose
  driving force spans both signs.
- Verified first-hand:
  1. **Salamone, Galeotti, Romero-Montalvo, van Santen, Groff, Mayer, DiLabio & Bietti, "Bimodal Evans–Polanyi
     Relationships in Hydrogen Atom Transfer from C(sp³)–H Bonds to the Cumoxyl Radical…", *JACS*
     143(30):11759–11776 (2021), DOI `10.1021/jacs.1c05566`** — CC-BY full text via Europe PMC
     (`…/PMC8343544/fullTextXML`). Abstract, opening printed p. 11759, verbatim: "The log k_H′ vs C–H BDE plot
     shows **two distinct EP relationships**, one for substrates bearing benzylic and allylic C–H bonds
     (unsaturated group) and the other one, **with a steeper slope**, for saturated hydrocarbons, alcohols,
     ethers, diols, amines, and carbamates (saturated group)"; and "**A good fit to the Marcus equation is
     observed only for the saturated group, with λ = 58 kcal mol⁻¹**, indicating that with the unsaturated
     group **λ must increase with increasing driving force**". ⇒ the fixed-`λ` premise is a **default the
     literature contradicts**, the "same family" premise gets a page-level basis, and the instance layer has a
     real violation family. Per-substrate `(k_H, BDE)` are bitmaps in the OA copy ⇒ `not-accessed`, no numbers
     transcribed.
  2. **npj Comput. Mater. 10:98 (2024), SI Table 1** (`media.springernature.com/…/41524_2024_1244_MOESM1_ESM.pdf`,
     10 pp., HTTP 200) — 14 metals, **the only family in the record with both signs of x** (Bi −103.3 kJ/mol …
     Ni +27.0). **Read the SI's own header before using its α column**: "The α and ΔG₀‡ are **obtained from
     fitting experimental cyclic voltammograms** for computing ΔG‡_EXP" ⇒ those α values are *electrochemical
     transfer coefficients of individual electrodes*, **not** BEP slopes of the family's `(ΔG_H, ΔG‡)` scatter,
     so a delegated reading of "individual fitted BEP slopes 0.37–0.66" is **not** supported by the table
     itself. What the column legitimately shows is material-dependence **within one reaction class** (Co 0.37 …
     Rh 0.66), independently matching Exner's "ß may vary within a class of materials".
- 试过且失败 / 教训：**an SI table's extra columns are the most tempting place to over-read a source.** The α
  column looked like a ready-made "slope varies" datum; its own header says it comes from fitting CVs of a
  *different* observable. Before citing any digit from a table, read the **table title and footnotes in the
  same file** — not the caption quoted elsewhere.
- Reader warnings recorded for the next round: (i) the Denisov 2012 Table 6 text layer renders the **minus sign
  as the digit `7`** (`719.5` = −19.5) — misreading it flips exothermic rows to endothermic; (ii) a Wiley
  repository copy can carry a **watermark with the printed page range**, the cheapest reliable locus for
  article-number-style citations; (iii) `api.catalysis-hub.org` now demands an API key and MDPI 403s while
  Europe PMC serves the same OA text — don't re-discover these.

## 2026-09-20 — BEP round-1g: three distinct `α` objects, and coverage-dependence as a *kinetic* counterexample to constancy — literature_researcher — DONE (record §R1.17)

- Goal: settle how the plan may speak about "α" when the electrochemical literature is cited beside the
  model's own coefficient.
- Verified first-hand:
  1. **IUPAC Technical Report 2014, §5 Conclusions, printed p. 257** (read here in §R1.6.2 and independently
     re-read in round-1g via the same open repository route, Universidad de Alicante RUA DSpace 7; the page
     header inside the text layer prints "DOI 10.1515/pac-2014-5026  Pure Appl. Chem. 2014; 86(2): 245–258"):
     "The numerical value of the transfer coefficient `α` **can by no means be assumed**; it can only be
     obtained by measuring the Tafel slope"; and "**`αc + αa = n/ν` (43)** … The use of the cathodic symmetry
     factor … should be confined to an overall electrode reaction consisting **exclusively of a one-electron
     transfer step**." ⇒ the literature's complementarity is `n/ν`, so `α_f + α_r = 1` is a **single-electron /
     same-rds special case**, while our `transfer + reverseTransfer = 1` stays a model theorem.
  2. **Shinagawa, Garcia-Esparza & Takanabe, *Sci. Rep.* 5:13801 (2015), DOI `10.1038/srep13801`**, OA via
     Europe PMC `PMC4642571`, printed pp. 5–6, verbatim: "The Tafel slopes used to evaluate the rate
     determining steps generally assume extreme coverage of the adsorbed species (θ ≈ 0 or ≈1), although, in
     practice, **the slopes are coverage-dependent**"; and "**the same Tafel slopes can be obtained for
     different elementary steps with varied coverages**"; with measured slopes 30 / 120 / 125 mV dec⁻¹.
- Three `α` objects now separated with loci: (1) the **observable** electrochemical transfer coefficient
  (IUPAC *Recommendations* 2014 eq. (1), printed p. 259, `10.1515/pac-2014-5025`); (2) the **model's** BEP
  slope `transfer lam x = 1/2 − x/(2λ)` (a theorem); (3) the **Butler–Volmer symmetry factor** (equating it
  with (1) needs an extra premise — IUPAC TR printed pp. 255–256 predicts "large deviations of β from 0.5"
  when the two force constants differ; Fletcher 2009 needs a "conversion formula" — delegated).
- 试过且失败 / 教训：the plan-level risk was **naming collapse**, not a false statement. A reader who sees
  `α` in a theorem, `α` in an IUPAC quote and `β` in an electrocatalysis paper will silently equate three
  different objects. **Whenever a record cites a coefficient from a second field, write the defining equation
  and the observable it is measured from next to it** — here `α = (RT/F)(dE/dln|j|)⁻¹`, coverage-dependent,
  vs `∂Ea/∂x` of a model.
- Reusable pattern: for any "constant across the family" premise, look for **one thermodynamic and one kinetic**
  counterexample; they fail for different reasons (unequal force constants / non-constant λ vs coverage, site
  and RDS changes) and the plan's caveat must name both, or a reader will test the premise in the wrong regime.

## 2026-09-20 — BEP round-1h/1i (closing): premise-set anchor, branching LFER verified, and the `efetch` fallback — literature_researcher — DONE (record §R1.18–§R1.19)

- Goal: fold the last delegated items into the record after re-verifying each load-bearing one.
- Verified first-hand:
  1. **Migliore, Polizzi, Therien & Beratan, *Chem. Rev.* 114(7):3381–3465 (2014), §6.2** (OA `PMC4317057`) is
     the **single printed anchor for the model's whole premise set**: "For a homologous set of reactions with
     **approximately equal reorganization energies and work terms** …"; "Equations 6.23 and 6.24 **hold if the
     reorganization energy is constant for a reaction series**"; failure branch "**∂λ/∂ΔG_R°** … describes the
     variation in the intrinsic barrier".
  2. **Salamone et al. *JACS* 143:11759 (2021)** Figure 3 caption, read verbatim: saturated branch **α = 0.39**,
     **ΔG‡₀ = 13.9 ± 0.6 kcal/mol**; unsaturated **α = 0.23**, **ΔG‡₀ = 14.3 ± 0.7**; Marcus fits
     **λ = 58 ± 1** vs **76 ± 1 kcal/mol**, and for the unsaturated branch the fit "**does not match the slope of
     the data**" ⇒ slope, intercept *and* λ all differ between branches of one 56-substrate experimental family.
  3. **Huang & York, *PCCP* 16:15846 (2014)** — a **branching** Brønsted correlation in RNA transesterification
     ("convex break at pKa of 12.58"; β_lg1 = −0.52 vs β_lg2 = −1.34) ⇒ third independent field with a
     piecewise LFER and slopes outside `(0,1)`.
  4. **"Breaking the BEP Relation with Dual-Metal Sites", *J. Phys. Chem. Lett.* 16:11302 (2025)** — "mixed
     low-affinity/high-affinity coadsorption … **decoupling the step responsible for the activation energy at
     the low-affinity site from the overall reaction energy determined by both sites**" ⇒ measured justification
     for the "same site" premise.
  5. **Mayr & Ofial 2023 p. 1**: the diffusion-control criterion is about the **reverse** step ("Hammond referred
     to SN1 reactions … if the reverse reaction is diffusion-controlled") ⇒ the model's α = 0 at x = λ must not
     be sold as a diffusion plateau.
- 试过且失败 / 教训（本轮最有价值的可复用点）：**when Europe PMC's `…/PMC<id>/fullTextXML` returns HTTP 500
  (or `oa.fcgi` 404s after the service migration), the NCBI EUtils route still works**:
  `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=pmc&id=PMC<id>&rettype=xml`. Two of this round's
  three verifications (`PMC4366550`, `PMC12581165`) were only possible through that fallback — try it before
  declaring an OA article `not-accessed`.
- Also recorded as standing negatives: the sentence "constant entropy of activation is required for a linear BEP"
  has **0 first-hand hits** (it can only be synthesised from the glossary's entropy-of-activation /
  compensation-effect / isokinetic-relationship entries), and the textbook line "diffusion control ⇒ Ea =
  viscous-flow activation energy" is likewise uncited. **A premise with no source must be declared as
  assumption-only, not dressed with a citation.**

## 2026-09-20 — BEP B1+B2: description layer + law layer (`Basic.lean` 33 declarations, `Criterion.lean` 28) — prover_a — DONE

- 目标：deliver the BEP description layer (definitions `eact` / `bepLine` / `bepDefect` / `transfer` /
  `reverseTransfer` / `secSlope` / `bepRadius` / `bepBestLine` / `EPBounds` / `EPLinearOn` / `EPExact` /
  `EPConformsOnWindow` / `EPBestOnWindow` / `EPZone` / `epZone` / `EPRegime` / `EPConforms` /
  `EPDescriptor` plus the 15 `epZone_eq_*_iff` rows; plan §4.1–§4.2, commits `793fd28`…`b2e3fd2`) and the
  law layer (`eact_expansion`, `bepDefect_eq`, the two thermoneutrality rows, `transfer_eq_tsCoord`,
  `transfer_thermoneutral`, `reverseTransfer_thermoneutral`, `transfer_add_reverse`,
  `reverseTransfer_eq_transfer_neg`, `secSlope_eq_transfer_mid`, `secSlope_midpoint_invariant`,
  `eact_neg_eq_add`, `eact_antitone`, `bepDefect_nonneg`, `bepDefect_pos_iff`, `epDescriptor_holds`,
  `epDescriptor_conforms`, `epConforms_iff_bounds`, the non-vacuity suite; plan §5, commits
  `07cfb54`…`4a23c9f`), every signature word for word with
  `theories/BEP/probes/bep-statement-skeleton.lean`.
- 试过且失败（七条，全部实测；前三条是语句层面的，后四条是战术/工具层面的）：
  1. **plan §4.2 row 4 `transfer_zero_lam` is FALSE as handed over.** The delivered body is the
     linear-response coefficient `transfer lam x = 1/2 - x/(2*lam)`, and Lean's division is totalised, so
     at `lam = 0` the second term is `x/0 = 0` and `transfer 0 x = 1/2`, **not** `0` — the `0` belonged to
     the discarded transition-state-coordinate body. Kernel counterexample produced before any proof work;
     the row was corrected to the linear-response value in plan §4.2, pushed to `api_researcher`, and the
     same body change silently made the plan §8.2 I8 cell "`α = 0`" false (it is `1/2`). Lesson: a
     statement-first probe is worth exactly the counterexamples it produces.
  2. **`nlinarith` cannot close `eact_antitone` from the plan's sketch.** Goal after `unfold eact`:
     `(lam - x₂)^2 / (4*lam) < (lam - x₁)^2 / (4*lam)` under `0 < lam`, `x₁ < x₂ ≤ lam`; `nlinarith` has no
     handle on the division's positivity side condition and returns either a wrong-direction square
     comparison or a nonlinear blow-up. **What works** (delivered body): `have h4 : (0:ℝ) < 4*lam := by
     linarith`, `rw [div_lt_div_iff_of_pos_right h4]`, then `exact (sq_lt_sq₀ h0 h01).2 hlt` with
     `h0 : 0 ≤ lam - x₂`, `h01 : 0 ≤ lam - x₁`, `hlt : lam - x₂ < lam - x₁` all by `linarith`. Note
     `sq_lt_sq₀` (the `0 ≤`-hypothesis form) rather than `sq_lt_sq`: no `abs` appears, so no
     `abs_of_nonneg` glue is needed.
  3. **`decide` is unusable on the ℝ-side classifier goals, and `native_decide` is banned by the
     contract.** `epZone lam x = EPZone.exergonic ↔ 0 < x ∧ x < lam` is a `Prop` over `ℝ`; `decide` cannot
     reduce it because `Real.decidableEq` / the `Real` order instances block kernel reduction (measured as
     a "failed to reduce" error, not a timeout). The working route for the whole `epZone` family is
     `unfold epZone; norm_num` (plus `split_ifs`/`by_cases` where a guard must be *used*, and `linarith`
     only where the arithmetic is genuinely symbolic); the ℚ twins in B5a close the same way.
  4. **`field_simp` sometimes closes the goal by itself, and a following `ring` is then a hard error**
     ("no goals to be solved"), not a harmless no-op — so `…; field_simp; ring` is *not* a safe universal
     idiom in this toolchain. Recipe used: write `field_simp` alone, check what remains, add `ring` only
     where something remains (never a bare `try ring`, which would swallow real failures).
  5. **`if`-cascade guard-level trap.** Rewriting an equation (`x = 0`) into an already-unfolded cascade
     hits the *guards* as well as the branches, and `split_ifs` assigns case names in the cascade's own
     order (here `degenerate` is consumed first, before any `x` is inspected) — so a "natural" rewrite
     order can produce side goals in which the guard hypothesis is the wrong one. Discipline that worked:
     `unfold` the definition first, then `split_ifs`/`by_cases` and discharge each guard with the
     hypothesis that actually replaces it, never a blind `rw` into the cascade.
  6. **Delivery-driver self-swallowing.** The driver that assembled the delivered module out of the
     skeleton's blocks matched its own output file in its input glob, so a second run read the
     already-assembled file (re-emitting headers and, in one direction, growing). Fix: exclude the
     destination path from the source set and always extract from the statement authority only. A variant
     of the same driver appended the namespace's `end` while the extracted block already carried it →
     `unexpected token 'end'`; emit `end` exactly once, with the skeleton's own tail as the reference.
  7. **`set_option linter.unusedVariables false in` placement rule.** The option must sit immediately
     before the declaration it modifies; inside a namespace/section it applies to the *next* declaration
     only and must be repeated for each one, and adding a docstring between the option and the declaration
     is fine while putting the option after the docstring is not. A misplaced option either fails to parse
     or silently fails to cover the theorem it was meant for.
- 奏效：`PhotoLean/BEP/Basic.lean` (33 declarations) and `PhotoLean/BEP/Criterion.lean` (28) delivered,
  0 fidelity differences against the skeleton (`theories/BEP/probes/bep-fidelity.py`), worker gate PASS
  (`lake build` per module + `proofs/scripts/check.sh --strict` + `proofs/scripts/axioms.sh` on every
  declaration: only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`); both files carry their
  physical assumptions (`lam ≠ 0`, `0 < lam`, `h ≠ 0`, `x ≠ 0`) as explicit hypotheses and none in a
  definition. Handed to the independent verifier as one batch with `RatModel.lean`.
- 可复用模式：**prove the statement's premises before the statement's conclusion.** Two of the seven
  failures were kernel counterexamples to the *handed-over text* (a totalised-division body change and a
  stale cell downstream of it) — both were caught by rewriting the body into a probe first. On the tactic
  side the reusable pair is: "reduce `div`-comparisons with `div_lt_div_iff_of_pos_right` and finish on a
  nonnegative square lemma (`sq_lt_sq₀`), and never assume `field_simp; ring` is a safe compound motif —
  `field_simp` may already be done, and a leftover `ring` is an error."

## 2026-09-20 — BEP B4: microscopic + cross-module layer (`PhotoLean/BEP/Compose.lean`, 12 declarations) — prover_b — DONE

- 目标：deliver plan §7: rows 1–6 bridge the BEP description layer to the two delivered two-parabola
  modules (`Marcus.Basic`, `Hammond.Basic`), rows 7–12 compose the reorganization energy out of an inner
  and an outer part (`lam = lamInner + lamOuter`) and show that a larger total reorganization energy
  shrinks the violation and widens the conforming window. Statements word for word with the B4 block of
  `theories/BEP/probes/bep-statement-skeleton.lean`; commits `6dcb691`…`b3569c3`.
- 试过且失败：
  1. **The two definitional bridges are `rfl`, and tactics are wasted on them.** `Marcus.barrier` and the
     BEP `eact` are *definitionally equal* (identical bodies, independently stated), so
     `eact_eq_barrier : eact lam x = Marcus.barrier lam x` is `:= rfl`; the same `rfl` settles
     `rate_eq_exp_neg_eact` (the delivered Marcus rate descriptor written through the BEP barrier). Any
     `unfold`/`ring` attempt on these two goals is dead work; and a trailing tactic on an `rfl`-closed goal
     is a hard error.
  2. **Rows 9–11 could not quote the plan §6.3 helpers because `Sharp.lean` did not exist yet** (B3 was
     still being proved by another owner, and importing it would have introduced a cross-milestone
     dependency). The three rows were therefore **derived locally from `PhotoLean.BEP.Basic`** while keeping
     the plan's hypothesis shape (including the hypotheses the proofs do not consume, e.g.
     `hli : 0 ≤ lamInner` in `bepRadius_add`): `Real.sqrt_le_sqrt` + `mul_le_mul_of_nonneg_right` for the
     radius monotonicity, and the radius/window criterion by **squaring** (`Real.sq_sqrt` + `sq_le_sq` +
     `abs_of_nonneg`) instead of through the not-yet-available `epConformsOnWindow_iff_radius`.
  3. **`field_simp` refinement.** `field_simp` does not invent the nonvanishing side conditions of the
     defect identity, so unfolding `bepDefect eact bepLine` separately at each use site leaves side goals it
     cannot discharge. Refinement that made rows 10–11 close: prove **one local `key` lemma**
     `∀ L x : ℝ, L ≠ 0 → bepDefect L x = x^2/(4*L)` by `intro L x hL0; unfold bepDefect eact bepLine;
     field_simp; ring`, then reuse it everywhere with `ne_of_gt` supplying `L ≠ 0`; the remaining
     `div_le_div_of_nonneg_left` / `sq_le_sq` steps then see a clean `x^2/(4*L)` form.
- 奏效：all 12 rows delivered; `Compose.lean` imports only `BEP.Basic` + `Marcus.Basic` +
  `Hammond.Basic` (no `Sharp`, no `Marcus.Compose`, no Pekar machinery), the microscopic hypotheses
  `0 < lamInner` / `0 < lamOuter` are explicit premises of every statement that needs them, gate PASS
  (12/12 `#print axioms` clean, 0 fidelity differences), handed to the verifier together with B2.
- 可复用模式：**check definitional equality before reaching for a tactic** (a cross-module bridge between
  two independently stated modules is often literally `rfl`), and when a dependency milestone has not
  landed, derive the two or three helper rows locally from the earliest module instead of importing a file
  that does not exist — then hoist any repeated `field_simp` identity into one local lemma whose
  nonvanishing hypothesis is explicit.

## 2026-09-20 — BEP B5b instance cross-check script (`theories/BEP/probes/bep-instance-check.py`, non-Lean) — prover_a — DONE

- 目标：give the verifier an evidence chain for the future `PhotoLean/BEP/Instances.lean` that does **not**
  go through the delivered Lean theorems: recompute in exact rational arithmetic (`fractions.Fraction`
  only) every number the instance layer will assert — `alphaObs`, `lamOfPair`, the second divided
  difference, the six-branch `epQVerdict` verdict, the I1–I10 model-constructed rows and the §R1.10
  literature families — from `theories/BEP/LITERATURE.md` §R1.10, and exit 1 with a per-number diff if a
  Lean-side literal in plan §8.2 or the skeleton's B5b block disagrees. 280 Lean-side values checked;
  result `CROSS-CHECK: OK`, exit 0.
- 试过且失败（脚本自身的三个实测缺陷，全部只有靠"算出来的数不对"才发现）：
  1. **A helper mirroring Lean's totalised division leaked floats.** `qdiv(a, b) = F(0) if b == 0 else
     a / b` looked exact, but with the *int* literals of `qTransfer` (`qdiv(1, 2)`) Python does **float**
     division, so `qTransfer 3 2` returned `0.16666666666666669` and every downstream comparison was
     silently inexact (it happened to pass for 1/2, 3/8, 3/4 and failed for 1/6, which is what exposed it).
     Fix: coerce both arguments (`a, b = F(a), F(b)`) inside the helper — with an exact-rational mirror,
     "the value looks right" is not evidence, `==` against a `Fraction` is.
  2. **`str(Fraction)` is `4/5`, not `0.8`**, so a token-level read-back of the record's prose
     ("does the value printed there equal mine?") was vacuously true/false for every non-terminating
     decimal. Fix: render with an explicit decimal formatter before searching the record.
  3. The first version read the record only through my own transcription. Now the script **re-reads
     §R1.10** (section [1b], 133 cells: every `(ΔG°, ΔG‡, kJ/mol, λ̂)` cell of F1/F2/F5, the aggregate rows
     of F3/F4, F3's prose rows, the family means/ranges) and a mismatch is a hard failure, so a stale
     transcription can never silently invalidate the cross-check. Verified by mutating a copy of the
     record: the run then exits 1 naming the exact cell.
- 奏效：`python3 theories/BEP/probes/bep-instance-check.py` → exit 0, `CROSS-CHECK: OK`, 280 checked values,
  a final paste-ready table (`family | alphaObs | lamOfPair | sdd-sign | verdict | provenance flag`) and
  explicit `UNSUPPORTED` lines for F4 (aggregate-only) and for the six §R1.10.7 families (no pair data);
  the script also refuses to invent per-point rows and states per number whether it is `kcal/mol`,
  dimensionless or `1/(kcal/mol)`.
- 可复用模式：**an independent check must also check its own input.** Two classes of finding came out of
  this that no proof gate would see: (i) transcription/drift (fixed by re-reading the source file, 133
  cells, hard-fail on mismatch), and (ii) source-arithmetic defects — §R1.10.5's printed per-row `λ̂`
  column is wrong for two of five rows (R4 prints 41.6 where the model quadratic's larger root is
  ≈34.640112; R5 prints 32.5 where it is ≈36.468035), while that family's summary (mean 37.5, range
  32.5–44.0) matches the correct roots, so the defect is confined to those two cells. Also recorded:
  §R1.10's "curvature" is used with the quadratic-coefficient convention (`λ = 1/(4·curvature)`, matching
  the Lean `qSecondDividedDiff = 1/(4λ)`) although §R1.10.1's prose writes `d²Ea/dx² = 1/(2λ)` — a factor-2
  labelling question that does not change the verdict (negative curvature ⇒ no positive λ), and the
  literature-side findings were reported to the lead rather than "fixed" in the record.

## 2026-09-20 — BEP round-1j: the AUDIT-FAIL was real, and the *checker's own ledger* is a second, hidden copy of the data — literature_researcher — DONE (record §R1.10.5 + §R1.10.1)

- Goal: fix the two flagged λ̂ cells of §R1.10.5 and relabel the two curvature conventions, without touching
  anything else.
- Result: **the flag was correct.** The 2-butanol CCSD(T) family's printed rows are `(ΔE, V‡f)` in kcal/mol =
  (7.62,12.38), (13.14,17.57), (14.56,17.47), (15.80,20.32), (19.82,21.72) (re-read from the source table itself,
  `PMC5950756` Table 1). With the single convention `x = −ΔE` the large roots of `λ² − (2x+4Ea)λ + x² = 0` are
  32.493019, 39.644841, 34.640112, 44.007305, 36.468035 (mean 37.4507, range 32.493–44.007) ⇒ the cells
  `R4 = 41.6` and `R5 = 32.5` were wrong; R1/R2/R3 were within rounding. The family summary was already right,
  which is how the error survived: the summary was computed from the *correct* roots while two table cells were
  not (the wrong `R5` cell even coincides numerically with the correct `R2` root, 32.4930).
- 试过且失败 / 教训（本条是本轮最有价值的东西）：
  1. **A cross-check script can hold a second copy of the data.** After correcting the record, the script still
     failed — because *its own* hardcoded transcription (`F5.aggregates["printed_lam_hat"]`, and the F5
     `aggregates=dict(mean=…, range=…)` ledger) still encoded the old cells, and its read-back step compares the
     record against that ledger. **Lesson: when a record and a checker disagree, decide which side is stale and
     fix both; a "fix the record only" edit leaves the gate failing and looks like a new defect.**
  2. **Never assert a cause you have not reproduced.** I first wrote "those two cells used the opposite sign
     orientation" — that reproduces `R5` exactly (`λ̂(x=+19.82, Ea=21.72) = 32.4930`) but **not** `R4`
     (41.6 is not reproducible from R4's own two numbers under any sign/column permutation tried). The note now
     says so explicitly instead of inventing a tidy diagnosis.
  3. **The large root is not sign-invariant** (`x + 2Ea + 2√(Ea²+x·Ea)`), and I briefly "verified" the wrong
     invariance by comparing `λ_+(−x)` with `λ_+(x)` through a mislabelled helper. A one-line print of both
     branches would have caught it immediately — print the quantity, do not reason about it.
  4. Prefix `grep` probes with `-a`/count guards: a `grep -c` on a large binary-ish log emitted a broken-pipe
     write error that nearly hid the final status line.
- Reusable pattern: **a numeric record that a script audits must state its convention once and in-tree.** The
  record already implied two normalizations (`d²Ea/dx² = 1/(2λ)` in prose vs `λ = 1/(4·curvature)` in the tables),
  differing by exactly a factor 2; the verdict (negative curvature ⇒ no positive λ) is invariant, but the printed
  `λ` values are not. §R1.10.1 now carries a two-row convention-labelled table, and the script's own audit line
  for that check is back to `AUDIT-OK` with the label recorded.
- Verification: `python3 theories/BEP/probes/bep-instance-check.py` → **exit 0**, `17 audit check(s), 0
  AUDIT-FAIL`, `no disagreement: every checked value follows from the recomputation`, `CROSS-CHECK: OK`.

## 2026-09-20 — BEP B1+B2 post-verification comment-only wording round (token-stream gate) — prover_a — DONE

- 目标：close the independent verifier's documentation findings on `PhotoLean/BEP/Basic.lean` (B1) and
  `PhotoLean/BEP/Criterion.lean` (B2) — O2/O3 (the headers and `eact_at_zero` claimed every physical
  premise is needed by the statement, while the kernel proves three zone characterizations and both
  value lemmas without it) and O4–O8 (five B1 comments narrated B2/B3 results as if proved in B1) —
  while keeping the delivered token streams byte-identical, so the acceptance record still applies.
- 试过且失败（both failures are gate-design failures, not proof failures）：
  1. **A comment-strip check that silently passes on empty input.** The first version of the stripper was
     written to `/tmp` with the file tool, but the bash tool's `/tmp` is a different mount, so
     `python3 /tmp/strip_lean_comments.py …` failed on both sides; command substitution then produced the
     empty string for the pre- and post-edit hash, the two strings compared equal, and the shell printed
     `same=yes` — a **false PASS** on the one gate whose whole job is proving that the token stream did not
     move. Fix: recreate the script through the bash heredoc, print the stripped byte count, and require a
     non-empty hash; agreement between two empty strings must never be reported as evidence.
  2. **Rewrapping a comment can trip the strict scanner.** `check.sh --strict` greps
     `^[[:space:]]*axiom([[:space:]]|$)`, so the natural rewrap of the header ("… no custom\naxiom
     anywhere in this file.") put `axiom anywhere in this file.` at the start of a line: a strict-scan
     FAIL that has nothing to do with any proof. Fix: rewrap so that no line begins with `axiom` (and no
     `sorry` appears anywhere in the new prose); the hit was diagnosed from the scanner's regex, not by
     touching the proof.
- 奏效：A1–A4 in B1 (commit `90e7f15`), B1–B3 in B2 (commit `02a5a54`); token streams identical before and
  after — B1 `d2898dc4e1eb3cca6891c6cc3b774840234e11e1567718e24b3962f669490124`, B2
  `4a4eacda63828ea8ded7e5df41dc660f449cf6a77e418567f10044acba013535` (nested `/- -/`-aware stripper,
  string literals preserved, byte count printed alongside the hash);
  `check.sh --strict PhotoLean.BEP.Basic` and `… PhotoLean.BEP.Criterion` both `verdict: PASS`, scan
  `clean`; both commits are path-limited (`git commit -- <file>`), so the concurrent B4/B5a edits present
  in the working tree were not swept in.
- 可复用模式：
  1. **A no-op gate needs a negative control.** Any check comparing two derived artifacts must be run once
     against a *known* difference (mutate one token → the hash must change) and once against a
     known-equivalent difference (rewrite one comment → the hash must not change); otherwise an empty or
     erroring pipeline reports agreement. Print the artifact size, not only the boolean.
  2. **Comment-only does not mean gate-invisible.** The strict scan is a text grep, so prose rewording must
     be written against the scanner's regex; run the strip check *first* and the gate second, so that a
     scanner hit is attributed to the prose instead of being misread as a phantom proof regression.
  3. **Honesty wording must be kernel-backed per declaration.** Before writing "this hypothesis is
     decorative", prove the hypothesis-free form in a scratch probe (here `transfer_add_reverse`,
     `bepLine_exact_at_thermoneutrality`, `bepDefect_at_thermoneutrality`, each closed by
     `rcases eq_or_ne` + `field_simp; ring`): a reworded claim is a new claim and the verifier checks it
     like any theorem.

## 2026-09-20 — B5b instance/verdict layer (`PhotoLean/BEP/Instances.lean`, 48 declarations) + the `qReverseTransfer_cast` bridge — prover_c — DONE

- Goal: deliver the whole B5b block of the statement authority (plan §8.2, rows I1–I12: I1–I8 three rows
  each, I9 four, I10 two, I11 four rows × four literature families, I12, `inst_nonvacuous`) with one
  commit per lemma, plus the missing `qReverseTransfer_cast` bridge in `RatModel.lean` (the delivery
  review's finding that `qReverseTransfer` was the only ℚ definition with no theorem constraining it).
- Delivered: 49 commits (1 bridge + 48 instances); **96 `verdict: PASS` lines** in the driver log
  (one `check.sh --strict` plus one `axioms.sh` per step) with **0** `FAIL|error|warning` lines; the
  official fidelity checker reports `delivered, word-for-word 191`, `not delivered yet 0`,
  `signature differences 0` (the whole BEP skeleton, not just this block).
- 试过且失败 (measured this round):
  1. **The file tool's `/tmp` is a different mount from the bash tool's `/tmp`.** The master copy was
     written to `/tmp/b5b-master.lean` with the file tool and then did not exist for the shell:
     `proofs/scripts/lake env lean /tmp/b5b-master.lean` → `file '/tmp/b5b-master.lean' not found`, while
     `ls /tmp` showed only what bash itself had created. Same defect prover_a hit in the B1/B2 wording
     round. The working scratch area is **`.lake/tmp/`**: gitignored, outside `SOURCE_DIRS`, and
     `lake env lean` resolves the imports of a file there.
  2. **Splicing a lemma into an existing file at the first matching line orphans the neighbour's
     docstring.** Inserting `qReverseTransfer_cast` before `theorem qSecSlope_cast` put the new block
     *between* the `set_option linter.unusedVariables false in` and the docstring that belongs to
     `qSecSlope_cast` (the option line + docstring + declaration are one unit, and a docstring after
     `set_option … in` still attaches to the next declaration, so the region silently re-associated).
     Fix: splice the whole unit at a statement boundary and re-read the region before building.
  3. `by decide` / `native_decide` stay unusable for this layer (re-confirmed, already known from B5a):
     every verdict goal contains a `/`-literal, and `native_decide` would add `Lean.ofReduceBool` to
     `#print axioms`. **No `norm_num`-closed row needed a fallback tactic** — the recipes measured by the
     API round closed all 48 rows on the first attempt, so this round produced no new tactic failures.
- Worked (reusable):
  - **Master copy + prefix emitter driven from `.lake/tmp`.** Keep the full intended file (with
    `-- @DECL: <name>` markers) in `.lake/tmp/b5b-master.lean`; a small Python driver emits
    "header + first k declarations + footer" into the delivered path, strips the markers, and runs
    build + `check.sh --strict` + `axioms.sh` + `git commit -- <path>` per step (≈6–7 s per step,
    48 steps). Compile the master standalone (`lake env lean .lake/tmp/b5b-master.lean`, 0 error /
    0 warning) **before** the first delivery: that is the statement-first gate for the whole batch.
  - **Fidelity before delivery, not after.** Re-run the `bep-fidelity.py` signature regex against the
    master: 48/48 signatures equal, 0 extras, 0 diffs on the first run — "word for word" becomes a
    measurement instead of a promise, and a typo in a literal is caught before any commit.
  - **Make the strict gate concurrency-tolerant, not narrower.** `check.sh --strict` scans all of
    `SOURCE_DIRS`, so a co-worker's transient placeholder makes *our* gate FAIL. The driver retries the
    check while the hits are outside our own file and fails immediately when our file is named
    (0 retries were needed, but one step took 52 s under concurrent build load — the transient
    whole-tree FAIL documented earlier is real, not a defect signal).
  - **Provenance re-read + independent recomputation.** Every I11 literal is the source's printed
    **kcal/mol** value re-read from `LITERATURE.md` §R1.10 (F1/F2: Table 1 water / PE; F3: Table 2 water
    *representative* rows; F5: Table 1 `CCSD(T)-F12a/jun-cc-pVTZ`), and every statement was recomputed
    independently in exact rationals before writing it: F1 `34/63`, `9/20`, `-9/52`; F2 `89/153`,
    `16/15`, `-185/896`; F3 `83/107`, `22/5`, `-8175/118342`; F5 `467/610`, `7958/675`,
    `-1215125/3277506` — all four families agree with the skeleton's printed rationals. The record's
    kJ/mol column is the record's arithmetic and is deliberately never used in a statement.
- Deliberately NOT delivered, with the reason:
  1. the optional `_lamHat_pair_dependent` rows — they are **not in the 48-declaration statement
     authority**, and the λ-independent refutation is already carried by the four
     `_not_model_consistent` rows plus I12; the computed evidence is recorded here instead: the model's
     two-point solver at two printed pairs of the same family gives F1 `9/20` vs `8/5`, F2 `16/15` vs
     `-53/60`, F3 `22/5` vs `-749/108`, F5 `7958/675` vs `-19667/1620`.
  2. any F4 row (`_alphaObs` / `_lamHat` / `_curvature_negative` / `_not_model_consistent`): §R1.10.4
     prints only family aggregates for Table 2 "PE", and the skeleton contains **no** `inst_I11_F4_*`
     declaration (checked: 0 matches), so there is no skeleton/authority mismatch to arbitrate and no
     number was invented.

## 2026-09-20 — BEP B3 sharp conditions (`PhotoLean/BEP/Sharp.lean`, 32 declarations: radius + monotonicity + minimax + necessity) — prover_d — DONE

- 目标：deliver the whole B3 block of the statement authority (plan §6.1–§6.5, 25 rows, plus the AUX
  section "literal sup-norm form of the minimax block", 7 rows = **32** declarations; the dispatch
  brief's "33" was an off-by-one and the measured count is 32), reusing the recipes already
  kernel-verified in the Sprint-0 risk probe (`bep-risk-probe.lean`), `bep-api-abs-sqrt.lean`,
  `bep-api-algebra.lean` and `bep-api-minimax.lean`. One commit per declaration, per-lemma
  `lake build` + `check.sh --strict` + `axioms.sh`; the module imports `Basic.lean` only, so B3 has
  exactly one upstream file. Verifier: PASS (`32/32` axiom footprints clean, set equality 32/32, the
  minimax bound confirmed in the authority's original `∀ c a, ∃ x ∈ Set.Icc (-w) w` form, the §11
  disjunctive fallback unused, 11 hypothesis-necessity counterexamples, anti-circularity clean).
- 试过且失败 (measured this round):
  1. **`field_simp` does not turn an inequality hypothesis into a denominator fact.** In
     `bepDefect_sign_flips` (`hlam : lam < 0`) the sequence `unfold …; field_simp; ring` left the goal
     `-(lam*2) - lam*x*lam⁻¹*4 + lam^2*lam⁻¹*2 + x*4 + x^2*lam⁻¹*2 = x^2*lam⁻¹*2` — unsolved, with
     `lam⁻¹` still present. With `hlam : lam ≠ 0` the same sequence closes (verified in the API probes),
     so what matters is the *shape* of the hypothesis: `field_simp`'s discharger consumes `≠`-facts, not
     `lam < 0`. Fix: `have h4 : (4 : ℝ) * lam ≠ 0 := mul_ne_zero (by norm_num) (ne_of_lt hlam)` before
     `field_simp`. Generic rule: carry an explicit `≠ 0` (or `0 <`) fact for every denominator that the
     context only bounds by an inequality.
  2. **`exact` after a rewrite can change the goal's shape.** `rw [e₂ 0, zero_pow …, zero_div, abs_zero]`
     turns the goal into `0 ≤ tol`, while `h.2.1 : 0 < tol` no longer matches: `type mismatch
     0 < tol vs 0 ≤ tol`. Fix: `exact le_of_lt h.2.1`.
  3. **`-0` and `0` are not definitionally equal for `Set.Icc` membership.** After substituting `w = 0`,
     `⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩` failed on `Set.Icc (-0) 0` (`le_rfl : ?m ≤ ?m` against `-0 ≤ 0`).
     Fix: `⟨0, ⟨by norm_num, le_rfl⟩, rfl⟩`.
  4. **The unused-variable linter fires on decorative premises, and the fix is an option, not a
     deletion.** `epSupError_bddAbove`'s `hw` produced `warning: unused variable 'hw'` (the API probe's
     copy carried `set_option linter.unusedVariables false in`, which I had not copied). The repo
     convention (`Basic.lean`) is to keep the physical premise for signature fidelity and disable the
     linter locally; four premises of this file end up in that class and are listed in the module header.
- Worked (reusable):
  - The delivered file was produced **block-by-block from an already-compiling staging copy**:
    `.lake/tmp/b3-full.lean` (header + 32 blocks separated by `-- @@BLOCK feat(B3): <name>` markers) was
    compiled standalone with `proofs/scripts/lake env lean .lake/tmp/b3-full.lean` (0 error / 0 warning
    — the statement-first gate for the batch), its signatures were diffed against the skeleton with the
    official checker's own `signatures()` (32/32 equal, 0 extras, 0 differences) *before* the first
    commit, and a Python driver then emitted "header + blocks[0..k] + footer" into
    `PhotoLean/BEP/Sharp.lean`, ran the three gates and committed with `git add -- <file>` +
    `git commit -m <subject> -- <file>` (pathspec-limited, so concurrent edits of other provers were
    never swept in). 32/32 `verdict: PASS` on both scripted gates, ≈5 s per declaration.
  - Route for the radius theorem (the only `Real.sqrt` statement): `rw [bepRadius, ← hsqrt4,
    div_le_iff₀ h4, Real.le_sqrt hw h4nonneg]; ring_nf` with `hsqrt4 : Real.sqrt (4*(lam*tol)) =
    2 * Real.sqrt (lam*tol)` from `Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)` + `norm_num`; the `∀`-side
    is tested at the endpoint `x = w` via `Set.right_mem_Icc.mpr`, the window side uses `abs_le.mpr` +
    `sq_abs`/`pow_le_pow_left₀` + `div_le_div_of_nonneg_right` + `le_trans`.
  - Route for the minimax lower bound: `by_contra h; push_neg at h`, one `abs_lt.mp` per sampled error
    (`-w`, `0`, `w`), then a single `linarith` against `bep_error_three_point` plus
    `w^2/(2*lam) = 4*(w^2/(8*lam))` (`field_simp; ring`). The risk probe's `set A/B/C` + triangle-helper
    route needs one extra top-level helper declaration, which the fidelity report would list as an
    "extra", so the helper-free route was preferred and the pre-registered disjunction fallback stayed
    unused.
  - `sSup` block: `le_antisymm (csSup_le hne hle) (le_csSup hbdd hmem)`; `epSupError_sharp` splits on
    `eq_or_lt_of_le hw` because `EPBestOnWindow` carries the strict `0 < w` — the `w = 0` branch is just
    `abs_nonneg` + `le_csSup`.
  - B2's `bepDefect lam x = x^2/(4*lam)` was re-derived locally (`have … := by unfold …; field_simp;
    ring`) instead of importing `Criterion.lean`: one upstream file, immune to a co-worker's mid-edit
    state, and the dependency is visible in the proof rather than in the import list.
  - The comment-only follow-up round (verifier MEDIUM-1/LOW-1) kept the comment-stripped text
    byte-identical: sha256 `815e9a3614a7af9d3bd2bec92b2e9a66873e5d99ae871ef42f79e4f8ce2f60ab` (15618 characters = 16328 bytes
    on both sides, stripper = the official checker's `strip_comments`); raw file sha256 before
    `b9b3b568f0d0b37c2df22a1721e4d9cd8e29e6234f5f68300e887c8ada1c81cf`, after
    `a874ce82e85db1c496590d6bf80541d74e40296fde740a6765e7c462d3bbc068` (commit `bff7cfa`);
    `check.sh --strict PhotoLean.BEP.Sharp` → `verdict: PASS`.
- 可复用模式：
  1. **Stage the whole milestone outside `SOURCE_DIRS`, then deliver it one declaration at a time.** The
     staging copy carries the statement-first evidence (it compiles) and the fidelity evidence
     (signatures diffed before any commit), while the driver buys the contract's per-lemma gate + commit
     discipline for the cost of one background run. `PhotoLean/` then never contains an unproved
     placeholder at any commit, so no co-worker's `check.sh --strict` can be broken by our intermediate
     state — the failure mode a naive "write the file with placeholders, fill them in later" delivery
     would introduce in a multi-prover tree.
  2. **A milestone's declaration order is a proof-order problem, not a fidelity problem.** The checker is
     name-keyed, so the three forced reorderings (no forward references: AUX `eact_second_difference`
     before §6.1 #8/#7, `not_epLinearOn_of_ne_zero` (#8) before `epExact_iff_degenerate` (#7), AUX
     `bep_error_three_point` before §6.4 #19) cost 0 differences; record them in the file header instead
     of duplicating an argument to preserve the authority's order.
  3. **Comment-only rounds need a token-stream hash gate with two negative controls.** Strip comments
     from `git show HEAD:<file>` and from the edited file with the *same* stripper the official fidelity
     checker uses, print the stripped byte counts and both hashes, then additionally check that a
     mutated code token changes the hash and that a comment-content rewrite with the same line count
     does not. Without the controls an empty or erroring pipeline reports "identical" (prover_a's
     recorded false PASS). My first "comment addition" control was itself wrong — it appended a blank
     line, which *is* a change in the stripped text — which is exactly why the control is worth running:
     it caught a mis-designed control rather than a real regression.
  4. **Disclose decorative premises per statement, and scope witness claims to what they cover.** The
     verifier strengthened `epConformsOnWindow_iff_radius` to a form without `hw : 0 ≤ w` (for `w < 0`
     the window is empty and `0 ≤ bepRadius lam tol` keeps the right-hand side true), so the header now
     lists four premises the *statement* does not need while saying explicitly which ones the *proof*
     still consumes; likewise the §6.5 bullet now names the four witness rows and states that the sharp
     statements' remaining premises (`0 < tol`, `a < b`, `0 < w`) have no witness row in the authority
     (the verifier's counterexamples live outside the file). A "one witness per premise" claim that is
     not per-premise is a documentation defect the verifier will find.

## 2026-09-20 — B1: kernel extraction (`PhotoLean.Kernel`, owner prover_a)

- Delivered: `PhotoLean/Kernel.lean` (69 lines, `import Mathlib` as the only import, zero warnings) plus
  `"PhotoLean.Kernel"` appended to `defaultTargets` in `lakefile.toml`; commit `3ef20a4` with exactly
  those two files (`git show --stat` confirms nothing under `PhotoLean/{Marcus,Hammond,BEP}`).
- Gates, all run on the committed content:
  - `proofs/scripts/lake build` → `Build completed successfully.`, and `grep -ci warning` on the full log = 0.
  - `proofs/scripts/check.sh --strict` → scan section `clean`, `verdict: PASS`.
  - `proofs/scripts/axioms.sh PhotoLean.Kernel <thm>` for both theorems → `verdict: PASS (only mathlib
    infrastructure axioms)`, each printing its own name.
  - The three statement-fidelity probes: Marcus 51/51, hammond 102/102, BEP 191/191, **0 signature
    differences each**.
- Tried and failed (recorded so a later round does not repeat it):
  1. **Dropping the `hlam : lam ≠ 0` hypothesis of `transfer_eq_tsCoord` (the strictly stronger form)
     is refuted by the kernel**, not merely unproved: at `lam = 0` the two totalised divisions differ —
     `transfer 0 1 = 1/2` while `tsCoord 0 1 = 0` (both closed by `norm_num` in a throwaway probe under
     `.lake/tmp`, so the hypothesis is necessary rather than decorative). Any later attempt to "unify the
     two presentations" must keep that premise explicit.
  2. Checking the gate order the wrong way round is a real trap: running a bare `check.sh --strict`
     **before** registering a new module in `defaultTargets` yields a scan that covers the whole
     `PhotoLean/` directory while the build covers only the old targets — a "scanned but never compiled"
     false PASS. Here the `lakefile.toml` registration was made *before* the first gate run, so the build
     genuinely covered the new module.
  3. The three fidelity scripts each glob only their own `PhotoLean/<Theory>/*.lean`, so a new sibling
     module cannot move their counts — verified by reading the scripts rather than assumed; the baseline
     numbers 51/102/191 came back unchanged.
- Reusable pattern: treat the dispatch's code block as the *statement authority* and diff it against the
  delivered file with the same comment stripper the official fidelity checker uses
  (`strip_comments`) before running any gate — 795 = 795 bytes of code, byte-identical, which is much
  harder to fool than a visual check. Note also that the header of `PhotoLean/Kernel.lean` forward-refers
  to `PhotoLean/Relations.lean` (the regression certificates), which does not exist yet: a deliberate
  forward reference required by the task spec, not a delivered module.

## 2026-09-20 — C: relation module + relation-graph draft (owner lead) — DONE

- Delivered: `PhotoLean/Relations.lean` (28 declarations: 8 `rfl` kernel certificates, 6 reused
  equivalences, 3 one-way edges — one of them new — 4 reuse rows, 4 ledger rows, 3 new theorems),
  `theories/RELATIONS.md` (bilingual relation-graph draft), `lakefile.toml` registration; commits
  `f42a7d5` (inventory), `3dd1239` (new theorems), `efa74c1` (document).
- Gates: build with zero warnings; `check.sh --strict` → `verdict: PASS`; 30/30 declarations of
  `Kernel.lean` + `Relations.lean` at `[propext, Classical.choice, Quot.sound]`; the three fidelity
  probes unchanged (51 / 191 / 102, 0 differences).
- Tried and failed (recorded so a later round does not repeat it):
  1. **Batch-harness bugs, three in a row.** `axioms.sh` prints its verdict on the *second-to-last*
     line (`allowed: ...` is last), so judging by `tail -1` produced 25 false FAILs on correct
     theorems. Then `grep -oP 'depends on axioms: \[.*\]'` missed long theorem names because the
     axiom list wraps across lines. Then `grep -q "^theorem $n"` **prefix-matched**
     (`transfer_eq_tsCoord` also matches `transfer_eq_tsCoord_bridge`) and ran the wrong module,
     producing one more false FAIL. Working harness: build a module+name file with an anchored
     extraction, read it line by line, and judge only by `grep -q "verdict: PASS"`. A false FAIL
     from the harness looks exactly like a real gate failure — always re-run one suspect by hand
     before believing a whole-table verdict.
  2. **A scratch file outside the repository is not where it seems**: the file-writing tool reported
     success for `/tmp/Relations.lean`, but no such file existed (and an in-repo `find`/`grep` could
     not locate it either). Draft inside the gitignored `.lake/tmp/` and copy into `PhotoLean/` when
     ready — that path is inside the workspace and is also what `axioms.sh` uses for its probes.
  3. **Splitting one new file into two logical commits without any intermediate unproved state**:
     write the full file, truncate it at the section marker, commit the compiling part, restore the
     rest from `.lake/tmp/Relations.full.lean`, commit again. Both commits build and pass the strict
     gate; no version of the file ever carried a placeholder.
- What went right, worth reusing: the eight `rfl` kernel certificates closed on the **first** build —
  that is the independent confirmation that the kernel bodies are definitionally identical to the
  three delivered copies, and it is exactly why the certificate design (fail ⇒ stop and investigate)
  is cheap insurance. Also cheap and effective: re-exporting each bridge with its statement written
  out **verbatim** turns the whole inventory into a compile-time statement pin, and `axioms.sh` per
  re-export is a few seconds each.
- Lesson the read-only verifier forced (worth more than the code): **a kernel-checked theorem does
  not make the prose around it true.** The verifier found one *false* parenthetical in
  `theories/RELATIONS.md` §4 ("the truth value does not depend on `A, kB, T`"), refuted by kernel
  counterexample (`Marcus.InvertedDescriptor (-1) (-1) 1 1` holds while
  `¬ Marcus.InvertedDescriptor 1 (-1) 1 1`, same `lam/kB/T`) and contradicted by the same document's
  own N2; plus a missing `0 < lam` qualifier on the reading "the trend needs no tolerance parameter"
  (at `lam < 0` the coordinate is affine but *increasing*). Reusable pattern: mark every piece of
  prose attached to a statement as a reading, and re-check quantifier by quantifier and parameter by
  parameter against the statement text; four further findings were board/coverage bookkeeping
  (no `Kernel`/`Relations` rows on the task board, the fidelity probes' glob does not cover the new
  modules, and the commit-granularity deviation) and all are now recorded on the Marcus board.

## 2026-09-20 — D: final frozen-state acceptance (owner lead) — DONE

- Frozen state `e916783` re-gated end to end: `lake build` OK, `check.sh --strict` → `verdict: PASS`
  (three per-theory leaf planes 5/5), 30/30 declarations of `Kernel.lean` + `Relations.lean` at
  `[propext, Classical.choice, Quot.sound]`, fidelity 51 / 191 / 102 with 0 differences, working tree
  clean, 15 commits since the pre-task HEAD `10713d1`.
- Tried and failed / worth remembering:
  1. **A bare `lake build` on an unchanged tree is a cached no-op, so "zero warnings" from it is
     vacuous evidence.** The final verifier caught this (the build log was 43 bytes) and rebuilt the
     claim independently by re-elaborating all 23 modules from source with `lake env lean`
     (23/23 rc=0, 0 warnings). Whenever "no warnings" is part of the acceptance evidence, force
     re-elaboration (touch the files, or compile each module to a scratch olean) instead of reading
     the tail of a cached build.
  2. Three more false-FAIL traps in the batch axiom harness, beyond the ones recorded in the
     previous entry: word-splitting a module/name file with `for x in $(...)` iterates over *words*
     and silently swaps module and theorem name (30 bogus FAILs); an unanchored `grep "^theorem $n"`
     matches `transfer_eq_tsCoord` against `transfer_eq_tsCoord_bridge` and runs the wrong module;
     and `axioms.sh` writes its verdict on the second-to-last line. The working pattern is: build an
     anchored module + fully-qualified-name list in a file, iterate with `while read -r m n`, and
     judge only by `grep -q "verdict: PASS"`.
  3. Documenting a *commit* in a board row is a claim about history: my own board row attributed the
     new edge O3 to the second commit while it had actually shipped in the first — caught while
     cross-checking the release notes, fixed in `bd9cd27`. Verifying a commit's membership is
     `git show --stat <hash>`, nothing else.
- Findings the read-only verifier raised in this round (all doc-level, all closed in `bd9cd27`):
  a cross-reference in `Relations.lean`/`RELATIONS.md` pointed at a theorem that does not state the
  fact being cited (fixed by citing the delivered witness `Hammond.exists_direction_reversal_of_neg`
  instead); one Chinese rendering used a different term for "ledger rows" than the rest of the file;
  the two pointer paragraphs in the hammond/BEP boards used `<Theory>` where the statement was only
  true for each board's own theory; and the board's commit attribution noted above. Pattern: after a
  theorem is named in prose, check that the *named* statement is the one that carries the claim —
  and after a round of fixes, expect one round of "the fix is itself a claim" findings.
- What held: the additivity property survived the whole task — from `10713d1` to HEAD the only change
  inside `PhotoLean/{Marcus,Hammond,BEP}` is the F2 linter scoping, with comment-stripped code of
  `Barrier.lean` byte-identical both before and after once those three `set_option ... in` lines are
  removed as well (2038 = 2038 chars, 1566 = 1566 without whitespace; the whole comment-stripped text
  differs only by those three named lines), and every re-gate of the three
  fidelity probes returned 51 / 191 / 102 with 0 differences.

## 2026-09-20 — K1 description layer (PhotoLean/Kasha/Basic.lean) — prover_a — DONE

- Goal: K1 of the Kasha theory — the whole description layer, 44 declarations (17 definitions +
  `RateData` + `KashaZone` + 25 theorems), signatures and definition bodies word for word against
  `theories/kasha/probes/kasha-statement-skeleton.lean` (authority hash at delivery
  `801983702a9dc0129e7a2ab4ec6505c4d7c9967daed444c58b460910bc7e3cb0`; the dispatch-time hash
  `e3ddc2d0…` was superseded mid-round by the statement correction below). 30 commits on the file
  (`1f88266` definitions → `66e2ea7` `kashaZone_eq_violating_iff` → `a09a0f1` blank-line house
  style; the two classifier docs/probe commits outside the module path are `014ea0e`
  counterexample, `c204f80` API probe).
- Gate verdicts (clean tree, committed): `proofs/scripts/lake build PhotoLean.Kasha.Basic` →
  `Build completed successfully.`; `proofs/scripts/check.sh --strict PhotoLean.Kasha.Basic` →
  scan `clean`, `build: OK`, `verdict: PASS`; `proofs/scripts/axioms.sh` on **all 25** theorems →
  25 × `verdict: PASS (only mathlib infrastructure axioms)`, 0 FAIL, every row exactly
  `[propext, Classical.choice, Quot.sound]`; `bep-fidelity.py --theory kasha` → 44 word-for-word,
  0 signature differences, 0 declarations outside the authority.
- Tried and failed (seven items; the first is the round's headline):
  1. **Skeleton row §4.2 #24 `kashaZone_eq_violating_iff` was FALSE as handed over**, and the
     falsity is structural, not tactical: the classifier tests the vanishing leak *first*, so
     `upperYield = 0` parks it in `pure`, while `¬ KashaWithin` can still hold there when
     `tol < 0` — and `h : RateData rad ic N` bounds `decay`/`rad`/`ic`, never `tol`. Kernel
     counterexample `theories/kasha/probes/kasha-k1-counterexample.lean` (witness `rad ≡ 1`,
     `ic ≡ 1`, `N = 0`, `tol = -1`: `RateData` holds, `kashaZone = pure`, `KashaWithin` is
     `0 ≤ -1 * (1/2)`, false). Reported to the lead before any proof attempt on that row; the
     authority added `(htol : 0 < tol)` (plan §3.1 correction log) and the row then went through
     in one pass. **The ℚ twin K5a `kashaQVerdict_eq_violating_iff` carried the same defect** and
     was corrected in the same pass. Lesson: a three-way classifier's characterizations are
     *branch* statements — the `violating` branch needs *both* earlier guards negated, and a
     one-sided right-hand side silently imports a sign premise that `RateData` does not carry.
  2. `if_neg`/`if_pos` rewrite the **syntactic** guard, not the definitionally equal one. In
     `kashaZone_eq_violating_iff` the guard is `upperYield rad ic N ≤ tol * fluoYield rad ic N`
     while the hypothesis arrived as `hw : ¬ KashaWithin rad ic tol N`; `rw [if_neg hw]` failed
     with `did not find instance of the pattern in the target expression
     \`if KashaWithin rad ic tol N then …\`` — and the same defeq trap hit `rw [h0]` inside a goal
     displayed as `KashaWithin`. Working fix: materialize the unfolded form first,
     `have hw' : ¬ (upperYield rad ic N ≤ tol * fluoYield rad ic N) := hw`, then rewrite with `hw'`.
  3. `simp` does **not** prove `1 + 1 = 2` at a concrete `ℝ` after unfolding a witness: the
     leftover goal is literally `⊢ 1 + 1 = 2`; `norm_num` closes it (measured while drafting the
     counterexample probe).
  4. `split_ifs … <;> first | exact h1 | <fallback>` reports `this tactic is never executed` /
     `tactic does nothing`, because `split_ifs` already discharges the branches whose generated
     equality is `Ctor₁ = Ctor₂` for distinct constructors: exactly one goal survives, so the
     plain `split_ifs at hz with h1 h2` plus a single `exact h1` / `exact h2` is shorter and
     warning-free (the `first |` alternative is only needed when the leaves really are several —
     cf. the Hammond seven-branch recipe).
  5. `Finset.Icc_succ_right` **does not exist** in this toolchain (Lean 4.17.0 + mathlib v4.17.0);
     the K2 recursion must split `Icc a (b+1)` with `Finset.prod_Icc_succ_top` /
     `Finset.sum_Icc_succ_top` (both verified). Calibration: `kasha-api-k1-finset.lean`.
  6. Decorative premises trip `linter.unusedVariables`: `h : RateData` in #13/#20/#22/#23/#25 and
     `h1 : i ≤ N` in #8/#9 belong to the authority's signature and are *not* consumed by those
     proofs. House pattern: keep the premise and put `set_option linter.unusedVariables false in`
     immediately *before* the docstring (after it, the option does not parse).
  7. Re-emitting a **prefix** of the module is unsafe once the authority changes mid-round: the
     last driver step would have re-emitted "segments 1..28" from the old master and deleted the
     already-committed `kashaRule_of_rad_zero` (it sits after the corrected row). Fix: after an
     authority change emit the *full* file and let the git diff be the change; and never read the
     delivered file back as input (the self-swallowing driver of the BEP round).
- What worked (reusable for K2, which imports this module):
  - Draft the whole module in a **gitignored master copy** (`.lake/tmp/k1-master.lean`, split by
    `-- @@@` markers) and emit the delivered file from it, running
    build + `check.sh --strict` + `axioms.sh` + `git commit -m … -- <path>` per segment. No
    placeholder ever enters the scanned tree, and the history stays one-lemma-per-commit without
    any interactive editing of the delivered file.
  - K1 index toolkit, every name `#check`-verified: `Finset.Icc_eq_empty` (`cascade_self`),
    `Finset.range (N+1) = insert 0 (Icc 1 N)` by `ext; simp only [Finset.mem_range,
    Finset.mem_insert, Finset.mem_Icc]; omega` + `Finset.sum_insert` (`fluoYield_eq_low_add_upper`),
    `Finset.sum_range_one` (`fluoYield_zero`), `Finset.sum_div` used **backwards** (`specFrac_sum`),
    `Finset.prod_nonneg` / `Finset.prod_le_one` (`cascade_nonneg`, `cascade_le_one`),
    `Finset.sum_nonneg`, `Finset.sum_eq_zero` (`kashaRule_of_rad_zero`, after `rw [hzero …]` +
    `simp`), `div_nonneg`, `← add_div` + `div_self` (`radBranch_add_icBranch`),
    `mul_le_of_le_one_right` (`emitYield_le_radBranch`), `div_le_iff₀`
    (`kashaWithin_iff_specFrac`), and `lt_of_le_of_ne … (Ne.symm hF)` to turn `0 ≤ F` + `F ≠ 0`
    into `0 < F`.
  - Classifier recipe, three independent uses, 0 warnings: forward
    `unfold kashaZone at hz; split_ifs at hz with h1 h2` + one bullet; backward
    `unfold kashaZone; exact if_pos hr` (#22), `rw [if_neg …, if_pos …]` (#23), or
    `rw [if_neg hne, if_neg hw']` (#24, with `hne` derived from `0 < tol` and `RateData` via
    `mul_nonneg (le_of_lt htol) (fluoYield_nonneg h)`).
  - The module header must not spell the two literal keywords the strict scan looks for: the scan
    covers `PhotoLean/**/*.lean` including block comments, so even prose about them is a
    false-positive FAIL. Verified with the same `grep -E` as `check.sh` before the first commit
    (the note is now part of the header, inside a block comment, deliberately without the
    literals).
