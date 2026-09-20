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
