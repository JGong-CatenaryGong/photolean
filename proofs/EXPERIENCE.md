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

## 2026-09-20 — ⚠️ lead 的并发提交事故：`git add -A` 吞掉工人的中间产物 — lead — FAIL→已修正

- 目标：把 `plan.md` §8.3 的文献参数回填与任务板状态更新提交。
- 试过且失败：提交时用了 `git add -A`（图省事）。当时有三个工人在并发写自己的工作文件，
  于是：
  - `e53d562`（本应是"任务板 + lakefile"）里混进了 `proofs/LITERATURE.md` 的 453 行初稿、
    `api_researcher` 的两个探针、`prover_b` 的 scratch 探针，以及 **`marcus-lemma-skeletons.lean` 的删除**；
  - `c000996`（本应是"plan 文档更新"）里混进了 **`PhotoLean/Marcus/Barrier.lean` 的 WIP** 与两个 scratch 探针。
  后果：**`barrier_nonneg`（M2 第一条）失去了自己的 per-lemma 提交** —— 内容落在一个
  标题为 `docs(plan): ...` 的提交里，审计轨迹被污染。
- 奏效（修正）：
  1. **规则写进任务板**：lead 只用 `git add <显式路径>`（`plan.md`/`proofs/TASKS.md`/`proofs/EXPERIENCE.md`/`lakefile.toml`），
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
  签名须与 `proofs/probes/marcus-statement-skeleton.lean` 的 M2 段**逐字一致**：
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
  - 实测确认的名字（v4.17.0，探针 `proofs/probes/marcus-prover_a2-scratch.lean` 留 `#check` 原文）：
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

<!-- 条目从这里继续往下追加 -->
