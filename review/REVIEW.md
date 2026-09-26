# PhotoLean 三理论形式化审查报告

> 审查对象：`PhotoLean/` 下三个唯象理论的 Lean 4 交付源码（Marcus 8 模块、Hammond 6 模块、BEP 6 模块 + Smoke）
> 及其文档面（`theories/*/{plan,TASKS,RESULTS,LITERATURE}.md`、`proofs/`、`README.md`、`AGENTS.md`）。
> 审查基准日：2026-09-20 工作区状态（`git` HEAD）。
> 审查方式：**全部结论以一手证据为准**——本报告中的每条扫描、计数、脚本判决、公理探针均在审查期间
> 于本仓库实际执行；另有两位独立只读审查代理并行复核（机械扫描与文档一致性），其结论与本报告
> 一致处标注「双确认」。**未修改任何证明文件**；本报告是 `review/` 下唯一新增物。

---

## 0. 总体结论（TL;DR）

| 审查项 | 判决 | 一句话理由 |
|---|---|---|
| ① 名实相符 | **通过（有保留项）** | 三组 `Criterion`/`Sharp` 定理真实表达了对应化学命题；无 vacuous 主定理、无结论塞假设。保留项：少量"薄"定理（定义展开/投影/rfl 别名）计入定理总数；若干前提"写了但证明未用"（只使定理更强，不使更弱） |
| ② 关系判定严格性 | **通过** | 跨理论桥接全清单 13 行（16 条定理）：真 `↔` 5 条（均有实质双向证明）、实质 `Eq` 桥 2 条（刻意做成非定义性再证明）、单向蕴含 6 条（文档正确标注 "entails"）、`rfl` 级别名证书 3 条（全部为 `Eq`、全部如实标注 "definitional"）。**无 `Iff.rfl` 伪造等价**；唯一的 `Iff.rfl`（`Marcus/RatModel.lean:91`）出现在两条实质重写之后，闭合的是定义展开 |
| ③ 非平凡性 | **通过** | 三个理论均同时交付**模型**（可采纳实例）与**非模型**（不可采纳/被证伪实例），且以具名定理形式交付，非注释声称 |
| ④ 零 sorry/零公理可信度 | **通过（脚本有两处应补的洞）** | `check.sh --strict` PASS；11 条关键定理 `#print axioms` 全部 = `[propext, Classical.choice, Quot.sound]`；无 `native_decide`/`opaque`/`unsafe`/`#eval`/显式 `Classical`。但 `check.sh` 的正则**不含 `admit`**、axiom 锚定不匹配 `private axiom`——当前代码 0 命中，属"门此刻有效、但挡不住两类已知绕过" |
| ⑤ 文档-代码一致性 | **代码侧几乎无懈可击；文档层有 1 处确凿笔误与一组政策漂移** | 全部可数声称（三理论声明数 82/102/191、每模块计数、提交数 47/87/164、保真 51/102/191、公理 70/70）经独立复数与实跑**精确吻合**。但：`RESULTS.md` 有一处定理名笔误（中英两版同错）；Hammond 任务板属主自相矛盾；语言政策在 README/AGENTS/ENGINE 三文件间互相矛盾，且 3 个 `.en.md` 已实际漂移；README「现状」节停留在只有 Marcus 的时代 |
| ⑥ 模板可复用性 | **部分成立** | 真正可复用的是**方法学**（语句权威先行、ℝ 理论+ℚ 判定影子+cast 桥、锐利 iff、双向非平凡实例、显式物理前提）；模块骨架（`Basic/Criterion/RatModel/Sharp/Compose/Instances`）三理论已发生两处结构变异（Marcus 无 `Criterion` 而有 `Barrier/Rate/Reorg`；BEP 的 `Compose` 不用 Pekar 机制），证明它不是刚性抽象而是良好默认。**三个理论共享同一数学基质（等曲率双抛物面），模板尚未在不同基质的理论上受过压** |

**总评**：这是一套纪律执行罕见地严格的 LLM-agent 形式化工程。审查者特别核查的六类常见造假面
（vacuous 定理、结论塞假设、`Iff.rfl` 伪造、`sorry`/`admit` 变体、`native_decide` 偷渡、`#eval`
冒充证明）**全部阴性**。发现的问题均为工程级（脚本正则覆盖、文档政策漂移、模板抽象层级），
无一影响已交付定理的数学可信性。

---

## 1. 审查范围与方法

### 1.1 范围

| 层 | 内容 | 审查深度 |
|---|---|---|
| 交付源码 | `PhotoLean/{Marcus,Hammond,BEP,Smoke}.lean` 共 21 文件、5235 行 | **逐行通读**全部 `Basic`/`Criterion`/`Sharp`/`Compose`，逐条核对 `RatModel`/`Instances` 的声明与抽样证明体 |
| 验收脚本 | `proofs/scripts/{check.sh,axioms.sh,lake}`、`proofs/ENGINE.yml`、`lakefile.toml` | 逐行审读 + 实际运行 + 绕过面分析 |
| 文档面 | 三理论 `plan/TASKS/RESULTS/LITERATURE`、`proofs/EXPERIENCE.md`、`README.md`、`AGENTS.md` | 可数声称逐条核对；政策类声称交叉比对 |
| 探针 | `theories/*/probes/*` | **按约定排除在 sorry 扫描外**（语句骨架故意含 sorry 占位：BEP 157 条、Hammond 85 条、Marcus 39 条定理占位——grep 字面命中 157/85/44，Marcus 的 44 含 5 处注释提及，已实测确认）；仅用于保真度脚本 |

### 1.2 一手执行的验证命令（全部实测，非转述）

```bash
proofs/scripts/lake build                       # exit 0，全量构建通过
proofs/scripts/check.sh --strict                # verdict: PASS（叶数据面 3 理论 5/5、构建 OK、扫描 clean）
proofs/scripts/axioms.sh <Module> <theorem>     # 11 条关键定理逐条，全部 PASS
python3 theories/Marcus/probes/marcus-fidelity.py   # 51/51 逐字一致，0 差异
python3 theories/BEP/probes/bep-fidelity.py         # 191/191 逐字一致，0 差异
python3 theories/hammond/probes/hammond-fidelity.py # 102/102 逐字一致，0 差异
```

公理探针覆盖的 11 条定理（每条输出均为 `[propext, Classical.choice, Quot.sound]`，双确认）：
`Marcus.descriptor_sharp`、`Marcus.inverted_descriptor_holds`、`Marcus.descriptor_holds_of_microscopic`、
`Marcus.descriptor_holds_of_nonoverlap`、`Hammond.hammond_sharp`、`Hammond.hammond_descriptor_of_microscopic`、
`Hammond.exists_reactionRegion_of_microscopic`、`BEP.epConformsOnWindow_iff_radius`、`BEP.epSupError_sharp`、
`BEP.epBounds_iff_no_inverted_direction`、`BEP.epDescriptor_of_microscopic`。

---

## 2. 审查项①：名实相符

**审查问题**：`Criterion`/`Sharp` 里的定理是否真的表达了对应的化学命题？是否被削弱成 vacuous、
或把结论塞进假设？

### 2.1 逐理论核对：主定理的语句 vs 化学命题

#### Marcus（`Sharp.lean`）

化学命题：**马库斯反转区**——电子转移速率随驱动力（`-ΔG°`）增大，在驱动力超过重组能 `λ`
后反而下降。

- `InvertedDescriptor A lam kB T := ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate … x₂ < rate … x₁`
  （`Basic.lean:71-72`）。忠实编码：量程恰为反转区（`lam < x₁`），结论为严格递减。**非 vacuous**：
  前提联立可满足（`A=kB=T=lam=1, x₁=2, x₂=3`）。
- 主定理 `descriptor_sharp`（`Sharp.lean:273-274`）：
  `(∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T ↔ 0 < A ∧ 0 < lam`。
  - **结论未塞入假设**：左侧合取不含 `0 < A` 或 `0 < lam`；`0 < A` 由 `sharp_A_pos` 从速率正性
    **证出**（取 `x = lam`，由 `0 < A·exp u` 与 `exp u > 0` 反推），`0 < lam` 由 `lt_trichotomy`
    三分支证出（`lam<0` 与 `lam=0` 两支各自导出与描述矛盾的严格不等式）。
  - **必要性方向是真的数学内容**：`lam = 0` 支依赖除零约定使势垒恒零、速率恒为 `A`，取
    `x₁=1, x₂=2` 得 `A < A` 矛盾；`lam < 0` 支依赖 `barrier_antitone_of_neg` 的方向反转。
    两支机制不同、分别成条——这是反"伪造"的正向证据：伪造者不会需要自己补出两条机制不同的分支。
  - **该 iff 是规划期的真实发现**：单写 `InvertedDescriptor` 不足以蕴含 `lam > 0`——非物理分支
    `A < 0 ∧ lam < 0` 下描述形式成立但速率为负（`inverted_descriptor_holds_of_neg`，
    `Sharp.lean:312`，作为"正性合取项不可去"的**可检查证据**保留为定理）。这正是形式化相对于
    教科书陈述的增量价值。

#### Hammond（`Criterion.lean` + `Sharp.lean`）

化学命题：**Hammond 假说**——放能越多，过渡态越早（越像反应物）。

- `HammondDescriptor lam := ∀ x₁ x₂, x₁ < x₂ → tsCoord lam x₂ < tsCoord lam x₁`
  （`Basic.lean:66-67`）：`tsCoord = (λ-x)/(2λ)` 是过渡态坐标，对驱动力严格递减即"越放能越早"。忠实。
- 主定理 `hammond_sharp`（`Sharp.lean:63`）：`HammondDescriptor lam ↔ 0 < lam`。
  充分性是 `tsCoord_antitone`；必要性由**两个显式反例见证**支撑（`lam < 0` 时坐标反向递增、
  `lam = 0` 时坐标常值，均在 `x₁=0, x₂=1` 处见效）——不是用否定量词搪塞，而是构造性反证。
- `lefflerSecant_eq_midpoint`（`Criterion.lean:65`）：**由势垒数据测得的** Brønsted 系数
  （有限差商）等于所比较对中点的过渡态坐标。文档如实限定为**模型恒等式**而非实验斜率断言
  （"never a claim about an experimentally measured Brønsted slope"，plan §13 row 13）——
  这是对"名实相符"的自觉守护，值得记为正面实践。

#### BEP（`Criterion.lean` + `Sharp.lean`）

化学命题：**Bell–Evans–Polanyi 原理**——活化能随反应能近似线性变化（线性自由能关系）。

- 形式化的核心动作是把"近似"拆成两层：精确缺陷律 `bepDefect_eq : bepDefect lam x = x²/(4λ)`
  （`Criterion.lean:51`）+ 容差/窗口表述。主定理群：
  - `epBounds_iff_region`（`Sharp.lean:68`）：`0 ≤ α ≤ 1 ↔ -λ ≤ x ≤ λ`（`0 < lam` 下）。真 iff。
  - `epExact_iff_degenerate`（`Sharp.lean:157`）：全域上仿射律精确 `↔ lam = 0`。
    左向由 `not_epLinearOn_of_ne_zero`（二阶差分恒等式）支撑——`λ ≠ 0` 时在**任何非退化区间**
    上都没有仿射律能复现势垒，这是真内容；右向 `lam = 0` 是除零约定的退化（文档如实标注
    "the affine witness is the constant 0 law"）。
  - `epConformsOnWindow_iff_radius`（`Sharp.lean:202`）：窗口 `[-w,w]` 上容差内符合
    `↔ w ≤ 2√(λ·tol)`。真 iff，且半径可达（`epConformsOnWindow_at_radius`）——"锐利"名副其实。
  - `epBestOnWindow_holds`（`Sharp.lean:386`）：极小极大最优性，三点等振荡证明。真内容。
- **结论塞假设检查（阴性）**：`EPConformsOnWindow` 等符合性谓词把 `0 < lam`、`0 < tol` 做成
  **谓词的合取项**（`Basic.lean:89-95`），相关定理再在签名里显式带前提——这不是塞结论，
  而是把"物理定义域"变成类型上可见的合取，防止 vacuous 接受。`inst_I9_unphysical_bounds_blind`
  （`BEP/Instances.lean:279`）还专门证明：`EPBounds` 在 `λ = -2` 时可被满足（`α = 3/4 ∈ [0,1]`），
  即"界"单独看不见曲率符号——所以 `EPConforms` 必须含 `0 < lam` 合取。这是用定理封堵
  "名实漏洞"的范例。

### 2.2 发现的保留项（不阻断，但应知情）

1. **"薄"定理计入总数**。三类低内容声明包含在 82/102/191 的计数里：
   - `rfl` 别名证书 3 条（见 §3.1）；
   - 定义展开/投影，如 `Hammond.conforms_requires_pos : HammondConforms lam x → 0 < lam := h.1`
     （投影一个合取项）、`BEP.epConforms_iff_bounds`（`EPConforms` 的定义展开）；
   - 求值引理，如 `transfer_thermoneutral : transfer lam 0 = 1/2`。
   这些都**如实标注**（"definitional"、"it is the first component"），不构成伪造；但读者应知
   "157 条定理"≠"157 条深结果"。Marcus 的 verifier 自己在验收记录里就标记过同类问题
   （`zone_trichotomy` "本身信息量弱……真正钉住语义的是三条 `zone_eq_*_iff`"，
   `theories/Marcus/TASKS.md:141`）——说明这一弱点是流程内自知、而非审查者首曝。
2. **"写了但证明未用"的前提约 15 处**（`barrier_symm` 的 `lam ≠ 0`、`barrier_antitone_of_pos` 的
   `0 ≤ x₁`、`lamOuter_pos` 的五条定义域前提、`lefflerSecantQ_cast` 的 `x₁ ≠ x₂` 等）。
   关键定性：这些前提**未被使用但不可由其余前提推出**（每条都附内核级反例，如
   `lam=1, x₁=-5, x₂=-4` 使 `0 ≤ x₁` 为假而其余前提为真），保留它们只使定理**更强**（适用面更窄
   的语句被证出，等价于证了更弱前提下的版本再收缩），**方向上与"削弱成 vacuous"相反**。
   每一处都有文档说明 + 局部 `set_option linter.unusedVariables false in`。
   **一处例外**值得点名：`Marcus/Barrier.lean:58` 是**文件级**（无 `in` 作用域）的 linter 关闭，
   抑制面扩到整个文件——建议改为逐声明作用域（见 §7 建议清单）。
3. **退化分支依赖除零约定**：`lam = 0` 时多条定理（`barrier_zero_lam`、`tsCoord_zero_lam`、
   `epExact_iff_degenerate` 右向、`transfer_zero_lam`）的数值内容由 Lean 的 `x/0 = 0` 全域化约定
   承载。这是**形式约定而非物理事实**——文档在每一处都如实标注（如 `RatModel.lean` 对
   `barrierQ_cast` 的 ⚠️ 警告："不得被当作『势垒在 lam=0 取值为 0』的物理数值证据"）。
   处理是诚实的，但审查意见是：这类约定依赖是模型的**已知失真点**，引用这些定理做下游论断时
   必须连同约定一起引用。
4. **一处轻微名实缝隙**：`Marcus.NormalRegion lam x := x < lam` 含 `x < 0`（吸能侧），而
   `NormalDescriptor` 量程要求 `0 ≤ x₁`（放能域）。两者不是同一集合——文档以"正常区的物理
   定义域"解释，可接受；但 `zone_eq_normal_iff` 把分类器的 `normal` 判到 `NormalRegion`（全域），
   实例层判定"正常区"时用的是宽口径。建议在文档一句话点明两种口径的用途分野（当前散见于
   多处注释，未集中声明）。

---

## 3. 审查项②：关系判定的严格性

**审查问题**：跨模块桥接是单向蕴含还是真等价？共享签名 Σ 是否显式固定？有无"把 B 的定义写成 A
然后 `Iff.rfl`"的伪造？

### 3.1 跨理论桥接全清单（13 行、共 16 条定理，逐条分类）

| # | 定理（文件:行） | 形态 | 证明 | 判定 |
|---|---|---|---|---|
| 1 | `BEP.eact_eq_barrier`（BEP/Compose.lean:71） | `Eq` | `rfl` | **别名证书**（如实标注 "definitional"） |
| 2 | `BEP.rate_eq_exp_neg_eact`（BEP/Compose.lean:77） | `Eq` | `rfl` | **别名证书**（同上） |
| 3 | `Hammond.barrier_eq_gapReactant`（Hammond/Criterion.lean:149） | `Eq` | `rfl` | **别名证书**（标注 "literally the Marcus barrier"） |
| 4 | `BEP.transfer_eq_tsCoord_bridge`（BEP/Compose.lean:84） | `Eq` | `field_simp`（需 `lam ≠ 0`） | **真定理**：BEP 刻意把 `transfer` 定义为线性响应形 `1/2 - x/(2λ)` 而非 `(λ-x)/(2λ)`，使同一性**不可定义展开**（`lam = 0` 时两侧取值不同：`1/2 ≠ 0`）——这是反"伪造等价"的主动设计 |
| 5 | `BEP.secSlope_eq_lefflerSecant`（BEP/Compose.lean:276） | `Eq` | `unfold`+`rw`+`ring` | **真定理**（文档明确："The link is not definitional……hence it is proved rather than closed by `rfl`"） |
| 6 | `BEP.epBounds_iff_no_inverted_direction`（BEP/Compose.lean:95） | `↔` | 双向算术证明 | **真等价（headline）**：`0 ≤ α ≤ 1 ↔` 正逆两方向都不在 Marcus 反转区 |
| 7 | `Hammond.tsCoord_lt_zero_iff_inverted`（Hammond/Criterion.lean:89） | `↔` | 双向（`div_lt_iff₀`） | **真等价**：过渡态坐标越过反应物端 ⟺ Marcus 反转区 |
| 8 | `Hammond.lefflerSecant_neg_iff_inverted`（Hammond/Criterion.lean:97） | `↔` | 经 #4 同型引理复合 | **真等价**：Brønsted 系数为负 ⟺ Marcus 反转区 |
| 9 | `Hammond.Rat.hammondZoneQ_beyondReactant_iff_inverted`（Hammond/RatModel.lean:220） | `↔` | 两条特征化引理复合 | **真等价**：两个分类器在 ℚ 上判同一批实例 |
| 10 | `BEP.epBounds_of_reactionRegion`（BEP/Compose.lean:119） | `→` | 单向 | 单向蕴含，文档标注 "entails"，**未过度声称** |
| 11 | `BEP.epBounds_of_marcus_normal`（BEP/Compose.lean:128） | `→` | 单向 | 同上 |
| 12 | `Marcus.Rat.zoneQ_inverted_iff`（Marcus/RatModel.lean:89） | `↔` | 两条重写 + `Iff.rfl` | 合法：唯一的 `Iff.rfl` 出现在 `rw [zoneQ_eq_zone, zone_eq_inverted_iff]` 之后，闭合的是 `InvertedRegion` 的**定义展开**——实质内容在两条转移引理里，不在最后一行 |
| 13 | `Hammond.Compose` 对 `Marcus.Reorg` 的复用（`hammond_descriptor_of_microscopic` 等 4 条） | `→` | 直接实例化 | 跨理论**定义复用**（不重新定义 `lamInner/lamOuter`），是最干净的一种桥 |

**伪造模式排查结论（阴性）**：全库 `:= rfl` / `:= Iff.rfl` / `exact Iff.rfl` / `by rfl` 仅 4 处
（上表 #1/#2/#3/#12），无一构成"把 B 的定义写成 A 再一行伪造等价"：
- #1–#3 是 `Eq`（不是 `Iff`），证明的是"两个定义逐字节相同"——其认识论地位是**命名校验**
  （certify the copy），不是数学发现。考虑到本项目的目标②恰恰是"机械裁决同一物理本质被起了
  不同名字"，这类证书是切题的交付物，且**每条都如实标注 definitional**；
- 真正有内容的同一性（#4、#5）都被**刻意做成非定义的**再证明——设计方向与伪造相反。

### 3.2 共享签名 Σ 的固定方式

判定"两理论等价"需要两套理论在同一签名上解释。本项目的做法：

- **Σ 的内容**：`{lam : ℝ（= 重组能/抛物面曲率），x : ℝ（= 驱动力 -ΔG°）}`，三个理论共用；
- **固定机制**：(i) 桥接定理在**同一对变量** `lam x : ℝ` 上量化两侧命题（如 #6 的语句
  `EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ …)` 本身就是签名钉合）；(ii) `eact` 与
  `Marcus.barrier`、`gapReactant` 的函数体逐字节相同，由 #1/#3 的 `rfl` **机械钉死**——
  物理量 `lam` 跨理论的同一性因此不依赖命名约定，而有内核级凭证。
- **审查意见（改进点，非缺陷）**：Σ 的固定是**纪律性**而非**结构性**的——没有
  `structure TwoParabolaModel` 一类的签名对象把"同一模型"做成类型；若未来第四个理论复用
  `lam` 名字但赋不同含义，现行机制无法自动拦截（只能靠新写 `rfl` 别名失败来事后发现）。
  对"关系裁决"模板而言，引入显式签名结构是值得的下一步（见 §7）。

### 3.3 文档中的"等价"声称 vs 代码实际

抽查全部对外"iff/当且仅当/exactly"声称，均有对应真 `↔` 定理：`hammond_sharp`（"成立当且仅当
λ>0"）、`epBounds_iff_region` + `epBounds_iff_no_inverted_direction`（"iff -λ≤x≤λ iff 两方向
都不在反转区"）、`lefflerSecant_neg_iff_inverted`（"系数为负恰好是反转区"）、
`epExact_iff_degenerate`（"精确只在退化模型"）、`epConformsOnWindow_iff_radius`（"iff 半径"）。
单向蕴含在文档中均用 "entails" 措辞，未发现把 `→` 说成 `↔` 的过度声称。

---

## 4. 审查项③：非平凡性

**审查问题**：每个理论是否都存在模型且存在非模型？

| 理论 | 模型（存在性证据，均为内核检查的具名定理） | 非模型（同样具名） |
|---|---|---|
| Marcus | `inst_I4_mcc_admissible`（文献 MCC 参数 `(A,λ)=(1,1.20)`：`∀ x, 0 < rate` ∧ 描述成立，且对**任意** `kBT>0` 全称化）；`inst_I4_mcc_descriptor_any_kT`、`inst_I6_rc_descriptor_any_kT`；`inst_I1/I3/I4/I6_*_inverted` | `inst_I7_unphysical_not_admissible`（`(A,λ)=(-1,-1)`：描述形式成立但速率非正 ⇒ 不可采纳）；`inst_I7_nonpos_lam_not_descriptor`；`inst_I2_not_inverted`、`inst_I5_mcc_not_inverted` |
| Hammond | `inst_I4_family_descriptor : HammondDescriptor 1`；`inst_I1/I2/I3_*_conforms`；`exists_reactantLike/productLike/reactionRegion` | `inst_I8_nonphysical_fails_neg : ¬ HammondDescriptor (-1/2)`、`inst_I8_nonphysical_fails_zero : ¬ HammondDescriptor 0`；`inst_I4_barrierless_notConforms`；`exists_direction_reversal_of_neg/_eq`（Sharp 层的显式反向见证） |
| BEP | `exists_epDescriptor`；`inst_I1–I3_*_conforming`；`qConformsWindow_witness`、`inst_I10_threshold_conforms` | `exists_conforms_fails`；`inst_I6_inverted_notBounds`、`inst_I7_reverseInverted_notBounds`；`inst_I10_threshold_fails`；`inst_I11_F1/F2/F3/F5_not_model_consistent`（四个**真实文献族**被等曲率模型证伪）；`inst_nonvacuous` 把正负两向打包成一条总定理 |

要点：
- 非平凡性不是抽查性质，而是**每个理论都交付了成对的正/负见证**，BEP 甚至把"符合判决、
  不符合判决、符合窗口、失败窗口四者同存"做成单条定理 `inst_nonvacuous`；
- 最有分量的一组非模型：BEP 的 I11/I12 用**一手文献数据**（四个光化学/抗氧化族）证明
  "仿射 BEP 描述符合（两点斜率 ∈ (0,1)）**但**其背后的等曲率双抛物模型被证伪（二阶差商为负，
  而 `λ>0` 的模型强制 `1/(4λ)>0`）"——`RESULTS.md` 如实报告"计划原先希望至少一个文献族
  conforming 的愿望**未满足、也不假装满足**"。这是"理论蕴含关系"类结论有实质意义的直接证据：
  若理论只有平凡模型，这张证伪表不可能存在。

---

## 5. 审查项④：「零 sorry、零自定义公理」的可信度

### 5.1 扫描结果（只扫交付目录 `PhotoLean/`；双确认）

| 检查项 | 结果 |
|---|---|
| `sorry` / `sorryAx` / `admit` | **0 命中** |
| 自定义 `axiom` 声明 | **0 条**（12 处 "axiom" 命中均为头注释套话，逐条人工确认在块注释内） |
| `native_decide` | **0 命中**（仅 2 处注释解释其被禁用：`Lean.ofReduceBool` 不在允许公理清单） |
| `opaque` / `unsafe` / `partial def` / `implemented_by` / `extern` | **0 命中** |
| `#eval`（及一切 `#` 命令） | **0 命中**——实例层的数值判定全部走 `by decide`/`norm_num` **证明项**，无运行时网格搜索冒充证明 |
| 显式 `Classical.choice`/`Classical.em`/`open Classical` | **0 处**；仅 3 处 `by_contra` 战术与 1 处 `h.choose`（`BEP/Sharp.lean:162`，从**假设** `EPLinearOn` 的存在性中取见证——这是消费前提的合法选择，**不是**凭空选择反例） |
| `set_option` | 25 处，**全部**为 `linter.unusedVariables false`（24 处 `in` 作用域 + 1 处文件级，见 §2.2.2）；无 maxHeartbeats、无 warningAsError、无其他 linter 关闭 |
| `by decide` 使用面 | 仅两类：(i) `Zone`/`HZone`/`EPQVerdict` 有限构造子的互异（派生 `DecidableEq` 的内核归约）；(ii) ℚ 整数字面量的分类器计算（`inst_I1_zoneQ` 是唯一整条由 decide 证明的定理）。`decide` 走 `Decidable` 实例内核归约，**不引入任何公理**（已被 11 条公理探针覆盖性证实）；含除法的有数字面量实测会卡 decide，代码已改用 `norm_num`（边界实测记录在案） |

### 5.2 公理层

`check.sh --strict` PASS（实测输出：叶数据面 3 理论 5/5 OK、build OK、扫描 clean、verdict PASS）。
11 条关键定理（三理论主定理 + 全部 Compose 桥接）`#print axioms` 全部恰为
`[propext, Classical.choice, Quot.sound]`——`Classical.choice` 为 mathlib 实数/上确界机制的
传递依赖，非项目显式经典化。Marcus 侧另有全量探针 `theories/Marcus/probes/marcus-all-axioms.lean`
（70/70 干净，其中 1 条仅依赖 `propext`），本审查抽查与其一致。

### 5.3 验收脚本本体的绕过面（应补，但不影响当前交付）

逐行审读 `check.sh`/`axioms.sh` 后确认的已知绕过面（当前代码 0 命中，属"门有效但未覆盖"）：

1. **`check.sh` 的正则 `sorry|^[[:space:]]*axiom([[:space:]]|$)` 不含 `admit`**——Lean 4 的
   `admit` 战术与 `sorry` 等价（引入 `sorryAx`），grep 层会漏；目前仅靠 `axioms.sh` 的
   `sorryAx` 拦截兜底。同理 `private axiom`/`protected axiom` 不匹配行首锚定。
   **复合残余洞**：`private axiom` + verifier 漏测某条依赖它的定理 ⇒ 两层都漏。
   建议：正则扩为 `sorry|admit`，axiom 锚定放宽；流程上要求**每条**交付定理过公理探针
   （Marcus 的 `marcus-all-axioms.lean` 已是此实践的雏形，应推广为门的标准件）。
2. `axioms.sh` 只查被点名定理；其 sed 解析在异常输出下只会假 FAIL 不会假 PASS（安全方向）；
   探针文件名 `.$$.$RANDOM` 并发安全（2026-09-20 事故后的修复，已在注释记录）。

另注一个**正面设计**：`check.sh` 连块注释也扫（宁误报不漏报），各文件头因此刻意不写出两个
关键字字面量——门与代码互相适配的细节是到位的；`lakefile.toml` 的 `defaultTargets` 覆盖全部
21 个模块，与扫描目录全集一致，堵住了"扫描全覆盖、构建不覆盖"的验收洞（该洞在引擎文档中被
明确预警过，当前不存在）。

---

## 6. 审查项⑤：文档与代码的一致性

### 6.1 可数声称的独立复数（剔除注释后精确计数，本审查自写脚本复核）

| 声称（出处） | 文档值 | 实测值 | 判决 |
|---|---|---|---|
| Marcus 交付声明 = 70 定理 + 12 定义级（`RESULTS.md` §摘要） | 82 | **82**（70 + 11 def + 1 inductive） | ✅ 精确吻合 |
| Marcus 语句保真 51/51，31 条实例定理在骨架外（`RESULTS.md` 已知偏离 #3） | 51+31 | 保真脚本实测 **51/51**，骨架外恰 **31** 条且全部位于 `Instances.lean` | ✅ 吻合，且缺口如实登记 |
| Hammond 102 声明 = 85 定理 + 16 def + 1 inductive（`RESULTS.md` §1） | 102 | **102** | ✅ 精确吻合 |
| BEP 191 声明 = 157 定理 + 32 def + 2 inductive（`RESULTS.md` §1） | 191 | **191** | ✅ 精确吻合 |
| BEP/Hammond 保真 191/191、102/102 | 全一致 | 两脚本实测 **0 差异、0 权威外声明** | ✅ |
| 三理论 TASKS.md 全部打勾、0 待验收 | 全 done | `[ ]` 未打勾行实测 **0**（Marcus 54 行、Hammond 75 行、BEP 119 行 `[x]`） | ✅ |
| README 复核命令中的定理名 `PhotoLean.Marcus.descriptor_sharp`、`smoke_ring` | 存在 | 存在且可运行（本审查实跑 PASS） | ✅ |
| BEP `Basic.lean` "17 def + 1 inductive"（`RESULTS.md` §2） | 17+1 | 17+1 | ✅ |
| Marcus 提交数 47（`RESULTS.md:25`，复现命令为 git log 过滤 `^feat(`） | 47 | git 实测 **47** | ✅ |
| Hammond 87 工人提交 = 85 定理 + 2 定义（`RESULTS.md` §1） | 87 | git 实测 **87** | ✅ |
| BEP 164 提交分桶 18/28/32/13/25/48（`RESULTS.md:26`） | 164 | git 实测 **164** | ✅ |
| Marcus 全量公理探针 "69 条三公理 + 1 条仅 propext"（`RESULTS.md:311`） | 70/70 | 实跑 `marcus-all-axioms.lean`：70 行，唯一仅 `propext` 的正是 `inst_I1_zoneQ` | ✅ 逐字吻合 |
| M5b "31 条装 6 提交（2/4/12/4/4/5）"（`TASKS.md:151`，自报的铁律偏离） | 2/4/12/4/4/5 | 逐提交数 `+theorem` 行实测吻合 | ✅（偏离属实且未粉饰） |
| BEP 实例交叉核对 "checked 280 … CROSS-CHECK: OK"（`RESULTS.md:212`） | OK | 实跑 `bep-instance-check.py` 输出一致 | ✅ |
| 三理论 TASKS.md 全部 `[x]` 行涉及的定理/定义名 | 全部存在 | 逐一比对源码：**全部存在**（含 Hammond I1–I10 的 29 条 `inst_*`、BEP AUX 7 条、I11 四族×4 定理、`inst_I12`、`inst_nonvacuous`） | ✅ |
| 三个语句骨架 0 error 编译；sorry 占位计数 BEP 157 / Hammond 85 / Marcus 39（声明数 191/102/51 = 占位定理 + 定义级） | — | 实测吻合（探针目录按约定不在交付扫描内；Marcus 骨架另有 5 处注释提及 sorry 字样，非占位） | ✅ |

抽样核对模块内计数声称：`Marcus/Rate.lean` 头注释"6 条定理"（实测 6 ✓）；
`Marcus/Sharp.lean` 头注释"5 条签名与骨架逐字一致"（实测全文件 9 条 = 5 骨架 + 4 必要性内核，
头注释与 `TASKS.md` 验收记录对此有明确记账 ✓）；BEP 验收表各批计数（33、28、32=25+7AUX、
37=14+1+22、48）与 `plan.md §12` 清单逐行吻合 ✓。

### 6.2 发现的文档缺陷（全部一手复核确认；均不影响数学内容）

**确凿错误（2 处）**：

1. **定理名笔误（中英两版同错）**：`theories/Marcus/RESULTS.md:174` 与
   `theories/Marcus/RESULTS.en.md:169` 写 `lamTotal_pos`；实际定理名是 `lam_total_pos`
   （`PhotoLean/Marcus/Reorg.lean:183`；`plan.md:417`、`TASKS.md:81` 均写对）。这是全部
   定理名抽查中**唯一**的名字不一致（Marcus/Hammond/BEP 三份 RESULTS 中其余几十处名字
   全部与源码逐字一致）。
2. **任务板属主自相矛盾**：`theories/hammond/TASKS.md:97`（节标题）与 99–102 行把 H4
   `Compose.lean` 的属主记为 `prover_b`；同文件 173–176 行的偏离备注明确记录"delivered by
   `prover_a` instead of `prover_b`"。备注是有意的偏离登记，但属主列未随之更新。

**政策漂移（3 处互相矛盾 + 3 处实际漂移）**：

3. **README「双语文档」一节 vs 语言政策（直接冲突）**：`README.md:61-80` 把 10 对 `.en.md`
   作为现行"双语文档"体系展示、宣称"中文（权威，契约路径）"；而
   `AGENTS.md:38-40` 与 `proofs/ENGINE.md:80` 明文"**禁止镜像副本**……现存 `.en.md` 保留
   但不再扩展"、"一个产物写一次、写英文"。README 与该禁令抵触，且其对照表只列 Marcus 时代
   文件（hammond/BEP 并无 `.en.md`），与"每份都有并列英文版"的口径也不符。
4. **`.en.md` 已实际漂移 3 处**：README 列的 10 个镜像全部存在，但 (a) `proofs/ENGINE.en.md`
   **缺的恰恰是 §1.5 语言政策与 §1.6 多理论布局两节**（`ENGINE.md:65-110` 在英文版无对应）；
   (b) `EXPERIENCE.en.md` 未同步 `10713d1` 新增条目；(c) `API-NOTES.en.md` 未同步 `95f5744`
   订正。镜像禁令正是为防此类漂移，漂移实测发生了——这是禁令正确性的反向证据，也是 README
   继续展示镜像的现实代价。
5. **政策文本与 Marcus 时代文件实况不符**：政策（`AGENTS.md:29,32`、`ENGINE.md:42`）称
   Marcus 的 `plan/TASKS/LITERATURE`、`proofs/EXPERIENCE.md`、`proofs/API-NOTES.md` 为
   English 产物、`theories/Marcus/RESULTS.md` 为"每节英文原文+中文对照"的双语文件；实际
   **全部是中文**（RESULTS.md 全中文、英文在镜像里）。hammond/BEP 的对应文件才符合政策——
   政策显然晚于 Marcus，旧文件从未转换，政策文本也未登记这一既有例外。

**陈旧（2 处）**：

6. `README.md:52` 称 `theories/Marcus/plan.md`"**待填**"（实际 681 行、三理论均已交付）；
   README「现状」节（9–16 行）只字未提 hammond/BEP。
7. 时点性陈旧（均带时间语境、同文件内已有闭环解释，列为知情项）：`Marcus/TASKS.md:30`
   "LITERATURE.md 552 行"（现 692 行）；`:26` 骨架"31 处 sorry"（回填后现 39 处，
   `RESULTS.md:47` 已说明）；`BEP/RESULTS.md:241` 验收表 "Compose.lean (12)/12/12"（现 13
   定理，同文件 252–255 行已说明第 13 条 `secSlope_eq_lefflerSecant` 为验收后补交付）；
   `hammond/TASKS.md:25` `THEORIES="Marcus hammond"`（`ENGINE.yml:106` 现含 BEP）。

### 6.3 文档内部值得表扬的诚实记录（抽查确认属实）

- Marcus `RESULTS.md`「已知偏离」四条（`barrier_nonneg` 无独立提交的 `git add -A` 事故、
  M5b 提交粒度违反"每 lemma 一 commit"铁律、31 条实例定理不进骨架的保真覆盖缺口、
  6 条骨架外声明的后补回填）——逐条与代码/脚本实测吻合，**未粉饰**；
- Marcus `TASKS.md` 验收记录中 verifier 多次给出**内核级反例**纠正文档措辞（"被蕴含"实为
  "未使用"），纠正后的措辞与代码注释一致；
- BEP `RESULTS.md` 如实报告文献族全被证伪、"计划愿望未满足且不假装满足"。

---

## 7. 审查项⑥：模板是否真可复用

### 7.1 三理论模块结构对比

| 模块槽位 | Marcus | Hammond | BEP | 三理论一致？ |
|---|---|---|---|---|
| 描述层 | `Basic` | `Basic` | `Basic` | ✅ 稳定 |
| 定律层 | **`Barrier` + `Rate`**（势垒代数 + 速率/exp 层） | `Criterion` | `Criterion` | ⚠️ Marcus 分裂且名字不同 |
| 锐利成立条件 | `Sharp`（iff 主定理落点） | `Sharp` | `Sharp` | ✅ 稳定（均为 iff + 双失败分支见证） |
| 微观化/复合 | `Reorg` + `Compose`（Pekar 内外球重组能） | `Compose`（**直接复用** Marcus 的 Reorg） | `Compose`（**不用** Pekar 机制，`lamInner/lamOuter` 作抽象正实数） | ⚠️ 内容各异，仅槽位名稳定 |
| ℚ 判定层 | `RatModel` | `RatModel` | `RatModel` | ✅ 稳定（ℝ 定义→ℚ 副本→cast 桥→判定 iff） |
| 实例判决 | `Instances` | `Instances` | `Instances` | ✅ 稳定（具名判决定理 + 正负双向见证） |

用户所述"共用一套 `Basic/Criterion/RatModel/Sharp/Compose/Instances`"**字面上已不成立**：
六槽位中两槽在三理论间已变异（Marcus 无 `Criterion`；`Compose` 语义三理论三样——理论内复合 /
跨理论复用复合 / 跨理论桥接+抽象复合）。

### 7.2 真正可复用的是方法学，不是模块骨架

三理论 invariant（跨三案例 100% 保持、且与具体化学内容解耦）：

1. **语句权威先行**：探针骨架（含 sorry）先编译 → 交付逐字替换 → 保真脚本机械比对
   （三个 `*-fidelity.py` 实测全过）；
2. **ℝ 理论 + ℚ 可判定影子 + cast 转移引理**：ℝ 的序不可计算 ⇒ 实例判决无法在 ℝ 上内核算出，
   ℚ 影子是**可计算性的结构性解**，三理论同构复用（`zoneQ`/`hammondZoneQ`/`qEact…`，
   连"`decide` 卡含除法字面量须换 `norm_num`"的实测边界都一并复用）；
3. **锐利 iff 形态**：成立条件一律做成 `描述 ⟺ 参数条件`，必要性方向一律配**显式失败见证**
   （非否定量词搪塞）；正性/定义域前提并入刻画（Marcus 的速率正性合取、BEP 的 `0 < lam` 合取）
   是三案例独立收敛出的同一招；
4. **双向非平凡实例**：每个理论同时交付可采纳与不可采纳的具名判决；
5. **物理近似显式化**：前提写进签名、不折进定义；未使用前提保留并附内核反例说明。

这五条换一个化学理论（如 Arrhenius 温度律、Eyring 方程、Stern–Volmer 猝灭、Bell 隧穿校正）
依然成立，是模板的真资产。

### 7.3 过拟合风险（如实评估）

- **单一基质风险**：三个理论共享同一数学对象（等曲率双抛物面 + ℝ 初等代数；Marcus 多一个
  `Real.exp`）。模板的"定律层用 `field_simp; ring` 与 `nlinarith` 打天下"的策略，只在
  **有理函数 + 一个超越函数**的复杂度内被验证过。一个需要 ODE（动力学方案）、无穷级数
  （态密度和）、或概率语义（辐射/非辐射竞争）的理论，会要求定律层引入 mathlib 的分析/测度
  机制——`Criterion`/`RatModel` 两槽届时大概率要像 Marcus 一样再分裂。**模板未在这类
  不同基质上受过压，"换一个理论还站得住吗"目前只能回答：方法学站得住，模块骨架预期要变**。
- **`Compose` 槽语义未定**：三理论三种用法说明"复合/微观化"是每理论自定义的，不是抽象；
  建议把槽位改述为"主定理前提的降级层（假设→推导）"以名实相符。
- **签名未结构化**（见 §3.2）：跨理论关系裁决目前靠"同名单变量 + rfl 别名"钉合，第四个理论
  加入时建议引入显式签名结构，否则"等价"判定的严格性依赖纪律维持。

### 7.4 对目标①（AI 形式化能力边界）的旁证

`proofs/EXPERIENCE.md` 与 `TASKS.md` 验收记录显示：AI 在**代数恒等式与序推理**上已能
一次通过或少量迭代通过；失败模式集中在 (i) mathlib API 名漂移（靠 `API-NOTES.md` 校准沉淀）、
(ii) `decide` 的计算边界、(iii) "未使用 vs 被蕴含"的元推理错误（被 verifier 内核反例纠正）。
能力边界的如实陈述应是：**在已标定语句 + 初等实代数范围内，prover 是可靠的；语句标定本身
（把化学命题译成不多不少的 Lean 语句）仍是人类+规划期的核心贡献**——三个理论的关键语句
（描述谓词、锐利形式）都是规划期设计、Sprint 0 冻结的。

---

## 8. 问题清单（按严重度）

**阻塞级**：无。

**应修级**（建议下一迭代处理，均不危及已交付定理）：

| # | 问题 | 位置 | 建议 |
|---|---|---|---|
| F1 | `check.sh` 正则漏 `admit`、axiom 锚定不匹配 `private/protected` | `proofs/scripts/check.sh:136` | 扩正则；并把"每条交付定理过 `axioms.sh`"从 Marcus 特例推广为门标准件 |
| F2 | 文件级 `set_option linter.unusedVariables false`（无 `in`） | `PhotoLean/Marcus/Barrier.lean:58` | 改为逐声明 `in` 作用域，与其余 24 处一致 |
| F3 | `lamTotal_pos` 笔误（中英两版同错） | `theories/Marcus/RESULTS.md:174`、`RESULTS.en.md:169` | 改为 `lam_total_pos` |
| F4 | 任务板属主列与偏离备注互相矛盾 | `theories/hammond/TASKS.md:97,99-102` vs `:173-176` | 属主列改为 `prover_a`（偏离备注已解释调度原因，保留即可） |
| F5 | README「双语文档」节与镜像禁令冲突；「现状」节与 plan"待填"过时 | `README.md:9-16,52,61-80` | 镜像节改写为"历史镜像冻结"；现状节补入 hammond/BEP；删去"待填" |
| F6 | Marcus 时代文件语言与政策文本不符（plan/TASKS/LITERATURE/EXPERIENCE/API-NOTES 实为中文，RESULTS.md 中文主体+镜像） | `theories/Marcus/*`、`proofs/*.md` | 二选一：把政策文本登记为"Marcus 时代文件豁免、冻结不扩展"，或按政策转换；当前状态是政策说了但没执行，属于真源失真 |

**建议级**（模板演进方向）：

| # | 建议 | 动机 |
|---|---|---|
| S1 | 引入显式共享签名结构（如 `structure TwoParabolaModel`），让跨理论等价判定的 Σ 固定从纪律升级为类型 | §3.2：第四理论加入时防"同名不同义" |
| S2 | 模板文档把模块槽位改述为方法学五件套（§7.2），并注明 `Criterion`/`Compose` 是预期变异点 | §7.1：名实相符 |
| S3 | 定理计数在文档中区分"实质定理 / 桥接与别名证书 / 求值引理" | §2.2.1：防止"157 定理"被误读为 157 个深结果 |
| S4 | 选一个**不同基质**的第四理论（建议含温度依赖或动力学竞争）压测模板 | §7.3：单一基质是模板复用性证据的当前边界 |

---

## 9. 复核方式

本报告全部关键结论可由以下命令复跑（仓库根目录）：

```bash
proofs/scripts/lake build
proofs/scripts/check.sh --strict
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp
proofs/scripts/axioms.sh PhotoLean.Hammond.Sharp PhotoLean.Hammond.hammond_sharp
proofs/scripts/axioms.sh PhotoLean.BEP.Compose PhotoLean.BEP.epBounds_iff_no_inverted_direction
python3 theories/{Marcus,BEP,hammond}/probes/*-fidelity.py   # 各理论保真脚本
grep -rn --include='*.lean' -E 'sorry|admit' PhotoLean/       # 应为空
grep -rn --include='*.lean' -E ':= rfl|Iff\.rfl' PhotoLean/   # 应仅 4 处（见 §3.1）
```

—— 审查完毕。本报告仅新增 `review/` 目录，未触碰任何证明文件。
