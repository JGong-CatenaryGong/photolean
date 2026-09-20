# 形式化引擎契约（Formalization Engine Contract）

> 本文档定义**项目无关的形式化引擎**与**具体理论项目**之间的接口。
> 引擎实现为 DSH Agent preset；本项目（PhotoLean）是它的一个实例。

## 0. 设计命题

把 AI 用于唯象理论的严格化，工程上真正难的不是"让模型写 Lean"，而是三件事：

1. **纪律不能靠自觉** —— 无 `sorry`、无自定义 `axiom` 必须是**脚本级的可执行判据**，
   而不是 persona 里的一句叮嘱；
2. **迭代必须有记忆** —— 失败路径要沉淀，否则每一轮 fresh agent 都在重踩死路；
3. **验收必须独立** —— 写证明的角色不能自己判定"证完了"。

因此引擎的架构是：**角色分工（写入）+ 脚本证据门（判定）+ 经验库（记忆）**。
三者都落在数据文件上，因此换一个理论只需重写数据，不需要改引擎。

### 与 Hyra / AlphaEvolve 的关系

| | 机制核心 | 在 Lean 场景的落地 |
|---|---|---|
| **AlphaEvolve** | 候选**种群** + 变异 + 选择压力 | 一个 lemma 的多条战术路径作为候选；`workflow` 并发探索后择优 |
| **Hyra-1.0** | **经验库**（Experience Bank）+ producer-consumer，评估器与解**共进化** | `EXPERIENCE.md` 为经验库；`workflow`/`ralph` 为 producer |
| **关键简化** | 评估器可能被 reward hacking，故需外层循环精炼 | **Lean 内核不可 hack**：`lake build` 通过即真。两层循环坍缩为单层，只需积累经验，无需进化评估器 |

这个化简是本引擎相对通用科学发现 agent 的结构性优势：**终止判据是可信的**，
不存在"分数涨了但解是假的"这一类失效。

## 1. 叶子数据面（Leaf Data Plane）— 唯一接口

引擎只读这些文件的**声明**；它们的路径写在 `proofs/ENGINE.yml`。
换项目 = 换仓库 + 重写这些文件。

| 文件 | 作用 | 写入者（唯一真源） |
|---|---|---|
| `theories/Marcus/plan.md` | 理论规划：里程碑、语句、证明草图、sprint 顺序、验收标准 | 人类 + lead |
| `theories/Marcus/TASKS.md` | 任务板：状态唯一真源 | **仅 lead** 打勾 |
| `proofs/EXPERIENCE.md` | 经验库：成败模式，跨轮复用 | 所有角色回写 |
| `proofs/API-NOTES.md` | mathlib API 校准日志（名字漂移的唯一真源） | api_researcher |
| `theories/Marcus/LITERATURE.md` | 文献调研记录：源、结论、**可形式化含义** | literature_researcher |
| `theories/Marcus/probes/` | `#check` 探针，可提交 | api_researcher |
| `theories/Marcus/RESULTS.md` | **唯一的双语文件**：面向人类提问的答复，每节英文原文 + 中文对照 | lead |

**规则：任何角色都不得绕过 TASKS.md 声称任务完成。**
工人报告 DONE ≠ 任务 DONE；只有 verifier PASS 后由 lead 打勾。

### 1.1 多理论扩展（2026-09-20 起）

一个仓库可以承载多个理论：上表的 `PLAN` / `TASKS` / `LITERATURE` / `PROBES` / `RESULT`
是**规范理论**（当前为 Marcus）的叶子；追加理论在 `ENGINE.yml` 里用
`<LEAF>_<theory>`（如 `PLAN_hammond`）声明，并把理论名登记进 `THEORIES`。
`check.sh` 会按 `THEORIES` 逐项做叶子存在性检查；`SOURCE_DIRS` 保持**全局** ——
任何交付源码都必须落在扫描范围内，否则验收门看不见它。

第二个理论（Hammond 假说）的布局即此扩展的样例：

| 对象 | 路径 |
|---|---|
| 理论过程产物 | `theories/hammond/{plan.md,TASKS.md,LITERATURE.md,RESULTS.md,probes/}` |
| Lean 源码 | `PhotoLean/Hammond/*.lean`（命名空间 `PhotoLean.Hammond`，含子命名空间 `.Rat`） |

**注意**：新增理论时 `lakefile.toml` 的 `defaultTargets` 必须同步补入新模块 ——
否则裸跑 `check.sh --strict` 只构建旧目标，而扫描覆盖全目录（验收漏洞）。

## 1.5 语言政策（Language Policy）

产物一个语言，对话另一个语言。原因很实际：模型在英文下写 Lean 注释与
markdown 更稳、检索 mathlib 文档更顺；而人类读者需要用中文参与判断。
两者不该互相污染，**更不该靠维护翻译副本来同时满足** —— 镜像文件是双份成本，
且必然漂移（违反"单一真源"）。

| 对象 | 语言 |
|---|---|
| 上表一切**证明过程产物**的 markdown | **English** |
| Lean 代码注释 / docstring、commit message、分支名、任务板行 | **English** |
| 与人类的对话：答复、提问、计划、状态汇报、判决摘要 | **中文** |
| `theories/Marcus/RESULTS.md` | **双语**（唯一例外：每节英文原文 + 中文对照） |
| Lean 标识符、定理名、mathlib 名、命令原始输出 | **原样**，不翻译 |

**禁止镜像副本**（`.en.md` / `-en.md` / `.zh.md`）：一个产物写一次、写英文。

**控制面例外**：`AGENTS.md`、`proofs/ENGINE.md`、`proofs/ENGINE.yml` 是工作区
规则与契约本身（人类维护、agent 读取），保持中文。

这条政策同时编码在 preset 的 lead persona、全部 7 个角色 persona 与
`formalization-engine` skill 中 —— 换 preset 版本不会丢，因为工作区自己也声明了。

## 1.6 多理论布局（引擎扩展）

一个仓库可承载**多个理论**：每个理论 = `theories/<理论>/`（数据面）+ `PhotoLean/<理论>/`（Lean 源码）。
`theories/<理论>/` 必须含五项，缺一项即 FAIL（由 `check.sh` 的第二遍遍历强制）：

```
theories/<理论>/
  plan.md        TASKS.md        LITERATURE.md        RESULTS.md        probes/
```

验收门对每个理论做**两遍**检查，两遍并存、互不替代：

| 遍 | 机制 | 覆盖 |
|---|---|---|
| 变量遍 | 契约里的 `<LEAF>_<理论>` 变量（如 `PLAN_BEP`） | 只覆盖**显式列进 `THEORIES`** 的理论 |
| 目录遍 | 遍历 `<THEORIES_DIR>/*/`（`THEORIES_DIR` 亦由契约声明） | 覆盖**任何**理论目录，包括刚建的 |

**为什么两遍都要**：变量遍在实测中被发现**会静默漏过**新建的理论目录 —— 契约里没声明变量，
循环就 `continue`，门照样 PASS。目录遍专门堵这个洞，且能拦住"半初始化的理论目录"。
这是本引擎反复出现的同一类教训：**门的覆盖范围必须被独立验证**（见 `EXPERIENCE.md`）。

引擎级（跨理论共享）的叶子只有两个：`EXPERIENCE.md`（经验库）与 `API-NOTES.md`（mathlib 校准）。

## 2. 角色名册（项目无关）

引擎的 preset 注册固定角色名；**每个角色的具体职责从叶子数据面读取**，
persona 只描述"怎么做"，不写死"哪个文件"。

| 角色 | 工具名 | 权限 | 职责 |
|---|---|---|---|
| `prover_a` … `prover_d` | 同名工具 | 读写源码 | 按分配区域证明；独占文件所有权 |
| `api_researcher` | `api_researcher` | 读写 `API-NOTES.md`/`probes/` | mathlib 名字校准，禁止猜名 |
| `verifier` | `verifier` | **只读** | 独立跑证据门，返回 PASS/FAIL |
| `literature_researcher` | `literature_researcher` | 读写 `LITERATURE.md` | 文献调研，产出"可形式化含义" |

`prover_a..d` 是**池**而非硬绑定：具体区域划分由 `theories/Marcus/plan.md` 的里程碑与
`TASKS.md` 的属主列决定。一个项目只有两个区域就只用 a、b。

## 3. 验收门（脚本化，引擎不内联判据）

交付一个 lemma 必须依次通过：

```bash
lake build <module>                          # 1. 编译
proofs/scripts/check.sh --strict <module>    # 2. sorry/axiom 扫描 + 构建
proofs/scripts/axioms.sh <Module> <theorem>  # 3. #print axioms 只含基础设施公理
git log -1 --oneline                         # 4. 提交信息符合 feat(<area>): <lemma>
```

第 3 步的通过标准由 `ENGINE.yml` 的 `ALLOWED_AXIOMS` 定义
（默认 `propext Classical.choice Quot.sound`）。**出现 `sorryAx`
或任何自定义 `axiom` 即 FAIL** —— 这是"axiom 纪律"的可执行形式。

## 4. 迭代循环（自反思）

工具选择按任务规模分三档，**共同点是每轮结束后回写经验库**：

| 场景 | 工具 | 循环形态 |
|---|---|---|
| 一批独立 lemma | `workflow` | 一次扇出，`parallel`/`pipeline` 并发，结构化结果回收 |
| 单个卡住的证明 | `ralph` | fresh agent 多轮，工作区为长期记忆，`EXPERIENCE.md` 逐轮细化 |
| 一个长里程碑 | 目标工具（`create_goal`） | 跨轮持续，`TASKS.md` 为进度真源 |

**经验库回写是强制的**：任何 BLOCKED 或成功都追加一条（格式见 `EXPERIENCE.md`）。
"试过且失败"一栏不得为空 —— 没有失败信息的条目视为无效。

### 经验库条目示例（格式参考）

```markdown
## 2026-09-20 — strictMono 复合 1/x — prover_b — DONE
- 目标：`StrictAntiOn f s` 下 `fun x => 1 / f x` 的单调性
- 试过且失败：
  - `positivity` 单独收尾 → 需要先有 `f x > 0` 的显式前提
  - `linarith [one_div_lt_one_div_of_lt ...]` → 缺 `0 < f b`，方向反了
- 奏效：先 `have hb : 0 < f b := ...`，再 `one_div_lt_one_div_of_lt hb h`；commit <hash>
- 可复用模式：**先建正性 `have`，再引 `*_div_*` 类引理**，不要指望 `linarith` 自动补前提
```

## 5. 文献调研流程

`literature_researcher` 的产出必须落到 `LITERATURE.md`，每条含：

1. **源**：DOI / arXiv id / 标题，可核查；
2. **结论**：该文献对理论的主张；
3. **可形式化含义**：哪些假设能被显式化为 Lean 前提、哪些是物理近似、哪些
   在当前 mathlib 下不可表达（这一栏是**唯一**对形式化有用的部分）。

原始论文 PDF 与 LaTeX 源放 `theories/Marcus/literature/`，禁止把整篇 PDF 内容灌进上下文。

## 6. 工具链环境（本机特有，务必遵守）

- 工具链解包在 `.toolchain/`（Lean 4.17.0），**不在 PATH 上**；
  永远通过 `proofs/scripts/lake` 调用 `lake`。
- `.lake/packages` 与 `.toolchain` 是指向已构建缓存的**符号链接**：
  `lake build` 冷启动约 10 秒（mathlib olean 已缓存）。**不要 `lake update`** ——
  会重写 manifest 并触发数小时全量重建。
- mathlib rev 必须与 `lean-toolchain` 一致；升级需成对修改并重拉缓存。
