# AGENTS.md — PhotoLean 工作区规则

本仓库是**光化学/光物理唯象理论的 Lean 4 形式化工程**，由"项目无关形式化引擎"
（DSH Agent preset）驱动。**先读 `proofs/ENGINE.md`** —— 它定义契约、角色与验收门。

## 铁律（不可协商）

1. **无 `sorry`、无自定义 `axiom`** 出现在交付定理中。判定靠脚本，不靠自觉：
   ```bash
   proofs/scripts/check.sh --strict <Module>
   proofs/scripts/axioms.sh <Module> <theorem>
   ```
2. **statement-first**：语句必须先在 Lean 中编译通过，才允许开始证明。
   语句改动只允许因 API 漂移，且必须记入 `proofs/API-NOTES.md`。
3. **物理近似显式化**：正性、连续性、可微性、参数不等式一律写成定理前提，
   禁止藏在定义里。前提必须是**承载的**（load-bearing）：发现"证明不消费的前提"时，按
   **最弱前提**修订语句并记入该理论的语句修正日志（Goldschmidt 确立的标准，见其
   plan §3.1）；第一批理论冻结的旧语句不回扫（未用前提只使定理更强），但 2026-09-21 起的
   新理论一律执行最弱前提标准。
4. **API 名不猜**：不确定就查 `proofs/API-NOTES.md`；没有就交 `api_researcher`
   用 `#check` 探针确认。
5. **文件所有权独占**：同一文件同一时间只有一个属主（见 `theories/Marcus/TASKS.md`）。
6. **验收独立**：写证明的人不能自判 PASS。verifier 只读、独立跑门、返回证据。
7. **打勾只在 verifier PASS 之后**，由 lead 执行。
8. **理论关闭清单**：任务板全勾 + verifier PASS **不等于理论关闭**。lead 在关闭一个理论前
   必须完成三件登记，缺一不可：
   ① **更新 `README.md` 现状节**（理论条目、模块构成、声明数、保真数）——这一接缝已三次
   漏更（模块数 21→23、理论数三→四→五），靠记忆必漏；
   ② **登记关系边**：在 `PhotoLean/Relations.lean` 与 `theories/RELATIONS.md` 登记本理论与
   既有理论的关系边；**无边时也必须显式登记"无边"** —— 关系图的完整性靠"每个理论都在
   图上"，不靠记忆；
   ③ **状态翻转的下游同步**：任何 review → done 的翻转（打勾）必须同步下游状态文本——
   该理论 `RESULTS.md` 的验证历史/状态段、`TASKS.md` 的**行体与表头**（两者一致）、以及
   **验收表**（新 verifier run 记入表内而非另立裸表、删除重复行、过期的 "in review"/
   "is running"/"todo" 措辞清除）。此接缝已四次出现（README 模块数 21→23、理论数三→四→五、
   Marcus 时代文档、Goldschmidt 的 RESULTS §7 与任务板行体），根因是翻转动作本身没有
   同步清单。

## 语言政策（Language policy）

产物一个语言，对话另一个语言 —— 硬规则，不是偏好：

| 对象 | 语言 |
|---|---|
| 仓库内一切**证明过程产物**的 markdown：`theories/Marcus/plan.md`、`theories/Marcus/TASKS.md`、`proofs/EXPERIENCE.md`、`proofs/API-NOTES.md`、`theories/Marcus/LITERATURE.md` | **English** |
| Lean 代码注释与 docstring、commit message、分支名、任务板行 | **English** |
| 与人类的对话：答复、提问、解释、计划、状态汇报、判决摘要 | **中文** |
| `theories/<理论>/RESULTS.md`（面向人类提问的答复） | **双语**：每节英文原文 + 中文对照 |
| 跨理论总结性文档 `theories/RELATIONS.md`（增量讨论稿）、`theories/GRAPH-REPORT.md`（总结报告） | **双语**：英文段 + 中文对照（登记于 2026-09-24 审查修正轮） |
| Lean 标识符、定理名、mathlib 名、命令原始输出 | **原样**，不翻译 |

**政策前的 Lean 源码例外（登记）**：Marcus 时代的 8 个交付模块与 `PhotoLean/Smoke.lean` 的注释/
docstring 为中文主体（代码与字符串字面量中无中文）。属政策前产物，**登记为例外、不回译**（回译会改动
已由 verifier 记录在案的模块 blob，须另起一轮验收）；2026-09-23 起纳入的新理论按英文写。

**控制面文件例外**：`AGENTS.md`、`proofs/ENGINE.md`、`proofs/ENGINE.yml` 是
工作区规则与契约本身（人类维护、agent 读取），继续用中文写。

**禁止镜像副本**：不要维护 `.en.md` / `-en.md` / `.zh.md` 一类的翻译副本。
一个产物写一次、写英文；双语只用于 `RESULTS.md` 类面向人类的答复与上表登记的两份跨理论文档。
（现存 `.en.md` 文件是在本政策之前生成的，保留但不再扩展。）

## 工具链（易踩坑，务必遵守）

```bash
proofs/scripts/lake build                     # 用这个，不要直接调 lake（不在 PATH）
proofs/scripts/lake build PhotoLean.Smoke     # 单模块
```

- `.toolchain/` 与 `.lake/packages/` 是**符号链接**，指向已构建的 mathlib 缓存。
- **禁止 `lake update`** —— 会重写 manifest 并触发数小时全量重建。
- 冷启动 `lake build` 约 10 秒是正常的（mathlib olean 已缓存）。
- **多 agent 并发工作区禁止 `git commit --amend`、`git rebase`、`git reset`**：
  2026-09-20 实测一次 `--amend` 与另一 agent 的提交构成 TOCTOU 竞态，改写了**别人的**
  commit message（靠 reflog 才还原）。提交只用 `git add <显式路径> && git commit -m ...`；
  也**禁止 `git add -A`**（2026-09-20 lead 实测吞掉工人的中间产物）。并发提交可能撞
  `.git/index.lock`：等 2 秒重试，不要删锁文件。
- commit message 里出现 `(cid:…)` 一类转义残渣时**不要改写历史**：加一个新提交或在
  经验库记录即可（历史是可核查证据，不是排版对象）。

## 迭代与记忆

- 一批独立 lemma → `workflow` 扇出；单个卡死 → `ralph`；长里程碑 → 目标工具。
- **每轮结束必须回写 `proofs/EXPERIENCE.md`**，包含"试过且失败"一栏。
  只记成功的条目视为无效。
- 文献调研结果进 `theories/Marcus/LITERATURE.md`，必须含"可形式化含义"。

## 当前状态

**已交付状态的单一真源是 `README.md` 现状节**（七个理论：Marcus 反转区、Hammond 假说、
BEP 原理、Kasha 规则、Sabatier 原则/火山图、Goldschmidt 容忍因子与取代规则，以及对称因子裁决
SymmetryFactor——本仓库第一条**已裁决混同** A1，把"β=1/2 对称因子"与结构转移系数的等同判为
`↔ kr=kp`；另加共享内核 `PhotoLean/Kernel.lean` 与关系图 `PhotoLean/Relations.lean` /
`theories/RELATIONS.md`）。各理论的进度真源是各自的 `theories/<理论>/TASKS.md`；跨理论关系边的
登记状态见 `theories/RELATIONS.md`。**注**：SymmetryFactor 与两个 Kasha 评审修正行（M1/M3）均已由独立
verifier 复核 **PASS**（2026-09-21，判决记于 `theories/SymmetryFactor/TASKS.md` run 1），看板已据
判决打勾、理论已关闭。

**关系边登记已闭环**：铁律 8 第 ② 项对第二批理论（Kasha、Sabatier）的补登记于 2026-09-21 完成——
`PhotoLean/Relations.lean` §7–§10（Kasha → Marcus 条件性组合边、Sabatier → BEP 组合边、
Sabatier ↔ Marcus 形似实异簇、无边登记），讨论稿见 `theories/RELATIONS.md` §2.4–§2.5 与 §3 N3；
对第六个理论（Goldschmidt，2026-09-21）的登记为**无边 + 形状相似**：`Relations.lean` §10 的
Goldschmidt 段与 `theories/RELATIONS.md` §2.5 / §3 N4——它是纯几何判据（离子半径与堆积），与
双抛物面家族不共享模块、不共享对象，故**显式登记无边**，并另记一条"只有形状相似"的登记（对称带 =
绝对偏差界、三分类器）以免把"同样的语句形状"误读成"同样的语句"。

**开工前必须先读目标理论 `TASKS.md` 的属主列与"验收记录"表** —— 该表记录了各里程碑的
verifier 判决、已关闭的缺陷、以及若干**已实测的坑**（并发窗口内的门判定、
`git add -A` 的并发事故、"未使用"≠"可推出" 等）。不要自行发明里程碑或改动已验收的语句。
