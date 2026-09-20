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
   禁止藏在定义里。
4. **API 名不猜**：不确定就查 `proofs/API-NOTES.md`；没有就交 `api_researcher`
   用 `#check` 探针确认。
5. **文件所有权独占**：同一文件同一时间只有一个属主（见 `theories/Marcus/TASKS.md`）。
6. **验收独立**：写证明的人不能自判 PASS。verifier 只读、独立跑门、返回证据。
7. **打勾只在 verifier PASS 之后**，由 lead 执行。

## 语言政策（Language policy）

产物一个语言，对话另一个语言 —— 硬规则，不是偏好：

| 对象 | 语言 |
|---|---|
| 仓库内一切**证明过程产物**的 markdown：`theories/Marcus/plan.md`、`theories/Marcus/TASKS.md`、`proofs/EXPERIENCE.md`、`proofs/API-NOTES.md`、`theories/Marcus/LITERATURE.md` | **English** |
| Lean 代码注释与 docstring、commit message、分支名、任务板行 | **English** |
| 与人类的对话：答复、提问、解释、计划、状态汇报、判决摘要 | **中文** |
| `theories/Marcus/RESULTS.md`（面向人类提问的答复） | **双语**：每节英文原文 + 中文对照 |
| Lean 标识符、定理名、mathlib 名、命令原始输出 | **原样**，不翻译 |

**控制面文件例外**：`AGENTS.md`、`proofs/ENGINE.md`、`proofs/ENGINE.yml` 是
工作区规则与契约本身（人类维护、agent 读取），继续用中文写。

**禁止镜像副本**：不要维护 `.en.md` / `-en.md` / `.zh.md` 一类的翻译副本。
一个产物写一次、写英文；双语只用于 `theories/Marcus/RESULTS.md` 这一个文件。
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

理论方向已定：**Marcus 反转区**（经典马库斯模型，`theories/Marcus/plan.md` M1–M5，人类确认于 2026-09-20）。
交付物：`PhotoLean/Marcus/{Basic,Barrier,Rate,Sharp,Reorg,Compose,RatModel,Instances}.lean`；
面向人类提问的答复：`theories/Marcus/RESULTS.md`；进度真源：`theories/Marcus/TASKS.md`。

**开工前必须先读 `theories/Marcus/TASKS.md` 的属主列与"验收记录"表** —— 该表记录了各里程碑的
verifier 判决、已关闭的缺陷、以及若干**已实测的坑**（并发窗口内的门判定、
`git add -A` 的并发事故、"未使用"≠"可推出" 等）。不要自行发明里程碑或改动已验收的语句。
