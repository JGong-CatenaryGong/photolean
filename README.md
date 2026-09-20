# PhotoLean

光化学/光物理**唯象理论的 Lean 4 形式化**工程，由 DSH 的"项目无关形式化引擎"
Agent preset 驱动。

本仓库同时是这套引擎的**参考实例**：引擎只读 `proofs/ENGINE.yml` 声明的叶子
数据面，因此换个理论只需要换一个仓库、重写那几个数据文件，不必改引擎。

## 现状

- Lean 4.17.0 + mathlib，工具链与缓存已联通（`lake build` 冷启动 ~10s）
- 验收门脚本可用：`proofs/scripts/check.sh --strict`、`proofs/scripts/axioms.sh`
- **三个理论已交付**（`PhotoLean/` 共 21 个模块 = 20 个理论模块 + `Smoke`，均零占位证明、零自定义公理，
  `#print axioms` 只含 `propext` / `Classical.choice` / `Quot.sound`）：
  - **Marcus 反转区**（经典马库斯模型）——`PhotoLean/Marcus/`（8 模块：描述层 / 势垒代数 / 速率层 /
    锐利成立条件 / 微观重组能 / ℚ 判定层 / 复合 / 实例判决），**82 条声明**，语句保真 **51/51**
    （`theories/Marcus/probes/marcus-fidelity.py`）；
  - **Hammond 假说**（过渡态坐标随驱动力递减）——`PhotoLean/Hammond/`（6 模块），**102 条声明**，
    语句保真 **102/102**；
  - **Bell–Evans–Polanyi 原理**（线性自由能关系的精确缺陷律）——`PhotoLean/BEP/`（6 模块），
    **191 条声明**，语句保真 **191/191**。
- 每个理论的规划 / 任务板 / 文献 / 面向人类提问的答复：`theories/<理论>/{plan,TASKS,LITERATURE,RESULTS}.md`
- **跨理论关系图**（三个"原理"作为同一二次对象的三种读法）：共享内核 `PhotoLean/Kernel.lean`、
  可检查的关系清单 `PhotoLean/Relations.lean`、双语讨论稿 `theories/RELATIONS.md`
- `PhotoLean/Smoke.lean` 是环境冒烟测试

### 复核方式

```bash
proofs/scripts/check.sh --strict                                   # 全树扫描 + 构建（应 verdict: PASS）
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp   # 主定理公理检查
proofs/scripts/lake env lean theories/Marcus/probes/marcus-statement-skeleton.lean           # 语句权威（含抱歉占位，仅编译）
```
**`lake build` 返回 0 不是验收**：零占位证明与自定义公理都会返回 0，必须三层齐备
（构建 + 扫描 + `#print axioms`），且由不写证明的角色独立执行。

## 快速开始

```bash
proofs/scripts/lake build                     # 全量（首次 ~10s，mathlib 已缓存）
proofs/scripts/lake build PhotoLean.Smoke     # 单模块
proofs/scripts/check.sh --strict              # 构建 + sorry/axiom 扫描（交付前必跑）
proofs/scripts/axioms.sh PhotoLean.Smoke smoke_ring   # 打印定理实际依赖的公理
```

> `lake` 不在 PATH 上 —— 永远通过 `proofs/scripts/lake` 调用。
> **禁止 `lake update`**（会重写 manifest 并触发数小时全量重建）。

## 纪律

交付定理不得含 `sorry` 或自定义 `axiom`；`#print axioms` 只允许
`propext` / `Classical.choice` / `Quot.sound`。所有物理近似必须显式化为
定理前提。判定由脚本执行，不依赖模型自觉。

## 文档

| 文件 | 作用 |
|---|---|
| `proofs/ENGINE.md` | **引擎契约**：叶子数据面、角色、验收门、迭代循环 |
| `AGENTS.md` | 工作区铁律与工具链坑 |
| `theories/Marcus/plan.md` | 理论规划（语句、证明草图、里程碑、验收标准） |
| `theories/Marcus/TASKS.md` | 任务板（状态唯一真源） |
| `proofs/EXPERIENCE.md` | 经验库：成败模式，跨轮复用 |
| `proofs/API-NOTES.md` | mathlib API 校准日志 |
| `theories/Marcus/LITERATURE.md` | 文献调研记录 |

同类已完成实例（写法范本）：`[local path removed]`（RACI/AIE，
M1–M4 + M1* 全证完，0 sorry / 0 自定义 axiom）。

## 双语文档 / Bilingual documentation —— 历史镜像（冻结，不再扩展）

语言政策（`AGENTS.md`、`proofs/ENGINE.md` §1.5）是：**一个产物写一次，写英文**；
中文只用于与人类的对话，契约声明的 `RESULT` 是唯一的双语文件（每节英文原文 + 中文对照）——
hammond / BEP 的 `RESULTS.md` 即按此格式书写，两者从一开始就没有 `.en.md` 镜像。
下表列出的 `.en.md` 是**政策之前**生成的**历史镜像**，**保留但冻结**：不再同步、不再新增。

**为什么冻结**：镜像已实测漂移三次 —— `proofs/ENGINE.en.md` 缺 §1.5 语言政策与 §1.6 多理论布局两节；
`proofs/EXPERIENCE.en.md` 落后于 `10713d1`；`proofs/API-NOTES.en.md` 落后于 `95f5744`。
这正是"双份维护必然漂移"的反向证据，所以读镜像时**以"当前维护版本"列为准**；
此外 Marcus 时代的产物（`plan` / `TASKS` / `LITERATURE` / `EXPERIENCE` / `API-NOTES`）实际是中文主体，
英文在镜像里 —— 政策晚于这批文件，此处如实登记为既有例外，不再回译。

| 历史镜像（冻结） | 当前维护版本（漂移时以此为准） |
|---|---|
| `README.en.md` | `README.md` |
| `AGENTS.en.md` | `AGENTS.md`（控制面文件） |
| `proofs/ENGINE.en.md` | `proofs/ENGINE.md`（控制面文件） |
| `theories/Marcus/plan.en.md` | `theories/Marcus/plan.md` |
| `theories/Marcus/TASKS.en.md` | `theories/Marcus/TASKS.md` |
| `proofs/EXPERIENCE.en.md` | `proofs/EXPERIENCE.md` |
| `proofs/API-NOTES.en.md` | `proofs/API-NOTES.md` |
| `theories/Marcus/LITERATURE.en.md` | `theories/Marcus/LITERATURE.md` |
| `theories/Marcus/RESULTS.en.md` | `theories/Marcus/RESULTS.md` |
| `theories/Marcus/literature/README.en.md` | `theories/Marcus/literature/README.md` |

**禁止新增镜像**：新的产物（含本 README 的后续修改）只写一次、写英文。

## 许可

Apache-2.0
