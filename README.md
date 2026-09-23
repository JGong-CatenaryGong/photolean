# PhotoLean

光化学/光物理**唯象理论的 Lean 4 形式化**工程，由 DSH 的"项目无关形式化引擎"
Agent preset 驱动。

本仓库同时是这套引擎的**参考实例**：引擎只读 `proofs/ENGINE.yml` 声明的叶子
数据面，因此换个理论只需要换一个仓库、重写那几个数据文件，不必改引擎。

## 现状

- Lean 4.17.0 + mathlib，工具链与缓存已联通（`lake build` 冷启动 ~10s）
- 验收门脚本可用：`proofs/scripts/check.sh --strict`、`proofs/scripts/axioms.sh`
- **十六个理论已交付**（`PhotoLean/` 均零占位证明、零自定义公理，`#print axioms` 只含
  `propext` / `Classical.choice` / `Quot.sound`）：
  - **Marcus 反转区**（经典马库斯模型）——`PhotoLean/Marcus/`（8 模块：描述层 / 势垒代数 / 速率层 /
    锐利成立条件 / 微观重组能 / ℚ 判定层 / 复合 / 实例判决），**82 条声明**，语句保真 **51/51**
    （`theories/Marcus/probes/marcus-fidelity.py`）；
  - **Hammond 假说**（过渡态坐标随驱动力递减）——`PhotoLean/Hammond/`（6 模块），**102 条声明**，
    语句保真 **102/102**；
  - **Bell–Evans–Polanyi 原理**（线性自由能关系的精确缺陷律）——`PhotoLean/BEP/`（6 模块），
    **191 条声明**，语句保真 **191/191**；
  - **Kasha 规则**（发光只来自该多重度的最低激发态）——`PhotoLean/Kasha/`（6 模块：描述层 / 定律层 /
    锐利容差条件 / 复合与 Marcus 桥 / ℚ 判定层 / 实例判决），**151 条声明**，语句保真 **151/151**
    （2026-09-21 评审修正轮后：`kashaDescriptor_nonvacuous` 语句强化 + 新增
    `perLevel_ic_ge_rad_insufficient`，见 `theories/kasha/plan.md` §3.1）
    （`python3 theories/BEP/probes/bep-fidelity.py --theory kasha --milestone <K1…K5b>`；该检查器
    亦服务其余理论，并支持按里程碑分级）；
  - **Sabatier 原则 / 火山图**（有效势垒在顶点取唯一全局最小 ⟺ 两支 BEP 斜率同号非零）——
    `PhotoLean/Sabatier/`（6 模块：描述层 / 定律层 / 锐利条件 / 双抛物面跨理论形式 / ℚ 判定层 /
    实例判决），**134 条公开声明**（107 定理 + 27 定义/归纳类型；另有 36 条 private 辅助引理），
    语句保真 **132/132**（`python3 theories/BEP/probes/bep-fidelity.py --theory Sabatier`；
    2 条描述层辅助定理在权威之外，已登记）；
  - **Goldschmidt 容忍因子与取代规则**（钙钛矿几何：`t = (r_A + r_O) / (√2 (r_B + r_O))`，其带判决、
    理想堆积 `t = 1` 的等价刻画、三条离子取代规则，以及 Shannon 半径实例的内核判决）——
    `PhotoLean/Goldschmidt/`（6 模块：描述层 / 规则层 / 定律层 / 锐利条件 / ℚ 判定层 / 实例判决），
    **139 条公开声明**（98 定理 + 40 定义 + 1 归纳类型；另有 8 条 private 辅助引理。2026-09-21 评审
    修正 M6：原括注"含 15 条定义与 1 个归纳类型"把 G1 `Basic.lean` 一层的定义级计数误挂到了全理论，
    逐模块分解见 `theories/goldschmidt/RESULTS.md` §8），
    语句保真 **139/139**（`python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt`）；
    该理论是**纯几何**判据（离子半径、堆积比值、其上的容忍带、电荷与电负性规则），与双抛物面家族
    **不共享任何对象**，因此经**无边登记**接入关系图（`Relations.lean` §10、`RELATIONS.md` §2.5/§3 N4）；
  - **对称因子裁决**（H1 跨越，2026-09-21；本仓库第一条**已裁决混同** A1）——把双抛物面模型推广到
    **非等曲率** `(kr, kp)`，证明热中性交叉坐标 `= √kp/(√kr+√kp)`（`[0,1]` 内唯一、无微积分），从而
    裁决电化学"转移系数/对称因子 = 1/2"的工作读法：`BetaHalfReading kr kp ↔ kr = kp`——**恰在等曲率
    时成立**（内核见证 `(1,4) ↦ 2/3 ≠ 1/2`、`(4,1) ↦ 1/3`；等曲率对角线经证书回接 `Kernel.tsCoord`
    与 `BEP.transfer`）。这解释了混同为何长存：教科书画的对称图正是它成立的区域——
    `PhotoLean/SymmetryFactor/`（5 模块：描述层 / 定律层 / 判决层 / ℚ 判定层 / 实例判决），
    **35 条声明**（28 定理 + 7 定义），语句保真 **35/35**
    （`python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor`）；文献位点成对：一手
    **实践位点**（"usually both taken to be equal to 0.5"，arXiv:2104.05424 §2.1）+ IUPAC TR 2014
    的**印刷警告**（pp.255–257），见 `theories/SymmetryFactor/LITERATURE.md`。**独立 verifier 复核 PASS**
    （2026-09-21，run 1 记于其看板；理论已按铁律 8 关闭）；
  - **光物理批次（2026-09-22/23，九个理论，A/B/C 三组）**——全部交付并经独立 verifier 复核
    （run 1–5 PASS + 阶段三终审），阶段三完成了权威修订（16 行前提修剪、3 行空泛化重冻结、
    2 条负结果定理）与关系图登记（`Relations.lean` §12–§16，23 条新行）：
    - **Kasha–Vavilov 独立性**（D2 裁定，A2 类新边类）——`PhotoLean/KashaVavilov/`（3 模块），
      **29 条声明**，保真 **29/29**；双向逐点独立见证 + 闭合量化 iff 边界 + 无损角分离；
    - **Stern–Volmer 可辨识性**（D1 裁定，A3 类新边类）——`PhotoLean/SternVolmer/`（4 模块），
      **46 条声明**，保真 **46/46**；强度观测非单射 + 寿命通道 iff 判别 + 二阶差分共存见证；
    - **量子产率可加性**（并行通道演算，批次的代数脊柱）——`PhotoLean/QuantumYield/`（4 模块），
      **29 条声明**，保真 **29/29**；
    - **荧光/磷光竞争**——`PhotoLean/FluorPhos/`（4 模块），**30 条声明**（含负结果行
      `fpC5_firstForm_refuted`），保真 **30/30**；
    - **能隙律**（Englman–Jortner 形式，经典极限）——`PhotoLean/EnergyGapLaw/`（5 模块），
      **26 条声明**，保真 **26/26**；
    - **Stokes 位移规则**——`PhotoLean/StokesShift/`（4 模块），**36 条声明**（含负结果行
      `invertedCorner_firstForm_refuted`），保真 **36/36**；
    - **内转换 vs 系间窜越**（FC 竞争 + 自旋折扣）——`PhotoLean/ICvsISC/`（4 模块），
      **20 条声明**，保真 **20/20**；
    - **Förster 共振能量转移**（含 κ² 紧界 4 与 2/3 标架平均）——`PhotoLean/Forster/`（4 模块），
      **32 条声明**，保真 **32/32**；
    - **Einstein A/B 系数等价链**——`PhotoLean/Einstein/`（4 模块），**33 条声明**，
      保真 **33/33**；
- 每个理论的规划 / 任务板 / 文献 / 面向人类提问的答复：`theories/<理论>/{plan,TASKS,LITERATURE,RESULTS}.md`
- **跨理论关系图**（覆盖全部十六个理论：三个双抛物面"原理"是同一二次对象的三种读法，Kasha 与
  Sabatier 经**组合边**接入，Sabatier↔Marcus 另有一组"形似实异"非关系边，Goldschmidt 经**无边登记**
  接入并另有一条"只有形状相似"的 N4 登记，SymmetryFactor 以**已裁决混同**（A1 类）接入并与
  Marcus/Hammond/BEP 有特化证书边；光物理九理论经 §12 内核证书 / §13 D2 裁定（A2 类：
  已裁决独立性）/ §14 D1 裁定（A3 类：可辨识性）/ §15 组合边（全部经过 QuantumYield 代数脊柱）
  接入，其余理论对**显式登记无边**于 §16）：
  共享内核 `PhotoLean/Kernel.lean`、可检查的关系清单 `PhotoLean/Relations.lean`（**73 条声明**：内核证书 /
  真等价 / 单向蕴含 / 定义复用 / 组合边 / 非关系 / 无边登记（含 Goldschmidt）/ 已裁决混同（A1）/
  批次内核证书（§12）/ D2 裁定（§13）/ D1 裁定（§14）/ 批次组合边与形似（§15）/ 扩展无边登记（§16））、
  双语讨论稿 `theories/RELATIONS.md`
- `PhotoLean/Smoke.lean` 是环境冒烟测试
- 注：`README.en.md` 是语言政策生效前的英文镜像，按仓库政策**不再扩展**；权威内容以本文件为准

### 复核方式

```bash
proofs/scripts/check.sh --strict                                   # 全树扫描 + 构建（应 verdict: PASS）
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp   # 主定理公理检查
proofs/scripts/lake env lean theories/Marcus/probes/marcus-statement-skeleton.lean           # 语句权威（含抱歉占位，仅编译）
# 七个理论的语句保真（应各报 0 signature differences）
python3 theories/Marcus/probes/marcus-fidelity.py
python3 theories/BEP/probes/bep-fidelity.py                         # BEP，另支持 --theory kasha|Sabatier|goldschmidt|SymmetryFactor
python3 theories/hammond/probes/hammond-fidelity.py
# 第七个理论（SymmetryFactor，H1 跨越 / A1 已裁决混同）的专属复核：判决 iff 与证伪行的公理检查
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Sharp PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants
proofs/scripts/axioms.sh PhotoLean.SymmetryFactor.Instances PhotoLean.SymmetryFactor.inst_conflation_falsified
python3 theories/BEP/probes/bep-fidelity.py --theory SymmetryFactor  # 35/35, 0 differences
# 第六个理论（Goldschmidt）的专属复核：主等价式的公理检查 + off-kernel 精确有理实例交叉检查
proofs/scripts/axioms.sh PhotoLean.Goldschmidt.Criterion PhotoLean.Goldschmidt.conforms_iff_radius_window
python3 theories/goldschmidt/probes/goldschmidt-instance-check.py   # exit 0, 0 mismatches
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
| `proofs/METHOD.md` | **可复用形式化模板**（目标③交付物）：方法学五件套、模块骨架的稳定核与变异槽、四种基质的适配模式、关系图五类边、已实测的坑 |
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
