# PhotoLean 任务板（状态唯一真源）

- 状态词汇：`todo`（未开始）→ `stmt`（语句已校准且编译）→ `proving`（证明中）
  → `review`（已交 verifier）→ `done`（verifier PASS 且已提交）。
- 行格式：`- [ ] 定理 — 文件 — 属主 — 状态 — 备注`。
- **打勾（`[x]`）只允许发生在 verifier PASS 之后**，由 lead 执行；工人不得自行打勾。
- 属主列填引擎角色名（`prover_a` / `prover_b` / `prover_c` / `prover_d`）；
  同一文件不得有两个并发属主。
- 契约与角色定义：`proofs/ENGINE.md`；规划与语句：`theories/Marcus/plan.md`；
  **语句权威 = `theories/Marcus/probes/marcus-statement-skeleton.lean`（已编译通过）**。
- 理论方向：**Marcus 反转区（经典马库斯模型）**，人类确认于 2026-09-20。

---

## Sprint 0 — 环境与语句校准（已收尾）

- [x] Lean 工具链与 mathlib 缓存联通（`lake build` 冷启动 ~10s，`PhotoLean.Smoke` 通过）
- [x] 验收门脚本可用（`proofs/scripts/check.sh --strict` / `axioms.sh`）
- [x] **验收门行为已验证**：干净树 PASS；`sorry` / 自定义 `axiom` / 隐藏 `sorry`
      三类违规全部被拦（证据见 `proofs/EXPERIENCE.md` 首条 —— 关键发现：
      `lake build` 对三类违规**都返回 0**，单靠构建通过不构成验收）
- [x] 项目契约落盘（`proofs/ENGINE.yml`，叶子数据面齐备）
- [x] **理论规划落盘**：`theories/Marcus/plan.md` = Marcus 反转区 M1–M5
      （人类确认：完整五段 + 双轨实例 + 文献可核查参数）
- [x] **语句骨架编译通过**：`theories/Marcus/probes/marcus-statement-skeleton.lean`
      （M1–M5 全部语句，31 处 `sorry` warning、**0 error**；末尾 4 个风险探针无 sorry 真通过）
- [x] `theories/Marcus/probes/` 目录建立；`git init` + 基线 commit
- [x] API 校准完成（`api_researcher`）：`proofs/API-NOTES.md` 重写（可用/漂移/不可用三栏 + 20 个保留 token 的标识符合法性矩阵）、
      5 个探针 0 error，另附 `theories/Marcus/probes/marcus-proof-skeletons.lean`（36 条**已跑通**证明体，覆盖 M1–M5a）
- [x] 文献参数表完成（`literature_researcher`）：`theories/Marcus/LITERATURE.md` 552 行，含 6 组"已核实"参数、
      DOI 更正、Pekar 条件、5 条必显式化近似、不可表达清单排序

---

## M1 — 描述层（`PhotoLean/Marcus/Basic.lean`；属主 prover_a；Sprint 1）

- [x] 定义 `barrier` / `rate` / `InvertedRegion` / `NormalRegion` / `InvertedDescriptor`
      / `NormalDescriptor` / `Zone` / `zone` — Marcus/Basic.lean — prover_a — done — plan §2.2；commit 3644a82
- [x] `zone_eq_normal_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit f3d2055
- [x] `zone_eq_barrierless_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit ac80776
- [x] `zone_eq_inverted_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit c98c85d
- [x] `zone_trichotomy` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit 1376f8e

## M2 — 势垒代数（`PhotoLean/Marcus/Barrier.lean`；属主 prover_a；Sprint 2）

- [x] `barrier_nonneg` — Marcus/Barrier.lean — prover_a — done — plan §5；⚠️ **提交偏差**：内容已被
      lead 的 `c000996`（`git add -A` 误卷）吸收，本条无独立 feat 提交；余下 8 条仍各自一提交
- [x] `barrier_at_lam` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 8d9c2ff
- [x] `barrier_symm` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 03c740f
- [x] `barrier_min_at_lam` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 169a0c7
- [x] `barrier_mono_of_pos` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 3dc2fcc
- [x] `barrier_antitone_of_pos` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 4ab7259
- [x] `barrier_antitone_of_neg` — Marcus/Barrier.lean — prover_a — done — plan §5；commit 4561931
- [x] `barrier_zero_lam` — Marcus/Barrier.lean — prover_a — done — plan §5；commit ae1276e
- [x] `barrier_mono_cases` — Marcus/Barrier.lean — prover_a — done — plan §5；commit f0d79ee

## M3 — 速率层（`PhotoLean/Marcus/Rate.lean`；属主 prover_b）

- [x] `rate_pos` — Marcus/Rate.lean — prover_b — done — plan §6（Sprint 2；只依赖 M1）；commit 8840fdf
- [x] `rate_gt_of_barrier_lt` — Marcus/Rate.lean — prover_b — done — plan §6（**核心引理**；Sprint 2）；commit 464edbf
- [x] `normal_rate_increases` — Marcus/Rate.lean — prover_b — done — plan §6（Sprint 3；依赖 M2）；commit 671bee1
- [x] `inverted_rate_decreases` — Marcus/Rate.lean — prover_b — done — plan §6（Sprint 3；依赖 M2）；commit 8cfde00
- [x] `rate_peak_at_lam` — Marcus/Rate.lean — prover_b — done — plan §6（Sprint 3；依赖 M2）；commit c4a70fd
- [x] `rate_ratio`（拉伸目标，不阻塞）— Marcus/Rate.lean — prover_b — done — plan §6；commit 60fe95f

## M4a — 锐利刻画（`PhotoLean/Marcus/Sharp.lean`；属主 prover_a；Sprint 4）

- [x] `inverted_descriptor_holds` — Marcus/Sharp.lean — prover_a — done — plan §7.1；commit e15e9d5
- [x] `normal_descriptor_holds` — Marcus/Sharp.lean — prover_a — done — plan §7.1；commit ccab8fe
- [x] `descriptor_fails_of_nonpos_lam` — Marcus/Sharp.lean — prover_a — done — plan §7.1；commit a520b0a
- [x] `descriptor_sharp`（**关键路径**；verifier 重点复核必要性两支）— Marcus/Sharp.lean — prover_a — done — plan §7.1；commit bfcbb6c
- [x] `inverted_descriptor_holds_of_neg`（拉伸；证明"速率正性"前提不可去）— Marcus/Sharp.lean — prover_a — done — plan §7.1；commit 67c42f5
- [x] 必要性内部内核（4 条，不在骨架中）`sharp_A_pos` / `sharp_lam_pos_of_lt` / `sharp_lam_pos_of_eq` / `sharp_lam_pos` — Marcus/Sharp.lean — prover_a — done — plan §7.1；commit f28288b / 692763d / da9aa17 / df5b9f3（随 M4a 验收一并 PASS）— Marcus/Sharp.lean — prover_a — done — plan §7.1；commit 67c42f5

## M4b — 微观重组能正性（`PhotoLean/Marcus/Reorg.lean`；属主 prover_d；Sprint 1，**零依赖**）

- [x] `lamInner` / `lamOuter` 定义 — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit 2d4e296
- [x] `lamInner_nonneg` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit 723034d
- [x] `lamInner_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit acc5e8e
- [x] `lamOuter_pos`（Pekar 因子正性）— Marcus/Reorg.lean — prover_d — done — plan §7.2；commit fcb7589
- [x] `lam_total_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit de63c09
- [x] **[拉伸]** `hgeom_of_nonoverlap`（`a1+a2 ≤ R ⇒ 几何因子正`，把 `hgeom` 从假设变成推导）— Marcus/Reorg.lean — prover_d — done — plan §7.2；commit 61759b3

## M4c — 复合定理（`PhotoLean/Marcus/Compose.lean`；属主 prover_d；Sprint 5）

- [x] `descriptor_holds_of_microscopic`（import Sharp + Reorg）— Marcus/Compose.lean — prover_d — done — plan §7.2；commit c778d4e
- [x] `descriptor_holds_of_nonoverlap`（拉伸：几何替代 hgeom）— Marcus/Compose.lean — prover_d — done — plan §7.2；commit 6338f7f

## M5a — ℚ 判定层（`PhotoLean/Marcus/RatModel.lean`；属主 prover_c；Sprint 2）

- [x] `zoneQ` / `barrierQ` — Marcus/RatModel.lean — prover_c — done — plan §8.1；commit 77e45c8
- [x] `zoneQ_eq_zone`（转移引理）— Marcus/RatModel.lean — prover_c — done — plan §8.1；commit d43f806
- [x] `zoneQ_inverted_iff` — Marcus/RatModel.lean — prover_c — done — plan §8.1；commit 166ab4e

## M5b — 实例与判定（`PhotoLean/Marcus/Instances.lean`；属主 prover_c）

> **编号以文件为准**（与 plan §8.2 旧编号不同，交付者已在文件内写"编号说明"）：
> I1/I2 = 纯数（反转区/正常区）；**I3 = 文献 MCC 无势垒点 (1.20, 1.23)**；
> **I4 = 文献 MCC 反转区对 (1.20, 2.40 / 2.00)**；**I5 = 文献 MCC 正常区 (1.20, 0.60)**；
> **I6 = 光合反应中心深反转区 (0.25, 1.10)**；I7 = 非物理参数；I8 = 文献参数的**描述算子实例化 + 速率比较**。

> **⚠️ 实例层文案边界（文献定量警示）**：经典模型在反转区**下降过快**（λ=1.2 时 x: 2.0→2.4 掉约 5 个数量级，
> 实验只掉约 2 个数量级）。实例结论只能写"该体系落在反转区，且**经典 Marcus 模型**在该 (lam,x,T,A) 上满足描述"，
> **不得**写成对实验的断言。

- [x] 转移辅助 `normalRegion_of_zoneQ_normal` / `not_invertedRegion_of_zoneQ_normal` — Marcus/Instances.lean — prover_c — done — plan §8.2；commit f3f93f5
- [x] I1 反转区（纯数 `lam=1, x=3`）+ I2 正常区（`3/4`）判定链 — Marcus/Instances.lean — prover_c — done — plan §8.2；commit 4e14952 / f3f93f5
- [x] I3 文献无势垒点 (1.20, 1.23)：`barrier 1.20 1.23 = 0.0001875`（与文献 `ΔG‡ ≈ 0.0002 eV` 吻合）+ 反转区判定 — Marcus/Instances.lean — prover_c — done — plan §8.3；commit 6df4cf9
- [x] I4 文献 MCC 反转区对 (1.20, 2.40) 与 (1.20, 2.00) — Marcus/Instances.lean — prover_c — done — plan §8.3；commit 6df4cf9
- [x] I5 文献 MCC 正常区 (1.20, 0.60)（含"不符合反转区"否定判定）— Marcus/Instances.lean — prover_c — done — plan §8.3；commit 6df4cf9
- [x] I6 光合反应中心深反转区 (0.25, 1.10) — Marcus/Instances.lean — prover_c — done — plan §8.3；commit 6df4cf9
- [x] I7 非物理参数判定（`lam ≤ 0` ⇒ 描述失效；`A<0 ∧ lam<0` ⇒ 描述成立但速率非正 ⇒ 不可采纳）— Marcus/Instances.lean — prover_c — done — plan §8.2；commit cb72b16
- [x] I8 文献参数的**描述算子实例化** + **速率比较**（`rate(x=2.40) < rate(x=1.23)` 等，`kBT` 作显式前提）— Marcus/Instances.lean — prover_c — done — plan §8.2；commit a83bfe7 / 8f8f041

---

## M5b 的 lead 预验收证据（已被 verifier 判决取代，保留作交叉核对）

> **2026-09-20 更新**：M5b 已由**两路独立 verifier 判决 PASS**（见下），8 行已打勾。
> 下表保留作"lead 快路径证据 vs verifier 独立证据"的交叉核对记录。

## ⏳ M5b 的 lead 预验收证据（原始记录）

2026-09-20，在 verifier 判决到达前，lead 用**快路径**独立跑了一遍 M5b 的验收清单，结论如下
（证据可复跑；但按纪律，**verifier 未 PASS 之前这 8 行不得打勾**）：

| 检查 | 命令 | 结果 |
|---|---|---|
| 门 | `check.sh --strict PhotoLean.Marcus.{Instances,RatModel}` | 均 `verdict: PASS` |
| 批量公理 | 单探针 `#print axioms` × 35（Instances 31 + RatModel 4） | **35/35、0 error**：34 条三公理 + 1 条仅 `propext` |
| 脚本抽查 | `axioms.sh` × 3（含 `inst_I4_mcc_rate_drop`） | 3/3 打印名 = 请求名，无竞态 |
| 提交规范 | `git show --name-only` × 6 | 6 个 `feat(M5b)` 提交，**每个恰 1 个文件** |
| 定义层交叉验证 | `theories/Marcus/probes/marcus-lead-crosscheck.lean` | **9 条**：不调用任何交付实例定理，直接从定义重推同一批结论（含 `rate(2.40) < rate(1.23)` ∀`kBT>0`） |
| 数值核对 | Python 按定义计算 | 四条实例定理逐条印证；`barrier 1.20 1.23 = 0.0001875` 与文献 `≈0.0002 eV` 吻合 |
| 证据链阅读 | 读证明体 | `inst_I1_zoneQ` = `by decide`；`inst_I2_not_inverted` 经正常区转移引理；`inst_I4_mcc_rate_drop` 由 `inverted_rate_decreases` 实例化（非重新展开 exp 论证） |

## 验收记录（verifier 独立跑门；lead 据此打勾）

| 批次 | 范围 | 判决 | 关键证据 | 备注 |
|---|---|---|---|---|
| M1 + M4b | `Basic.lean`(12 声明) + `Reorg.lean`(6) | **PASS / PASS** | 四步门 + 8/8 `axioms.sh` 均 `[propext, Classical.choice, Quot.sound]`；18/18 语句与骨架**逐字一致**；8/8 提交各含**恰一条**定理、恰一个文件；耍花招排查 0 命中；对抗性探针内核级验证 | 1 条**注释级**缺陷待修（`Reorg.lean` 把 5 条定义域前提说成"被蕴含"，实为"未被使用" —— verifier 给了内核反例）；另：`zone_trichotomy` 本身信息量弱（对任意 `ℝ→ℝ→Zone` 函数均成立），真正钉住语义的是三条 `zone_eq_*_iff` |

| M2 | `Barrier.lean`(9 条) | **PASS** | 四步门 + 9/9 `axioms.sh` 干净（另用唯一路径隔离探针独立重取）；9/9 语句与骨架逐字一致；8/8 提交各含恰一条定理、只含该文件；`c000996` 偏差**核实为真**（`barrier_nonneg` 内容确在其中，行数闭合 35+4+6+4+9+8+11+5+13 = 95 = 文件总行数）；三条对抗性内核检查全过（`barrier_antitone_of_neg` 方向/`mono_cases` 四支穷尽且 `lam=0` 支未混入/`barrier_min_at_lam` 真全局最小且前提必需） | **发现 A**：文件与 API-NOTES 共 3 处把 `h₁ : 0 ≤ x₁` 说成"可由其他前提推出" —— **错**（反例 `lam=1,x₁=-5,x₂=-4`），正确定性是"**未被使用**（unused）"；**发现 D**：`lam = 0` 分支依赖除零约定（形式约定，非物理事实）⇒ 已补进 plan §13 |

| M3 + M5a | `Rate.lean`(6) + `RatModel.lean`(2 定理+2 定义) | **PASS / PASS** | 四步门 + 8/8 `axioms.sh` 干净（另用唯一路径隔离探针二次取证，含 5 个定义）；10/10 语句与骨架逐字一致（含定义体）；9/9 提交各含恰一条定理、只含属主文件；**三条对抗性内核检查**：正常区/反转区**方向**数值核对（0.852<0.939 升；0.368<0.779 降；峰=1.0）、`rate_ratio` 在 5 类边界赋值下全部成立且给出 `hA` 必要性反例（`A=0` 时等式假）、`zoneQ_eq_zone` 在 **16 组**含 `lam=0`/`lam<0` 的点上与 Python 期望三方一致 | **发现 (a)**：`theories/Marcus/plan.md §13` 第 4 行说 Lean 形态是 `0<kB ∧ 0<T`，实际交付用 `0 < kB*T`（乘积）⇒ 已改计划；**(b)** `barrierQ` 无伴随定理（相对 ℝ 理论未被约束）⇒ 已派补转移引理；**(c)** `normal_rate_increases` 的 `0 ≤ x₁` 数学多余（verifier 证了更强的无此前提版本）；**(d)** `theories/Marcus/plan.md §8.2` 表格 I2 行仍写 `by decide`（代码块已纠正）⇒ 已改；**(e)** M5b 实例若用 ℚ 侧势垒数值须先有转移引理 |

| M4a | `Sharp.lean`(9 条，含主定理) | **PASS** | 门 + 9/9 `axioms.sh` 干净（打印名与请求名逐字相符）；**5/5 语句三方一致**（plan §7.1 / 骨架 / 交付，字符级比对 + 内核 `#check` 精化类型对照）；grep 0 命中（另查 `set_option/macro/elab/run_cmd/#eval/private/@[` 等"花招面"亦 0）；9/9 提交各含恰一条定理、只含 `Sharp.lean`；**对抗性**：`lam=0` 支由 4 条无前提 `example` 独立复现（`barrier 0 x = 0` ⇒ `rate ≡ A` ⇒ `A < A`），`lam<0` 支数值核对（`barrier(-1,0)=-1/4`、`barrier(-1,1)=-1` ⇒ 速率递增、与描述反向），组装用 `#print` 证明项确认 `lt_trichotomy` 三分支**都**被接上；**并用内核反例回答**："若删掉左边 `(∀x, 0<rate)` 合取项，定理即不成立"（反例 `A=lam=-1`） |

| M4c + M4b 追加 | `Compose.lean`(2 条) + `Reorg.lean` 的 `hgeom_of_nonoverlap` | **PASS / PASS** | 门 + 10 条 `axioms.sh`（含 regression）干净；`descriptor_holds_of_microscopic` 与骨架/plan **逐字一致**；`descriptor_holds_of_nonoverlap` 与 microscopic 的机械差异**仅为** `(hR, hgeom)` → `hRge` 一处替换（`hgeom`/`0<R` 均不在其前提中）；`e626884` 注释改动经**位置感知解析器**确认 16 条变更行全在注释内、token 流 292=292 一致；**最强证据**：把源文件逐字节复制到 `/tmp` 从零重建，olean md5 与项目一致 ⇒ 排除 stale olean；**对抗性**：`hgeom_of_nonoverlap` 边界 + 256 组有理扫描全部成立且前提不可去（`a1=a2=1,R=1` 反例）；`descriptor_holds_of_microscopic` 用 12 条前提逐条 `norm_num` 消掉得 λ=1/3 并导出**具体速率不等式**（非空转，证明项 12/12 前提 used）；nonoverlap 版证明项**真调用** `hgeom_of_nonoverlap`（11/11 前提 used） | **记账缺口（已修）**：两个拉伸语句原先未回填骨架 ⇒ 已补（骨架 43→45 条，保真度检查当时覆盖 45/45；2026-09-20 又回填了 Sharp 的 4 条必要性内核与 RatModel 的 2 条数值桥 ⇒ 现为 **51/51**）；`one_div_le_one_div_of_le` 未入 API-NOTES ⇒ 已转校准者 |

| M5b + M5a 追加 | `Instances.lean`(31 条) + `RatModel.lean` 新增 2 条 | **PASS / PASS**（**两路独立 verifier** 同时判定） | 门 2/2 PASS（全树扫描 clean）；**批量公理 33/33**（32 条三公理 + 1 条仅 `propext`，0 error）+ 官方脚本抽查 3/3（打印名=请求名）；grep 花招面 0 命中；6 个 `feat(M5b)` 各含恰 1 文件；**判定性内核复核**：`#print` 证明项确认 `inst_I1_zoneQ` = `of_decide_eq_true`、`inst_I2_not_inverted` 真经正常区转移引理、`inst_I4_mcc_rate_drop` **项内 `Real.exp` 出现 0 次**（真实例化）；`kBT` 用 1 与 10 两赋值实例化皆过 ⇒ 全称性成立；非物理分支独立重算（速率 −1.284 → −2.718 严格递减）；**文案边界核查**：31 条无一条断言实测速率/降幅 | **发现（不阻断）**：① **合同纪律偏离**：M5b 的 31 条装在 6 个提交里（2/4/12/4/4/5），不满足 铁律 7"每 lemma 一 commit"（派发时允许"语义批次"，但与铁律冲突 ⇒ 记为已知偏离）；② `RatModel.lean` 头注释"2 定义与 2 定理"过期（现 4 条）→ 已修；③ `Instances.lean` 一处注释缺"经典模型"限定词 → 已修；④ **`Instances.lean` 的 31 条（实例/证据层）未进权威骨架** ⇒ 保真度检查（现 51/51）**不覆盖**这 31 条（已知覆盖缺口；同批的 Sharp 4 条内核与 RatModel 2 条数值桥已于 2026-09-20 回填骨架）；⑤ `one_div_le_one_div_of_le` 等已补入 API-NOTES |

**M2 发现 A 的关闭****M2 发现 A 的关闭**：三处（`Barrier.lean` 头注释与 doc comment、`API-NOTES.md`）均已修正为
"**证明未使用（unused）**"，并保留内核反例作为"典型误写"警示 ——
`Barrier.lean` 见 `8ca59d7`（纯注释，机械证据：剥离注释后代码逐字节相同）；
`API-NOTES.md` 见 `a0796fc`（新增"未使用 ≠ 可推出"的专项订正记录）。

**verifier 提出的诚实性提醒（已采纳）**：
1. **`zone_trichotomy` 强度很弱** —— 它没有断言分类器与三个区的对应，也没有断言三支互斥；
   语义由三条 `zone_eq_*_iff`（穷尽且一致）承担。文档与最终报告里**不得**夸大它的作用。
2. **几何约定不在 Lean 语句里**：`lamOuter_pos` 的前提在数学上允许 `a1 < 0, R < 0` 的赋值
   （结论仍为真）。即"两球、`R ≥ a1 + a2`、连续介质"只写在 plan 与注释里 ——
   **M5 实例层若用到 `lamOuter`，必须显式断言物理定义域**（`0 < a1`、`0 < a2`、`a1 + a2 ≤ R`）。
3. **并发窗口**：`check.sh --strict` 的扫描覆盖整个 `PhotoLean/`，别人的 WIP 会翻转门的判定 ⇒
   **打勾/最终结论必须在 frozen 提交上重跑门**（本表已如此执行）。
   **实测确认**：2026-09-20 曾观察到一次裸跑全量门 `build: FAILED` —— 复查发现是 `Rate.lean`/`Sharp.lean`
   正被写入的**瞬时状态**；逐个复核已验收的四模块全部 OK，写者停笔后全量门重新 PASS。
   并发环境下的**稳定验收通道是逐模块跑门**（`check.sh --strict <Module>`），裸跑全量门只做最终冻结检查。

## 备注与冲突记录

- **🔧 基础设施 BUG 已修（2026-09-20，prover_b 报障）**：`proofs/scripts/axioms.sh` 原先用**固定探针路径**
  `.lake/tmp/AxiomsProbe.lean`，并发跑验收门时互相覆盖 → 出现"问 A 答 B"的**假证据**
  （prover_b 实测：问 `rate_pos` 却打印 `Rat.zoneQ_eq_zone` 的公理）。已改为
  `AxiomsProbe.$$.$RANDOM.lean` + `trap ... EXIT` 清理；**并发隔离已实测**
  （4 个不同定理同时跑，各自打印自己的名字且均 PASS）。判定标准未变，仅消除竞态。
- **⚠️ lead 流程失误与修正（2026-09-20，必须记住）**：我在做 `docs(plan)`/`chore(board)` 提交时用了
  `git add -A`，把当时**未提交的中间产物**（`Barrier.lean` 的 WIP、`RatModel.lean`、若干探针、
  `LITERATURE.md` 初稿）卷进了我的提交（`e53d562`、`c000996`）。**规则从此刻起**：lead 只允许
  `git add <自己拥有的显式路径>`（`theories/Marcus/plan.md` / `theories/Marcus/TASKS.md` / `proofs/EXPERIENCE.md` / `lakefile.toml`），
  永不使用 `git add -A` / `git add .`；工人同理只 add 自己的属主文件。
  影响：交付定理（M1 四条、M4b 五条）的 per-lemma 提交**未受影响**；仅 `barrier_nonneg` 一条被吸收（见上）。
- **块注释扫描坑（M1 交付者实测，2026-09-20）**：`check.sh --strict` 的 sorry/axiom 扫描
  **包含块注释 `/- ... -/`**（只跳过行首 `--` 的行注释），因此在**文件头文档注释里写出被扫描的
  关键字字面量**会造成假 FAIL。全队约定：交付文件的文档注释里改用「零占位证明」等措辞。
- **Sprint 0 实测发现**（已写入 `theories/Marcus/plan.md` §2.4 与 `proofs/EXPERIENCE.md`）：
  1. Lean 4 里 `λ` 是关键字，**不能作标识符** → Lean 侧一律 ASCII
     （`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`）；
  2. `by decide` 对 ℚ 上**整数**字面量可算，对**含除法**的有理字面量卡在 `Rat` 的
     gcd/除法归约上 → 判定证据改用 `norm_num [zoneQ]`；
  3. 语句骨架必须放在 `SOURCE_DIRS` 之外（`theories/Marcus/probes/`），否则触发 sorry 扫描。
- **验收门漏洞提示**：`defaultTargets` 已随交付补入 `PhotoLean.Marcus.Basic` 与 `PhotoLean.Marcus.Reorg`；
  后续模块交付时 lead 继续同步补入，
  否则裸跑 `check.sh --strict` 只构建 Smoke（**扫描仍覆盖全目录**）。逐模块跑
  `check.sh --strict <Module>` 时不受影响。
