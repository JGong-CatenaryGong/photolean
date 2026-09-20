# PhotoLean 任务板（状态唯一真源）

- 状态词汇：`todo`（未开始）→ `stmt`（语句已校准且编译）→ `proving`（证明中）
  → `review`（已交 verifier）→ `done`（verifier PASS 且已提交）。
- 行格式：`- [ ] 定理 — 文件 — 属主 — 状态 — 备注`。
- **打勾（`[x]`）只允许发生在 verifier PASS 之后**，由 lead 执行；工人不得自行打勾。
- 属主列填引擎角色名（`prover_a` / `prover_b` / `prover_c` / `prover_d`）；
  同一文件不得有两个并发属主。
- 契约与角色定义：`proofs/ENGINE.md`；规划与语句：`plan.md`；
  **语句权威 = `proofs/probes/marcus-statement-skeleton.lean`（已编译通过）**。
- 理论方向：**Marcus 反转区（经典马库斯模型）**，人类确认于 2026-09-20。

---

## Sprint 0 — 环境与语句校准（已收尾）

- [x] Lean 工具链与 mathlib 缓存联通（`lake build` 冷启动 ~10s，`PhotoLean.Smoke` 通过）
- [x] 验收门脚本可用（`proofs/scripts/check.sh --strict` / `axioms.sh`）
- [x] **验收门行为已验证**：干净树 PASS；`sorry` / 自定义 `axiom` / 隐藏 `sorry`
      三类违规全部被拦（证据见 `proofs/EXPERIENCE.md` 首条 —— 关键发现：
      `lake build` 对三类违规**都返回 0**，单靠构建通过不构成验收）
- [x] 项目契约落盘（`proofs/ENGINE.yml`，叶子数据面齐备）
- [x] **理论规划落盘**：`plan.md` = Marcus 反转区 M1–M5
      （人类确认：完整五段 + 双轨实例 + 文献可核查参数）
- [x] **语句骨架编译通过**：`proofs/probes/marcus-statement-skeleton.lean`
      （M1–M5 全部语句，31 处 `sorry` warning、**0 error**；末尾 4 个风险探针无 sorry 真通过）
- [x] `proofs/probes/` 目录建立；`git init` + 基线 commit
- [x] API 校准完成（`api_researcher`）：`proofs/API-NOTES.md` 重写（可用/漂移/不可用三栏 + 20 个保留 token 的标识符合法性矩阵）、
      5 个探针 0 error，另附 `proofs/probes/marcus-proof-skeletons.lean`（36 条**已跑通**证明体，覆盖 M1–M5a）
- [x] 文献参数表完成（`literature_researcher`）：`proofs/LITERATURE.md` 552 行，含 6 组"已核实"参数、
      DOI 更正、Pekar 条件、5 条必显式化近似、不可表达清单排序

---

## M1 — 描述层（`PhotoLean/Marcus/Basic.lean`；属主 prover_a；Sprint 1）

- [x] 定义 `barrier` / `rate` / `InvertedRegion` / `NormalRegion` / `InvertedDescriptor`
      / `NormalDescriptor` / `Zone` / `zone` — Marcus/Basic.lean — prover_a — review — plan §2.2；commit 3644a82
- [x] `zone_eq_normal_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit f3d2055
- [x] `zone_eq_barrierless_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit ac80776
- [x] `zone_eq_inverted_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit c98c85d
- [x] `zone_trichotomy` — Marcus/Basic.lean — prover_a — done — plan §4.2；commit 1376f8e

## M2 — 势垒代数（`PhotoLean/Marcus/Barrier.lean`；属主 prover_a；Sprint 2）

- [ ] `barrier_nonneg` — Marcus/Barrier.lean — prover_a — review — plan §5；⚠️ **提交偏差**：内容已被
      lead 的 `c000996`（`git add -A` 误卷）吸收，本条无独立 feat 提交；余下 8 条仍各自一提交
- [ ] `barrier_at_lam` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 8d9c2ff
- [ ] `barrier_symm` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 03c740f
- [ ] `barrier_min_at_lam` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 169a0c7
- [ ] `barrier_mono_of_pos` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 3dc2fcc
- [ ] `barrier_antitone_of_pos` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 4ab7259
- [ ] `barrier_antitone_of_neg` — Marcus/Barrier.lean — prover_a — review — plan §5；commit 4561931
- [ ] `barrier_zero_lam` — Marcus/Barrier.lean — prover_a — review — plan §5；commit ae1276e
- [ ] `barrier_mono_cases` — Marcus/Barrier.lean — prover_a — review — plan §5；commit f0d79ee

## M3 — 速率层（`PhotoLean/Marcus/Rate.lean`；属主 prover_b）

- [ ] `rate_pos` — Marcus/Rate.lean — prover_b — review — plan §6（Sprint 2；只依赖 M1）；commit 8840fdf
- [ ] `rate_gt_of_barrier_lt` — Marcus/Rate.lean — prover_b — review — plan §6（**核心引理**；Sprint 2）；commit 464edbf
- [ ] `normal_rate_increases` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `inverted_rate_decreases` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `rate_peak_at_lam` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `rate_ratio`（拉伸目标，不阻塞）— Marcus/Rate.lean — prover_b — review — plan §6；commit 60fe95f

## M4a — 锐利刻画（`PhotoLean/Marcus/Sharp.lean`；属主 prover_a；Sprint 4）

- [ ] `inverted_descriptor_holds` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `normal_descriptor_holds` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `descriptor_fails_of_nonpos_lam` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `descriptor_sharp`（**关键路径**；verifier 重点复核必要性两支）— Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `inverted_descriptor_holds_of_neg`（拉伸；证明"速率正性"前提不可去）— Marcus/Sharp.lean — prover_a — todo — plan §7.1

## M4b — 微观重组能正性（`PhotoLean/Marcus/Reorg.lean`；属主 prover_d；Sprint 1，**零依赖**）

- [x] `lamInner` / `lamOuter` 定义 — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit 2d4e296
- [x] `lamInner_nonneg` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit 723034d
- [x] `lamInner_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit acc5e8e
- [x] `lamOuter_pos`（Pekar 因子正性）— Marcus/Reorg.lean — prover_d — done — plan §7.2；commit fcb7589
- [x] `lam_total_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2；commit de63c09
- [x] **[拉伸·建议]** `hgeom_of_nonoverlap`（`a1+a2 ≤ R ⇒ 几何因子正`，把 `hgeom` 从假设变成推导）— Marcus/Reorg.lean — prover_d — todo — plan §7.2（Sprint 5）

## M4c — 复合定理（`PhotoLean/Marcus/Compose.lean`；属主 prover_d；Sprint 5）

- [ ] `descriptor_holds_of_microscopic`（import Sharp + Reorg）— Marcus/Compose.lean — prover_d — todo — plan §7.2

## M5a — ℚ 判定层（`PhotoLean/Marcus/RatModel.lean`；属主 prover_c；Sprint 2）

- [ ] `zoneQ` / `barrierQ` — Marcus/RatModel.lean — prover_c — review — plan §8.1；commit 77e45c8
- [ ] `zoneQ_eq_zone`（转移引理）— Marcus/RatModel.lean — prover_c — review — plan §8.1；commit d43f806
- [ ] `zoneQ_inverted_iff` — Marcus/RatModel.lean — prover_c — review — plan §8.1；commit 166ab4e

## M5b — 实例与判定（`PhotoLean/Marcus/Instances.lean`；属主 prover_c）

> **⚠️ 实例层文案边界（文献定量警示）**：经典模型在反转区**下降过快**（λ=1.2 时 x: 2.0→2.4 掉约 5 个数量级，
> 实验只掉约 2 个数量级）。实例结论只能写"该体系落在反转区，且**经典 Marcus 模型**在该 (lam,x,T,A) 上满足描述"，
> **不得**写成对实验的断言。

- [ ] I1 反转区（纯数 `lam=1, x=3`）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I2 正常区（`lam=1, x=3/4`）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I3 无势垒点（`x = lam`，速率峰）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I4 文献参数·反转区 — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5；待 LITERATURE 表）
- [ ] I5 文献参数·正常区 — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）
- [ ] I6 反例 `lam ≤ 0` 判"不符合" — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）
- [ ] I7 非物理分支 `A<0 ∧ lam<0` 判"不可采纳" — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）

---

## 验收记录（verifier 独立跑门；lead 据此打勾）

| 批次 | 范围 | 判决 | 关键证据 | 备注 |
|---|---|---|---|---|
| M1 + M4b | `Basic.lean`(12 声明) + `Reorg.lean`(6) | **PASS / PASS** | 四步门 + 8/8 `axioms.sh` 均 `[propext, Classical.choice, Quot.sound]`；18/18 语句与骨架**逐字一致**；8/8 提交各含**恰一条**定理、恰一个文件；耍花招排查 0 命中；对抗性探针内核级验证 | 1 条**注释级**缺陷待修（`Reorg.lean` 把 5 条定义域前提说成"被蕴含"，实为"未被使用" —— verifier 给了内核反例）；另：`zone_trichotomy` 本身信息量弱（对任意 `ℝ→ℝ→Zone` 函数均成立），真正钉住语义的是三条 `zone_eq_*_iff` |

**verifier 提出的诚实性提醒（已采纳）**：
1. **`zone_trichotomy` 强度很弱** —— 它没有断言分类器与三个区的对应，也没有断言三支互斥；
   语义由三条 `zone_eq_*_iff`（穷尽且一致）承担。文档与最终报告里**不得**夸大它的作用。
2. **几何约定不在 Lean 语句里**：`lamOuter_pos` 的前提在数学上允许 `a1 < 0, R < 0` 的赋值
   （结论仍为真）。即"两球、`R ≥ a1 + a2`、连续介质"只写在 plan 与注释里 ——
   **M5 实例层若用到 `lamOuter`，必须显式断言物理定义域**（`0 < a1`、`0 < a2`、`a1 + a2 ≤ R`）。
3. **并发窗口**：`check.sh --strict` 的扫描覆盖整个 `PhotoLean/`，别人的 WIP 会翻转门的判定 ⇒
   **打勾/最终结论必须在 frozen 提交上重跑门**（本表已如此执行）。

## 备注与冲突记录

- **🔧 基础设施 BUG 已修（2026-09-20，prover_b 报障）**：`proofs/scripts/axioms.sh` 原先用**固定探针路径**
  `.lake/tmp/AxiomsProbe.lean`，并发跑验收门时互相覆盖 → 出现"问 A 答 B"的**假证据**
  （prover_b 实测：问 `rate_pos` 却打印 `Rat.zoneQ_eq_zone` 的公理）。已改为
  `AxiomsProbe.$$.$RANDOM.lean` + `trap ... EXIT` 清理；**并发隔离已实测**
  （4 个不同定理同时跑，各自打印自己的名字且均 PASS）。判定标准未变，仅消除竞态。
- **⚠️ lead 流程失误与修正（2026-09-20，必须记住）**：我在做 `docs(plan)`/`chore(board)` 提交时用了
  `git add -A`，把当时**未提交的中间产物**（`Barrier.lean` 的 WIP、`RatModel.lean`、若干探针、
  `LITERATURE.md` 初稿）卷进了我的提交（`e53d562`、`c000996`）。**规则从此刻起**：lead 只允许
  `git add <自己拥有的显式路径>`（`plan.md` / `proofs/TASKS.md` / `proofs/EXPERIENCE.md` / `lakefile.toml`），
  永不使用 `git add -A` / `git add .`；工人同理只 add 自己的属主文件。
  影响：交付定理（M1 四条、M4b 五条）的 per-lemma 提交**未受影响**；仅 `barrier_nonneg` 一条被吸收（见上）。
- **块注释扫描坑（M1 交付者实测，2026-09-20）**：`check.sh --strict` 的 sorry/axiom 扫描
  **包含块注释 `/- ... -/`**（只跳过行首 `--` 的行注释），因此在**文件头文档注释里写出被扫描的
  关键字字面量**会造成假 FAIL。全队约定：交付文件的文档注释里改用「零占位证明」等措辞。
- **Sprint 0 实测发现**（已写入 `plan.md` §2.4 与 `proofs/EXPERIENCE.md`）：
  1. Lean 4 里 `λ` 是关键字，**不能作标识符** → Lean 侧一律 ASCII
     （`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`）；
  2. `by decide` 对 ℚ 上**整数**字面量可算，对**含除法**的有理字面量卡在 `Rat` 的
     gcd/除法归约上 → 判定证据改用 `norm_num [zoneQ]`；
  3. 语句骨架必须放在 `SOURCE_DIRS` 之外（`proofs/probes/`），否则触发 sorry 扫描。
- **验收门漏洞提示**：`defaultTargets` 已随交付补入 `PhotoLean.Marcus.Basic` 与 `PhotoLean.Marcus.Reorg`；
  后续模块交付时 lead 继续同步补入，
  否则裸跑 `check.sh --strict` 只构建 Smoke（**扫描仍覆盖全目录**）。逐模块跑
  `check.sh --strict <Module>` 时不受影响。
