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
- [ ] API 校准（`api_researcher` 进行中 → `proofs/API-NOTES.md`）
- [ ] 文献参数表（`literature_researcher` 进行中 → `proofs/LITERATURE.md` §实例参数候选表）

---

## M1 — 描述层（`PhotoLean/Marcus/Basic.lean`；属主 prover_a；Sprint 1）

- [ ] 定义 `barrier` / `rate` / `InvertedRegion` / `NormalRegion` / `InvertedDescriptor`
      / `NormalDescriptor` / `Zone` / `zone` — Marcus/Basic.lean — prover_a — todo — plan §2.2
- [ ] `zone_eq_normal_iff` — Marcus/Basic.lean — prover_a — todo — plan §4.2
- [ ] `zone_eq_barrierless_iff` — Marcus/Basic.lean — prover_a — todo — plan §4.2
- [ ] `zone_eq_inverted_iff` — Marcus/Basic.lean — prover_a — todo — plan §4.2
- [ ] `zone_trichotomy` — Marcus/Basic.lean — prover_a — todo — plan §4.2

## M2 — 势垒代数（`PhotoLean/Marcus/Barrier.lean`；属主 prover_a；Sprint 2）

- [ ] `barrier_nonneg` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_at_lam` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_symm` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_min_at_lam` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_mono_of_pos` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_antitone_of_pos` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_antitone_of_neg` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_zero_lam` — Marcus/Barrier.lean — prover_a — todo — plan §5
- [ ] `barrier_mono_cases` — Marcus/Barrier.lean — prover_a — todo — plan §5

## M3 — 速率层（`PhotoLean/Marcus/Rate.lean`；属主 prover_b）

- [ ] `rate_pos` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 2；只依赖 M1）
- [ ] `rate_gt_of_barrier_lt` — Marcus/Rate.lean — prover_b — todo — plan §6（**核心引理**；Sprint 2）
- [ ] `normal_rate_increases` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `inverted_rate_decreases` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `rate_peak_at_lam` — Marcus/Rate.lean — prover_b — todo — plan §6（Sprint 3；依赖 M2）
- [ ] `rate_ratio`（拉伸目标，不阻塞）— Marcus/Rate.lean — prover_b — todo — plan §6

## M4a — 锐利刻画（`PhotoLean/Marcus/Sharp.lean`；属主 prover_a；Sprint 4）

- [ ] `inverted_descriptor_holds` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `normal_descriptor_holds` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `descriptor_fails_of_nonpos_lam` — Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `descriptor_sharp`（**关键路径**；verifier 重点复核必要性两支）— Marcus/Sharp.lean — prover_a — todo — plan §7.1
- [ ] `inverted_descriptor_holds_of_neg`（拉伸；证明"速率正性"前提不可去）— Marcus/Sharp.lean — prover_a — todo — plan §7.1

## M4b — 微观重组能正性（`PhotoLean/Marcus/Reorg.lean`；属主 prover_d；Sprint 1，**零依赖**）

- [ ] `lamInner` / `lamOuter` 定义 — Marcus/Reorg.lean — prover_d — todo — plan §7.2
- [ ] `lamInner_nonneg` — Marcus/Reorg.lean — prover_d — todo — plan §7.2
- [ ] `lamInner_pos` — Marcus/Reorg.lean — prover_d — todo — plan §7.2
- [ ] `lamOuter_pos`（Pekar 因子正性）— Marcus/Reorg.lean — prover_d — todo — plan §7.2
- [ ] `lam_total_pos` — Marcus/Reorg.lean — prover_d — todo — plan §7.2

## M4c — 复合定理（`PhotoLean/Marcus/Compose.lean`；属主 prover_d；Sprint 5）

- [ ] `descriptor_holds_of_microscopic`（import Sharp + Reorg）— Marcus/Compose.lean — prover_d — todo — plan §7.2

## M5a — ℚ 判定层（`PhotoLean/Marcus/RatModel.lean`；属主 prover_c；Sprint 2）

- [ ] `zoneQ` / `barrierQ` — Marcus/RatModel.lean — prover_c — todo — plan §8.1
- [ ] `zoneQ_eq_zone`（转移引理）— Marcus/RatModel.lean — prover_c — todo — plan §8.1
- [ ] `zoneQ_inverted_iff` — Marcus/RatModel.lean — prover_c — todo — plan §8.1

## M5b — 实例与判定（`PhotoLean/Marcus/Instances.lean`；属主 prover_c）

- [ ] I1 反转区（纯数 `lam=1, x=3`）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I2 正常区（`lam=1, x=3/4`）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I3 无势垒点（`x = lam`，速率峰）— Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 3）
- [ ] I4 文献参数·反转区 — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5；待 LITERATURE 表）
- [ ] I5 文献参数·正常区 — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）
- [ ] I6 反例 `lam ≤ 0` 判"不符合" — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）
- [ ] I7 非物理分支 `A<0 ∧ lam<0` 判"不可采纳" — Marcus/Instances.lean — prover_c — todo — plan §8.2（Sprint 5）

---

## 备注与冲突记录

- **Sprint 0 实测发现**（已写入 `plan.md` §2.4 与 `proofs/EXPERIENCE.md`）：
  1. Lean 4 里 `λ` 是关键字，**不能作标识符** → Lean 侧一律 ASCII
     （`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`）；
  2. `by decide` 对 ℚ 上**整数**字面量可算，对**含除法**的有理字面量卡在 `Rat` 的
     gcd/除法归约上 → 判定证据改用 `norm_num [zoneQ]`；
  3. 语句骨架必须放在 `SOURCE_DIRS` 之外（`proofs/probes/`），否则触发 sorry 扫描。
- **验收门漏洞提示**：`defaultTargets` 目前只含 `PhotoLean.Smoke`；交付新模块时 lead 必须同步补入，
  否则裸跑 `check.sh --strict` 只构建 Smoke（**扫描仍覆盖全目录**）。逐模块跑
  `check.sh --strict <Module>` 时不受影响。
