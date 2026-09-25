# PhotoLean

**English.** PhotoLean is a Lean 4 formalization of **seventeen phenomenological photochemistry and
photophysics theories** over a **shared kernel**, together with a **machine-checked relation module**
that registers, for all **136 pairs** of theories, either a compiled relation (definitional
certificate, true equivalence, one-way entailment, composition with its premise recorded, or an
**adjudication**) or a registered reason for its absence. Three adjudications decide inherited
literature conflations with if-and-only-if boundaries and witnesses on both sides; falsified drafts
are preserved as counterexample-witness theorems rather than deleted. Every delivered theorem's axiom
footprint is exactly `[propext, Classical.choice, Quot.sound]` — no `sorry`, no custom axiom.

**中文。** PhotoLean 把**十七个光化学/光物理唯象理论**形式化到 Lean 4，共用**一个内核对象**，并用一个
**机器检查的关系模块**登记全部 **136 对**理论之间的关系：要么是一条可编译的关系（定义证书 / 真等价 /
单向蕴含 / 带前提登记的组合边 / **裁定**），要么是一条已登记的"无此关系"的理由。三个**裁定**把文献中
长期含混的等同问题判决为带 iff 边界与两侧见证的**特例**；被内核证伪的草稿一律以**反例见证定理**保留，
绝不删除。所有交付定理的公理足迹恰为 `[propext, Classical.choice, Quot.sound]`——无 `sorry`、无自定义公理。

> **This README is bilingual.** English first, Chinese rendering directly after each section.
> **本 README 为双语**：每节英文在前、中文对照紧跟其后。

---

## 1. What is in the repository / 仓库内容

**English.** The corpus is a closed set of seventeen theories; each has a statement authority, a
per-theory plan, task board, literature record and human-facing results. The relation module is the
only cross-theory source file; the kernel sits below everything; the tooling reproduces every number
in the accompanying manuscript. The repository is also the reference instance of a
**project-agnostic formalization engine** whose roles, iron rules and iteration loop are fixed by
`AGENTS.md` and the contract `proofs/ENGINE.yml` — the same engine drives any theory set, so adding a
theory means adding a directory and its leaf files, not rewriting the pipeline.

**中文。** 语料是十七个理论的封闭集合；每个理论都有语句权威、规划、任务板、文献记录与面向人类的答复。
关系模块是唯一跨理论源文件；内核位于依赖图底部；工具链可从仓库重算出论文中的每个数字。本仓库同时是
**项目无关形式化引擎**的参考实例：角色、铁律与迭代循环由 `AGENTS.md` 与契约 `proofs/ENGINE.yml`
固定——同一引擎可驱动任意理论集合，新增理论只需新增目录与叶子文件，不必改写流水线。

| path | English | 中文 |
|---|---|---|
| `PhotoLean/Kernel.lean` | the shared object: 6 definitions + 2 theorems, `import Mathlib` only | 共享内核：6 定义 + 2 定理，只 import `Mathlib` |
| `PhotoLean/<Theory>/` | the seventeen theories, 92 modules (95 `.lean` files with kernel, relations, smoke) | 十七个理论、92 个模块（含内核/关系/冒烟共 95 个 `.lean`） |
| `PhotoLean/Relations.lean` | the machine-checked edge inventory: 78 declarations in 17 sections | 机器检查的边清单：17 节、78 条声明 |
| `theories/<T>/` | `plan.md` · `TASKS.md` · `LITERATURE.md` · `RESULTS.md` · `probes/` | 规划 · 任务板 · 文献 · 双语答复 · 语句权威与探针 |
| `theories/RELATIONS.md` | bilingual relation discussion draft (grows batch by batch) | 双语关系讨论稿（按批次增量） |
| `theories/GRAPH-REPORT.md` | bilingual consolidated graph report (all 17 nodes in one pass) | 双语总结报告（17 节点一次成型） |
| `proofs/` | the engine contract, gates, experience bank, API calibration log | 引擎契约、验收门、经验库、API 校准日志 |
| `paper/` | manuscript assets: figure sources, claim map, drop-in point for the LaTeX source | 论文资产：图件源、断言映射、正文源落点 |
| `tools/` | the census: every number the manuscript quotes, recomputed from the tree | 普查工具：论文引用的每个数字都从树里重算 |
| `docs/REPRODUCE.md` | command-by-command reproduction guide | 逐命令复现指南 |
| `review/` | review prompt + the two completed adversarial audit rounds | 审查 prompt + 两轮已完成的对抗性审查 |
| `AGENTS.md` | the working protocol (roles, iron rules, language policy) | 工作协议（角色、铁律、语言政策） |

## 2. Quick start / 快速开始

**English.** Two setup paths. A fresh machine needs Lean `4.17.0` (see `lean-toolchain`) and the
prebuilt mathlib `v4.17.0` cache; the author environment instead ships a pinned toolchain at
`.toolchain/` and calls it through the wrapper `proofs/scripts/lake`. **Never run `lake update`** —
the toolchain and mathlib rev are a pinned pair.

**中文。** 两条安装路径：新机器装 Lean `4.17.0`（见 `lean-toolchain`）并拉取 mathlib `v4.17.0` 预编译
缓存；作者环境则在 `.toolchain/` 内置固定工具链，通过包装器 `proofs/scripts/lake` 调用。**禁止
`lake update`**——工具链与 mathlib rev 是固定配对。

```bash
# fresh machine / 新机器
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake exe cache get          # prebuilt mathlib v4.17.0 oleans (~4.7 GB) / 预编译 mathlib 缓存
lake build                  # builds every defaultTarget / 构建全部默认目标

# author environment / 作者环境
proofs/scripts/lake build

# python tooling / Python 工具（图件需要；探针与普查只需标准库）
python3 -m pip install -r requirements.txt
```

```bash
proofs/scripts/check.sh --strict          # whole-tree gate / 全树验收门
python3 tools/counts.py --md              # census: quoted vs computed / 普查：论文值 vs 重算值
python3 paper/figures/make_figures.py     # regenerate Figures 1-3 / 重新生成图 1-3
```

## 3. Acceptance gates / 验收门

**English.** Three layers, because `lake build` alone is **not** acceptance: a placeholder proof or
a custom axiom compiles with exit 0. The strict scan is a text-level check, the probes compare
statements, and `#print axioms` audits trust.

**中文。** 三层验收，因为**`lake build` 通过不等于验收**：占位证明与自定义公理都能以 exit 0 编过。
严格扫描是文本层检查，保真探针比较语句，`#print axioms` 审计信任基础。

| gate / 门 | command / 命令 | expected at the release commit / 发布提交上的期望值 |
|---|---|---|
| whole tree / 全树 | `proofs/scripts/check.sh --strict` | `build: OK`, scan `clean`, 17/17 leaf planes, **verdict: PASS** |
| statement fidelity / 语句保真 | `python3 theories/BEP/probes/bep-fidelity.py --theory <T>` | 17/17 probes: `0` undelivered, `0` signature differences; authority **1153**, delivered **1214** |
| axiom audit / 公理审计 | `proofs/scripts/axioms.sh <Module> <fully.qualified.name>` | `verdict: PASS (only mathlib infrastructure axioms)` |

Exhaustive variant of the third gate (the manuscript's Methods cite it): `python3 tools/counts.py
--axioms` — 1,303 public declarations, 1,288 axiom footprints printed + 15 axiom-free, **0
footprints outside the allowed triple** (the earlier manual sweep of 2026-09-24 is recorded in
`review/REVIEW-PROMPT.md` §10.4). Five pre-existing `unused variable` warning lines in three files are registered
residue; the strict scan is clean.

## 4. The corpus / 语料

**English.** Families follow the relation graph: **F1** reads one equal-curvature two-parabola object
three ways; **F1′** generalizes it beyond equal curvature; **F1″** are photophysical readings carrying
kernel copies; **F2** is excited-state kinetic bookkeeping without potential-energy surfaces; **F3**
supplies geometric/spectroscopic scalars; **F4** is nonadiabatic dynamics at a codimension-2 conical
intersection. "Authority" = declarations calibrated before proof work and matched word for word;
"Delivered" = authority + probe-registered auxiliaries (the rule documented in `tools/README.md`).

**中文。** 家族与关系图一致：**F1** 是同一等曲率双抛物面对象的三种读法；**F1′** 是它的非等曲率推广；
**F1″** 是携带内核副本的光物理读法；**F2** 是无势能面的激发态动力学记账；**F3** 提供几何/谱学标量；
**F4** 是余维 2 锥形交叉的非绝热动力学。"权威" = 证明工作前标定、逐字匹配的声明数；"交付" = 权威 +
探针登记的辅助声明（口径见 `tools/README.md`）。

| theory / 理论 | family | modules | authority | delivered |
|---|---|---|---|---|
| Marcus inverted region | F1 | 8 | 51 | 82 |
| Hammond postulate | F1 | 6 | 102 | 102 |
| Bell–Evans–Polanyi | F1 | 6 | 191 | 191 |
| Kasha's rule | F2 | 6 | 151 | 151 |
| Sabatier principle / volcano | — | 6 | 132 | 134 |
| Goldschmidt tolerance factor | F3 | 6 | 139 | 139 |
| Symmetry factor (A1) | F1′ | 5 | 35 | 35 |
| Kasha–Vavilov (A2) | F2 | 3 | 29 | 39 |
| Stern–Volmer (A3) | F2 | 4 | 46 | 46 |
| Quantum yield (spine) | F2 | 4 | 29 | 29 |
| Fluorescence/phosphorescence | F2 | 4 | 30 | 30 |
| Energy gap law | F1″ | 5 | 26 | 27 |
| Stokes shift | F1″ | 4 | 36 | 36 |
| Internal conversion vs ISC | F1″ | 4 | 20 | 20 |
| Förster transfer | F3 | 4 | 32 | 32 |
| Einstein A/B coefficients | F3 | 4 | 33 | 33 |
| RACI / conical intersection | F4 | 13 | 71 | 88 |
| **total** | | **92** | **1153** | **1214** |

## 5. The relation graph / 关系图

**English.** `PhotoLean/Relations.lean` is the register of record: 17 sections, 78 declarations, six
edge kinds — definitional certificates (15 `rfl` pins, regression alarms that add no mathematics),
true equivalences (E1–E7), one-way entailments (O1–O3), compositions with the premise carried on the
edge (the Kasha → Marcus edge is conditional on `hic`; the photophysics batch factorizes through the
`QuantumYield` algebraic spine; RACI enters through five rows), adjudications, and registered
absences. Coverage: **26 machine edges + 110 registered absences = 136 pairs, 0 unaccounted** (per-pair
counts and citations are recomputed by `tools/counts.py`; the RACI ↔ Marcus row pins the classical
side, but the manuscript and the registry both treat that pair as a shape look-alike *without* an edge,
so it counts as a registered absence). Shape
look-alikes are recorded *without* asserting an edge, and the registry repeats one lesson three
times: the same statement shape is not the same statement; a shared predicate is not a shared
mechanism.

**中文。** `PhotoLean/Relations.lean` 是登记在案的清单：17 节、78 条声明、六类边——定义证书（15 条
`rfl` 钉，回归报警器，不含新数学）、真等价（E1–E7）、单向蕴含（O1–O3）、前提随边登记的组合边
（Kasha → Marcus 以 `hic` 为条件；光物理批次经 `QuantumYield` 代数脊柱因子化；RACI 经五行接入）、
裁定、以及已登记的缺席。覆盖：**26 条机器边 + 110 条登记缺席 = 136 对，0 对无账**（逐对计数与引用由
`tools/counts.py` 重算；RACI ↔ Marcus 一行只钉住经典侧，论文与登记处都把它归入形状相似、
不建边，因此计为登记缺席）。形状相似者只登记、
不建边；登记处三次重复同一条教训：**同样的语句形状不等于同样的语句；共享谓词不等于共享机制**。

* Incremental draft / 增量讨论稿: `theories/RELATIONS.md`
* Consolidated report / 总结报告: `theories/GRAPH-REPORT.md`

## 6. Three adjudications / 三个裁定

**English.** An adjudication delivers three things: an if-and-only-if boundary, witnesses on both
sides, and an explanation of why the conflation persists in practice.

**中文。** 一个裁定交付三样东西：iff 边界、两侧见证、以及"混同为何在实践层面长存"的解释。

| class | verdict / 判决 | witnesses / 见证 |
|---|---|---|
| **A1** adjudicated conflation | `SymmetryFactor.betaHalf_iff_equalForceConstants` — the thermoneutral crossing coordinate is `1/2` **iff** `kr = kp` (`0 < kr, 0 < kp`); closed form `√kp/(√kr+√kp)`, unique in `[0,1]` without calculus | `(1,4) ↦ 2/3` (`betaHalf_falsified_by_unequal`), `(4,1) ↦ 1/3` (a stiffer product well is already past the midpoint); on the diagonal it is a theorem (`betaHalf_holds_in_kernel`) |
| **A2** adjudicated independence | `KashaVavilov.d2_verdict` — four conjuncts: Kasha-without-Vavilov witness, Vavilov-without-Kasha witness (both at positive excitation), coincidence `KashaRule ↔ VavilovUpTo` under the closed quantification with a loss channel, and separation at the lossless corner | `kv_antiKasha_boundary`: every Kasha violation is observable anti-Kasha emission (`0 < upperYield ↔ ¬ KashaRule`) |
| **A3** identifiability | `SternVolmer.d1_verdict` (weakest premises `k0 ≠ 0`, `0 < Ka`) — both plots linear, the intensity-only observation is **non-injective**, and `LifetimeTracks m ↔ m = Mech.dyn` | `mixed_witness`: second difference `= 1`; upward curvature is the coexistence signature; `sv_identifiability_boundary` needs only `0 < Ka` |

## 7. Negative results / 负结果

**English.** When the kernel refuted a drafted statement, the statement was re-frozen **with** a
counterexample-witness theorem, never silently weakened or deleted. Ten delivered rows are named as
refutations, falsifications or model-mismatches (scan pattern and names: `tools/counts.py`; the four
`inst_I11_F*_not_model_consistent` rows refute four literature families read as equal-curvature
two-parabola models; `invertedCorner_firstForm_refuted` and `fpC5_firstForm_refuted` are re-frozen
first forms; `symmetryFactor_conflation_falsified_and_holds_in_kernel` packs both halves of A1), plus
three existential over-generalization re-freezes and one namespace-shadowing repair recorded in the
per-theory correction logs. The operational rule adopted after the premise audit: **a premise is
decorative if and only if the statement without it still proves**.

**中文。** 内核证伪草拟语句后，语句**连同反例见证定理**一起重冻结，绝不悄悄削弱或删除。共有十条交付行
以证伪/假/模型不符命名（扫描模式与名单见 `tools/counts.py`；四条 `inst_I11_F*_not_model_consistent`
把四个文献族读成等曲率双抛物模型并逐一证伪；`invertedCorner_firstForm_refuted` 与
`fpC5_firstForm_refuted` 是被重冻结的初式；`symmetryFactor_conflation_falsified_and_holds_in_kernel`
一行打包 A1 的证伪与成立两半），另有三次存在量词空泛化重冻结与一次命名空间遮蔽修复，记于各理论的
§3.1 修正日志。前提审计后采用的判据是：**去掉该前提后语句仍能证明，才是装饰性前提**。

## 8. The manuscript / 论文

**English.** `paper/CLAIMS.md` maps every quantitative or named claim in the manuscript to a Lean
declaration, a command, or a registered convention. `paper/figures/make_figures.py` regenerates
Nature LaTeX source goes into `paper/manuscript/` (not committed here); the compiled draft PDF of an
unpublished manuscript is deliberately not committed.

**中文。** `paper/CLAIMS.md` 把论文中每一条定量或具名断言映射到 Lean 声明、命令或已登记约定；
的 LaTeX 正文源放在 `paper/manuscript/`（不随本仓库提交）；未发表手稿的编译 PDF 有意不入库。

## 9. Reproducibility and auditing / 可复现与审查

**English.** Reproduce everything with `docs/REPRODUCE.md`. Every number quoted anywhere in the
repository or the manuscript is recomputed by `python3 tools/counts.py --md`, which prints quoted vs
computed values and marks MATCH/DIFF. Adversarial auditing is a first-class procedure: paste
`review/REVIEW-PROMPT.md` into a fresh LLM session; two rounds are recorded
(`review/AUDIT-2026-09-24.md`, `review/REAUDIT-2026-09-24.md`), and the
whole-tree gate result is only meaningful together with the tree state (`git log -1 --oneline` +
`git status --short`) it was taken in.

**中文。** 用 `docs/REPRODUCE.md` 复现一切。仓库与论文中引用的每个数字都由
`python3 tools/counts.py --md` 重算，并打印"论文值 vs 重算值"及 MATCH/DIFF。对抗性审查是一等流程：
把 `review/REVIEW-PROMPT.md` 粘进全新 LLM session 即可；已记录两轮审查（`review/AUDIT-*.md`、
`review/REAUDIT-*.md`）。**全树门的结果只有连同当时树状态**（`git log -1 --oneline` +
`git status --short`）**才有意义**。

## 10. Honest boundaries / 诚实边界

**English.** (1) Every row is a statement *inside a declared model*; an edge relates statements
about named models, and no row claims that one theory is derivable from another. (2) Conditional
edges stay conditional: premises such as `hic` are registered, not proved. (3) Fidelity probes
compare signatures (up to the first `:=`); definition bodies are pinned by the `rfl` certificates, and
`Kernel.lean` / `Relations.lean` are pinned by compile-time verbatim re-export rather than by a
skeleton probe. (4) Certificate discipline is opt-in for future theories. (5) Totalized conventions
(`x / 0 = 0`, `Real.sqrt` of a negative `= 0`) are documented everywhere and no substantive row
depends on them. (6) Three files carry five registered `unused variable` warnings. (7) The relation
module's completeness claim is about the *graph* (edges and registered absences), not about physics.

**中文。** ①每条行都是**声明模型内部**的陈述；边关联的是具名模型上的命题，不声称理论之间的可推导性。
②条件边保持条件：`hic` 之类的前提是登记项，不是定理。③保真探针比较**签名**（到第一个 `:=` 为止），
定义体由 `rfl` 证书钉住；`Kernel.lean` 与 `Relations.lean` 由编译期逐字 re-export 保障，而非骨架探针。
④证书纪律对未来理论是**自愿登记**。⑤全定义约定（`x / 0 = 0`、`Real.sqrt` 对负数取 0）处处注明，
无实质行依赖它们。⑥三个文件带 5 条已登记的 `unused variable` 警告。⑦关系图的"完整"是关于**图**的
（边与已登记缺席），不是关于物理的。

## 11. Citation, licenses, and pre-push checklist / 引用、许可与推送前清单

**English.** Cite the software via `CITATION.cff` and the manuscript via `paper/CLAIMS.md`'s
preferred citation; the the archive service metadata is in `the archive-metadata file (removed)`. Code is MIT (`LICENSE`); text and
figures are CC BY 4.0 (`LICENSE-DOCS`).

**中文。** 软件引用见 `CITATION.cff`，论文引用见 `paper/CLAIMS.md` 的 preferred citation；the archive service
元数据在 `the archive-metadata file (removed)`。代码采用 MIT（`LICENSE`），文字与图件采用 CC BY 4.0（`LICENSE-DOCS`）。

**Before the first push / 首次推送前**：replace `TODO_REPOSITORY_URL` in `CITATION.cff` and
`the archive-metadata file (removed)`, and set the author ORCIDs in `CITATION.cff`; drop the manuscript LaTeX source into
`paper/manuscript/`; then tag `v1.0.0` and archive on the archive service.

## 12. Language policy / 语言政策

**English.** Repository artifacts are written in English; this README and the three cross-theory
documents (`theories/RELATIONS.md`, `theories/GRAPH-REPORT.md`, all `theories/<T>/RESULTS.md`) are
bilingual by registration; conversation with the human is Chinese. Quotations, Lean identifiers,
mathlib names and raw command output are never translated. Translation mirrors are not maintained:
historical `.en.md` files are frozen (or reduced to pointers) and no new ones are created.

**中文。** 仓库产物用英文书写；本 README 与三份跨理论文档（`theories/RELATIONS.md`、
`theories/GRAPH-REPORT.md`、各 `theories/<T>/RESULTS.md`）按登记为双语；与人类的对话用中文。引文、
Lean 标识符、mathlib 名字与命令原始输出不翻译。不维护翻译镜像：历史 `.en.md` 冻结（或退化为指针），
不再新建。
