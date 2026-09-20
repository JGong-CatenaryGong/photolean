# theories/BEP/RESULTS.md — the Bell–Evans–Polanyi principle, formalized in Lean

> The single bilingual deliverable of the BEP theory: every section carries the English original
> immediately followed by its Chinese rendering (contract `proofs/ENGINE.yml`, language policy in
> `proofs/ENGINE.md` §1.5). The human request had three parts — (①) turn the BEP principle into a
> formal description, (②) prove the description / find its exact validity conditions, (③) plug
> instances in and decide whether they conform — and the answers are §2, §3 and §4 below.
>
> 本文件是 BEP 理论的唯一双语交付物：每节英文原文后紧跟中文对照。人类需求分三部分 ——
> ①把 BEP 原理转化为形式化描述、②证明该描述/找出其精确成立条件、③代入实例判断是否符合 ——
> 答复分别在下面的 §2、§3、§4。
>
> Status / 状态: **sprint 0 — plan confirmed, statements in preparation**; no theorem is claimed
> until the acceptance gate has passed. Every number in this file is filled from the delivered
> measurement, never from the plan's target.
> 状态：**sprint 0 —— 计划已确认、语句在校准中**；在验收门通过之前本文件不声明任何定理。
> 本文件的每个数字都来自交付时的实测值，而不是计划里的目标值。

---

## 1. Executive summary

**Delivered.** (to be written after the B-series is delivered)
**摘要**：（B 系列交付后填写）

## 2. Part ① — the formal description

**English.** (model assumptions, definition inventory, the decidable regime classifier)
**中文**：（模型假设、定义清单、可判定区域分类器）

## 3. Part ② — the laws and their exact validity conditions

**English.** (the exact defect law, the mean-value identification of the measured slope with the
transition-state coordinate, thermoneutrality `α = 1/2`, complementarity, the bounds–regime
equivalence, exactness only in the degenerate model, the tolerance radius `2√(λ·tol)`, the minimax
line, λ-monotonicity, and the cross-module bridges to `Marcus`/`Hammond`)
**中文**：（精确偏离律、实测斜率与过渡态坐标的中值恒等式、中性点 `α = 1/2`、互补关系、
界与区域等价、仅退化模型下精确成立、容差半径 `2√(λ·tol)`、极小极大最优线、关于 λ 的单调性、
以及通向 `Marcus`/`Hammond` 的跨模块桥）

## 4. Part ③ — instance verdicts

**English.** (the verdict table: family, parameters, provenance, kernel-checked verdict)
**中文**：（判决表：族、参数、出处、内核检验的判决）

## 5. Acceptance evidence

**English.** (build / `check.sh --strict` / `#print axioms` / statement fidelity / verifier batches)
**中文**：（构建 / 严格扫描 / 公理打印 / 语句保真度 / 验证器批次）

## 6. Boundaries of the claim (what is NOT proved)

**English.** (the honesty table of `theories/BEP/plan.md` §13 in reader-facing form: model
assumptions, the ΔH/ΔG° premise, out-of-scope physics)
**中文**：（`theories/BEP/plan.md` §13 的读者版：建模假设、ΔH/ΔG° 前提、超出范围的物理）

## 7. Reproduction

**English.** (exact commands to re-run the gate and the instance checks)
**中文**：（重跑验收门与实例检查的确切命令）

## 8. Provenance and literature

**English.** (the sources on which the statements and the instance numbers rest, with their
`first-hand` / `not-accessed` status, pointing at `theories/BEP/LITERATURE.md`)
**中文**：（语句与实例数字所依赖的文献及其 `first-hand` / `not-accessed` 状态，指向
`theories/BEP/LITERATURE.md`）
