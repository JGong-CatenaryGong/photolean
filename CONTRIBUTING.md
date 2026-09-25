# CONTRIBUTING.md — onboarding an eighteenth node

**English.** This repository is a *machine-checked relation graph*, not a collection of definitions:
a theory is on the graph only when it carries a registered relation — or a registered reason for its
absence — against **every** existing node. The protocol below is the one the seventeenth node (RACI)
and the nine-theory photophysics batch were admitted by; it is also the paper's Methods §5.10. The
same protocol applies to human- and AI-authored proposals: the gates, not the generating process, are
the trust layer.

**中文。** 本仓库是**机器检查的关系图**，不是定义集合：一个理论只有在与**每一个**既有节点之间都给出
已登记的关系（或已登记的缺席理由）之后，才算"在图上"。下面这套流程正是第十七个节点（RACI）与九理论
光物理批次被接纳时使用的流程，也是论文 Methods §5.10 的内容。它对人类与 AI 提出的语句同样适用：
**信任来自验收门，而不是生成过程**。

---

## 1. Required deliverables / 必备交付物

| # | artifact | English requirement | 中文要求 |
|---|---|---|---|
| 1 | `theories/<T>/probes/<T>-statement-skeleton.lean` | every public declaration written out verbatim with the body replaced by a placeholder; it must compile (placeholders are intentional) | 每个公开声明逐字写出、证明体替换为占位；必须能编译（占位是有意的） |
| 2 | fidelity probe | `python3 theories/BEP/probes/bep-fidelity.py --theory <T>` reports `not delivered yet: 0` and `signature differences: 0` | 探针必须报 0 未交付、0 签名差异 |
| 3 | kernel copies + `rfl` certificates | if the theory reads the shared quadratic object, it keeps its own copy and a definitional certificate pins it to `PhotoLean.Kernel`; a failing certificate is a **stop-and-investigate** event, never a reason to edit a delivered module | 若读共享二次对象，保留自带副本并以定义证书钉到内核；证书失败是**停下来排查**事件，绝不去改交付模块 |
| 4 | relation rows | an edge or a registered absence with its dependency fact and modelling reason, against **all** existing nodes, in a new numbered section of `PhotoLean/Relations.lean` | 对**全部**既有节点给出边或带依赖事实与建模理由的登记缺席，写入 `PhotoLean/Relations.lean` 的新编号小节 |
| 5 | adjudication (optional but then mandatory in full) | if the contribution decides a literature conflation: an iff boundary, witnesses on **both** sides, and an account of why the conflation persists | 若裁定文献混同：iff 边界、**两侧**见证、以及混同为何长存；三者缺一不可 |
| 6 | negative results | any draft the kernel refutes is re-frozen **with** a counterexample-witness theorem; deletions are not accepted | 被内核证伪的草稿**连同反例见证定理**一起重冻结；不接受删除 |
| 7 | weakest premises | only load-bearing hypotheses; the criterion is: a premise is decorative iff the statement without it still proves | 只带承重前提；判据：去掉该前提后语句仍能证明，才是装饰性的 |
| 8 | leaves | `plan.md` (with a §3.1 correction log), `TASKS.md` (with the verifier record), `LITERATURE.md` (sources with formalizable implications), `RESULTS.md` (bilingual) | 四件叶子：规划（含 §3.1 修正日志）、任务板（含 verifier 记录）、文献（含可形式化含义）、双语答复 |
| 9 | registration | the new node appears in the README corpus table, in `theories/RELATIONS.md`, and in `theories/GRAPH-REPORT.md`; `tools/counts.py`'s node list is extended | 新节点登记进 README 表、`RELATIONS.md`、`GRAPH-REPORT.md`，并扩展 `tools/counts.py` 的节点表 |

## 2. Gate sequence / 验收顺序

```bash
# 1. the new module set must be built by the bare gate (not just exist on disk)
python3 .github/scripts/default_targets.py

# 2. three-layer acceptance
proofs/scripts/check.sh --strict
python3 theories/BEP/probes/bep-fidelity.py --theory <T>
proofs/scripts/axioms.sh <Module> <fully.qualified.name>

# 3. counts and coverage
python3 tools/counts.py --md

# 4. registration texts
git grep -n '<T>' -- README.md theories/RELATIONS.md theories/GRAPH-REPORT.md   # must appear in all three
```

`lake build` succeeding is **not** acceptance: placeholders and custom axioms compile with exit 0.
A layer is accepted only when the command's own output says so, at a recorded tree state
(`git log -1 --oneline` + `git status --short`).

## 3. Review / 审查

* The board is ticked only after an **independent verifier PASS** is recorded on
  `theories/<T>/TASKS.md`; the author of a proof never signs it off.
* Adversarial review is a procedure, not an attitude: paste `review/REVIEW-PROMPT.md` (a complete
  auditor brief) into a fresh session with shell and read access, and treat its findings as blocking
  at severity S1/S2.
* Nothing is ever "fixed" by editing a delivered module to make a gate green. A failing certificate
  means the definitions drifted: investigate.

## 4. Style / 风格

* English for artifacts (Lean comments, docstrings, markdown, commits); Chinese for conversation with
  the human; bilingual for `README.md`, `RESULTS.md` and the two cross-theory reports. Identifiers,
  mathlib names and raw command output stay verbatim. See `AGENTS.md` §language policy.
* One commit per theory (or per lemma for single-lemma work), with the contract's message format.
* Do not run `lake update`; use `proofs/scripts/lake` (or `lake` on a machine with elan).
