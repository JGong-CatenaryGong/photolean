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
5. **文件所有权独占**：同一文件同一时间只有一个属主（见 `proofs/TASKS.md`）。
6. **验收独立**：写证明的人不能自判 PASS。verifier 只读、独立跑门、返回证据。
7. **打勾只在 verifier PASS 之后**，由 lead 执行。

## 工具链（易踩坑，务必遵守）

```bash
proofs/scripts/lake build                     # 用这个，不要直接调 lake（不在 PATH）
proofs/scripts/lake build PhotoLean.Smoke     # 单模块
```

- `.toolchain/` 与 `.lake/packages/` 是**符号链接**，指向已构建的 mathlib 缓存。
- **禁止 `lake update`** —— 会重写 manifest 并触发数小时全量重建。
- 冷启动 `lake build` 约 10 秒是正常的（mathlib olean 已缓存）。

## 迭代与记忆

- 一批独立 lemma → `workflow` 扇出；单个卡死 → `ralph`；长里程碑 → 目标工具。
- **每轮结束必须回写 `proofs/EXPERIENCE.md`**，包含"试过且失败"一栏。
  只记成功的条目视为无效。
- 文献调研结果进 `proofs/LITERATURE.md`，必须含"可形式化含义"。

## 当前状态

理论方向已定：**Marcus 反转区**（经典马库斯模型，`plan.md` M1–M5，人类确认于 2026-09-20）。
交付物：`PhotoLean/Marcus/{Basic,Barrier,Rate,Sharp,Reorg,Compose,RatModel,Instances}.lean`；
面向人类提问的答复：`proofs/RESULTS.md`；进度真源：`proofs/TASKS.md`。

**开工前必须先读 `proofs/TASKS.md` 的属主列与"验收记录"表** —— 该表记录了各里程碑的
verifier 判决、已关闭的缺陷、以及若干**已实测的坑**（并发窗口内的门判定、
`git add -A` 的并发事故、"未使用"≠"可推出" 等）。不要自行发明里程碑或改动已验收的语句。
