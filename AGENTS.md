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

`plan.md` 尚未确定理论方向（Sprint 0 最后一项）。开工前先与人类确认形式化目标，
不要自行发明里程碑。
