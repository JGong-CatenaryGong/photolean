# PhotoLean

光化学/光物理**唯象理论的 Lean 4 形式化**工程，由 DSH 的"项目无关形式化引擎"
Agent preset 驱动。

本仓库同时是这套引擎的**参考实例**：引擎只读 `proofs/ENGINE.yml` 声明的叶子
数据面，因此换个理论只需要换一个仓库、重写那几个数据文件，不必改引擎。

## 现状

- Lean 4.17.0 + mathlib，工具链与缓存已联通（`lake build` 冷启动 ~10s）
- 验收门脚本可用：`proofs/scripts/check.sh --strict`、`proofs/scripts/axioms.sh`
- `plan.md` **等待理论方向**（Sprint 0 最后一项）；`PhotoLean/Smoke.lean` 是环境冒烟测试

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
| `plan.md` | 理论规划（语句、证明草图、里程碑、验收标准）—— **待填** |
| `proofs/TASKS.md` | 任务板（状态唯一真源） |
| `proofs/EXPERIENCE.md` | 经验库：成败模式，跨轮复用 |
| `proofs/API-NOTES.md` | mathlib API 校准日志 |
| `proofs/LITERATURE.md` | 文献调研记录 |

同类已完成实例（写法范本）：`[local path removed]`（RACI/AIE，
M1–M4 + M1* 全证完，0 sorry / 0 自定义 axiom）。

## 许可

Apache-2.0
