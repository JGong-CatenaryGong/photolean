# mathlib API 校准日志

规则：

- prover 遇到不确定的 lemma 名时**不得猜测**，把问题交给 `api_researcher`。
- 每条记录格式：`## <日期> — <主题> — <校准人> — <结论>`（附 `#check` 输出、源码位置或链接）。
- `#check` 探针统一放 `proofs/probes/`，用 `proofs/scripts/lake env lean proofs/probes/<name>.lean` 运行；
  探针文件可提交（它们也是文档）。
- 校准只针对"名字/签名"层；语句/证明改动由对应 prover 执行并在此留痕。
- **mathlib 版本：v4.17.0**（rev 见 `lakefile.toml`）。名字漂移以此为基准。

## 待校准清单

<!-- 语句校准（Sprint 0）时逐条勾选，格式示例：
- [x] `Real.exp_strictMono`（旧名 `strictMono_exp`）— **已漂移**，见记录 8
- [ ] `...` — 待查
-->

（待 `plan.md` 定理语句确定后填写）

## 校准记录

<!--
## YYYY-MM-DD — <主题> — api_researcher — <结论>
```
#check <名字>
-- 输出
```
源码位置 / 备注：...
-->
