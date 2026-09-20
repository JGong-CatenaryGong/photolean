/-
marcus-fidelity.lean — 全项目语句保真度比对器（lead 维护，非交付文件）。

用途：把 `PhotoLean/Marcus/*.lean` 里每个**在语句权威中出现过**的声明的签名，
与 `theories/Marcus/probes/marcus-statement-skeleton.lean` 逐字比对（去空白），一次跑完全部模块。

规则：
- 权威 = marcus-statement-skeleton.lean（statement-first）。
- 只在权威里出现过的名字参与比对；交付文件里新增的辅助定理（如 sharp_A_pos、
  barrierQ_cast、normalRegion_of_zoneQ_normal 等）不在权威中，**不算差异**。
- 比对范围：`theorem`/`def` 名起到第一个 `:=` 之前（定义体不参与，因为权威里的
  `noncomputable def` 带 `sorry` 占位的是定理；定义体另行由 verifier 人工核对）。

运行：python3 theories/Marcus/probes/marcus-fidelity.py   （见同目录脚本；本文件是说明+占位）
本文件不是 Lean 源码，扩展名故意用 .lean 以便与 probes 放一起。实际比对实现见同名 .py。

English: marcus-fidelity.lean — project-wide statement fidelity comparator (maintained by the lead; not a deliverable file).

Purpose: for every declaration in `PhotoLean/Marcus/*.lean` that **has appeared in the statement
authority**, compare its signature character-for-character (whitespace removed) against
`theories/Marcus/probes/marcus-statement-skeleton.lean`, covering all modules in a single run.

Rules:
- Authority = marcus-statement-skeleton.lean (statement-first).
- Only names that appear in the authority take part in the comparison; helper theorems newly added in
  the deliverable files (such as sharp_A_pos, barrierQ_cast, normalRegion_of_zoneQ_normal, etc.) are
  not in the authority and **do not count as differences**.
- Comparison scope: from the `theorem`/`def` name up to the first `:=` (definition bodies do not take
  part, because in the authority the `noncomputable def` entries carrying an unfinished-proof
  placeholder are theorems; definition bodies are checked separately by hand by the verifier).

Run: python3 theories/Marcus/probes/marcus-fidelity.py   (see the script in the same directory; this file is
documentation + placeholder)
This file is not Lean source; the extension is deliberately .lean so that it sits together with the
probes. The actual comparison implementation is in the same-named .py file.
-/
