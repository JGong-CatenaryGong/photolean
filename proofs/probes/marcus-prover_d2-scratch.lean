/-
prover_d 探针 #2 —— M4b 几何拉伸 + M4c 复合定理（prover_d 私有 scratch；交付后保留作文档）。

运行：`proofs/scripts/lake env lean proofs/probes/marcus-prover_d2-scratch.lean`

本文件**不是**交付物（在 proofs/probes/ 下，不参与 check.sh 的 `PhotoLean/**/*.lean` 扫描）。
价值 = 名字校准的 `#check` 原始输出 + 在写进交付文件之前把骨架跑通/跑挂的记录。

交付状态（2026-09-20）：
- `PhotoLean.Marcus.hgeom_of_nonoverlap` — DONE（Marcus/Reorg.lean，commit 61759b3）
- `PhotoLean.Marcus.descriptor_holds_of_microscopic` — DONE（Marcus/Compose.lean，commit c778d4e）
- `PhotoLean.Marcus.descriptor_holds_of_nonoverlap`（拉伸）— DONE（同文件，commit 6338f7f）

## 实测失败路径（勿再走）

- 想在 `hgeom_of_nonoverlap` 里**直接**对原目标用 `nlinarith` / `gcongr`：不行 —— 目标含
  `1 / R`、`1 / (2 * a1)` 三个除法，未通分前非线性算术看不到分母符号（API-NOTES G-5/G-6 同型教训）。
- 想把 `field_simp` 作用在**不等式**（`1/(a1+a2) < 1/(2a1) + 1/(2a2)`）上：`simp made no progress`。
  正确姿势：先证**等式** `1/(2a1) + 1/(2a2) = (a1+a2)/(2a1a2)`（`field_simp` + `ring`），
  再用 `div_lt_div_iff₀` 交叉相乘把不等式交给 `nlinarith`。
- `div_lt_div_iff₀` 的两个参数是**分母正性**，顺序 `(hb : 0 < b) (hd : 0 < d)`，
  与目标 `a / b < c / d` 的分母一一对应；写反会得到 `a * d < c * b` 的错误目标并卡住。

prover_d probe #2 — M4b geometric stretch + M4c composition theorems (prover_d private scratch; kept as documentation after delivery).

Run: `proofs/scripts/lake env lean proofs/probes/marcus-prover_d2-scratch.lean`

This file is **not** a deliverable (it lives under proofs/probes/ and is not covered by the check.sh scan of `PhotoLean/**/*.lean`).
Its value = the raw `#check` output from name calibration + a record of the skeletons that ran (or broke) before being written into the delivery files.

Delivery status (2026-09-20):
- `PhotoLean.Marcus.hgeom_of_nonoverlap` — DONE (Marcus/Reorg.lean, commit 61759b3)
- `PhotoLean.Marcus.descriptor_holds_of_microscopic` — DONE (Marcus/Compose.lean, commit c778d4e)
- `PhotoLean.Marcus.descriptor_holds_of_nonoverlap` (stretch) — DONE (same file, commit 6338f7f)

## Measured failure paths (do not walk them again)

- Wanting to use `nlinarith` / `gcongr` **directly** on the original goal inside `hgeom_of_nonoverlap`: does not work — the goal contains
  `1 / R`, `1 / (2 * a1)` with three divisions, and before clearing denominators nonlinear arithmetic cannot see the signs of the denominators (the same pattern of lesson as API-NOTES G-5/G-6).
- Wanting to apply `field_simp` to an **inequality** (`1/(a1+a2) < 1/(2a1) + 1/(2a2)`): `simp made no progress`.
  The right move: first prove the **equality** `1/(2a1) + 1/(2a2) = (a1+a2)/(2a1a2)` (`field_simp` + `ring`),
  then cross-multiply with `div_lt_div_iff₀` to hand the inequality to `nlinarith`.
- The two arguments of `div_lt_div_iff₀` are the **positivity of the denominators**, in the order `(hb : 0 < b) (hd : 0 < d)`,
  matching the denominators of the goal `a / b < c / d` one-to-one; swapping them yields the wrong goal `a * d < c * b` and gets stuck.
-/

-- ⚠️ 探针若要 `#check` 复合定理，必须 import `Compose`（它才是两条复合定理的所在模块）；
-- English: ⚠️ For a probe to `#check` the composition theorems, it must import `Compose` (that is the module where the two composition theorems actually live);
--    只 import `Sharp` + `Reorg` 会报 `unknown identifier '…descriptor_holds_of_microscopic'`
-- English: importing only `Sharp` + `Reorg` reports `unknown identifier '…descriptor_holds_of_microscopic'`
--    （实测失败路径，记在此处：**模块名 ≠ 定理名所在模块**时 `#check` 需要 import 到定义模块）。
-- English: (a measured failure path, recorded here: when **the module name ≠ the module holding the theorem name**, `#check` must import up to the defining module).
import PhotoLean.Marcus.Sharp
import PhotoLean.Marcus.Reorg
import PhotoLean.Marcus.Compose

namespace PhotoLean.Marcus.ProbeD2

open PhotoLean.Marcus

/-! ## A. 名字校准（不猜名：先 `#check`）—— 以下全部存在（实测 0 error）

## A. Name calibration (never guess a name: `#check` first) — all of the following exist (measured: 0 errors)
-/

#check @one_div_le_one_div_of_le
-- @one_div_le_one_div_of_le : ∀ {α} [LinearOrderedSemifield α] {a b : α}, 0 < a → a ≤ b → 1 / b ≤ 1 / a

#check @div_lt_div_iff₀
-- @div_lt_div_iff₀ : ∀ {G₀} [CommGroupWithZero G₀] …, 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)

#check @div_lt_iff₀
-- @div_lt_iff₀ : … 0 < c → (b / c < a ↔ b < a * c)

#check @one_div_add_one_div
-- @one_div_add_one_div : ∀ {K} [Semifield K] {a b : K}, a ≠ 0 → b ≠ 0 → 1 / a + 1 / b = (a + b) / (a * b)
--   （本交付未用它 —— 通分走 field_simp；记在此处备查）
-- English: (this delivery does not use it — clearing denominators goes through field_simp; recorded here for reference)

#check @div_add_div
-- @div_add_div : ∀ {K} [Semifield K] {b d : K} (a c : K),
--   b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + b * c) / (b * d)

#check @sq_pos_of_ne_zero
-- @sq_pos_of_ne_zero : ∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2
--   ⚠️ `a` 是**隐式**参数（API-NOTES C-2）：写 `sq_pos_of_ne_zero (ne_of_gt ha1)`，不要写 `sq_pos_of_ne_zero a1 …`
-- English: ⚠️ `a` is an **implicit** argument (API-NOTES C-2): write `sq_pos_of_ne_zero (ne_of_gt ha1)`, not `sq_pos_of_ne_zero a1 …`

/-! ## B. 交付定理的签名复核（`#check` 直接打出来，供人工比对 plan §7.2）

## B. Signature re-check of the delivered theorems (the `#check`s printed out directly, for manual comparison against plan §7.2)
-/

#check @PhotoLean.Marcus.hgeom_of_nonoverlap
#check @PhotoLean.Marcus.descriptor_holds_of_microscopic
#check @PhotoLean.Marcus.descriptor_holds_of_nonoverlap

/-! ## C. `hgeom_of_nonoverlap` 的交付骨架（与 Reorg.lean 逐字相同）

## C. Delivery skeleton of `hgeom_of_nonoverlap` (verbatim identical to Reorg.lean)
-/

example {a1 a2 R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2) (hRge : a1 + a2 ≤ R) :
    1 / R < 1 / (2 * a1) + 1 / (2 * a2) := by
  have hpos : 0 < a1 + a2 := by linarith
  have h1 : 1 / R ≤ 1 / (a1 + a2) := one_div_le_one_div_of_le hpos hRge
  have hden : 0 < 2 * a1 * a2 := by positivity
  have hsum : 1 / (2 * a1) + 1 / (2 * a2) = (a1 + a2) / (2 * a1 * a2) := by
    field_simp
    ring
  have h2 : 1 / (a1 + a2) < 1 / (2 * a1) + 1 / (2 * a2) := by
    rw [hsum]
    rw [div_lt_div_iff₀ hpos hden]
    nlinarith [sq_nonneg a2, sq_pos_of_ne_zero (ne_of_gt ha1)]
  linarith

/-! ## D. 两条复合定理在真实模块上的组装复核

## D. Re-checking how the two composition theorems assemble against the real modules
-/

example {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T :=
  inverted_descriptor_holds hA
    (lam_total_pos (lamInner_nonneg hkk dq)
      (lamOuter_pos hdE ha1 ha2 hR hgeom hnSq hepsS hPekar))
    (mul_pos hkB hT)

example {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) (hnSq : 0 < nSq) (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T :=
  descriptor_holds_of_nonoverlap hA hkB hT hkk hdE ha1 ha2 hRge hnSq hepsS hPekar

/-! ## E. 非空性/相容性取证：把拉伸版喂具体数字（几何侧 `a1 = a2 = 1`、`R = 3`）

前提集**可满足**（不是空洞定理）：
- `hRge : 1 + 1 ≤ 3` ✓；`hgeom` 的结论 `1/3 < 1/(2·1) + 1/(2·1) = 1` ✓（下面第一条 example）；
- Pekar 侧 `nSq = 1 < epsS = 2` ⇒ `1/2 < 1` ✓；
- 取 `kk = 0`（无内层重组，内层只要求非负 —— 正是 `lamInner_nonneg` 而非 `lamInner_pos`
  的用武之地）、`dE = 1`、`A = kB = T = 1`。
  此时 `lamInner 0 dq = 0`、`lamOuter 1 1 1 3 1 2 = (1/2 + 1/2 - 1/3) · (1 - 1/2) = 1/3`，
  结论退化为 `InvertedDescriptor 1 (1/3) 1 1`（在 `x > 1/3` 处速率随驱动力严格递减）——
  一条**具体的、可继续代入实例层**的判断。

## E. Non-emptiness / compatibility evidence: feed concrete numbers to the stretch version (geometry side `a1 = a2 = 1`, `R = 3`)

The hypothesis set is **satisfiable** (the theorem is not vacuous):
- `hRge : 1 + 1 ≤ 3` ✓; the conclusion of `hgeom`, `1/3 < 1/(2·1) + 1/(2·1) = 1` ✓ (the first example below);
- Pekar side: `nSq = 1 < epsS = 2` ⇒ `1/2 < 1` ✓;
- take `kk = 0` (no inner reorganization; the inner term only has to be nonnegative — exactly what `lamInner_nonneg`
  rather than `lamInner_pos` is for), `dE = 1`, `A = kB = T = 1`.
  Then `lamInner 0 dq = 0` and `lamOuter 1 1 1 3 1 2 = (1/2 + 1/2 - 1/3) · (1 - 1/2) = 1/3`,
  so the conclusion degenerates to `InvertedDescriptor 1 (1/3) 1 1` (the rate is strictly decreasing in the driving
  force for `x > 1/3`) — a **concrete judgement that can be fed further into the instance layer**.
-/

example : (1 : ℝ) / 3 < 1 / (2 * 1) + 1 / (2 * 1) :=
  hgeom_of_nonoverlap (by norm_num) (by norm_num) (by norm_num)

example (dq : ℝ) : InvertedDescriptor 1 (lamInner 0 dq + lamOuter 1 1 1 3 1 2) 1 1 :=
  descriptor_holds_of_nonoverlap (A := 1) (kB := 1) (T := 1) (kk := 0) (dq := dq) (dE := 1)
    (a1 := 1) (a2 := 1) (R := 3) (nSq := 1) (epsS := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- 同一条链的 microscopic 版（几何前提显式给出），确认两条定理取值一致：
-- English: the microscopic version of the same chain (with the geometric hypothesis given explicitly), confirming that the two theorems take the same value:
-- ⚠️ 坑（实测）：**不要混用位置参数与具名参数** —— 上面 nonoverlap 版那样全位置最省事；
-- English: ⚠️ trap (measured): **do not mix positional and named arguments** — going fully positional as in the nonoverlap version above is the least trouble;
--    microscopic 版有 12 条显式前提（多一个 `hR`），混写会少喂一个参数，
-- English: the microscopic version has 12 explicit hypotheses (one more, `hR`), so mixing the two styles feeds one argument too few,
--    报 `type mismatch … but is expected to have type …`（缺参 = 部分应用）。
-- English: reporting `type mismatch … but is expected to have type …` (a missing argument = a partial application).
example (dq : ℝ) : InvertedDescriptor 1 (lamInner 0 dq + lamOuter 1 1 1 3 1 2) 1 1 :=
  descriptor_holds_of_microscopic (A := 1) (kB := 1) (T := 1) (kk := 0) (dq := dq) (dE := 1)
    (a1 := 1) (a2 := 1) (R := 3) (nSq := 1) (epsS := 2)
    (hA := by norm_num) (hkB := by norm_num) (hT := by norm_num) (hkk := by norm_num)
    (hdE := by norm_num) (ha1 := by norm_num) (ha2 := by norm_num) (hR := by norm_num)
    (hgeom := by norm_num) (hnSq := by norm_num) (hepsS := by norm_num) (hPekar := by norm_num)

end PhotoLean.Marcus.ProbeD2
