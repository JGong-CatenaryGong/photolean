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
-/

-- ⚠️ 探针若要 `#check` 复合定理，必须 import `Compose`（它才是两条复合定理的所在模块）；
--    只 import `Sharp` + `Reorg` 会报 `unknown identifier '…descriptor_holds_of_microscopic'`
--    （实测失败路径，记在此处：**模块名 ≠ 定理名所在模块**时 `#check` 需要 import 到定义模块）。
import PhotoLean.Marcus.Sharp
import PhotoLean.Marcus.Reorg
import PhotoLean.Marcus.Compose

namespace PhotoLean.Marcus.ProbeD2

open PhotoLean.Marcus

/-! ## A. 名字校准（不猜名：先 `#check`）—— 以下全部存在（实测 0 error） -/

#check @one_div_le_one_div_of_le
-- @one_div_le_one_div_of_le : ∀ {α} [LinearOrderedSemifield α] {a b : α}, 0 < a → a ≤ b → 1 / b ≤ 1 / a

#check @div_lt_div_iff₀
-- @div_lt_div_iff₀ : ∀ {G₀} [CommGroupWithZero G₀] …, 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)

#check @div_lt_iff₀
-- @div_lt_iff₀ : … 0 < c → (b / c < a ↔ b < a * c)

#check @one_div_add_one_div
-- @one_div_add_one_div : ∀ {K} [Semifield K] {a b : K}, a ≠ 0 → b ≠ 0 → 1 / a + 1 / b = (a + b) / (a * b)
--   （本交付未用它 —— 通分走 field_simp；记在此处备查）

#check @div_add_div
-- @div_add_div : ∀ {K} [Semifield K] {b d : K} (a c : K),
--   b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + b * c) / (b * d)

#check @sq_pos_of_ne_zero
-- @sq_pos_of_ne_zero : ∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2
--   ⚠️ `a` 是**隐式**参数（API-NOTES C-2）：写 `sq_pos_of_ne_zero (ne_of_gt ha1)`，不要写 `sq_pos_of_ne_zero a1 …`

/-! ## B. 交付定理的签名复核（`#check` 直接打出来，供人工比对 plan §7.2） -/

#check @PhotoLean.Marcus.hgeom_of_nonoverlap
#check @PhotoLean.Marcus.descriptor_holds_of_microscopic
#check @PhotoLean.Marcus.descriptor_holds_of_nonoverlap

/-! ## C. `hgeom_of_nonoverlap` 的交付骨架（与 Reorg.lean 逐字相同） -/

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

/-! ## D. 两条复合定理在真实模块上的组装复核 -/

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
  一条**具体的、可继续代入实例层**的判断。 -/

example : (1 : ℝ) / 3 < 1 / (2 * 1) + 1 / (2 * 1) :=
  hgeom_of_nonoverlap (by norm_num) (by norm_num) (by norm_num)

example (dq : ℝ) : InvertedDescriptor 1 (lamInner 0 dq + lamOuter 1 1 1 3 1 2) 1 1 :=
  descriptor_holds_of_nonoverlap (A := 1) (kB := 1) (T := 1) (kk := 0) (dq := dq) (dE := 1)
    (a1 := 1) (a2 := 1) (R := 3) (nSq := 1) (epsS := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- 同一条链的 microscopic 版（几何前提显式给出），确认两条定理取值一致：
-- ⚠️ 坑（实测）：**不要混用位置参数与具名参数** —— 上面 nonoverlap 版那样全位置最省事；
--    microscopic 版有 12 条显式前提（多一个 `hR`），混写会少喂一个参数，
--    报 `type mismatch … but is expected to have type …`（缺参 = 部分应用）。
example (dq : ℝ) : InvertedDescriptor 1 (lamInner 0 dq + lamOuter 1 1 1 3 1 2) 1 1 :=
  descriptor_holds_of_microscopic (A := 1) (kB := 1) (T := 1) (kk := 0) (dq := dq) (dE := 1)
    (a1 := 1) (a2 := 1) (R := 3) (nSq := 1) (epsS := 2)
    (hA := by norm_num) (hkB := by norm_num) (hT := by norm_num) (hkk := by norm_num)
    (hdE := by norm_num) (ha1 := by norm_num) (ha2 := by norm_num) (hR := by norm_num)
    (hgeom := by norm_num) (hnSq := by norm_num) (hepsS := by norm_num) (hPekar := by norm_num)

end PhotoLean.Marcus.ProbeD2
