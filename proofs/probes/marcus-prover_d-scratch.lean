-- prover_d scratch probe (M4b): 只做 #check / example，用于确认 mathlib 名字与战术可用性。
-- 运行：proofs/scripts/lake env lean proofs/probes/marcus-prover_d-scratch.lean
import PhotoLean.Marcus.Reorg

open PhotoLean.Marcus

-- 1) 平方正性引理的名字与签名
#check @sq_nonneg
#check @sq_pos_of_ne_zero
#check @pow_pos
#check @div_pos
#check @mul_pos
#check @one_div_pos
#check @one_div
#check @inv_pos

-- 2) 目标形态最小验证（无占位证明）
example {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ kk * dq ^ 2 / 2 := by positivity

-- 实测（v4.17）：`sq_pos_of_ne_zero` 的签名是 `{a : R} → a ≠ 0 → 0 < a ^ 2`
-- —— `a` 是**隐式**参数，因此必须写 `sq_pos_of_ne_zero hdq`；
-- 写成 `sq_pos_of_ne_zero dq hdq` 会报 application type mismatch（plan §7.2 的提示是错的）。
example {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) : 0 < kk * dq ^ 2 / 2 := by
  have hsq : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq
  positivity

example {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq)
    (hepsS : 0 < epsS) (hPekar : 1 / epsS < 1 / nSq) :
    0 < dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS) := by
  have hgeom' : 0 < 1 / (2 * a1) + 1 / (2 * a2) - 1 / R := by linarith
  have hPekar' : 0 < 1 / nSq - 1 / epsS := by linarith
  have hdE2 : 0 < dE ^ 2 := by positivity
  exact mul_pos (mul_pos hdE2 hgeom') hPekar'

-- 3) 前提的可满足性（非空真）与必要性：把 M4b 的语句代进一组物理上合理的参数。
--    参数：dE=1, a1=a2=1, R=2, nSq=2 (n≈1.41), epsS=80 (水)
--    ⇒ 几何因子 = 1/2 + 1/2 - 1/2 = 1/2 > 0；Pekar 因子 = 1/2 - 1/80 > 0
--    （注：R 必须 > a1 + a2 的一半尺度才使几何因子为正；R=1/2 时几何因子 = -1，见下方注释）
example : 0 < 1 / (2 * (1:ℝ)) + 1 / (2 * (1:ℝ)) - 1 / (2 : ℝ) := by norm_num
example : 0 < lamOuter 1 1 1 2 2 80 := by unfold lamOuter; norm_num

-- 非空真：lamInner 在 kk>0、dq≠0 下确实严格正
example : 0 < lamInner 1 (3/7) := by unfold lamInner; norm_num
-- 必要性：去掉 hdq（dq = 0）后结论为假 ⇒ `dq ≠ 0` 不可省
example : ¬ (0 < lamInner 1 0) := by unfold lamInner; norm_num
-- 必要性：去掉 hPekar（nSq=80 > epsS=2，即 n² > ε_s 的非物理溶剂，几何因子仍为正）后结论为假
example : ¬ (0 < lamOuter 1 1 1 2 80 2) := by unfold lamOuter; norm_num
