/-
PhotoLean.KashaVavilov.Criterion — KV2, the D2 core: Kasha versus Kasha–Vavilov independence.

This is the headline module of the theory and of adjudication target **D2** of the photophysics
batch. Kasha's rule (emission only from the lowest excited state of a given multiplicity) and
Vavilov's rule (the fluorescence quantum yield is independent of the excitation wavelength) are
run together in the textbooks and are often treated as one statement; the delivered
`PhotoLean.Kasha.Criterion` already contains the conditional equivalence
`kashaRule_iff_vavilovUpTo` (with a loss channel at the lowest level the two closed rules
coincide). D2 adjudicates the **pair** (plan §1.1):

* pointwise, the two predicates are **logically independent** — each has an admissible witness
  where it holds and the other fails (rows KV-C1, KV-C2), and both witnesses sit at the positive
  excitation level `N = 1` **inside the lossy regime** `0 < ic 0`, so the independence is not a
  degenerate corner (the M1 lesson applied prospectively);
* they coincide **exactly** under the closed quantification plus the loss premise — the delivered
  `Kasha.kashaRule_iff_vavilovUpTo`, re-stated as the third conjunct of the headline `d2_verdict`
  (KV-C4);
* at `ic 0 = 0` the closed forms **separate** (KV-C3): the yield is identically `1`
  (`Kasha.fluoYield_eq_one_sub_loss`), Vavilov's rule holds vacuously and Kasha's rule fails, so
  the `0 < ic 0` premise of the equivalence is load-bearing.

The remaining rows sharpen the same picture: the cascade is positive exactly when every
nonradiative rate above the level is (KV-C5), a level-resolved yield is positive exactly for a
radiative level reached by a positive cascade (KV-C6), and — the anti-Kasha boundary — a
**violation of Kasha's rule is always observable** in this model: the leak is positive precisely
when the rule fails (KV-C7). KV-C7 is the only row whose proof is not index arithmetic: it needs
the *maximal emitter* (KV-C7b), the largest radiative level of `[1, N]`, which has every level
above it nonradiative, converts with certainty (`icBranch = 1`, by the positivity of the total
decay rate in `RateData`) and therefore leaks a positive amount (KV-C7a).

What is NOT derived here: the ladder model itself and the identification of `ic 0` with the lowest
state's loss channel are inherited modelling assumptions (plan §9); every positivity stays an
explicit hypothesis (`Kasha.RateData` on every row), and the numeric witness values are the ones
pre-computed and proved in `theories/KashaVavilov/probes/KashaVavilov-api-probe.lean` — kernel
computation on rational literals, no runtime evaluation enters any theorem.

Statement authority: every theorem signature below is taken word for word from
`theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` (the frozen Phase-1 authority,
sha256 `5a51614d80d8340d76b605657802152f6574ad40c31aa6eb9e8d373d65dfdb15`, 29 declarations), which
transcribes `theories/KashaVavilov/plan.md` §4. The helper lemmas `icBranch_eq_one_of_rad_zero`
and `cascade_eq_one_of_rad_zero_above` are auxiliary declarations of this module (delivered rows
only, no new statement of the authority). Note deliberately: the two keyword literals that
`proofs/scripts/check.sh --strict` scans for are not spelled out anywhere in this file — the scan
covers `PhotoLean/**/*.lean` including block comments, so writing them (even in prose) would be a
false-positive FAIL.

Plan locus: `theories/KashaVavilov/plan.md` §4 (KV-C rows), sprint KV2; board
`theories/KashaVavilov/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.KashaVavilov.Criterion
    proofs/scripts/check.sh --strict PhotoLean.KashaVavilov.Criterion
    proofs/scripts/axioms.sh PhotoLean.KashaVavilov.Criterion PhotoLean.KashaVavilov.d2_verdict

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
`#print axioms` of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import PhotoLean.KashaVavilov.Basic
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace KashaVavilov

/-! ## The independence witnesses (plan §4, rows KV-C1–KV-C4) -/

/-- Plan section 4, row KV-C1 — first independence direction: Kasha's rule does not imply
Vavilov's rule. Witness `rad = fun n => if n = 1 then 0 else 1`, `ic = fun _ => 1` with
`fluoYield 1 = 1/2` and `fluoYield 2 = 3/4` (both pre-computed in the API probe); admissibility by
`interval_cases` on the literal ladder. The witness sits at the positive excitation level `N = 1`
inside the lossy regime (`ic 0 = 1 > 0`): the independence is not the degenerate corner (the M1
lesson applied prospectively). -/
theorem kashaRule_not_implies_vavilovAt :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.KashaRule rad ic 1 ∧
      ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0 := by
  have hR : Kasha.RateData (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 2 := by
    refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay]
    · by_cases hn : n = 1
      · subst hn
        norm_num
      · rw [if_neg hn]
        norm_num
    · norm_num
  have hR1 : Kasha.RateData (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 1 :=
    rateData_mono hR (by norm_num)
  refine ⟨fun n => if n = 1 then (0 : ℝ) else 1, fun _ => 1, hR, ?_, ?_, ?_⟩
  · exact Kasha.kashaRule_of_rad_zero hR1 fun i hi1 hi2 => by
      have hi : i = 1 := by omega
      subst hi
      norm_num
  · intro hV
    have h1 : Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 1 = 1 / 2 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    have h2 : Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 2 = 3 / 4 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    have hV' : Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) (1 + 1) =
        Kasha.fluoYield (fun n => if n = 1 then (0 : ℝ) else 1) (fun _ => 1) 1 := hV
    rw [h1, h2] at hV'
    norm_num at hV'
  · norm_num

/-- Plan section 4, row KV-C2 — second independence direction: Vavilov's rule does not imply
Kasha's rule. Witness `rad = fun n => if n = 2 then 0 else 1`, `ic = fun _ => 1` with
`fluoYield 1 = fluoYield 2 = 3/4` (the API probe's pre-computed values) while `rad 1 = 1 > 0`
refutes the exact rule by `Kasha.not_kashaRule_of_rad_pos`; `norm_num`, admissibility by
`interval_cases`. -/
theorem vavilovAt_not_implies_kashaRule :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.VavilovAt rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0 := by
  have hR : Kasha.RateData (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 2 := by
    refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay]
    · by_cases hn : n = 2
      · subst hn
        norm_num
      · rw [if_neg hn]
        norm_num
    · norm_num
  have hR1 : Kasha.RateData (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 1 :=
    rateData_mono hR (by norm_num)
  refine ⟨fun n => if n = 2 then (0 : ℝ) else 1, fun _ => 1, hR, ?_, ?_, ?_⟩
  · have h1 : Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 1 = 3 / 4 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    have h2 : Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 2 = 3 / 4 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    show Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) (1 + 1) =
      Kasha.fluoYield (fun n => if n = 2 then (0 : ℝ) else 1) (fun _ => 1) 1
    rw [h1, h2]
  · have hpos1 : 0 < (fun n => if n = 2 then (0 : ℝ) else 1) 1 := by norm_num
    exact Kasha.not_kashaRule_of_rad_pos (i := 1) hR1 (by norm_num) (by norm_num) hpos1
  · norm_num

/-- Plan section 4, row KV-C3 — the `0 < ic 0` premise of the delivered equivalence is
load-bearing: at `ic 0 = 0` the yield is identically `1` (`Kasha.fluoYield_eq_one_sub_loss`),
Vavilov's rule holds vacuously, and Kasha's rule fails. Witness `rad = fun _ => 1`,
`ic = fun n => if n = 0 then 0 else 1`, with `fluoYield 0 = fluoYield 1 = 1` (the API probe's
pre-computed values) and `rad 1 = 1 > 0`. -/
theorem lossless_separates_kasha_vavilov :
    ∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧ ic 0 = 0 ∧ Kasha.VavilovUpTo rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 := by
  have hR : Kasha.RateData (fun _ : ℕ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) 1 := by
    refine ⟨fun n hn => ?_, fun n => ?_, fun n => ?_⟩
    · interval_cases n <;> norm_num [Kasha.decay]
    · norm_num
    · by_cases hn : n = 0
      · subst hn
        norm_num
      · rw [if_neg hn]
        norm_num
  refine ⟨fun _ : ℕ => (1 : ℝ), fun n => if n = 0 then (0 : ℝ) else 1, hR, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i
    have h0 : Kasha.fluoYield (fun _ : ℕ => (1 : ℝ))
        (fun n => if n = 0 then (0 : ℝ) else 1) 0 = 1 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    have h1 : Kasha.fluoYield (fun _ : ℕ => (1 : ℝ))
        (fun n => if n = 0 then (0 : ℝ) else 1) 1 = 1 := by
      norm_num [Kasha.fluoYield, Kasha.emitYield, Kasha.cascade, Kasha.radBranch, Kasha.icBranch,
        Kasha.decay, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_Icc_succ_top,
        Finset.sum_singleton, Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
    show Kasha.fluoYield (fun _ : ℕ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) (0 + 1) =
      Kasha.fluoYield (fun _ : ℕ => (1 : ℝ)) (fun n => if n = 0 then (0 : ℝ) else 1) 0
    rw [h0, h1]
  · have hpos1 : 0 < (fun _ : ℕ => (1 : ℝ)) 1 := by norm_num
    exact Kasha.not_kashaRule_of_rad_pos (i := 1) hR (by norm_num) (by norm_num) hpos1

set_option linter.unusedVariables false in
/-- Plan section 4, row KV-C4 — **the D2 adjudication headline**: the two rules are pointwise
independent in both directions (KV-C1, KV-C2), they coincide exactly under the closed
quantification plus the loss premise (the delivered `Kasha.kashaRule_iff_vavilovUpTo` re-stated),
and the lossless corner separates the closed forms (KV-C3). One conjunct per component row. -/
theorem d2_verdict :
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.KashaRule rad ic 1 ∧
      ¬ Kasha.VavilovAt rad ic 1 ∧ 0 < ic 0) ∧
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 2 ∧ Kasha.VavilovAt rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1 ∧ 0 < ic 0) ∧
    (∀ rad ic : ℕ → ℝ, ∀ N : ℕ, Kasha.RateData rad ic N → 0 < ic 0 →
      (Kasha.KashaRule rad ic N ↔ Kasha.VavilovUpTo rad ic N)) ∧
    (∃ rad ic : ℕ → ℝ, Kasha.RateData rad ic 1 ∧ ic 0 = 0 ∧ Kasha.VavilovUpTo rad ic 1 ∧
      ¬ Kasha.KashaRule rad ic 1) :=
  ⟨kashaRule_not_implies_vavilovAt, vavilovAt_not_implies_kashaRule,
    fun rad ic N h h0 => Kasha.kashaRule_iff_vavilovUpTo h h0, lossless_separates_kasha_vavilov⟩

/-! ## The observability rows (plan §4, rows KV-C5–KV-C7) -/

set_option linter.unusedVariables false in
/-- Plan section 4, row KV-C5 — positivity of the cascade is exactly the positivity of every
nonradiative rate above level `i`. Both directions are product algebra: a positive product has
positive factors (`Finset.mul_prod_erase` on an otherwise nonnegative product), and a product of
positive factors is positive (`Finset.prod_pos`). The premise `hi : i ≤ N` is part of the
authority's signature and is not consumed by the proof (the product's own membership hypothesis
supplies `j ≤ N`); it is kept verbatim for statement fidelity. -/
theorem cascade_pos_iff {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N) (hi : i ≤ N) :
    (0 < Kasha.cascade rad ic i N ↔ ∀ j, i + 1 ≤ j → j ≤ N → 0 < ic j) := by
  unfold Kasha.cascade
  constructor
  · intro hpos j hj1 hjN
    have hnonneg : ∀ k ∈ Finset.Icc (i + 1) N, 0 ≤ Kasha.icBranch rad ic k := fun k hk =>
      Kasha.icBranch_nonneg h (Finset.mem_Icc.mp hk).2
    have hpos' : 0 < ∏ k ∈ Finset.Icc (i + 1) N, Kasha.icBranch rad ic k := hpos
    have hmem : j ∈ Finset.Icc (i + 1) N := Finset.mem_Icc.mpr ⟨hj1, hjN⟩
    have hrest : 0 ≤ ∏ k ∈ (Finset.Icc (i + 1) N).erase j, Kasha.icBranch rad ic k :=
      Finset.prod_nonneg fun k hk => hnonneg k (Finset.mem_of_mem_erase hk)
    have hfac : 0 < Kasha.icBranch rad ic j := by
      by_contra hc
      have hle : Kasha.icBranch rad ic j * (∏ k ∈ (Finset.Icc (i + 1) N).erase j,
          Kasha.icBranch rad ic k) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hrest
      rw [Finset.mul_prod_erase _ _ hmem] at hle
      linarith
    have hdec : 0 < Kasha.decay rad ic j := h.decay_pos j hjN
    unfold Kasha.icBranch at hfac
    exact (div_pos_iff_of_pos_right hdec).mp hfac
  · intro hic
    exact Finset.prod_pos fun j hj => by
      obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
      unfold Kasha.icBranch
      exact div_pos (hic j hj1 hjN) (h.decay_pos j hjN)

/-- Plan section 4, row KV-C6 — positivity of a level-resolved emission yield is exactly a
radiative level reached by a positive cascade. `emitYield i N = radBranch i · cascade i N` and
`radBranch i > 0` is `rad i > 0` under the positive total decay rate of `RateData`; the `→`
direction also reads the positivity of the cascade off the positive product. -/
theorem emitYield_pos_iff {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N) (hi : i ≤ N) :
    (0 < Kasha.emitYield rad ic i N ↔ 0 < rad i ∧ 0 < Kasha.cascade rad ic i N) := by
  have hR : 0 < Kasha.radBranch rad ic i ↔ 0 < rad i := by
    unfold Kasha.radBranch
    exact div_pos_iff_of_pos_right (h.decay_pos i hi)
  have hRnn : 0 ≤ Kasha.radBranch rad ic i := Kasha.radBranch_nonneg h hi
  have hCnn : 0 ≤ Kasha.cascade rad ic i N := Kasha.cascade_nonneg h hi
  have hem : Kasha.emitYield rad ic i N = Kasha.radBranch rad ic i * Kasha.cascade rad ic i N := rfl
  rw [hem]
  exact ⟨fun hp => ⟨hR.mp (pos_of_mul_pos_left hp hCnn), pos_of_mul_pos_right hp hRnn⟩,
    fun hp => mul_pos (hR.mpr hp.1) hp.2⟩

/-- Auxiliary row of this module (no statement of the authority): above its last radiative level
the ladder converts with certainty, i.e. every nonradiative branch is `1`. This is the engine of
KV-C7a: `rad j = 0` with `decay j > 0` forces `icBranch j = 1`. -/
theorem icBranch_eq_one_of_rad_zero {rad ic : ℕ → ℝ} {N i j : ℕ} (h : Kasha.RateData rad ic N)
    (habove : ∀ k, i < k → k ≤ N → rad k = 0) (hij : i < j) (hjN : j ≤ N) :
    Kasha.icBranch rad ic j = 1 := by
  have hrad : rad j = 0 := habove j hij hjN
  have hdec : Kasha.decay rad ic j = ic j := by
    rw [Kasha.decay_eq_rad_add_ic, hrad, zero_add]
  have hdecpos : 0 < Kasha.decay rad ic j := h.decay_pos j hjN
  unfold Kasha.icBranch
  rw [hdec]
  exact div_self (ne_of_gt (by rwa [hdec] at hdecpos))

/-- Auxiliary row of this module (no statement of the authority): with every level above `i`
nonradiative, the cascade from `i` to `N` is `1` — the product of unit factors, the base case
being `Kasha.cascade_self`. -/
theorem cascade_eq_one_of_rad_zero_above {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N)
    (hiN : i ≤ N) (habove : ∀ j, i < j → j ≤ N → rad j = 0) :
    Kasha.cascade rad ic i N = 1 := by
  rcases eq_or_lt_of_le hiN with rfl | hlt
  · exact Kasha.cascade_self rad ic i
  · unfold Kasha.cascade
    rw [Finset.prod_eq_one]
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
    exact icBranch_eq_one_of_rad_zero h habove (by omega) hjN

/-- Plan section 4, row KV-C7a (sub-row of KV-C7) — a radiative level above the lowest one whose
higher levels are all nonradiative makes the leak positive: its `icBranch` factors above are all
`1` (by `RateData.decay_pos`), so its cascade is `1`, its `emitYield` is the positive
`radBranch i` and a single positive summand inside a nonnegative sum bounds `Kasha.upperYield`
away from `0`. -/
theorem upperYield_pos_of_rad_pos {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N)
    (hi1 : 1 ≤ i) (hiN : i ≤ N) (hrad : 0 < rad i) (habove : ∀ j, i < j → j ≤ N → rad j = 0) :
    0 < Kasha.upperYield rad ic N := by
  have hcasc : Kasha.cascade rad ic i N = 1 :=
    cascade_eq_one_of_rad_zero_above h hiN habove
  have hemit : 0 < Kasha.emitYield rad ic i N := by
    unfold Kasha.emitYield Kasha.radBranch
    rw [hcasc, mul_one]
    exact div_pos hrad (h.decay_pos i hiN)
  have hmem : i ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hi1, hiN⟩
  have hsingle : Kasha.emitYield rad ic i N ≤ Kasha.upperYield rad ic N := by
    unfold Kasha.upperYield
    exact Finset.single_le_sum (fun j hj => Kasha.emitYield_nonneg h (Finset.mem_Icc.mp hj).2) hmem
  linarith

/-- Plan section 4, row KV-C7b (sub-row of KV-C7) — the maximal emitter exists: among the
radiative levels of `[1, N]` there is a largest one, and every level above it is nonradiative.
Proof route (plan §5): a maximal-element API over `{j ∈ Finset.Icc 1 N | 0 < rad j}`
(`Finset.exists_max_image`, classical). Weakest-premise standard: only `rad`-nonnegativity is
consumed (to read maximality as `rad j = 0` above), so no `RateData` bundle is taken. -/
theorem exists_maximal_emitter {rad : ℕ → ℝ} {N : ℕ} (hnn : ∀ n, 0 ≤ rad n)
    (h : ∃ i, 1 ≤ i ∧ i ≤ N ∧ 0 < rad i) :
    ∃ i, 1 ≤ i ∧ i ≤ N ∧ 0 < rad i ∧ ∀ j, i < j → j ≤ N → rad j = 0 := by
  obtain ⟨i0, hi01, hi0N, hi0p⟩ := h
  obtain ⟨x, hxmem, hxmax⟩ :=
    Finset.exists_max_image (Finset.filter (fun a => 0 < rad a) (Finset.Icc 1 N)) (fun a => a)
      ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi01, hi0N⟩, hi0p⟩⟩
  obtain ⟨hxIcc, hxp⟩ := Finset.mem_filter.mp hxmem
  obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp hxIcc
  refine ⟨x, hx1, hxN, hxp, fun j hxj hjN => ?_⟩
  by_contra hne
  have hp : 0 < rad j := lt_of_le_of_ne (hnn j) (Ne.symm hne)
  have hjm : j ∈ Finset.filter (fun a => 0 < rad a) (Finset.Icc 1 N) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hjN⟩, hp⟩
  have hle : j ≤ x := hxmax j hjm
  omega

/-- Plan section 4, row KV-C7 — **the anti-Kasha boundary**: a violation of the rule is always
observable in this model — the leak `Kasha.upperYield` is positive **iff** the exact rule fails.
`→` is the contrapositive of `Kasha.upperYield_eq_zero_iff` plus KV-C6; `←` uses the maximal
emitter (KV-C7b) read through `Kasha.kashaRule_iff_rad_zero`, whose cascade is `1` above it
(KV-C7a). -/
theorem antiKasha_observable_iff {rad ic : ℕ → ℝ} {N : ℕ} (h : Kasha.RateData rad ic N) :
    (0 < Kasha.upperYield rad ic N ↔ ¬ Kasha.KashaRule rad ic N) := by
  constructor
  · intro hpos hK
    exact absurd hK (ne_of_gt hpos)
  · intro hK
    have hex : ∃ i, 1 ≤ i ∧ i ≤ N ∧ 0 < rad i := by
      by_contra hc
      apply hK
      refine (Kasha.kashaRule_iff_rad_zero h).mpr fun i hi1 hiN => ?_
      by_contra hne
      exact hc ⟨i, hi1, hiN, lt_of_le_of_ne (h.rad_nonneg i) (Ne.symm hne)⟩
    obtain ⟨i, hi1, hiN, hirad, habove⟩ := exists_maximal_emitter h.rad_nonneg hex
    exact upperYield_pos_of_rad_pos h hi1 hiN hirad habove

end KashaVavilov

end PhotoLean
