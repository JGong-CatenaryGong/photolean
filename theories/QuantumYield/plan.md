# theories/QuantumYield/plan.md — PhotoLean formalization plan: quantum-yield additivity (QY1–QY4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/QuantumYield-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/QuantumYield/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group A (rate-cascade basis),
> third theory of the construction order.

---

## 1. Overall goal and boundaries

### 1.1 The claim

For parallel first-order decay channels of one excited state, the observable yield of channel
`i` is `kᵢ / Σⱼ kⱼ`; the yields are *additive* in two senses: they sum to `1` (conservation), and
adding a channel rescales every existing yield by the same factor `Σk / (Σk + c)` (the dilution
law — the algebraic spine underneath Stern–Volmer quenching and fluorescence/phosphorescence
competition). The channel yields share **one** lifetime `τ = 1/Σk` (the common-lifetime law:
`yieldOf k i = k i * tauOf k`).

### 1.2 The model (chosen, not derived)

`n` parallel channels with rates `k : Fin n → ℝ`; total rate `totalRate k := ∑ i, k i`; yield
`yieldOf k i := k i / totalRate k` (totalized division). The premise bundle `QYData` is
nonnegative rates + positive total. No time dependence, no sequential kinetics (the ladder is
Kasha's), no coherence effects.

### 1.3 Explicit non-goals

* No integration of rate laws (the exponential decay itself is not modeled; yields are the
  time-integrated content, registered).
* No channel-count dynamics: `n` is fixed per statement; the added channel is `Fin.cons`.

## 2. Conventions and symbols

`Fin n → ℝ` for the rate vector; `Finset.univ` sums; `Fin.cons c k` for the added channel (the
new channel sits at index `0`). Namespace `PhotoLean.QuantumYield`; rational layer
`PhotoLean.QuantumYield.Rat`.

## 3. Statement authority and inventory

The authority is `probes/QuantumYield-statement-skeleton.lean` (Phase-1 placeholder bodies;
sha256 on the board once compiling).

### 3.1 Statement-correction log

* **Entry 0 (2026-09-22, literature note — no statement change)** — the literature's current
  best quantum yields are fluorescein ≈ 0.95 (0.1 M NaOH) and quinine ≈ 0.546
  (0.5 M H₂SO₄); the named instances `9/10` and `11/20` are order-of-magnitude representatives,
  and their docstrings must not present them as the recommended values (LITERATURE.md).

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (QY-B), `Criterion.lean` (QY-C), `RatModel.lean` (QY-R),
`Instances.lean` (QY-I).

**QY-B (definitions):**

* QY-B1 `totalRate {n : ℕ} (k : Fin n → ℝ) : ℝ := ∑ i, k i`.
* QY-B2 `yieldOf {n : ℕ} (k : Fin n → ℝ) (i : Fin n) : ℝ := k i / totalRate k`.
* QY-B3 `tauOf {n : ℕ} (k : Fin n → ℝ) : ℝ := 1 / totalRate k` — the common lifetime.
* QY-B4 `structure QYData {n : ℕ} (k : Fin n → ℝ) : Prop` with fields `nonneg : ∀ i, 0 ≤ k i`
  and `total_pos : 0 < totalRate k` — the premise bundle.

**QY-C (laws):**

* QY-C1 `sum_yieldOf_eq_one {n} {k : Fin n → ℝ} (h : QYData k) : ∑ i, yieldOf k i = 1` —
  conservation (yield additivity, first sense).
* QY-C2 `yieldOf_eq_mul_tauOf (h : QYData k) (i : Fin n) : yieldOf k i = k i * tauOf k` —
  the common-lifetime law.
* QY-C3 `yieldOf_nonneg (h : QYData k) (i : Fin n) : 0 ≤ yieldOf k i`;
  `yieldOf_le_one (h : QYData k) (i : Fin n) : yieldOf k i ≤ 1`.
* QY-C4 `yieldOf_pos_iff (h : QYData k) (i : Fin n) : 0 < yieldOf k i ↔ 0 < k i`.
* QY-C5 `yieldOf_div_yieldOf (h : QYData k) {i j : Fin n} (hj : 0 < k j) :
  yieldOf k i / yieldOf k j = k i / k j` — relative yields measure rate ratios, independent of
  all other channels.
* QY-C6 `totalRate_cons {n} (c : ℝ) (k : Fin n → ℝ) :
  totalRate (Fin.cons c k) = c + totalRate k`;
  `yieldOf_cons_zero {n} (c : ℝ) (k : Fin n → ℝ) :
  yieldOf (Fin.cons c k) 0 = c / (c + totalRate k)`;
  `yieldOf_cons_succ (h : QYData k) (c : ℝ) (i : Fin n) :
  yieldOf (Fin.cons c k) i.succ = k i / (c + totalRate k)`;
  `yieldOf_cons_succ_factor (h : QYData k) (c : ℝ) (i : Fin n) :
  yieldOf (Fin.cons c k) i.succ = yieldOf k i * (totalRate k / (c + totalRate k))` — the
  dilution factor form (additivity, second sense).
* QY-C7 `yieldOf_cons_lt (h : QYData k) (hc : 0 < c) (hi : 0 < k i) :
  yieldOf (Fin.cons c k) i.succ < yieldOf k i` — a new channel strictly dilutes every live
  channel.
* QY-C8 `totalRate_zero_counterexample : ∃ k : Fin 2 → ℝ, (∀ i, 0 ≤ k i) ∧
  ¬ (0 < totalRate k) ∧ ∑ i, yieldOf k i ≠ 1` — the `total_pos` premise of QY-C1 is
  load-bearing (witness `k ≡ 0`: totalized `0/0 = 0`, the sum is `0`).
* QY-C9 `nonvacuous_all_channels_live : ∃ k : Fin 3 → ℝ, QYData k ∧ (∀ i, 0 < yieldOf k i) ∧
  ∑ i, yieldOf k i = 1` — witness `![1, 2, 3]` (yields `1/6, 1/3, 1/2`); the triple conjunct
  blocks the trivial-witness failure mode (the M1 lesson).

**QY-R (rational decision layer):**

* QY-R1 `Rat.totalRate`, `Rat.yieldOf`, `Rat.QYData` over `ℚ`; decidability of `Rat.QYData`
  (`decide`).
* QY-R2 cast coherence: `((Rat.totalRate kq : ℝ)) = totalRate (fun i => (kq i : ℝ))` and the
  same for `yieldOf` (API-calibrate: `map_sum`, `Rat.cast_div`, `Rat.cast_sum` variants).
* QY-R3 `Rat.yieldOf` verdict rows at the named instances (decide).

**QY-I (named instances):**

* QY-I1 `fluoresceinS1 : Fin 3 → ℚ := ![18, 1, 1]` (kF, kIC, kISC; φF = 9/10; representative of
  the literature yield ordering, LITERATURE) + verdict rows (`Rat.yieldOf · 0 = 9/10`,
  `decide`).
* QY-I2 `quinineLike : Fin 3 → ℚ := ![11, 5, 4]` (φF = 11/20) + verdict.
* QY-I3 `quenchDilution : Fin 4 → ℚ := Fin.cons 9 fluoresceinS1` + verdict: the added channel
  rescales φF to `18/29` and the Stern–Volmer ratio is `29/20` (the A2 edge rehearsal at ℚ).

## 5. Proof routes

QY-C1: `Finset.sum_div` + `div_self h.total_pos.ne'`. QY-C3 `≤ 1`: `div_le_one h.total_pos` +
`Finset.single_le_sum`. QY-C6: `Fin.sum_univ_cons`, `Fin.cons_zero`, `Fin.cons_succ`; then field
algebra. QY-C7: `mul_lt_mul_of_pos_left` with the factor `< 1` (`div_lt_one`). All rows are
`ring`/`field_simp`-closeable after the Finset manipulations; no `Real.exp`, no `Real.log`.

## 6. Sprint order, ownership, dispatch

Sprint QY0 (Phase 1) → QY1 `Basic` → QY2 `Criterion` → QY3 `RatModel` → QY4 `Instances`.
Owner: prover_c (after SternVolmer `Basic`/`Criterion`; the two theories share the field-algebra
proof style).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.QuantumYield.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.QuantumYield.Criterion
    proofs/scripts/axioms.sh PhotoLean.QuantumYield.Criterion PhotoLean.QuantumYield.sum_yieldOf_eq_one
    python3 theories/BEP/probes/bep-fidelity.py --theory QuantumYield

## 8. Risks and mitigations

* `Fin.cons` API drift (`Fin.sum_univ_cons`, `Fin.cons_succ` names): API-calibrate before the
  skeleton is frozen (iron rule 4); the fallback is an explicit `Fin.addCases` formulation.
* `yieldOf` under totalized division: every row consuming a yield either sits under `QYData` or
  states its own positivity premise — checked row by row at skeleton time.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Parallel first-order channels; yields as time-integrated branching | QY-C1..C9 |
| 2 | `QYData` (nonnegative rates, positive total) on the physical rows | — |
| 3 | Named instances reproduce the literature's yield ordering, not fitted data | their verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **Kasha — certificate candidate (machine target)**: `Kasha.radBranch rad ic n` *is* the
  two-channel yield of the pair `(rad n, ic n)`; one row pins it (`yieldOf` at `![rad n, ic n]`
  — the `Fin 2` cast coherence does the work).
* **SternVolmer — composition (machine target)**: `svRatioDyn` at `q` equals the yield ratio
  `yieldOf k 0 (with channel) / yieldOf k 0 (without)` inverted; the QY-C6 dilution factor *is*
  the SV ratio's inverse.
* **FluorPhos — composition (machine target)**: `FluorPhos.phiF` is the `Fin 3` yield at index 0;
  `phiP` is the two-step cascade product (the QY yields compose along the cascade).
* **Einstein — composition (machine target)**: the radiative channel rate is the Einstein `A`
  coefficient (`yield_radiative` row on the Einstein side).
* **Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / KashaVavilov /
  EnergyGapLaw / StokesShift / ICvsISC / Forster**: no direct edge (the QY layer carries no
  energy surface / cascade / geometry) — absence drafts registered; the Forster contact runs
  through the added-channel row (registered on the Forster side).

## 11. Position in the repository

Third theory of the batch; self-contained (`Mathlib` only); the algebraic spine of group A.
