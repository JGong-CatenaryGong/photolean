# mathlib API calibration log

> *English translation of `proofs/API-NOTES.md`. The Chinese original at `proofs/API-NOTES.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

Rules:

- When a prover meets an uncertain lemma name it **must not guess**; it hands the question to `api_researcher`.
- Every record has the format `## <date> — <topic> — <calibrator> — <conclusion>` (with the `#check` output, source location or link attached).
- `#check` probes live in `proofs/probes/` and are run with `proofs/scripts/lake env lean proofs/probes/<name>.lean`;
  probe files may be committed (they are documentation too).
- Calibration covers only the "name/signature" layer; statement/proof changes are made by the corresponding prover and leave a trace here.
- **mathlib version: v4.17.0** (rev in `lakefile.toml`). Name drift is judged against this baseline.

**Probe inventory for this round (2026-09-20, Marcus inverted region) — all 0 error / 0 warning:**

| Probe | Coverage | Run |
|---|---|---|
| `proofs/probes/marcus-exp-api.lean` | Group A (exp layer) + Group D (multiplication/order) | `proofs/scripts/lake env lean proofs/probes/marcus-exp-api.lean` |
| `proofs/probes/marcus-order-api.lean` | Group B (division/order) + Group C (squares/powers) + Group E (monotonicity wrappers) | the same command with the file name swapped |
| `proofs/probes/marcus-tactic-api.lean` | Group F (ℚ/cast) + Group G (tactic usability, measured) | as above |
| `proofs/probes/marcus-ident-rat-api.lean` | identifier ban list + reliable domain of `decide` on ℚ + independent re-check of the lead's risk probes | as above |
| `proofs/probes/marcus-proof-skeletons.lean` | **proof bodies of all M1–M5a theorems** (36 theorems, free of unfinished proofs) | as above |
| `proofs/probes/marcus-api-closeout.lean` | **closeout appendix re-check**: the `≤`-versions of the lemmas / the `rate_ratio` chain / the `decide` domain / three corrections to plan §8.2 | as above |
| `proofs/probes/marcus-api-cast-normnum.lean` | **closeout appendix re-check (batch 2)**: the `Rat.cast_*` family / `norm_num` boundaries / reciprocals and cross-multiplication / `field_simp` failure paths | as above |

> `proofs/probes/marcus-statement-skeleton.lean` is the **statement authority** (owned by the lead, containing placeholder proofs);
> `marcus-proof-skeletons.lean` is its **compilable completed version**, with signatures matching literally verbatim and only the proof bodies filled in.

---

## Ban list (nonexistent / drifted / signature mismatch)

**A. Nonexistent (`unknown constant` / `unknown identifier`) — forbidden in proofs:**

| Banned name | Measured error | Replacement |
|---|---|---|
| `Real.exp_lt_exp_iff` | `unknown constant` | **`Real.exp_lt_exp`** (it is itself an `↔`!) |
| `Real.exp_le_exp_iff` | `unknown constant` | **`Real.exp_le_exp`** (itself an `↔`) |
| `sq_lt_sq_iff` | `unknown identifier` | `sq_lt_sq₀` / `sq_lt_sq` / bare `nlinarith` |
| `strictMonoOn_iff` | `unknown identifier` | `Set.strictMonoOn_iff_strictMono` (different meaning, see Group E); or just write `intro a ha b hb hab` |
| `Rat.cast_pos_iff` | `unknown constant` | **`Rat.cast_pos`** (itself an `↔`) |
| `Rat.cast_lt_cast` | `unknown constant` | `Rat.cast_lt` |
| `div_lt_div_iff_of_neg_right` | `unknown identifier` | `div_lt_div_right_of_neg` (**iff, right-hand side is `b < a`**) |
| `div_lt_div_of_neg_right` | `unknown identifier` | `div_lt_div_right_of_neg`; or `div_lt_iff_of_neg` / `lt_div_iff_of_neg`; or the `div_neg` route of L5 |
| `div_lt_div_iff_of_neg_left` / `div_lt_div_of_neg_left` | `unknown identifier` | as above; or `div_lt_iff_of_neg` / `lt_div_iff_of_neg`; or the `div_neg` route of L5 |
| `strictAntiOn_inv` / `strictMonoOn_inv` | `unknown identifier` | do not exist; write `intro` yourself plus order lemmas |
| `div_neg_neg` | `unknown identifier` | `neg_div_neg_eq` |
| `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` | `invalid field notation` | dot notation is unavailable; write `intro a ha b hb hab` by hand |
| `Real.mul_pos` | `@[deprecated mul_pos (since := "2024-08-15")]` | `mul_pos` |

**B. Drifted (old name → new name; the old name still compiles but warns; new code uses the new name):**

| Old name (deprecated) | New name | since | Source |
|---|---|---|---|
| `div_lt_iff` | **`div_lt_iff₀`** | 2024-10-02 | `Mathlib/Algebra/Order/Field/Basic.lean:37` |
| `lt_div_iff` | **`lt_div_iff₀`** | 2024-10-02 | `Mathlib/Algebra/Order/Field/Basic.lean:31` |
| `div_lt_div_right` | **`div_lt_div_iff_of_pos_right`** | 2024-11-12 | `Mathlib/Algebra/Order/Field/Basic.lean:172` |
| `div_lt_div_left` | **`div_lt_div_iff_of_pos_left`** | 2024-11-13 | same as above |
| `pow_lt_pow_left` | **`pow_lt_pow_left₀`** | 2024-11-13 | `Mathlib/Algebra/Order/Ring/Basic.lean:99` |
| `pow_left_strictMonoOn` | **`pow_left_strictMonoOn₀`** | 2024-11-13 | same as above |
| `lt_of_mul_self_lt_mul_self` | **`lt_of_mul_self_lt_mul_self₀`** | 2024-11-12 | `Mathlib/Algebra/Order/Ring/Basic.lean:194` |
| `Real.mul_pos` | **`mul_pos`** | 2024-08-15 | `Mathlib/Data/Real/Basic.lean:344` |

**C. Identifier ban list (measured, 2026-09-20):**

Lean 4 **reserved tokens cannot be used as identifiers**; the error is uniformly `error: unexpected token '<tok>'; expected '_' or identifier`.
The 20 found **forbidden** by measurement:

```
λ  Π  Σ  ↓  ←  →  ↔  ∀  ∃  ∧  ∨  ¬  ≠  ≤  ≥  ∑  ∏  ∫  ∈  ⊆
```

The 30 found **legal** by measurement (usable as binder names, `example (ε : ℝ) : ε = ε := rfl` passes):

```
Λ  α  β  γ  Γ  δ  Δ  ε  ζ  η  θ  Θ  ι  κ  μ  ν  ξ  Ξ  π  ρ  σ  τ  υ  φ  Φ  χ  ψ  ω  Ω
```

- **`λ` absolutely must not be used** (`(λ x : ℝ)` → `unexpected token 'λ'`); `Λ` (capital) is legal.
- Lowercase `π` / `σ` are legal, but uppercase `Π` / `Σ` (dependent product/sum notation) are forbidden.
- `ε` / `δ` / `Δ` / `μ` **are legal** — a prover may use them as physical-quantity names if it wishes;
  but this project standardizes on ASCII (`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`).

---

## Calibration backlog

### Group A — exp layer (M3 critical path)

- [x] `Real.exp_lt_exp` — **exists**, and is an **`↔`** (not a `→`): `Real.exp x < Real.exp y ↔ x < y`. Use as `.mpr h` / `.mp h` / `rw [Real.exp_lt_exp]`
- [x] `Real.exp_le_exp` — **exists**, likewise an `↔`: `Real.exp x ≤ Real.exp y ↔ x ≤ y`
- [x] `Real.exp_le_exp_of_le` — exists, the `→` version: `(h : x ≤ y) : exp x ≤ exp y` (filed in the closeout appendix)
- [x] `Real.exp_le_exp_iff` — **does not exist** (`Real.exp_le_exp` is already an iff; closeout appendix re-check)
- [x] `Real.exp_lt_exp_iff` — **does not exist** (`Real.exp_lt_exp` is already an iff)
- [x] `Real.exp_pos` — exists, `(x : ℝ) : 0 < Real.exp x`
- [x] `Real.exp_nonneg` — exists, `(x : ℝ) : 0 ≤ Real.exp x`
- [x] `Real.exp_neg` — exists, `exp (-x) = (exp x)⁻¹`
- [x] `Real.exp_sub` — exists, `exp (x - y) = exp x / exp y`
- [x] `Real.exp_add` — exists, `exp (x + y) = exp x * exp y`
- [x] `Real.exp_zero` — exists, `exp 0 = 1`
- [x] `Real.exp_strictMono` — exists, `StrictMono Real.exp`
- [x] `Real.exp_monotone` — exists, `Monotone Real.exp`

### Group B — division/order (M3 critical path)

- [x] `div_lt_div_of_pos_right` — exists, `(h : a < b) (hc : 0 < c) : a / c < b / c`
- [x] `div_lt_div_iff_of_pos_right` — exists, **iff**, `(hc : 0 < c) : a / c < b / c ↔ a < b`
- [x] `div_lt_iff` — **drifted** → `div_lt_iff₀`
- [x] `lt_div_iff` — **drifted** → `lt_div_iff₀`
- [x] `div_pos` — exists, `(ha : 0 < a) (hb : 0 < b) : 0 < a / b`
- [x] `one_div_pos` — exists, **iff**: `0 < 1 / a ↔ 0 < a` (`inv_pos` has the same shape)
- [x] `neg_lt_neg_iff` — exists, **iff**: `-a < -b ↔ b < a` (note the right-hand side is `b < a`)
- [x] `neg_div` — exists, **argument order counterintuitive**: `(a b : R) : -b / a = -(b / a)`
- [x] `div_neg` — exists, `{b} (a : R) : a / -b = -(a / b)`
- [x] `div_nonneg` — exists, `(ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b`
- [x] `div_eq_mul_inv` — exists, `a / b = a * b⁻¹`
- [x] `mul_div_assoc` — exists, `a * b / c = a * (b / c)`
- [x] `div_lt_div_iff_of_neg_right` — **does not exist** → use `div_lt_div_right_of_neg` (rationale in record B-4)
- [x] `div_lt_div_of_neg_right` — **does not exist** (closeout appendix re-check; see record B-5)
- [x] `div_lt_div_right_of_neg` — exists, **iff**: `(hc : c < 0) : a / c < b / c ↔ b < a` (right-hand side order reversed)
- [x] `div_lt_iff_of_neg` / `lt_div_iff_of_neg` — exist (the iffs for a negative denominator)
- [x] `div_le_div_of_nonneg_right` — exists, `(hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c` (the `≤` version, used for the M3 peak)
- [x] `one_div_le_one_div_of_le` — exists, **taking reciprocals flips the direction**: `(ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a` (added in closeout batch 2, see record D-3)
- [x] `div_lt_div_iff₀` — exists, **both arguments are denominator positivity**: `(hb : 0 < b) (hd : 0 < d) : a/b < c/d ↔ a*d < c*b` (see record D-4)
- [x] `div_lt_iff₀` — exists, `(hc : 0 < c) : b / c < a ↔ b < a * c` (see record D-4)

### Group C — monotonicity of squares/powers

- [x] `sq_lt_sq` — exists, it is the **absolute-value** version `a^2 < b^2 ↔ |a| < |b|`
- [x] `sq_lt_sq_iff` — **does not exist**
- [x] `sq_le_sq` — exists, `a^2 ≤ b^2 ↔ |a| ≤ |b|`
- [x] `sq_lt_sq₀` — **exists, the least-effort lemma for `0 ≤ a < b ⇒ a^2 < b^2`**: `(ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b`
- [x] `sq_le_sq₀` — exists, `(ha) (hb) : a^2 ≤ b^2 ↔ a ≤ b`
- [x] `sq_pos_of_ne_zero` — exists, **`a` is an implicit argument**: `{a : R} : a ≠ 0 → 0 < a ^ 2`
- [x] `sq_nonneg` — exists, `(a : α) : 0 ≤ a ^ 2`
- [x] `sq_eq_zero_iff` — exists, `a^2 = 0 ↔ a = 0`
- [x] `pow_lt_pow_left₀` — exists, `(hab : a < b) (ha : 0 ≤ a) {n : ℕ} : n ≠ 0 → a^n < b^n`
- [x] `pow_lt_pow_left` — **drifted** → `pow_lt_pow_left₀`
- [x] `mul_self_lt_mul_self` — exists, `(ha : 0 ≤ a) (hab : a < b) : a * a < b * b` (the conclusion uses `*` not `^`, so `simpa only [pow_two]` is needed)
- [x] `sq_lt_sq'` — exists, `(h1 : -b < a) (h2 : a < b) : a^2 < b^2`

### Group D — multiplication/order

- [x] `mul_lt_mul_of_pos_left` — exists, `(bc : b < c) (a0 : 0 < a) : a * b < a * c`
- [x] `mul_lt_mul_of_pos_right` — exists, `(bc : b < c) (a0 : 0 < a) : b * a < c * a`
- [x] `mul_pos` — exists
- [x] `mul_nonneg` — exists
- [x] `mul_lt_mul₀` — exists, `(hab : a < b) (hcd : c < d) : a * c < b * d`
- [x] `pos_of_mul_pos_left` / `pos_of_mul_pos_right` — exist (they extract the left/right factor, **extremely easy to swap**, see record D-2)
- [x] `mul_lt_mul_of_neg_left` — exists, signature `(h : b < a) (hc : c < 0) : c * a < c * b`
- [x] `mul_le_mul_of_nonneg_left` — exists, `(h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c` (the `≤` version, used for the M3 peak)
- [x] `mul_div_mul_left` — exists, `(a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b` (used by the M3 `rate_ratio`)
- [x] `mul_neg_of_neg_of_pos` — exists, `(ha : a < 0) (hb : 0 < b) : a * b < 0` (the M4a backup verifier uses it to prove `rate (-1) (-1) 1 1 x < 0`)

### Group E — monotonicity wrappers

- [x] `StrictMonoOn` / `StrictAntiOn` / `MonotoneOn` — exist (`Mathlib/Order/Monotone/Defs.lean:83`)
- [x] `StrictMonoOn.lt_iff_lt` / `StrictAntiOn.lt_iff_lt` — exist, **iff versions, practical**
- [x] `strictMonoOn_iff` — **does not exist** (the real name is `Set.strictMonoOn_iff_strictMono`, whose meaning is "StrictMono on the subtype", useless for monotonicity on `Ici`/`Iic`)
- [x] `strictMonoOn_mul_self` — exists, `StrictMonoOn (fun x => x * x) {x | 0 ≤ x}`
- [x] `pow_left_strictMonoOn₀` — exists, `(hn : n ≠ 0) : StrictMonoOn (· ^ n) {a | 0 ≤ a}`
- [x] `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` — **unusable** (dot notation errors)

### Group F — ℚ layer and transfer

- [x] `Rat.cast_lt` — exists, **iff**, `↑p < ↑q ↔ p < q`
- [x] `Rat.cast_le` — exists, **iff**
- [x] `Rat.cast_pos` — exists, **iff**, `0 < ↑q ↔ 0 < q`
- [x] `Rat.cast_pos_iff` — **does not exist**
- [x] `Rat.cast_mk` — exists, `(a b : ℤ) : ↑(Rat.divInt a b) = ↑a / ↑b` (note the `Rat.divInt` form)
- [x] `Rat.cast_inj` / `Rat.cast_div` / `Rat.cast_one` / `Rat.cast_ofNat` — exist
- [x] `Rat.cast_pow` / `Rat.cast_mul` / `Rat.cast_sub` / `Rat.cast_add` / `Rat.cast_inv` / `Rat.cast_natCast` / `Rat.cast_zero` — exist (closeout batch 2, see record F-4)
- [x] `Rat.cast_ofNat` requires the `[n.AtLeastTwo]` instance — signature verified (same as above)
- [x] `Rat.cast_inj`'s `α` is implicit → under `apply` it gets stuck on `CharZero ?m`, so one must write `(Rat.cast_inj (α := ℝ))` (same as above)
- [x] `example : (1:ℚ) < 3 := by decide` — **passes** (measured as-is)
- [x] `by decide` on a ℚ literal containing division — **fails**, `norm_num [zoneQ]` is required (see record F-2)

### Group G — tactic usability

- [x] `nlinarith` — usable (the project's **workhorse**; after clearing denominators it proves square monotonicity bare)
- [x] `positivity` — usable (including `p * q`, `x^2 / (4*lam)`, `1 / exp x`)
- [x] `norm_num` — usable (decimal literals `0.5` / `1.2`, ℚ→ℝ mixtures, `norm_num [zoneQ]`)
  - ⚠️ **reliable-domain boundary** (closeout batch 2): `norm_num` **does not know about the positivity/monotonicity of `Real.exp`**.
    See the "three reliable-domain tables" below.
- [x] `field_simp` — **conditionally usable**: good when the goal is an **equality plus explicit nonzero hypotheses**; applied directly to an inequality it reports `simp made no progress`
- [x] `push_cast` — usable, but **carries no closing step** (it leaves `X = X`, so `ring`/`rfl` must be added)
- [x] `ring_nf` — usable (the symmetry `barrier lam x = barrier lam (2*lam-x)`, **no `lam ≠ 0` needed**)
- [x] `gcongr` — **conditionally usable**: works in linear/monotone positions; applied directly to `(lam-x₁)^2 < (lam-x₂)^2` (negative base) it **fails**
- [x] `linarith` — usable
- [x] `split_ifs` / `rw [if_pos/if_neg]` — usable (M1 zone layer)
- [x] `set_option linter.unusedVariables false in` **cannot directly follow a doc comment** (syntax pitfall, see record G-4)

### The three "reliable domain" tables (what the tools can / cannot do)

| Tool | Reliable domain | **Unreliable domain** | Way out |
|---|---|---|---|
| `decide` | **integer / division-free** ℚ literals (including negative integers) | ℚ literals containing division or decimals (gets stuck at `Rat.instDecidableLt` → `Int.decNonneg`) | `norm_num [zoneQ]` |
| `norm_num` | arithmetic reduction of polynomials/literals; `norm_num [barrier]` computes barrier values | **positivity/monotonicity of `Real.exp`** (leaves `⊢ False` unsolved) | `linarith [Real.exp_pos c]` |
| `field_simp` | **equalities** (+ explicit nonzero hypotheses) | **inequalities** (`simp made no progress`) | cross-multiply with `div_lt_div_iff₀` → `nlinarith` |
| `push_cast` | pushes casts through operations one at a time | **carries no closing step** (leaves `X = X`) | add `ring` (the `rw` chain is the opposite, see F-4) |

---

## Calibration records

<!-- Format: ## <date> — <topic> — api_researcher — <conclusion> -->

## 2026-09-20 — Group A: exp layer (M3 critical path) — api_researcher — all exist; key point: `Real.exp_lt_exp` is itself an iff

**Probe**: `proofs/probes/marcus-exp-api.lean` (0 error / 0 warning)

`#check` raw output (pasted in full):

```
Real.exp_lt_exp {x y : ℝ} : Real.exp x < Real.exp y ↔ x < y
Real.exp_le_exp {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y
Real.exp_pos (x : ℝ) : 0 < Real.exp x
Real.exp_nonneg (x : ℝ) : 0 ≤ Real.exp x
Real.exp_neg (x : ℝ) : Real.exp (-x) = (Real.exp x)⁻¹
Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
Real.exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y
Real.exp_zero : Real.exp 0 = 1
Real.exp_strictMono : StrictMono Real.exp
Real.exp_monotone : Monotone Real.exp
```

**Conclusion (the pivot of the M3 core lemmas — write it exactly this way)**:

- The direction of `Real.exp_lt_exp` is **`↔`**: `Real.exp x < Real.exp y ↔ x < y`.
  Starting from `h : a < b` to obtain `Real.exp a < Real.exp b`, use **`.mpr h`** (or `Real.exp_lt_exp.2 h`);
  the reverse direction uses `.mp`. **`Real.exp_lt_exp_iff` does not exist** — do not write that name.
- Equivalent phrasing: `Real.exp_strictMono h` (the `StrictMono` version) also passes.
- `Real.exp_le_exp` is likewise an `↔` (the non-strict version); `Real.exp_le_exp_of_le (h : x ≤ y) : exp x ≤ exp y` is the `→` version.

Source locations: all `Real.exp_*` live in `Mathlib/Data/Complex/Exponential.lean` (namespace `Real`):
`exp_zero:85`, `exp_add:98`, `exp_pos:268`, `exp_nonneg:274`, `exp_strictMono:284`,
`exp_lt_exp_of_lt:290`, `exp_monotone:293`, `exp_le_exp:304`, `exp_neg:148`, `exp_sub:151`, `exp_lt_exp:300`.

**Shortest skeleton already measured for M3 (`rate_gt_of_barrier_lt`, 2 tactic lines)**:

```lean
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA
```

The chain: negate (`by linarith`) → divide by a positive number (`div_lt_div_of_pos_right`) → strict monotonicity of exp
(`Real.exp_lt_exp.2`) → multiply by a positive number (`mul_lt_mul_of_pos_left`).
For a readable step-by-step version (the same proof expanded) see `L4_stepwise` in `marcus-exp-api.lean`.

## 2026-09-20 — Group B: division/order (M3 critical path) — api_researcher — all exist (2 drifted)

**Probe**: `proofs/probes/marcus-order-api.lean` (0 error / 0 warning)

`#check` raw output:

```
div_lt_div_iff_of_pos_right {G₀} [GroupWithZero G₀] [LinearOrder G₀] [ZeroLEOneClass G₀] {a b c : G₀}
  [PosMulStrictMono G₀] [MulPosStrictMono G₀] (hc : 0 < c) : a / c < b / c ↔ a < b
div_lt_div_of_pos_right {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] {a b c : G₀} [MulPosStrictMono G₀] (h : a < b) (hc : 0 < c) : a / c < b / c
div_pos {G₀} ... (ha : 0 < a) (hb : 0 < b) : 0 < a / b
div_nonneg {G₀} ... (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b
one_div_pos {G₀} ... {a : G₀} : 0 < 1 / a ↔ 0 < a
div_eq_mul_inv {G} [DivInvMonoid G] (a b : G) : a / b = a * b⁻¹
mul_div_assoc {G} [DivInvMonoid G] (a b c : G) : a * b / c = a * (b / c)
neg_div {R} [DivisionMonoid R] [HasDistribNeg R] (a b : R) : -b / a = -(b / a)
div_neg {R} [DivisionMonoid R] [HasDistribNeg R] {b : R} (a : R) : a / -b = -(a / b)
neg_lt_neg_iff {α} [AddGroup α] [LT α] [AddLeftStrictMono α] {a b : α} [AddRightStrictMono α] : -a < -b ↔ b < a
div_lt_iff_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : b / c < a ↔ b < a * c
lt_div_iff_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : a < b / c ↔ b < a * c
div_lt_div_right_of_neg {α} [LinearOrderedField α] {a b c : α} (hc : c < 0) : a / c < b / c ↔ b < a
div_lt_iff₀ {G₀} ... (hc : 0 < c) : b / c < a ↔ b < a * c
lt_div_iff₀ {G₀} ... (hc : 0 < c) : a < b / c ↔ a * c < b
div_lt_div_iff₀ {G₀} [CommGroupWithZero G₀] ... (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b
```

**B-1 (drift)**: `div_lt_iff` → **`div_lt_iff₀`**, `lt_div_iff` → **`lt_div_iff₀`**
(`@[deprecated … (since := "2024-10-02")]`, `Mathlib/Algebra/Order/Field/Basic.lean:31,37`).
The old names still compile but produce a deprecation warning (it does not affect acceptance, but new code should use the new names).

**B-2 (easily confused homonyms)**: `div_lt_div_iff₀` (**two denominators**, `a/b < c/d ↔ a*d < c*b`)
and `div_lt_div_iff_of_pos_right` (**the same denominator**) are **two different lemmas**. The barrier's
`(…)/(4*lam) < (…)/(4*lam)` is the latter.

**B-3 (argument-order pitfall)**: `neg_div (a b : R) : -b / a = -(b / a)` — the left-hand side of the conclusion is `-b / a`,
**not** `-(a / b)`. To prove `-(x) / y = -(x / y)` use `neg_div y x`. `div_neg {b} (a) : a / -b = -(a / b)` behaves normally.

**B-4 (negative denominator, a pitfall reported by the lead — independently re-checked)**:
- `div_lt_div_iff_of_neg_right` / `div_lt_div_of_neg_right` **do not exist** (`unknown identifier`).
- The right tool: `div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)`
  (`Mathlib/Algebra/Order/Field/Basic.lean:585`) — **it is an iff, and the right-hand side has direction `b < a` (counterintuitive)**.
- The other route for `lam < 0` (the one actually adopted and already verified in this project): rewrite `4*lam` as `-(4*(-lam))`,
  use `div_neg` + `neg_lt_neg_iff` to turn it into a positive denominator, then `div_lt_div_iff_of_pos_right`.
  For the full skeleton see "monotonicity of the two barrier branches" below.

## 2026-09-20 — Group C: monotonicity of squares/powers — api_researcher — the least-effort route to `0 ≤ a < b ⇒ a² < b²` is `sq_lt_sq₀` (or bare nlinarith)

**Probe**: `proofs/probes/marcus-order-api.lean` (0 error / 0 warning)

`#check` raw output:

```
sq_lt_sq₀ {M₀} [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀]
  [MulPosStrictMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b
sq_le_sq₀ {M₀} ... (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b
sq_lt_sq {α} [LinearOrderedRing α] {a b : α} : a ^ 2 < b ^ 2 ↔ |a| < |b|
sq_le_sq {α} [LinearOrderedRing α] {a b : α} : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b|
sq_lt_sq' {α} [LinearOrderedRing α] {a b : α} (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2
sq_le_sq' {α} [LinearOrderedRing α] {a b : α} (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2
sq_pos_of_ne_zero {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R} : a ≠ 0 → 0 < a ^ 2
sq_nonneg {α} [Semiring α] [LinearOrder α] ... (a : α) : 0 ≤ a ^ 2
sq_eq_zero_iff {M₀} [MonoidWithZero M₀] {a : M₀} [NoZeroDivisors M₀] : a ^ 2 = 0 ↔ a = 0
mul_self_lt_mul_self {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {a b : M₀} [PosMulStrictMono M₀]
  [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) : a * a < b * b
mul_self_lt_mul_self_iff {α} [Semiring α] [LinearOrder α] [PosMulStrictMono α] [MulPosMono α] {a b : α}
  (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b
lt_of_mul_self_lt_mul_self₀ {M₀} ... (hb : 0 ≤ b) : a * a < b * b → a < b
pow_lt_pow_left₀ {M₀} ... (hab : a < b) (ha : 0 ≤ a) {n : ℕ} : n ≠ 0 → a ^ n < b ^ n
pow_left_strictMonoOn₀ {M₀} ... (hn : n ≠ 0) : StrictMonoOn (fun x => x ^ n) {a | 0 ≤ a}
```

**C-1 (answer to the question)**: to derive `a^2 < b^2` from `0 ≤ a < b`, the least effort is

```lean
(sq_lt_sq₀ ha (ha.trans hab.le)).2 hab   -- explicit, no |a| needed
-- or directly:
by nlinarith                              -- measured: bare nlinarith goes through, no hint needed
```

`sq_lt_sq₀` is at `Mathlib/Algebra/Order/GroupWithZero/Unbundled.lean:1322`;
`sq_pos_of_ne_zero` is an alias, at `Mathlib/Algebra/Order/Ring/Basic.lean:304`.
**Do not use** `sq_lt_sq` (that is the `|a| < |b|` version; it turns the goal into an absolute value and takes the long way round).
**`sq_lt_sq_iff` does not exist.**

**C-2 (implicit-argument pitfall, reported by the lead — independently re-checked)**: `a` in `sq_pos_of_ne_zero` is **implicit**:

```
@sq_pos_of_ne_zero : ∀ {R : Type u_1} [inst : LinearOrderedSemiring R] [inst_1 : ExistsAddOfLE R] {a : R},
  a ≠ 0 → 0 < a ^ 2
```

Correct: `sq_pos_of_ne_zero hdq`. Writing `sq_pos_of_ne_zero dq hdq` reports
`application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`.
⚠️ **`plan.md` §7.2 originally wrote it with two explicit arguments, which is wrong** — this entry is the official correction.

**C-3**: the conclusion of `mul_self_lt_mul_self` is `a * a < b * b` (`*`, not `^`); a direct `exact` against
`a^2 < b^2` gives a `type mismatch`; one needs `simpa only [pow_two] using mul_self_lt_mul_self ha hab`.

**C-4**: `pow_lt_pow_left` **has drifted** → `pow_lt_pow_left₀` (since 2024-11-13);
the argument order is `(hab : a < b) (ha : 0 ≤ a)` followed by `{n : ℕ}`, and `n ≠ 0` comes **last** (it is not a premise).

## 2026-09-20 — Group D: multiplication/order — api_researcher — all exist; `pos_of_mul_pos_left/right` are extremely easy to swap

**Probe**: `proofs/probes/marcus-exp-api.lean` (0 error / 0 warning)

`#check` raw output:

```
mul_lt_mul_of_pos_left {α} [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α] (bc : b < c)
  (a0 : 0 < a) : a * b < a * c
mul_lt_mul_of_pos_right {α} [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α] (bc : b < c)
  (a0 : 0 < a) : b * a < c * a
mul_pos {α} [MulZeroClass α] [Preorder α] [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b
mul_nonneg {α} [MulZeroClass α] [Preorder α] [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b
mul_lt_mul₀ {α} [LinearOrderedCommGroupWithZero α] {a b c d : α} (hab : a < b) (hcd : c < d) :
  a * c < b * d
pos_of_mul_pos_left {α} [MulZeroClass α] [Preorder α] [MulPosReflectLT α] (h : 0 < a * b)
  (hb : 0 ≤ b) : 0 < a
pos_of_mul_pos_right {α} [MulZeroClass α] [Preorder α] [PosMulReflectLT α] (h : 0 < a * b)
  (ha : 0 ≤ a) : 0 < b
mul_lt_mul_of_neg_left {α} [Semiring α] [PartialOrder α] {a b c : α} [ExistsAddOfLE α] [PosMulStrictMono α]
  [AddRightStrictMono α] [AddRightReflectLT α] (h : b < a) (hc : c < 0) : c * a < c * b
```

**D-1**: the **argument order of `mul_lt_mul_of_neg_left` is counterintuitive**: `(h : b < a) (hc : c < 0) : c * a < c * b`
(the first argument is the reversed-direction `b < a`). Measured:
`example {A u v : ℝ} (hA : A < 0) (h : u < v) : A * v < A * u := mul_lt_mul_of_neg_left h hA` passes.

**D-2 (a pitfall reported by the lead — independently re-checked)**: `rate A lam kB T x = A * Real.exp (…)`, with the positive factor
`A` on the **left** of the product and `exp` on the **right**. To get `0 < A` from `0 < A * Real.exp u`, one must use
**`pos_of_mul_pos_left`** (whose hypothesis is "the right factor is nonnegative"):

```lean
example {A u : ℝ} (h : 0 < A * Real.exp u) : 0 < A :=
  pos_of_mul_pos_left h (Real.exp_pos u).le
```

Using `pos_of_mul_pos_right` reports `application type mismatch` (its conclusion is `0 < b`, i.e. the right factor).
Both are at `Mathlib/Algebra/Order/GroupWithZero/Unbundled.lean:448,451`.

## 2026-09-20 — Group E: monotonicity wrappers — api_researcher — only `lt_iff_lt` and the two ready-made `StrictMonoOn` are practical

**Probe**: `proofs/probes/marcus-order-api.lean` (0 error / 0 warning)

`#check` raw output:

```
StrictMonoOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
StrictAntiOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
MonotoneOn.{u, v} {α} {β} [Preorder α] [Preorder β] (f : α → β) (s : Set α) : Prop
StrictMonoOn.lt_iff_lt {α} {β} [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
  (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b
StrictAntiOn.lt_iff_lt {α} {β} [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
  (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a
Set.strictMonoOn_iff_strictMono {s : Set α} [Preorder α] [Preorder β] {f : α → β} :
  StrictMonoOn f s ↔ StrictMono fun a => f ↑a
strictMonoOn_mul_self {M₀} [MonoidWithZero M₀] [PartialOrder M₀] [PosMulStrictMono M₀]
  [MulPosMono M₀] : StrictMonoOn (fun x => x * x) {x | 0 ≤ x}
pow_left_strictMonoOn₀ {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {n : ℕ} [ZeroLEOneClass M₀]
  [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hn : n ≠ 0) : StrictMonoOn (fun x => x ^ n) {a | 0 ≤ a}
```

**Conclusion**:

- The definition of `StrictMonoOn` is exactly `∀ ⦃a⦄, a ∈ s → ⦃b⦄, b ∈ s → a < b → f a < f b`
  (`Mathlib/Order/Monotone/Defs.lean:83`), so **writing `intro a ha b hb hab` directly is the least effort**;
  there is no need to hunt for a `*_iff` lemma. `strictMonoOn_iff` **does not exist**.
- To use the iff form and extract `f a < f b → a < b`, use **`StrictMonoOn.lt_iff_lt`**
  (`Mathlib/Order/Monotone/Basic.lean:377`) / `StrictAntiOn.lt_iff_lt`.
- The right-hand side of `Set.strictMonoOn_iff_strictMono` (`Mathlib/Data/Set/Basic.lean:1480`) is
  **`StrictMono` on the subtype**; it is **useless** for monotonicity on `Set.Ici`/`Set.Iic`, so do not pick it.
- `StrictMonoOn.const_mul` / `StrictMonoOn.div_const` **error under dot notation** in v4.17; composite monotonicity must be written by hand.
- **⚠️ `a ∈ Set.Ici lam` cannot be fed to `linarith` directly** — one must first `rw [Set.mem_Ici] at ha hb`
  to turn the hypotheses into `lam ≤ a`. Otherwise it reports `linarith failed to find a contradiction` (`a✝ : 0 > a - lam`).

The `StrictMonoOn` / `StrictAntiOn` packaged form of `barrier` (already measured):

```lean
theorem barrier_strictMonoOn_Ici {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Ici lam) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith

theorem barrier_strictAntiOn_Iic {lam : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (fun x => (lam - x) ^ 2 / (4 * lam)) (Set.Iic lam) := by
  intro a ha b hb hab
  rw [Set.mem_Iic] at ha hb
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

## 2026-09-20 — Group F: ℚ layer and ℚ→ℝ transfer — api_researcher — the cast lemmas are all iffs; `decide` is reliable only for integer literals

**Probe**: `proofs/probes/marcus-tactic-api.lean` + `proofs/probes/marcus-ident-rat-api.lean` (both 0 error)

`#check` raw output:

```
Rat.cast_lt {p q : ℚ} {K} [LinearOrderedField K] : ↑p < ↑q ↔ p < q
Rat.cast_le {p q : ℚ} {K} [LinearOrderedField K] : ↑p ≤ ↑q ↔ p ≤ q
Rat.cast_pos {q : ℚ} {K} [LinearOrderedField K] : 0 < ↑q ↔ 0 < q
Rat.cast_inj {p q : ℚ} {α} [DivisionRing α] [CharZero α] : ↑p = ↑q ↔ p = q
Rat.cast_div (p q : ℚ) : ↑(p / q) = ↑p / ↑q
Rat.cast_one : ↑(1 : ℚ) = 1
Rat.cast_mk (a b : ℤ) : ↑(Rat.divInt a b) = ↑a / ↑b
```

**F-1 (reported verbatim as the task required)**: `example : (1 : ℚ) < 3 := by decide` — **passes** (measured, 0 error).
`decide` works for integer comparisons on ℚ (`1 < 3`, `¬ (3 < 1)`, `1 ≤ 3`).
`Rat.cast_pos_iff` **does not exist** (`Rat.cast_pos` is itself an iff).

**F-2 (the M5 decision-layer standard, reported by the lead — independently re-checked)**:

- ✅ `zoneQ (1 : ℚ) 3 = Zone.inverted` / `zoneQ (1 : ℚ) 1 = Zone.barrierless` — **`by decide` passes**.
- ❌ `zoneQ (1 : ℚ) (3 / 4) = Zone.normal` — **`by decide` fails**, raw error:

```
tactic 'decide' failed for proposition
  zoneQ 1 (3 / 4) = Zone.normal
since its 'Decidable' instance
  instDecidableEqZone (zoneQ 1 (3 / 4)) Zone.normal
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqBool', 'instDecidableEqNat',
'instDecidableEqZone', 'Bool.decEq', 'Int.decLt', 'Nat.decEq',
'Rat.instDecidableLt' and 'Int.decNonneg✝', reduction got stuck at the
'Decidable' instance
  match h : (zoneQ 1 (3 / 4)).toCtorIdx.beq Zone.normal.toCtorIdx with
  | true => isTrue ⋯
  | false => isFalse ⋯
```

  (the blockage is in the `Rat.instDecidableLt` → `Int.decNonneg` path, not in `Eq`.)

- ✅ Countermeasure: `by norm_num [zoneQ]` (it goes through a proof term rather than kernel reduction). Measured passing:
  `zoneQ 1 (3/4) = normal`, `zoneQ 1 (6/8) = normal`, `zoneQ 1 (5/4) = inverted`, `zoneQ 1 (4/4) = barrierless`.

**Standard**: **integer arguments use `decide`; rational literals containing division/reduction use `norm_num [zoneQ]`.**

**F-3 (M5a syntax pitfall)**: inside `zoneQ_eq_zone` one **cannot** use `rw [Rat.cast_lt, Rat.cast_inj]`,
which reports `tactic 'rewrite' failed, motive is not type correct` (dependent `Decidable` instance).
One must use **`simp only [Rat.cast_lt, Rat.cast_inj]`**:

```lean
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ) := by
  unfold zoneQ zone
  simp only [Rat.cast_lt, Rat.cast_inj]
```

## 2026-09-20 — Group G: tactic usability, measured — api_researcher — all three goal shapes pass; `gcongr`/`field_simp` are conditional

**Probe**: `proofs/probes/marcus-tactic-api.lean` (0 error / 0 warning)

**G-1 (the shape specified by the task, 1)**: `positivity` closing step — **passes**, and the shortest form is one line:

```lean
example {lam x : ℝ} (hlam : 0 < lam) : 0 ≤ (lam - x)^2 / (4*lam) := by positivity
```

`positivity` can also give `(0:ℝ) < 4*lam` directly from `hlam : 0 < lam`, and `0 < kB*T` from `h : 0 < kB*T`.

**G-2 (the shape specified by the task, 2 — the most critical one) — shortest `positivity`/`nlinarith` proof (2 tactic lines)**:

```lean
example {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ} (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) :
    (lam-x₁)^2/(4*lam) < (lam-x₂)^2/(4*lam) := by
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

This is the **shortest measured** successful proof for this topic (clear the denominator + bare `nlinarith`, the latter not even needing a `sq_nonneg` hint).

For comparison (the lead's version in `marcus-statement-skeleton.lean` R4, 3 lines, also passes and is more robust):

```lean
  have hpos : (0 : ℝ) < 4 * lam := by positivity
  have hsq : (lam - x₁) ^ 2 < (lam - x₂) ^ 2 := by nlinarith
  exact div_lt_div_of_pos_right hsq hpos
```

**Failure paths (already measured; do not go down them again)**:

- A single bare `nlinarith` applied directly to the **original** goal (without clearing the denominator) → **fails** (`a✝ : (lam-x₁)^2 ≥ (lam-x₂)^2`, the sign of the denominator is never exploited).
- `gcongr` applied directly to `(lam-x₁)^2 < (lam-x₂)^2` → **fails**:
  gcongr follows the monotonicity of `sq`, producing the subgoal `0 ≤ lam - x₁`, which is ≤ 0 when `lam ≤ x₁`.
  Either rewrite the base into a nonnegative form `(x₁ - lam)^2` first, or switch to the `nlinarith` route.
- L5 (`lam < 0`) via `div_lt_iff_of_neg` and then `nlinarith` → **fails** (after the `rewrite` the RHS becomes
  `(lam-x₁)^2/(4*lam) * (4*lam)`, which nlinarith cannot handle). Take the `div_neg` route (see below).

**G-3 (the shape specified by the task, 3 — symmetry)**: `ring_nf` — **passes, and `hlam : lam ≠ 0` is unused by the proof (unused)**:

```lean
example (lam x : ℝ) :
    (lam - x)^2/(4*lam) = (lam - (2*lam - x))^2/(4*lam) := by ring_nf
```

Reason: Lean's division-by-zero convention `x / 0 = 0` makes both sides 0 when `lam = 0`. The version with `hlam` also passes
(it only produces an unused-variable warning).

**G-4 (syntax pitfall, reported by the lead — independently re-checked)**: `set_option linter.unusedVariables false in`
**cannot directly follow a doc comment**:

```lean
/-- doc comment -/
set_option linter.unusedVariables false in     -- ❌ error: unexpected token 'set_option'; expected 'lemma'
theorem bad (z : Zone) : z = z := rfl
```

The correct order is "**plain block comment → `set_option … in` → doc comment + theorem**":

```lean
-- plain comment first
set_option linter.unusedVariables false in
/-- doc comment -/
theorem good (z : Zone) : z = z := rfl      -- ✅
```

The least-effort alternative: put a single `set_option linter.unusedVariables false` without `in` at the top of the file.

**G-5**: all the other tactics are usable — `nlinarith`, `linarith`, `norm_num` (decimals `0.5` / `1.2`),
`ring_nf`, `positivity`. `field_simp` is only good for "**equalities** + explicit nonzero hypotheses";
applied directly to an inequality it reports `error: simp made no progress`.

**G-6 (a boundary of `nlinarith`, negative evidence for provers)**: bare `nlinarith` **fails** on the following **true proposition**:

```lean
-- ❌ error: linarith failed to find a contradiction / a✝ : 0 ≥ a^2 + b^2
example {a b : ℝ} (h : a < b) : a ^ 2 + b ^ 2 > 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h]
```

One must explicitly establish "at least one of them is nonzero" and feed that in (there is a compilable version in `marcus-tactic-api.lean` G-7).
**Conclusion: `nlinarith` is powerful but not omnipotent; when it gets stuck, add explicit `have`s rather than tuning hints over and over.**

**G-7 (lemmas available in the M1 zone layer, the batch delivered by prover_a — each re-checked with `#check`)**:
`if_pos`, `if_neg`, `iff_of_true`, `iff_of_false`, `le_of_not_gt`, `le_of_lt`, `ne_of_lt`,
`lt_of_le_of_ne`, `Ne.symm`, `lt_irrefl`, `not_lt` — **all exist**.
The constructors of `Zone` (`deriving DecidableEq`) are pairwise distinct and can be discharged directly by `by decide` (all 6 groups measured passing).

Recommended tactics (measured on M1): `by_cases h : x < lam` + `rw [if_pos h] / rw [if_neg h]` + `simp`.
`split_ifs <;> simp_all` gets through `zone_trichotomy`, but for the first three cases it leaves goals such as `¬x = lam` / `lam < x`
that simp cannot derive, so one must supply `ne_of_lt h` or
`lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h2)` by hand.

## 2026-09-20 — monotonicity of the two barrier branches and monotonicity of rate (critical M2/M3 goal shapes) — api_researcher — three shortest measured skeletons

**Probe**: `proofs/probes/marcus-proof-skeletons.lean` (35 theorems, 0 error / 0 warning / no unfinished proofs)

**(1) Right branch (`0 < lam`, lemma 2 / `barrier_mono_of_pos`) — 3 lines**:

```lean
theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

**(2) Left branch (`0 < lam`, lemma 3 / `barrier_antitone_of_pos`) — same shape, `nlinarith` handles the direction automatically**:

```lean
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
```

> **⚠️ The hypothesis `h₁ : 0 ≤ x₁` is "unused by the proof", not "derivable from the other hypotheses"**
> — **these two statements mean different things; do not conflate them** (finding A by the M2 verifier; this log once mis-wrote it as the latter and has been corrected).
>
> - **Correct**: the hypothesis is **not used by the proof**. The theorem still holds without it (the kernel check passes, see
>   `marcus-proof-skeletons.lean` and the `…_no_h1` version below), so it merely produces an
>   unused-variable warning. It is an **explicit physical hypothesis** (nonnegative driving force) and, per the iron rule
>   "make physical approximations explicit", it is **kept**. Use a file-level `set_option linter.unusedVariables false` or accept the warning
>   (**warnings do not affect acceptance**; only unfinished proofs / custom axioms FAIL).
> - **Wrong (never write it again)**: "`h₁` can be derived from `h₃ : x₂ ≤ lam` and `h₂ : x₁ < x₂`".
>   **Kernel counterexample**: `lam = 1, x₁ = -5, x₂ = -4` ⇒ `0 < 1 ✓`, `-5 < -4 ✓`, `-4 ≤ 1 ✓`,
>   but `0 ≤ -5 ✗`. The statement `¬ ∀ lam x₁ x₂, 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁` has been machine-checked.
>   ⚠️ Treating it as a "reusable inference rule" leads straight to a wrong proof — a typical mis-write; let it be a warning.

```lean
-- evidence that it is "unused by the proof": the theorem still passes without `h₁`
theorem barrier_antitone_of_pos_no_h1 {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]
  nlinarith
-- evidence that it is "not derivable" (kernel counterexample)
example : ¬ (∀ (lam x₁ x₂ : ℝ), 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁) := by
  intro h; have := h 1 (-5) (-4) (by norm_num) (by norm_num) (by norm_num); norm_num at this
```

**(3) `lam < 0` (lemma 5 / `barrier_antitone_of_neg`) — 4 lines; a negative denominator needs a detour**:

```lean
theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁ := by
  unfold barrier
  rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
  rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]
  nlinarith
```

Key point: **there is no `div_lt_div_iff_of_neg_right`**. One must rewrite `4*lam` as `-(4*(-lam))`,
then use `div_neg` (`a / -b = -(a / b)`) to pull the minus sign outside and `neg_lt_neg_iff` (`-a < -b ↔ b < a`)
to flip it into a positive denominator, and finally close with `div_lt_div_iff_of_pos_right`.
⚠️ **Do not chain this set of rewrites in one go after `unfold rate`** — `rate` carries a minus sign of its own, which combines with the one produced by `div_neg`
into a double negation, and then `neg_lt_neg_iff` no longer matches (measured failure). First `have` the barrier
inequality separately, then use `rate_gt_of_barrier_lt` to reach the rate layer.

**(4) Core lemma 4 (monotonicity of rate / `rate_gt_of_barrier_lt`) — 2 lines**:

```lean
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x := by
  unfold rate
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) hkT)) hA
```

The chain: `h : barrier x < barrier y` → `by linarith` negates to `-(barrier y) < -(barrier x)`
→ `div_lt_div_of_pos_right … hkT` divides by a positive number → `Real.exp_lt_exp.2` consumes the exp
→ `mul_lt_mul_of_pos_left … hA` multiplies by the positive number `A`.

**(5) The `lam = 0` branch needs no positivity hypothesis at all** (necessity of sharpness; the signature of `sharp_lam_pos_of_eq`
can dispense with `hkB` / `hT` / `hA` entirely): the division-by-zero convention makes `barrier 0 x = 0`, so the rate is constantly `A`:

```lean
theorem sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False := by
  have hrate : ∀ x : ℝ, rate A 0 kB T x = A := by
    intro x; unfold rate; rw [barrier_zero_lam]; simp
  have hd := hdesc 1 2 (by norm_num) (by norm_num)
  rw [hrate 2, hrate 1] at hd
  exact lt_irrefl A hd
```

**(6) Semantic point (found during calibration, it affects the M4a statements)**: `InvertedDescriptor` ("inside the inverted region
the rate strictly decreases with the driving force") **holds only when `lam > 0`**, and is **false when `lam < 0`**. The reason: when `lam < 0`,
`barrier` **decreases** with `x` (lemma 5), so the rate **increases** with `x`, the opposite of the descriptor's direction.
`inverted_descriptor_holds` in `marcus-statement-skeleton.lean` already carries `hlam : 0 < lam`, so its
direction is correct; `inverted_descriptor_holds_of_neg` is a **non-physical stretched goal** carrying `hA : A < 0`,
where the flip of `A < 0` makes the descriptor hold again — the hypotheses of the two theorems are **neither interchangeable nor removable**.
The machine-checked counterexample has been committed in `marcus-proof-skeletons.lean`:
`not_invertedDescriptor_of_neg_lam : ¬ InvertedDescriptor 1 (-1) 1 1` (take `lam = -1, A = kB = T = 1`;
from `h : rate 1 (-1) 1 1 1 < rate 1 (-1) 1 1 0` one reduces to `Real.exp 1 < Real.exp (1/4)`,
then `Real.exp_lt_exp.mp` gives the contradiction `1 < 1/4`).

## 2026-09-20 — Closeout appendix: the `≤`-version lemmas + the `rate_ratio` chain — api_researcher — all 6 new names exist, signatures filed

**Probe**: `proofs/probes/marcus-api-closeout.lean` (0 error / 0 warning)

What was re-checked: a batch of new names reported by the M2/M3/M4a/M5a deliverers in their respective `#check`s. **Each was re-run independently, not copied.**

`#check` raw output:

```
Real.exp_le_exp {x y : ℝ} : Real.exp x ≤ Real.exp y ↔ x ≤ y
Real.exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : Real.exp x ≤ Real.exp y
div_le_div_of_nonneg_right {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] {a b c : G₀} [MulPosMono G₀] (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
mul_le_mul_of_nonneg_left {α} [Mul α] [Zero α] [Preorder α] [PosMulMono α] (h : b ≤ c)
  (a0 : 0 ≤ a) : a * b ≤ a * c
mul_div_mul_left {G₀} [CommGroupWithZero G₀] {c : G₀} (a b : G₀) (hc : c ≠ 0) :
  c * a / (c * b) = a / b
Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y
pow_lt_pow_left₀ {M₀} [MonoidWithZero M₀] [PartialOrder M₀] {a b : M₀} [ZeroLEOneClass M₀]
  [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hab : a < b) (ha : 0 ≤ a) {n : ℕ} :
  n ≠ 0 → a ^ n < b ^ n
sq_lt_sq₀ {M₀} [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀]
  [MulPosStrictMono M₀] {a b : M₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b
```

**Confirmed correct (consistent with my re-check)**:

- `Real.exp_le_exp` **is an `↔`** (`Real.exp x ≤ Real.exp y ↔ x ≤ y`); `Real.exp_le_exp_iff` **does not exist** (re-check: `unknown constant`);
  `Real.exp_le_exp_of_le` is the `→` version.
- The **direction** of `Real.exp_sub` is indeed `exp (x - y) = exp x / exp y` ⇒ to turn "a quotient of exps" into "a difference of exps"
  one must use **`← Real.exp_sub`** (which is exactly how `rate_ratio` uses it).
- `pow_lt_pow_left₀`: `n ≠ 0` comes **last** (not in premise position).
- `sq_lt_sq₀`: the right answer for `0 ≤ a < b ⇒ a² < b²`; less effort than `mul_self_lt_mul_self` + `sq_lt_sq'`, and no `|·|` needed.
- `mul_le_mul_of_nonneg_left`: the actual binder names are `(h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c`
  (differing from the reported `(h : a ≤ b) (hc : 0 ≤ c)` only by binder renaming; the signatures are equivalent).

**Measured body of the M3 `rate_peak_at_lam` (the `≤`-version peak)** (three `≤` lemmas working together):

```lean
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam := by
  unfold rate
  apply mul_le_mul_of_nonneg_left _ hA.le        -- multiply by a nonnegative number
  rw [Real.exp_le_exp]                           -- consume exp (iff, forward direction)
  exact div_le_div_of_nonneg_right (by linarith [barrier_min_at_lam hlam x]) hkT.le
```

**Measured body of the M3 `rate_ratio`** (`mul_div_mul_left` + `← Real.exp_sub` are the two key steps):

```lean
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T)) := by
  unfold rate
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  field_simp
  ring
```

## 2026-09-20 — Closeout appendix: additions to the Group B ban list — api_researcher — `div_lt_div_of_neg_right` does not exist; `a` in `sq_pos_of_ne_zero` is implicit

**Probe**: `proofs/probes/marcus-api-closeout.lean` (0 error / 0 warning)

- `div_lt_div_of_neg_right` — **re-checked and confirmed nonexistent** (`unknown identifier`).
  The only tool available under a negative divisor is `div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a`
  — **an iff, and the right-hand side is `b < a` (order reversed)**; the direction reversal of the two M2 branches relies entirely on it.
- `@sq_pos_of_ne_zero : ∀ {R : Type u_1} [inst : LinearOrderedSemiring R] [inst_1 : ExistsAddOfLE R] {a : R},
  a ≠ 0 → 0 < a ^ 2` — **`a` is an implicit argument**; the correct form is `sq_pos_of_ne_zero hdq`;
  writing `sq_pos_of_ne_zero dq hdq` reports
  `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`.
  ⚠️ This entry also **corrects the old hint in `plan.md` §7.2** (the old hint wrote two explicit arguments; the lead has already fixed it).

## 2026-09-20 — Closeout appendix: Group C tool facts (`decide` domain / three corrections to plan §8.2) — api_researcher — 4 items re-checked, 1 characterized by measurement

**Probe**: `proofs/probes/marcus-api-closeout.lean` (0 error / 0 warning)

**C-1 the reliable domain of `by decide` on ℚ** (consistent with the re-check):

- ✅ **integer / division-free literals** (including **negative integers**) compute: `zoneQ 1 3`, `zoneQ 1 (-3)`, `zoneQ 1 1`, `zoneQ 1 0` all pass `by decide`.
- ❌ anything **containing division or decimals** gets stuck at `Rat.instDecidableLt` → `Int.decNonneg`, reporting
  `'Decidable' instance … did not reduce to 'isTrue' or 'isFalse'` (both `0.5` and `3/4` reproduce it).
- ⇒ **Standard**: integer arguments use `decide`; those containing division/decimals use `norm_num [zoneQ]`.

**C-2 corrections to three old examples in `plan.md` §8.2** (I built a minimal reproduction for each of the three and **measured each one**):

1. **The direction of `rw [← zoneQ_eq_zone]` is case-dependent; it is not that one side is wrong** (characterized here from my measurements, which is more accurate than "the direction is reversed"):
   the rewrite pattern of `←` is `zone ↑?lam ↑?x`, and the forward pattern is `zoneQ ?lam ?x`.
   - If the goal is `zoneQ lam x = …` ⇒ one must use the **forward** `rw [zoneQ_eq_zone]` (the case of §8.2; the old example used `←`, hence the error);
   - if the goal is `zone ↑lam ↑x = …` ⇒ `rw [← zoneQ_eq_zone]` is the correct one.
   I measured both directions passing; **the choice depends on which side occurs in the goal**.
2. **cast literals ≠ `OfNat` literals** (not equal at the definitional level) ✅ consistent with the re-check:
   `exact h` (with `h : ↑1 < ↑3`) against the goal `InvertedRegion (1 : ℝ) 3` reports
   `type mismatch: h has type ↑1 < ↑3 but is expected to have type InvertedRegion 1 3`.
   Two ways out: write `((1:ℚ):ℝ)` explicitly, or use `norm_num [InvertedRegion]`.
3. **`rw` does not go through defeq** ✅ consistent with the re-check: `rw [← zoneQ_inverted_iff]` does not unfold `def InvertedRegion`, and reports
   `tactic 'rewrite' failed, did not find instance of the pattern ↑?lam < ↑?x`.
   Ways out: `exact (zoneQ_inverted_iff lam x).mp h` (which does go through defeq), or first `show (lam:ℝ) < (x:ℝ)`.

**C-3** The constructors of `Zone` (`deriving DecidableEq`) are pairwise distinct and can be discharged directly by `by decide` — all 6 groups measured passing.

## 2026-09-20 — ⚠️ Correction: "an unused hypothesis" ≠ "a derivable hypothesis" (finding A by the M2 verifier) — api_researcher

**This log previously mis-wrote (M2 passage)**: "the `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos` can be derived from
`h₃ : x₂ ≤ lam` and `h₂ : x₁ < x₂`". **That is a false proposition; it has been fixed.**

- **Correct statement**: `h₁` is a hypothesis **unused by the proof** — the theorem still holds without it
  (`barrier_antitone_of_pos_no_h1` passes the kernel), so it only produces an unused-variable warning.
- **Kernel counterexample** (given by the verifier, and I reproduced it independently): `lam = 1, x₁ = -5, x₂ = -4` ⇒
  `0 < 1 ✓`, `-5 < -4 ✓`, `-4 ≤ 1 ✓`, but `0 ≤ -5 ✗`.
  `¬ ∀ lam x₁ x₂, 0 < lam → x₁ < x₂ → x₂ ≤ lam → 0 ≤ x₁` has been machine-checked.
- **Why the distinction matters**: calling "unused" "derivable" leads later readers to treat it as a **reusable inference rule**
  and to write an incorrect proof. The same wording in G-3 ("`hlam : lam ≠ 0` is redundant") has accordingly been
  changed to "**unused by the proof (unused)**".
- The hypothesis is **kept** as an **explicit physical hypothesis** (nonnegative driving force); being unused is no reason to delete it.

## 2026-09-20 — Closeout appendix batch 2: the Group F `Rat.cast_*` family (M5a `barrierQ_cast`) — api_researcher — all 10 names exist; two pitfalls of "opposite tail rules"

**Probe**: `proofs/probes/marcus-api-cast-normnum.lean` (0 error / 0 warning)

`#check` raw output (`@` form, to expose the implicit arguments):

```
@Rat.cast_pow {α} [DivisionRing α] (p : ℚ) (n : ℕ) : ↑(p ^ n) = ↑p ^ n
@Rat.cast_mul {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p * q) = ↑p * ↑q
@Rat.cast_sub {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p - q) = ↑p - ↑q
@Rat.cast_div {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p / q) = ↑p / ↑q
@Rat.cast_add {α} [DivisionRing α] [CharZero α] (p q : ℚ) : ↑(p + q) = ↑p + ↑q
@Rat.cast_ofNat {α} [DivisionRing α] (n : ℕ) [n.AtLeastTwo] : ↑(OfNat.ofNat n) = OfNat.ofNat n
@Rat.cast_natCast {α} [DivisionRing α] (n : ℕ) : ↑↑n = ↑n
@Rat.cast_inv {α} [DivisionRing α] [CharZero α] (p : ℚ) : ↑p⁻¹ = (↑p)⁻¹
@Rat.cast_zero {α} [DivisionRing α] : ↑0 = 0
@Rat.cast_inj {α} [DivisionRing α] [CharZero α] {p q : ℚ} : ↑p = ↑q ↔ p = q
```

**F-4 (two pitfalls of "opposite tail rules", measured, extremely easy to get wrong)**: the goal is
`((barrierQ lam x : ℚ) : ℝ) = barrier (lam : ℝ) (x : ℝ)` (**no hypothesis needed**, including `lam = 0`):

- **Route 1 `push_cast`**: `unfold barrierQ barrier; push_cast` **is not enough on its own** —
  it normalizes both sides to `(↑lam - ↑x)^2/(4*↑lam) = (↑lam - ↑x)^2/(4*↑lam)`, **without a closing step**,
  so one must **add `ring`** (or `rfl`). Removing `ring` reports
  `error: unsolved goals`.
- **Route 2, an explicit `rw` chain**: `rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]`
  **comes with its own `rfl` closing step** and the goal is already closed; **writing `ring` afterwards reports `error: no goals to be solved`**.
  ⇒ this route **must not have a tail tactic**.
- **`Rat.cast_inj`'s `α` gets stuck under `apply`**: `apply Rat.cast_inj.mp` reports
  `typeclass instance problem is stuck, it is often due to metavariables / CharZero ?m.41`.
  One must **give the target domain explicitly**: `apply (Rat.cast_inj (α := ℝ)).mp`.
- Also note: `cast_pow` / `cast_ofNat` / `cast_natCast` / `cast_zero` **do not need** `[CharZero α]`;
  `mul` / `sub` / `div` / `add` / `inv` / `inj` **do need it**. `cast_ofNat` carries `[n.AtLeastTwo]`.

## 2026-09-20 — Closeout appendix batch 2: the reliable-domain boundary of `norm_num` — api_researcher — it does not know the positivity of `Real.exp`

**Probe**: `proofs/probes/marcus-api-cast-normnum.lean` (0 error / 0 warning)

**Re-check confirmed** (a measured deviation on M5b `inst_I7_unphysical_rate_not_pos`): the phrasing in the dispatch prompt,
`intro h; have := h 0; norm_num [rate, barrier] at this`, **is not enough to close the goal** —
it reduces the hypothesis to something like `Real.exp (1/4) < 0`, but `norm_num` **does not know the positivity of `Real.exp`**,
leaving the unsolved goal `⊢ False`.

✅ **The phrasing that works** (four steps, already adopted in `PhotoLean/Marcus/Instances.lean`):

```lean
theorem inst_I7_unphysical_rate_not_pos : ¬ (∀ x : ℝ, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  have hb : barrier (-1) 0 = -(1 / 4) := by norm_num [barrier]   -- ⑴ compute the barrier value first
  rw [rate, hb] at h0                                            -- ⑵ substitute back into rate
  norm_num at h0                                                 -- ⑶ reduce
  linarith [Real.exp_pos (1 / 4)]                                -- ⑷ hand exp positivity to linarith
```

⇒ it now sits alongside the `decide`/`Rat` reduction entries, forming the **"three reliable-domain tables"** (see the end of Group G in the "calibration backlog"):
`decide` (ℚ integers) · `norm_num` (polynomials/literals, **not including `Real.exp`**) · `field_simp` (**equalities only**).

`Real.exp_pos` is consistent with its registration in Group A of this log (`(x : ℝ) : 0 < Real.exp x`).
The backup tool on the same chain, `mul_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a * b < 0`, has been measured passing
(the M4a backup verifier uses it to prove `rate (-1) (-1) 1 1 x < 0`).

## 2026-09-20 — Closeout appendix batch 2: Group D reciprocals / cross-multiplication / `field_simp` failure paths — api_researcher — 3 names exist, direction pitfalls pinned down

**Probe**: `proofs/probes/marcus-api-cast-normnum.lean` (0 error / 0 warning)

`#check` raw output:

```
one_div_le_one_div_of_le.{u_2} {α} [LinearOrderedSemifield α] {a b : α} (ha : 0 < a) (h : a ≤ b) :
  1 / b ≤ 1 / a
div_lt_div_iff₀.{u_2} {G₀} [CommGroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
  [PosMulReflectLT G₀] [PosMulStrictMono G₀] {a b c d : G₀} (hb : 0 < b) (hd : 0 < d) :
  a / b < c / d ↔ a * d < c * b
div_lt_iff₀.{u_2} {G₀} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b c : G₀} [MulPosStrictMono G₀] (hc : 0 < c) : b / c < a ↔ b < a * c
```

**D-3 (direction pitfall)**: the conclusion of `one_div_le_one_div_of_le ha h` is **`1 / b ≤ 1 / a`** —
taking reciprocals of `a ≤ b` **flips the direction**. This log had not recorded the name before (it had only appeared in a
`#check` in `proofs/probes/marcus-prover_d2-scratch.lean:38`, and is used by `hgeom_of_nonoverlap` in
`PhotoLean/Marcus/Reorg.lean`); it is filed now.

**D-4 (the three-step method for inequalities with several denominators)**:

- **Both arguments of `div_lt_div_iff₀ hb hd` are "denominator positivity"** (`0 < b`, `0 < d`);
  note the distinction from `div_lt_div_iff_of_pos_right` (**the same** denominator).
- **`field_simp` is unreliable for inequalities**: it measured `error: simp made no progress` (it is reliable only for **equalities**).
- **The general three steps**: ⑴ when a common denominator is needed, first apply `field_simp` to an **equality**; ⑵ use `div_lt_div_iff₀ hb hd`
  (or `div_lt_iff₀ hc`) to **cross-multiply** away the denominators; ⑶ close with `nlinarith`.
  **Before clearing denominators, neither `nlinarith` nor `gcongr` can see the sign of the denominator, and the goal does not move.**

## 2026-09-20 — kernel lemma index (`barrier`/`rate` degenerate points) — api_researcher

An index reported for the M4a backup verifier (registered only, no new section);
the 5 signatures of `Sharp.lean` were cross-compared in three places (`plan §7.1` / the statement skeleton / the delivery) and agree:

- **`sharp_lam_pos_of_eq {A kB T : ℝ} (hdesc : InvertedDescriptor A 0 kB T) : False`**
  — ⚠️ **the signature contains no positivity hypothesis at all** (no `hkB` / `hT` / `hA`).
  Mechanism: Lean's division-by-zero convention `x / 0 = 0` makes `barrier 0 x = 0`, so the rate is constantly `A`;
  the descriptor demands `rate … 2 < rate … 1`, i.e. `A < A`, and `lt_irrefl` closes it.
  For a compilable proof body see `sharp_lam_pos_of_eq` in `proofs/probes/marcus-proof-skeletons.lean`.
- Other degenerate-point lemmas on the same chain: `barrier_at_lam` (`ring`, no hypotheses), `barrier_zero_lam` (`ring`, no hypotheses),
  `barrier_symm` (`ring_nf`, `lam ≠ 0` unused by the proof).

---

## Quick reference for provers (by M3/M5 priority)

**M3 (Sprint 3, the tightest)**:

```lean
-- right branch of the barrier
rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * lam)]; nlinarith
-- left branch of the barrier (lam<0): flip to a positive denominator first
rw [show (4 : ℝ) * lam = -(4 * (-lam)) by ring, div_neg, div_neg, neg_lt_neg_iff]
rw [div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * (-lam))]; nlinarith
-- exp layer
Real.exp_lt_exp.2 h          -- h : a < b  ⇒  Real.exp a < Real.exp b
Real.exp_lt_exp.mp h         -- reverse direction
-- multiplication layer
mul_lt_mul_of_pos_left h hA  -- h : b < c, hA : 0 < a  ⇒  a*b < a*c
pos_of_mul_pos_left h (le_of_lt (Real.exp_pos u))  -- get 0 < A from 0 < A * exp u
-- the ≤ version (the rate_peak_at_lam peak)
mul_le_mul_of_nonneg_left h hA.le    -- h : b ≤ c, hA : 0 < A
div_le_div_of_nonneg_right h hkT.le  -- h : a ≤ b, hkT : 0 < kB*T
rw [Real.exp_le_exp]                 -- the ≤ version is also an iff
-- the two key steps of rate_ratio
rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]   -- cancel A; exp quotient → exp difference (note the ←)
```

**M5 (end of Sprint 2)**:

```lean
-- integer arguments (including negative integers)
example : zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : zoneQ (1 : ℚ) (-3) = Zone.normal := by decide
-- contains division / decimals → decide gets stuck, norm_num is required
example : zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [zoneQ]
-- ℚ→ℝ
Rat.cast_lt.mpr h            -- h : p < q  ⇒  (p:ℝ) < (q:ℝ)
simp only [Rat.cast_lt, Rat.cast_inj]   -- key to classifier consistency (cannot use rw)
-- ⚠️ cast literals ≠ OfNat literals: ((1:ℚ):ℝ) and (1:ℝ) are not defeq
--    when the goal contains InvertedRegion (1:ℝ) 3, `exact h` (h : ↑1 < ↑3) gives a type mismatch
-- ⚠️ rw does not go through defeq: rw [← zoneQ_inverted_iff] does not unfold def InvertedRegion
--    use `exact (zoneQ_inverted_iff lam x).mp h` or first `show (lam:ℝ) < (x:ℝ)`
-- ℚ→ℝ cast family (barrierQ_cast): the two routes have **opposite tail rules**
push_cast; ring   -- route 1: push_cast has no closing step of its own; ring must be added
rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]  -- route 2: comes with rfl, so ring **must not** be added
apply (Rat.cast_inj (α := ℝ)).mp   -- ⚠️ α must be given explicitly, otherwise it gets stuck on CharZero ?m
-- three steps for multi-denominator inequalities: field_simp only for equalities → cross-multiply with div_lt_div_iff₀ → nlinarith
rw [div_lt_div_iff₀ hb hd]   -- hb : 0 < b, hd : 0 < d (**both are denominator positivity**)
one_div_le_one_div_of_le ha h   -- a ≤ b ⇒ 1/b ≤ 1/a (**reciprocation flips the direction**)
```

**⚠️ Tool boundaries (the three reliable-domain tables; details at the end of Group G in the "calibration backlog")**:
`decide` only accepts ℚ integers; `norm_num` **does not know the positivity of `Real.exp`** (use `linarith [Real.exp_pos c]`);
`field_simp` is reliable only for **equalities**.

**⚠️ Terminology discipline (finding A by the M2 verifier; this log has been corrected)**:
"a hypothesis **unused by the proof** (unused)" ≠ "a hypothesis **derivable from the other hypotheses**". The former only means it can be dropped;
the latter is a proposition that later readers may take as a **reusable inference rule**. The two must not be mixed up when writing documentation —
`h₁ : 0 ≤ x₁` in `barrier_antitone_of_pos` belongs to the **former** (the counterexample `lam=1, x₁=-5, x₂=-4` refutes the latter).

**Naming (hard constraint)**: in Lean 4, `λ` is a reserved token and **cannot be used as an identifier**. Use uniformly
`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2` (see the file header of
`marcus-statement-skeleton.lean`).
