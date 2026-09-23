# theories/EnergyGapLaw/plan.md — PhotoLean formalization plan: the energy-gap law (Englman–Jortner form) (EG1–EG5)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/EnergyGapLaw-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/EnergyGapLaw/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group B (two-parabola basis,
> reusing the Marcus kernel), first theory of the group.

---

## 1. Overall goal and boundaries

### 1.1 The claim

The energy-gap law (Englman–Jortner): the nonradiative rate of an electronic relaxation falls
off exponentially with the energy gap — `log k` is (approximately) affine and decreasing in the
gap. In the repository's classical two-parabola model the nonradiative rate is the Marcus rate
at the gap (`x = −ΔG = ΔE` up to the sign convention), and the kernel decides the content
precisely:

* the exact law is **quadratic** in the gap: `log k(x) = log A − (λ−x)²/(4λk_BT)`;
* the decrease direction holds **exactly in the inverted region** `λ < x` (and reverses in the
  normal region — the gap law is an inverted-regime law, a sharp boundary statement);
* the textbook affine form is the **tangent** at a reference gap `x*` with slope
  `(λ−x*)/(2λk_BT)`, it **overestimates** the log-rate everywhere off the tangent point with the
  exact quadratic defect `−(x−x*)²/(4λk_BT)`, and no affine law is exact on any non-degenerate
  interval (the BEP second-difference pattern transplanted);
* the tangent slope itself steepens as the reference gap grows — the formal reading of why each
  homologous series fits its own line.

### 1.2 The model (chosen, not derived)

Two-parabola surfaces of the kernel with reorganization energy `λ` and gap `x`; the rate is the
Arrhenius/Marcus rate over the crossing barrier. This theory carries **its own copies** of the
kernel objects (`nrBarrier`, `nrRate`, `InvertedGap`) pinned to `PhotoLean.Kernel` /
`PhotoLean.Marcus` by `rfl` certificates (hard constraint 1); the certificates are stated in
this inventory and delivered in `Basic.lean` (Phase 2) — a failing certificate is a compile-time
regression alarm, never an edit permit.

### 1.3 Explicit non-goals

* No quantum-mechanical FC factors (vibronic progressions, the `ℏω` quantum); the classical
  (Marcus) limit is the model, registered.
* The Englman–Jortner prefactor (`C²√(2π)/(ℏ√(2λℏω))`) is folded into the constant `A` —
  registered in the honesty table; only the gap dependence is the theory's content.

## 2. Conventions and symbols

`lam > 0` reorganization energy; `x` the energy gap (driving-force convention `x = −ΔG`);
`A > 0` the prefactor; `kB·T > 0` the thermal energy. `Real.log` of the rate throughout (the
rate is positive under `A > 0`, so no totalization issue arises — the premise is carried).
Namespace `PhotoLean.EnergyGapLaw`; rational layer `PhotoLean.EnergyGapLaw.Rat`.

## 3. Statement authority and inventory

The authority is `probes/EnergyGapLaw-statement-skeleton.lean` (Phase-1 placeholder bodies;
sha256 on the board once compiling).

### 3.1 Statement-correction log

* **Entry 1 (EG-I3, 2026-09-22, probe recompute)** — the tangent-defect witness value is
  `-5` (`((2 − 3/2)²/(4·(1/2)·(1/40))) = 5` by `norm_num`); the inventory's draft `-20` was
  wrong (the literature round's arithmetic note confirmed the probe). The skeleton carries
  `lnRate 2 = eglTangent (3/2) 2 - 5` at `lam = 1/2, kB = 1, T = 1/40`.
* **Entry 2 (EG-S4, 2026-09-22, weakest-premise standard)** — the `0 < A` premise was dropped:
  the statement never mentions `A`, so the premise is unconsumable (iron rule 3).
* **Entry 3 (EG-C4 corollary, 2026-09-22)** — the midpoint corollary is stated as the iff
  `secant < 0 ↔ lam < (x₁+x₂)/2` (the inventory's wording was already "exactly when"; the
  skeleton carries the iff form).
* **Entry 4 (EG-R2/R3, 2026-09-22)** — `EGZone`/`egZoneQ` live in the main namespace (the
  plan's naming had no `Rat.` prefix; cf. StokesShift), and the rate-ordering decision is
  stated on the barrier side (`Rat.nrBarrier` comparison), never on `Real.exp`.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (EG-B: copies, certificates, predicates), `Criterion.lean`
(EG-C: the exact laws), `Sharp.lean` (EG-S: the tangent/defect layer), `RatModel.lean` (EG-R),
`Instances.lean` (EG-I).

**EG-B (copies + certificates + predicates):**

* EG-B1 `nrBarrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)`;
  `cert_nrBarrier : nrBarrier = PhotoLean.Kernel.barrier` (pointwise `rfl` rows
  `nrBarrier lam x = Kernel.barrier lam x` if the `fun`-level `rfl` does not close).
* EG-B2 `nrRate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(nrBarrier lam x) / (kB * T))`;
  `cert_nrRate : nrRate A lam kB T x = PhotoLean.Marcus.rate A lam kB T x` (via `unfold` +
  `rfl` — the Marcus body is `A * Real.exp (-(Marcus.barrier lam x) / (kB * T))`).
* EG-B3 `InvertedGap (lam x : ℝ) : Prop := lam < x`;
  `cert_invertedGap : InvertedGap lam x ↔ PhotoLean.Marcus.InvertedRegion lam x` (`Iff.rfl`).
* EG-B4 `lnRate (A lam kB T x : ℝ) : ℝ := Real.log (nrRate A lam kB T x)`.

**EG-C (the exact laws):**

* EG-C1 `lnRate_eq (hA : 0 < A) (hlam : lam ≠ 0) (hkT : 0 < kB * T) (x : ℝ) :
  lnRate A lam kB T x = Real.log A - (lam - x) ^ 2 / (4 * lam * (kB * T))` — the exact quadratic
  law. (`Real.log_mul`, `Real.log_exp`, field normal forms; `hlam` as `≠` suffices for the
  algebra — positivity is needed only where the *order* matters, weakest-premise standard.)
* EG-C2 `lnRate_strictAnti_on_inverted (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
  (hx1 : lam < x₁) (h : x₁ < x₂) : lnRate A lam kB T x₂ < lnRate A lam kB T x₁` — the gap-law
  direction, exactly on the inverted region.
* EG-C3 `lnRate_strictMono_on_normal (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
  (hx2 : x₂ < lam) (h : x₁ < x₂) : lnRate A lam kB T x₁ < lnRate A lam kB T x₂` — the reversal:
  in the normal region the rate *increases* with the gap; together with EG-C2 this pins the law
  to its regime (the boundary `x = lam` is the barrierless point, `nrBarrier lam lam = 0`).
* EG-C4 `secant_slope_exact (hA : 0 < A) (hlam : lam ≠ 0) (hkT : 0 < kB * T) (h : x₁ ≠ x₂) :
  (lnRate A lam kB T x₂ - lnRate A lam kB T x₁) / (x₂ - x₁)
    = (2 * lam - x₁ - x₂) / (4 * lam * (kB * T))` — the secant slope of the log-rate is the
  midpoint form; corollary `secant_slope_neg_iff (… hx : lam < (x₁ + x₂) / 2 …)` : the secant is
  negative exactly when the window midpoint is inverted.

**EG-S (the tangent layer — the Englman–Jortner reading):**

* EG-S1 def `eglTangent (A lam kB T xStar x : ℝ) : ℝ :=
  lnRate A lam kB T xStar + (lam - xStar) / (2 * lam * (kB * T)) * (x - xStar)` — the affine
  gap law at the reference gap.
* EG-S2 `eglTangent_overestimates (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) (xStar x : ℝ) :
  lnRate A lam kB T x ≤ eglTangent A lam kB T xStar x ∧
  (lnRate A lam kB T x = eglTangent A lam kB T xStar x ↔ x = xStar)` — the tangent
  overestimates the log-rate with the exact defect `-(x - xStar)² / (4 * lam * (kB * T))`;
  equality only at the reference gap. (State the defect as its own row EG-S2a
  `eglTangent_defect : lnRate x = eglTangent xStar x - (x - xStar)^2/(4*lam*(kB*T))`.)
* EG-S3 `not_affine_on_window (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) {p q : ℝ}
  (hpq : p < q) : ¬ ∃ c k : ℝ, ∀ x ∈ Set.Icc p q, lnRate A lam kB T x = c + k * x` — no affine
  gap law is exact on any non-degenerate window (the second-difference engine; mirror
  `BEP.not_epLinearOn_of_ne_zero`, calibrate the pattern there).
* EG-S4 `eglTangent_slope_strictAnti (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
  (h : x₁ < x₂) : (lam - x₂) / (2 * lam * (kB * T)) < (lam - x₁) / (2 * lam * (kB * T))` —
  the tangent slope steepens with the reference gap (why each homologous series fits its own
  line).

**EG-R (rational decision layer):**

* EG-R1 `Rat.nrBarrier (lam x : ℚ) : ℚ` + cast coherence (`Rat.cast` commutes; pure polynomial
  division — no transcendental).
* EG-R2 `inductive EGZone | normal | barrierless | inverted`; `egZoneQ (lam x : ℚ) : EGZone`
  (`decide` by comparing `lam ? x`); correctness: `(egZoneQ lam x = .inverted) ↔ (lam : ℝ) < x`
  (cast row).
* EG-R3 rate-ordering decisions stay on the barrier side: `nrRate_decidable_order` is stated as
  the barrier comparison (exp strict monotonicity consumes it on ℝ); **no** `Real.exp`
  evaluation enters any instance row (hard constraint 3).

**EG-I (named instances):**

* EG-I1 `aromaticSeries` (representative): `lam = 1/2`, `kB·T = 1/40`, gaps `x ∈ {1, 3/2, 2}`
  (all inverted) — barrier chain `1/8 < 1/2 < 9/8`, hence rates strictly decreasing
  (the gap law at ℚ, decided on the barrier side).
* EG-I2 `normalRegionCounter`: `lam = 2`, gaps `x ∈ {1/2, 1}` (normal) — barriers decrease, so
  the rate *increases* with the gap: the refuting instance for a regime-free gap law (pins the
  EG-C2 premise as load-bearing).
* EG-I3 `tangentWitness`: `lam = 1/2`, `kB = 1`, `T = 1/40`, `x* = 3/2`, evaluated at `x = 2`: the
  defect is `-((2 - 3/2)²/(4·(1/2)·(1/40))) = -5` (probe-recomputed; the inventory's draft `-20` was
  wrong — §3.1 entry 1). The row states the exact rational defect and the equation
  `lnRate 2 = eglTangent 2 - 5`.
* **Instance-layer rate readings (M2, verifier run 2).** The instance rows are stated on the
  **barrier side** (rational comparisons, kernel-decided); their docstrings' rate-side readings
  ("hence the rate decreases/increases") are prose justified by the delivered EG-C2/EG-C3, not
  separate rows. `Rat.nrRate_decidable_order` likewise decides barrier order only — no `Real.exp`
  evaluation enters the rational layer (hard constraint 3).

## 5. Proof routes

EG-C1: `Real.log_mul` (positivity of `A` and of the exponential), `Real.log_exp`, then
`field_simp` + `ring`. EG-C2/C3: rewrite by EG-C1; the quadratic comparison factors as
`(x₂−x₁)·(x₁+x₂−2λ)`, whose sign the region premises fix; close by `nlinarith` or
`mul_pos`/`div_pos` chains. EG-C4: EG-C1 + `field_simp` + `ring`. EG-S2: EG-C1 + defect
identity (`ring`) + `div_nonneg`/`sq_nonneg`. EG-S3: three evaluations (`p`, `(p+q)/2`, `q`) of
the purported affine law force the second difference to vanish, but the exact law's second
difference is `-(q-p)²/(…)` after EG-C1 — contradiction by `nlinarith`. API-calibrate
`Real.log_mul`, `Real.log_exp`, `Real.exp_strictMono`-adjacent rows before freezing the skeleton.

## 6. Sprint order, ownership, dispatch

Sprint EG0 (Phase 1) → EG1 `Basic` (copies + certificates) → EG2 `Criterion` → EG3 `Sharp` →
EG4 `RatModel` → EG5 `Instances`. Owner: prover_a (group B lead; the kernel-copy pattern is the
historical one).

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.EnergyGapLaw.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.EnergyGapLaw.Sharp
    proofs/scripts/axioms.sh PhotoLean.EnergyGapLaw.Sharp PhotoLean.EnergyGapLaw.eglTangent_overestimates
    python3 theories/BEP/probes/bep-fidelity.py --theory EnergyGapLaw

## 8. Risks and mitigations

* The `Real.log` normal forms are the riskiest API surface of the batch; the API probe
  (`probes/EnergyGapLaw-api-probe.lean`) must confirm `Real.log_mul`, `Real.log_exp`,
  `Real.exp_pos` and the `div` normal forms before the skeleton is frozen.
* EG-I3's arithmetic is error-prone: the probe recomputes the defect by `norm_num` before the
  row is written.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Classical two-parabola Marcus rate for the nonradiative channel (no quantum FC factor) | EG-C/S rows |
| 2 | The Englman–Jortner prefactor is folded into `A` | — |
| 3 | `A, lam, kB·T` positivity explicit on every row | — |
| 4 | Named instances are representative rational models | their barrier verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **Marcus — definitional certificates + look-alike registration**: EG-B1..B3 pin the theory to
  the kernel/Marcus; EG-S3 mirrors `BEP.not_epLinearOn_of_ne_zero` (the same second-difference
  engine) — register the shared pattern as a shape edge (no new mathematics claimed).
* **BEP — shape edge**: the tangent-with-quadratic-defect structure is the BEP line law read on
  the log-rate; candidate one row: the defect functions agree up to the scalar `1/(kB·T)`.
* **Hammond — one-way candidate**: the crossing coordinate at the gap (`Kernel.tsCoord lam x`)
  locates the nonradiative transition state; the gap law's regime boundary `x = lam` is
  `tsCoord = 0` (the Hammond coordinate leaves the interval) — one machine-target row.
* **Kasha / KashaVavilov — composition candidate**: the ladder's IC rates ordered by the gap law
  (the kinetic rationale of the funnel; extends Relations §7). One machine-target row at the
  two-gap comparison.
* **ICvsISC — composition (machine target)**: the FC rates of ICvsISC are two EG rates; the
  crossover inherits EG-C2's monotonicity.
* **StokesShift — certificate**: the same surfaces; `lam` is half the Stokes shift (one row
  through `StokesShift.stokesShift_eq`).
* **Sabatier / Goldschmidt / SymmetryFactor / SternVolmer / QuantumYield / FluorPhos / Forster /
  Einstein**: no direct edge — absence drafts registered.

## 11. Position in the repository

Fifth theory of the batch, first of group B; imports `PhotoLean.Kernel` for the certificates and
`PhotoLean.Marcus.Basic` for the rate pin; nothing delivered is modified.
