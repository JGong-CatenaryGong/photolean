# plan.md — PhotoLean Formalization Plan: Marcus Inverted Region (M1–M5)

> *English translation of `plan.md`. The Chinese original at `plan.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

> Project: turn the "Marcus inverted region" into a set of **machine-checkable** theorems.
> Target system: Lean 4.17.0 + mathlib (`MODULE_PREFIX=PhotoLean`, see `proofs/ENGINE.yml`).
> Status: the plan is finalized (human-confirmed on 2026-09-20), implementation has not started.
> Authoritative contract: `proofs/ENGINE.yml`; task board: `proofs/TASKS.md`; experience bank: `proofs/EXPERIENCE.md`.

---

## 1. Overall objective and boundaries

### 1.1 Project objective

Formalize and prove, inside the classical Marcus model (single reaction coordinate, parabolic potentials, classical nuclear motion, Condon approximation):

> **Main theorem**: as soon as the reorganization energy `λ > 0`, the thermal energy `k_B T > 0` and the pre-exponential factor `A > 0`, the statement "the larger the driving force, the smaller the rate" holds inside the **inverted region**
> (driving force `x = -ΔG° > λ`);
> and these three conditions are **sharp (necessary and sufficient)** — remove any one of them and that description fails.

This is the executable version of the "Marcus inverted region": **the barrier `ΔG‡ = (λ - x)²/(4λ)` is minimal (barrierless) at `x = λ`,
hence the rate is maximal at `x = λ`, and the two sides are respectively monotonically increasing (normal region) and monotonically decreasing (inverted region).**

**Attribution (corrected after the literature branch verified the sources)**: the **first proposal** of the inverted region is
**Marcus 1960, *Discuss. Faraday Soc.* **29**, p. 28 §(v), whose title is precisely "Possibility of 'inverted' chemical behaviour"**
(original: *"If ΔF° becomes too negative, intersection of the two surfaces becomes possible only at
high potential energies … m² eventually increases with increasing −ΔF°, and the rate constant decreases."*
⇒ consistent with `ΔG° < -λ` ⟺ `x > λ`). **Marcus 1956 contains no occurrence of "inverted" at all** (confirmed by full-text search),
so the origin of the inverted region must not be recorded as 1956. The original printed source of the barrier formula itself is still 1956 (Eq. (38), p. 974).

### 1.2 Human requirements → milestone correspondence (three parts)

| Human requirement | Milestone | Deliverable |
|---|---|---|
| ① Turn the Marcus inverted region into a formalized description | **M1** (description layer) | `Marcus/Basic.lean`: `barrier` / `rate` / region predicates / `InvertedDescriptor` / decidable classifier `zone` |
| ②a Prove this description | **M2 + M3** (barrier algebra + rate layer) | `Marcus/Barrier.lean` (all the algebra), `Marcus/Rate.lean` (the exp layer + the monotonicity core of the main theorem) |
| ②b Find the **conditions under which** this description holds | **M4** (sharp characterization + microscopic sufficient conditions) | `Marcus/Sharp.lean` (the ⟺ necessary-and-sufficient characterization), `Marcus/Reorg.lean` (`lam = lamIn + lamOut`, positivity of the Pekar factor ⇒ `lam > 0`), `Marcus/Compose.lean` (composition) |
| ③ Plug in instances and decide whether they conform | **M5** (instances and decision) | `Marcus/RatModel.lean` (computable decision over ℚ + transfer lemma), `Marcus/Instances.lean` (instance set) |

### 1.3 Explicitly out of scope (preventing scope creep)

- **No quantum vibrational corrections** (Bixon–Jortner / Jortner energy-gap law / vibrational-mode sums / Franck–Condon factors):
  in the classical model the inverted region is **strictly monotonically decreasing**, while quantum corrections make it saturate; the latter needs
  infinite series and vibrational partition functions, which is too costly under mathlib. Recorded only as literature notes and as a "next stop", not as a milestone.
- **No derivation of non-adiabatic electronic coupling** (exponential decay of `V`, superexchange mechanism), no quantum-mechanical derivation of
  electron transfer, and no first-principles derivation of continuum solvent electrostatics (the Pekar factor is **given as an explicit premise**, not derived).
- **No Marcus cross relation** (`k₁₂ = √(k₁₁k₂₂K₁₂)`), no vibrational-mode sums, no spin–orbit coupling.
- **No competing reaction channels** (this formalization captures only the classical Marcus rate under **a single mechanism**). This is **not our invention**
  but a disclaimer carried by the original literature: the text of 1960 §(v) states *"unless in such cases a more favourable reaction
  mechanism is found"*. It is precisely one of the reasons why the M5 instance layer can only use "region decision + the classical description holds" and **cannot**
  claim to predict measured rates (same origin as the quantitative warning in §8.3).
- No **custom axioms** and no unfinished-proof placeholders are introduced (the criterion is enforced by `proofs/scripts/check.sh --strict` and
  `proofs/scripts/axioms.sh`).
- We **do not claim** that the formalized conclusions are stronger or more general than the classical theory: the value of this project is that it
  **excavates the implicit premises and sharpens them** (see the key finding in §7.1).

---

## 2. Formalization system design

### 2.1 Embedding strategy: build no new kernel, do embedded theory inside Lean

All objects live over `ℝ` (the decision layer lives over `ℚ`), using mathlib's order, division, `Real.exp` and its monotonicity.
**The monotonicity of `exp` is the only real-analysis tool**; everything else is algebraic inequalities over `ℝ`.
This choice is deliberate: it compresses API risk into a small group of `Real.exp_*` lemmas (see §12).

### 2.2 Global base definitions (M1; `Marcus/Basic.lean`)

```lean
import Mathlib

namespace PhotoLean.Marcus

/-- Classical Marcus barrier: driving force `x = -ΔG°` (for an exergonic reaction `x > 0`), reorganization energy `lam`.
    **Convention**: for `lam = 0` we take the value given by Lean's division-by-zero convention `x / 0 = 0`, so `barrier 0 x = 0`;
    this is one branch of the M4 sharpness and must be handled explicitly; one may not assume `lam ≠ 0`. --/
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- Marcus rate (Arrhenius/Eyring form): `k = A · exp(-ΔG‡/(k_B T))`. --/
noncomputable def rate (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(barrier lam x) / (kB * T))

/-- Inverted region: the driving force exceeds the reorganization energy. --/
def InvertedRegion (lam x : ℝ) : Prop := lam < x

/-- Normal region: the driving force is smaller than the reorganization energy. --/
def NormalRegion (lam x : ℝ) : Prop := x < lam

/-- **Inverted-region description** (the formalization target of this project): inside the inverted region the rate is strictly decreasing in the driving force. --/
def InvertedDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁

/-- Normal-region description: inside the normal region the rate is strictly increasing in the driving force. --/
def NormalDescriptor (A lam kB T : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → rate A lam kB T x₁ < rate A lam kB T x₂

/-- Region classification (the carrier of the M5 decision layer). --/
inductive Zone where
  | normal
  | barrierless
  | inverted
  deriving DecidableEq, Repr

/-- Classifier: `x < lam` normal region; `x = lam` barrierless point; `x > lam` inverted region. --/
noncomputable def zone (lam x : ℝ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

end PhotoLean.Marcus
```

**✅ Sprint 0 already measured in practice**: all the definitions above and the theorem signatures of M1–M5 compile in
`proofs/probes/marcus-statement-skeleton.lean` (31 unfinished-proof warnings, **0 errors**).
**That skeleton file is the sole authority on the statements**: the signatures in `PhotoLean/Marcus/*.lean` must match it verbatim.

**Design note (why the description is written as a predicate instead of a single "curve theorem")**:
`InvertedDescriptor` is a proposition that **supports nested negation and conjunction** (the M4 sharpness needs `¬ InvertedDescriptor`),
whereas `zone` turns "decide which region a given instance belongs to" into a **kernel-computable equality test** (M5).
The two are bridged by theorems such as `zone_eq_inverted_iff`, avoiding a semantic drift between the two notions "decision" and "description".

### 2.3 Decision layer and transfer (M5; `Marcus/RatModel.lean`)

The order on `ℝ` is **not computable** (it uses `Classical`), so M5 duplicates it over `ℚ`:

```lean
namespace PhotoLean.Marcus.Rat

/-- Classifier over ℚ: **fully computable** (the order and equality on `Rat` are decidable). --/
def zoneQ (lam x : ℚ) : Zone :=
  if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted

def barrierQ (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)

/-- Transfer lemma: the decision over ℚ agrees with the classifier over ℝ — this is the basis for the binding force of an "instance decision" on the ℝ theory. --/
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)

theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ)

end PhotoLean.Marcus.Rat
```

An instance's "decision" therefore has three **independent chains of evidence** (any one of them can testify on its own; M5 supplies all of them):
1. Kernel computation: `example : zoneQ 1 3 = Zone.inverted := by decide`;
2. Transfer to the ℝ theorem layer: `zoneQ_eq_zone` + `zone_eq_inverted_iff` ⇒ `InvertedRegion 1 3`;
3. Instantiating the main theorem: `InvertedDescriptor 1 1 1 1` (via `inverted_descriptor_holds` + `norm_num`).

### 2.4 Proof discipline (non-negotiable)

1. A delivered theorem must not contain unfinished-proof placeholders or custom axioms; `#print axioms` permits only
   `propext` / `Classical.choice` / `Quot.sound`;
2. **All physical approximations are made explicit** as theorem premises (`0 < λ`, `0 < k_B T`, `0 < A`, `λ = λ_in + λ_out`,
   `1/ε_s < 1/n²`, geometric-factor inequalities, …), and must not be hidden inside definitions or types;
3. One commit per lemma: `feat(<area>): <lemma>` (`<area>` = M1…M5);
4. Do not guess API names: consult `proofs/API-NOTES.md` first, otherwise hand the question to `api_researcher`;
5. Exclusive file ownership (see §10). **A passing `lake build` is not acceptance** (both unfinished-proof placeholders and custom axioms return 0).

**Naming convention (a hard constraint of the toolchain)**: in Lean 4, `λ` is the lambda keyword and **cannot be used as an identifier**
(Sprint 0 measurement: `(λ x : ℝ)` directly reports `unexpected token 'λ'`). Therefore the Lean side uses ASCII throughout:
reorganization energy `lam`, driving force `x`, pre-exponential factor `A`, `kB`, `T`, inner and outer terms `lamIn`/`lamOut`,
static dielectric constant `epsS`, squared refractive index `nSq`, radii `a1`/`a2`, amount of charge transferred `dE`, displacement `dq`.
**The Greek letters in the documentation are only physical notation, not Lean identifiers.**

**The statement-first landing mechanism** (specific to this project and mandatory):
any occurrence of an unfinished-proof placeholder **anywhere** inside `SOURCE_DIRS="PhotoLean"` is intercepted by `check.sh --strict`,
so **statement skeletons are written under `proofs/probes/`** (not in `SOURCE_DIRS`, where a placeholder is allowed);
once a skeleton compiles, its entries are moved one by one into `PhotoLean/Marcus/*.lean` with the proof filled in on the spot.
Skeleton file: `proofs/probes/marcus-statement-skeleton.lean` (the Sprint 0 acceptance artifact).

---

## 3. File layout and dependencies

```text
PhotoLean/
  Smoke.lean                 -- pre-existing: environment smoke test (kept)
  Marcus/
    Basic.lean               -- M1  : barrier / rate / region predicates / description predicates / Zone / zone
    Barrier.lean             -- M2  : pure barrier algebra (nonnegativity, zero barrier at x=lam, symmetry, monotonicity on the two branches, peak, the lam=0 degeneracy)
    Rate.lean                -- M3  : the exp layer (core transfer lemma) + normal region / inverted region / peak at the rate level
    Sharp.lean               -- M4a : sharp characterization of the description (⟺) and failure theorems for non-positive lam
    Reorg.lean               -- M4b : lam = lamIn + lamOut, positivity of the Pekar factor (**imports Mathlib only**)
    Compose.lean             -- M4c : composition theorem (import Sharp + Reorg ⇒ microscopic positivity ⇒ the description holds)
    RatModel.lean            -- M5a : ℚ classifier / barrierQ / transfer lemma
    Instances.lean           -- M5b : instance set (normal region, inverted region, barrierless, counterexample, non-physical branch)
proofs/probes/
  marcus-statement-skeleton.lean    -- Sprint 0: every statement compiles (with placeholders, not entering the source tree)
  marcus-{exp,order,tactic}-api.lean -- api_researcher's #check probes
```

Dependency graph (`→` denotes import):

```text
Basic.lean ──→ Barrier.lean ──→ Rate.lean ──→ Sharp.lean ──┐
    │                                                        ├──→ Compose.lean
    ├──→ RatModel.lean ──┐                                   │
    │                    └──────────────→ Instances.lean ←───┘
    └──→ (no dependencies) Reorg.lean ─────────────────────────┘
```

**The critical path is a single chain** (Basic → Barrier → Rate → Sharp → Compose); the two side branches that can run in parallel are
`Reorg.lean` (**imports Mathlib only, zero dependencies — it can start at the same time as Basic**) and
`RatModel.lean` (needs only Basic). The composition theorem was put into a separate `Compose.lean` precisely in order
**not to let Reorg's independent lemmas be blocked by Sharp** (parallelism inside the dependency graph, see iron rule 5). §10 schedules accordingly.

---

## 4. M1 — Description layer (`Marcus/Basic.lean`; owner prover_a)

**Objective**: turn the "inverted region" into an object in Lean that can be nested, negated and decided; every statement compiles (`stmt`).

### 4.1 Definitions (all of §2.2)

### 4.2 Correctness of the classifier

```lean
theorem zone_eq_normal_iff (lam x : ℝ) : zone lam x = Zone.normal ↔ NormalRegion lam x
theorem zone_eq_barrierless_iff (lam x : ℝ) : zone lam x = Zone.barrierless ↔ x = lam
theorem zone_eq_inverted_iff (lam x : ℝ) : zone lam x = Zone.inverted ↔ InvertedRegion lam x
theorem zone_trichotomy (lam x : ℝ) :
    zone lam x = Zone.normal ∨ zone lam x = Zone.barrierless ∨ zone lam x = Zone.inverted
```

**Proof steps**: do `by_cases` on `x < λ`, `simp [zone, NormalRegion, InvertedRegion, h]`;
for the remaining branch use `push_neg` + `lt_trichotomy` (or `le_antisymm`). For `zone_trichotomy` use `cases zone λ x <;> tauto`.

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Basic` PASS; the four theorems clean under `axioms.sh`.

---

## 5. M2 — Barrier algebra (`Marcus/Barrier.lean`; owner prover_a)

**Objective**: the complete monotonicity picture of `barrier` (the three cases positive λ, negative λ, zero λ), **without involving `exp`**.

```lean
/-- For lam>0 the barrier is non-negative. --/
theorem barrier_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ barrier lam x

/-- Barrierless point: the barrier vanishes at `x = lam` (**no premise needed**). --/
theorem barrier_at_lam (lam : ℝ) : barrier lam lam = 0

/-- Parabolic symmetry: the axis is `x = lam`. --/
theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) : barrier lam x = barrier lam (2 * lam - x)

/-- Peak (barrier minimum): for `lam>0`, `x = lam` is the global minimizer. --/
theorem barrier_min_at_lam {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : barrier lam lam ≤ barrier lam x

/-- `lam>0`, inverted region: the barrier is strictly increasing (this is the algebraic core of the inverted region). --/
theorem barrier_mono_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : lam ≤ x₁) (h₂ : x₁ < x₂) : barrier lam x₁ < barrier lam x₂

/-- `lam>0`, normal region: the barrier is strictly decreasing. --/
theorem barrier_antitone_of_pos {lam : ℝ} (hlam : 0 < lam) {x₁ x₂ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) : barrier lam x₂ < barrier lam x₁

/-- `lam<0`: the direction inside the inverted region is **reversed** (the barrier decreases). A necessary branch for the M4 sharpness. --/
theorem barrier_antitone_of_neg {lam : ℝ} (hlam : lam < 0) {x₁ x₂ : ℝ}
    (h₁ : lam < x₁) (h₂ : x₁ < x₂) : barrier lam x₂ < barrier lam x₁

/-- The `lam=0` degeneracy: the division-by-zero convention makes the barrier identically zero (the other necessary branch for the M4 sharpness). --/
theorem barrier_zero_lam (x : ℝ) : barrier 0 x = 0

/-- A structural theorem: the three cases are exhaustive. --/
theorem barrier_mono_cases (lam : ℝ) :
    (0 < lam → ∀ x₁ x₂ : ℝ, lam ≤ x₁ → x₁ < x₂ → barrier lam x₁ < barrier lam x₂) ∧
    (0 < lam → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ lam → barrier lam x₂ < barrier lam x₁) ∧
    (lam < 0 → ∀ x₁ x₂ : ℝ, lam < x₁ → x₁ < x₂ → barrier lam x₂ < barrier lam x₁) ∧
    (lam = 0 → ∀ x : ℝ, barrier lam x = 0)
```

**Proof sketch**:
- `barrier_mono_of_pos`: `λ ≤ x₁ < x₂ ⇒ 0 ≤ x₁ - λ < x₂ - λ`; via `(λ-x)² = (x-λ)²` (`ring_nf`)
  switch to `(x-λ)²`, get strict monotonicity of the square from `pow_lt_pow_left₀` (or `mul_self_lt_mul_self`),
  then `div_lt_div_of_pos_right _ (by positivity : 0 < 4*λ)`. **Establish positivity with `have` first**; do not expect `nlinarith` to supply the premise by itself.
- `barrier_antitone_of_pos`: same method, but one needs `x₁ < x₂ ≤ λ ⇒ 0 ≤ λ - x₂ < λ - x₁`,
  and reduces the goal `(λ-x₂)²/(4λ) < (λ-x₁)²/(4λ)` to a comparison of squares (beware: lemmas of the `sq_lt_sq` family involve absolute values).
- `barrier_antitone_of_neg`: for `λ < 0`, `(x-λ)²` is still strictly increasing, but dividing by `4λ < 0` reverses the direction
  (`div_lt_div_of_neg_right`, or prove `4λ < 0` first and then use `div_lt_div_iff_of_neg`).
- `barrier_at_lam` / `barrier_zero_lam`: `simp [barrier]` / `norm_num [barrier]`.
- `barrier_symm`: `(λ-x)² = (λ-(2λ-x))²` — `ring_nf` can close it, but **mind the division-by-zero convention**
  (whether the premise `λ ≠ 0` is really necessary: write the measurement outcome into `proofs/API-NOTES.md`).

**Fallback**: if lemmas of the `sq_lt_sq` family have an awkward name/shape in v4.17, switch to
`nlinarith [sq_nonneg (x₁ - λ), sq_nonneg (x₂ - x₁)]` to steamroll the square comparison directly — such goals are the sweet spot of `nlinarith`.

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Barrier` PASS; each item clean under `axioms.sh`.

---

## 6. M3 — Rate layer (`Marcus/Rate.lean`; owner prover_b)

**Objective**: lift the monotonicity of the barrier up to the rate. **All `exp` risk is concentrated in this single file**, isolated behind one core lemma.

```lean
/-- Positive pre-exponential factor ⇒ positive rate (one of the explicit premises of the M4 sharpness is exactly this one). --/
theorem rate_pos {A lam kB T : ℝ} (hA : 0 < A) (x : ℝ) : 0 < rate A lam kB T x

/-- **Core transfer lemma**: a smaller barrier ⇒ a larger rate. The only place in the whole project where monotonicity of exp is used. --/
theorem rate_gt_of_barrier_lt {A lam kB T : ℝ} (hA : 0 < A) (hkT : 0 < kB * T) {x y : ℝ}
    (h : barrier lam x < barrier lam y) : rate A lam kB T y < rate A lam kB T x

/-- Quantitative form (optional / stretch goal): exponential form of the inverted-region suppression factor. --/
theorem rate_ratio {A lam kB T : ℝ} (hA : A ≠ 0) (hkT : kB * T ≠ 0) (x y : ℝ) :
    rate A lam kB T y / rate A lam kB T x
      = Real.exp ((barrier lam x - barrier lam y) / (kB * T))

/-- Normal region: the larger the driving force, the larger the rate. --/
theorem normal_rate_increases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : 0 ≤ x₁) (h₂ : x₁ < x₂) (h₃ : x₂ ≤ lam) :
    rate A lam kB T x₁ < rate A lam kB T x₂

/-- Inverted region: the larger the driving force, the smaller the rate — the Marcus inverted region. --/
theorem inverted_rate_decreases {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    {x₁ x₂ : ℝ} (h₁ : lam < x₁) (h₂ : x₁ < x₂) :
    rate A lam kB T x₂ < rate A lam kB T x₁

/-- Peak: the rate is maximal at `x = lam` (the fastest reaction has a driving force exactly equal to the reorganization energy). --/
theorem rate_peak_at_lam {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T)
    (x : ℝ) : rate A lam kB T x ≤ rate A lam kB T lam
```

**Proof sketch**: `rate_gt_of_barrier_lt` is the **least laborious yet most crucial** lemma of the whole project:
from `h : Φx < Φy` get `-(Φy)/(kBT) < -(Φx)/(kBT)` (first `neg_lt_neg`, then `div_lt_div_of_pos_right` using `hkT`),
then `Real.exp_lt_exp` (**the direction must be `exp a < exp b ↔ a < b`, already measured by api_researcher**)
gives `exp(-(Φy)/(kBT)) < exp(-(Φx)/(kBT))`, and finally `mul_lt_mul_of_pos_left _ hA` closes it.
The three rate theorems are all two-line combinations of `barrier_mono_*` + `rate_gt_of_barrier_lt`.

**Risk**: the `Real.exp`-related names are the only place in this project where one may "guess wrong" → **guessing names is forbidden**; read `proofs/API-NOTES.md` first.
`rate_ratio` is a stretch goal (`Real.exp_sub` + `div_eq_mul_inv` + `ring_nf`); if it has not converged within 20 minutes, mark it `todo` and note that on the task board — it **does not block M4/M5**.

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Rate` PASS; each item clean under `axioms.sh`.

---

## 7. M4 — Conditions of validity (sharp characterization + microscopic sufficient conditions)

### 7.1 M4a Sharp characterization (`Marcus/Sharp.lean`; owner prover_c)

**Finding made during planning (the physical core of this project; it must be written into the theorems)**:
if one writes down `InvertedDescriptor` alone, it **does not imply `λ > 0`**. Counterexample (a non-physical branch):
with `A < 0 ∧ λ < 0 ∧ k_B T > 0`, `λ<0` makes `x ↦ barrier λ x` **decreasing** on the inverted region,
so `exp(-Φ/(kBT))` is increasing and multiplication by the negative `A` yields a **strictly decreasing** function — the description holds, but the rate is **negative**.
**Therefore "positivity of the rate" (equivalent to `A > 0`) is a premise needed for the description to be meaningful, and it must be made explicit.**

```lean
/-- Main theorem: `A>0 ∧ lam>0 ∧ k_B T>0` ⇒ the inverted-region description holds. --/
theorem inverted_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hkT : 0 < kB * T) : InvertedDescriptor A lam kB T

/-- The normal-region description holds as well (together with the inverted region it forms the complete rate–driving-force curve). --/
theorem normal_descriptor_holds {A lam kB T : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) :
    NormalDescriptor A lam kB T

/-- **Sharp characterization (conditions of validity)**: under the physical positivity premises `k_B > 0, T > 0`,
    "the rate is positive everywhere and the inverted-region description holds" ⟺ `A > 0 ∧ lam > 0`. --/
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam

/-- The "failure" form of necessity: for `lam ≤ 0` the description necessarily fails (under the physical positivity premises). --/
theorem descriptor_fails_of_nonpos_lam {A kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hA : 0 < A) {lam : ℝ} (hlam : lam ≤ 0) : ¬ InvertedDescriptor A lam kB T

/-- [stretch] The non-physical branch really does satisfy the description — showing that the "rate positivity" premise cannot be dropped. --/
theorem inverted_descriptor_holds_of_neg {A lam kB T : ℝ} (hA : A < 0) (hkT : 0 < kB * T)
    (hlam : lam < 0) : InvertedDescriptor A lam kB T
```

**⚠️ Precision of the statement (avoiding over-claiming)**: the rate depends only on the **product** `τ := kB * T`, so
`(∀x, 0<rate) ∧ description ⟺ 0<A ∧ 0<lam ∧ 0<τ` is a characterization **in terms of the product**;
when `0 < kB` and `0 < T` are taken as **explicit physical premises** (positive temperature), neither `kB` nor `T` is a "necessary condition" on its own
(`kB < 0 ∧ T < 0` also gives `τ > 0`). `descriptor_sharp` therefore states the `⟺` only over `A` and `lam`,
with `kB`, `T` appearing only as premises — **do not** claim in the documentation that "`kB` and `T` are each necessary".

**Proof sketch**:
- `(⟸)`: `inverted_descriptor_holds` ← `inverted_rate_decreases` (M3) instantiated directly at arbitrary
  `λ < x₁ < x₂`; `(∀x, 0 < rate _)` ← `rate_pos`.
- `(⟹) A > 0`: take `x := λ`; `0 < A * exp(…)` together with `exp(…) > 0` gives `A > 0`
  (`pos_of_mul_pos_right` / `lt_of_mul_lt_mul_left`).
- `(⟹) λ > 0`: argue by contradiction from `λ ≤ 0`, `rcases lt_or_eq_of_le hλ` splits into two branches —
  - `λ = 0`: `barrier_zero_lam` ⇒ `rate = A * exp 0 = A`, take `x₁ = 1 < 2 = x₂`
    to get `A < A`, a contradiction;
  - `λ < 0`: `barrier_antitone_of_neg` ⇒ on the inverted region `Φ` decreases ⇒ (with `hkT > 0`) `rate` increases,
    contradicting the strict decrease demanded by the description (take `x₁ = λ+1 < λ+2`).
  Both branches need only the ready-made lemmas of M2 plus `norm_num` for the bounds.
- `descriptor_fails_of_nonpos_lam` is an immediate corollary of the necessity direction above.

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Sharp` PASS; each item clean under `axioms.sh`;
**the verifier must re-examine in particular the two necessity branches of `descriptor_sharp`** (this is where the project is most likely to silently rely on the
"division by zero = 0" convention and miss a branch).

### 7.2 M4b Microscopic sufficient conditions (`Marcus/Reorg.lean`; owner prover_d)

**Objective**: downgrade the premise `λ > 0` from an "assumption" to something "**derived from microscopic parameters**" — that is the complete form of "finding the conditions of validity".

```lean
/-- Inner-sphere reorganization energy: normal-mode force constant × displacement squared / 2. --/
noncomputable def lamInner (kk dq : ℝ) : ℝ := kk * dq ^ 2 / 2

/-- Outer-sphere (solvent) reorganization energy (two-sphere continuum model, Pekar form):
    `Δe² · (1/(2a₁) + 1/(2a₂) - 1/R) · (1/n² - 1/ε_s)`. --/
noncomputable def lamOuter (dE a1 a2 R nSq epsS : ℝ) : ℝ :=
  dE ^ 2 * (1 / (2 * a1) + 1 / (2 * a2) - 1 / R) * (1 / nSq - 1 / epsS)

theorem lamInner_nonneg {kk : ℝ} (hkk : 0 ≤ kk) (dq : ℝ) : 0 ≤ lamInner kk dq
theorem lamInner_pos {kk : ℝ} (hkk : 0 < kk) {dq : ℝ} (hdq : dq ≠ 0) : 0 < lamInner kk dq

/-- **Positivity of the Pekar factor**: `n² < ε_s` (squared optical refractive index smaller than the static dielectric constant) + positive geometric factor
    ⇒ the outer-sphere reorganization energy is positive. This is the solvent-side sufficient condition for "the inverted region exists". --/
theorem lamOuter_pos {dE a1 a2 R nSq epsS : ℝ} (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) : 0 < lamOuter dE a1 a2 R nSq epsS

/-- [stretch · strongly recommended] Positivity of the geometric factor **can be derived from "the two spheres do not overlap"** instead of being assumed:
    `a1 + a2 ≤ R ⇒ 1/R < 1/(2*a1) + 1/(2*a2)` (because `1/R ≤ 1/(a1+a2)` and
    `1/(2a1)+1/(2a2)-1/(a1+a2) = (a1²+a2²)/(2a1a2(a1+a2)) > 0`).
    This is the **only** geometric lemma in this plan that genuinely needs an inequality; it depends on no physical approximation. --/
theorem hgeom_of_nonoverlap {a1 a2 R : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hRge : a1 + a2 ≤ R) : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)

/-- Additivity of the reorganization-energy decomposition: positivity is preserved under addition. --/
theorem lam_total_pos {lamIn lamOut : ℝ} (h₁ : 0 ≤ lamIn) (h₂ : 0 < lamOut) : 0 < lamIn + lamOut

/-- **Composition theorem**: microscopic positivity ⇒ the premises of the main theorem hold ⇒ the inverted-region description holds.
    It replaces the "assumption" `lam > 0` by a physically more basic condition. --/
theorem descriptor_holds_of_microscopic {A kB T kk dq dE a1 a2 R nSq epsS : ℝ} (hA : 0 < A)
    (hkB : 0 < kB) (hT : 0 < T) (hkk : 0 ≤ kk) (hdE : 0 < dE) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hR : 0 < R) (hgeom : 1 / R < 1 / (2 * a1) + 1 / (2 * a2)) (hnSq : 0 < nSq) (hepsS : 0 < epsS)
    (hPekar : 1 / epsS < 1 / nSq) :
    InvertedDescriptor A (lamInner kk dq + lamOuter dE a1 a2 R nSq epsS) kB T
```

**Proof sketch**: `lamInner_pos`/`lambdaOuter_pos`: `mul_pos` + `one_div_pos` + `linarith` handle
`1/(2a₁) + 1/(2a₂) - 1/R > 0` and `1/nSq - 1/εs > 0` (first turn `1/εs < 1/nSq` into `1/nSq - 1/εs > 0`).
Composition theorem: `lam_total_pos` gives `λ > 0`, then `inverted_descriptor_holds` (requires importing `Sharp`).

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Reorg` PASS; each item clean under `axioms.sh`;
every physical premise (`hnSq`, `hεs`, `hPekar`, `hgeom`) must be visible in the theorem signature and **must not be folded into a definition**.

---

## 8. M5 — Instances and decision (`Marcus/RatModel.lean` + `Marcus/Instances.lean`; owner prover_b)

**Objective**: substitute the instances and **decide** whether they conform to the inverted-region description; the decision must be produced by kernel computation or by a proof, not by a script assertion.

### 8.1 Decision layer (`RatModel.lean`)

```lean
def zoneQ (lam x : ℚ) : Zone
def barrierQ (lam x : ℚ) : ℚ
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)
theorem zoneQ_inverted_iff (lam x : ℚ) : zoneQ lam x = Zone.inverted ↔ (lam : ℝ) < (x : ℝ)
```

**Acceptance**: `check.sh --strict PhotoLean.Marcus.RatModel` PASS; clean under `axioms.sh`.

### 8.2 Instance set (`Instances.lean`) — every class of instance gets one piece of **decision** evidence

| # | Instance | Expected decision | Evidence shape |
|---|---|---|---|
| I1 | `λ = 1, x = 3` (pure numbers, inverted region) | conforms (in the inverted region) | `by decide` computes `zoneQ` + transfer |
| I2 | `λ = 1, x = 3/4` (normal region) | does not conform (normal region) | `by decide` yields `zoneQ = .normal` |
| I3 | `x = λ` (barrierless point) | boundary (rate maximal) | `zoneQ` + instantiated `rate_peak_at_lam` |
| I4 | literature parameters: an inverted-region pair | conforms | `norm_num` + transfer lemma |
| I5 | literature parameters: a normal-region pair | does not conform to the inverted-region description | as above + `normal_rate_increases` |
| I6 | `λ = -1/2, A = 1, kT = 1` (non-physical) | **does not conform** to the description | `descriptor_fails_of_nonpos_lam` |
| I7 | `A = -1, λ = -1, kT = 1` (non-physical branch) | the description holds but the **rate is non-positive** ⇒ judged unusable | `inverted_descriptor_holds_of_neg` (stretch) + positivity contradiction |

```lean
-- Shape example (I1; **already exercised successfully by the M5a owner**, see F1–F7 in proofs/probes/marcus-prover_c-scratch.lean)
-- ⚠️ Three corrections (the wording of the original plan does not compile; measured by the M5a owner):
--   (1) the direction of `rw` **depends on which symbol occurs in the object being rewritten** (the M5a/M5b owners each measured half of it; here is the unified rule):
--       * rewriting a **hypothesis** `h : Rat.zoneQ lam x = ...` (which contains `zoneQ`) → use the **forward** rule `rw [Rat.zoneQ_eq_zone] at h`
--         (the LHS of the rule is `zoneQ`, so it matches); writing `←` reports `did not find instance of the pattern`.
--       * rewriting an occurrence of `zone ↑lam ↑x` already present in the **goal** → use the **backward** rule `rw [← Rat.zoneQ_eq_zone]`
--         (the pattern of `←` is `zone ↑?lam ↑?x`). The M5b lemma `normalRegion_of_zoneQ_normal` is exactly this branch.
--       In one sentence: **look at the pattern, not at your intuition** — when `zoneQ` occurs in the expression use the forward direction, when `zone ↑↑` occurs use the backward direction.
--   (2) cast literals ≠ `OfNat` literals (**not definitionally equal**): after the transfer, the ℝ-side arguments are `↑(1:ℚ)`,
--       so a direct `exact (zone_eq_inverted_iff 1 3).mp h` gives a type mismatch
--       (`↑1 < ↑3` vs `(1:ℝ) < 3`). Ways out: write the ℝ-side arguments as `((·:ℚ):ℝ)` so that they align verbatim with the lemma's conclusion,
--       or bridge with `show (1:ℝ) < 3` + `exact_mod_cast`.
--   ⚠️ If the I2 row of the table still says "`by decide` yields `zoneQ = .normal`", that wording is **outdated** (found by the M3/M5a verifier, item (d)):
--       rational literals involving division must use `norm_num [zoneQ]`; `decide` computes only for integer arguments.
--   (3) `rw [← zoneQ_inverted_iff]` **does not unfold the def `InvertedRegion`** (`rw` does not use defeq);
--       one must first `show` the unfolded form, whereas `exact (…).mp/.mpr` does use defeq and has no such limitation.
example : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
example : InvertedRegion ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) := by
  have h : Rat.zoneQ (1 : ℚ) 3 = Zone.inverted := by decide
  rw [Rat.zoneQ_eq_zone] at h              -- forward direction (see correction (1))
  exact (zone_eq_inverted_iff _ _).mp h

-- Shape example (I2: a rational literal involving division — **must use norm_num, not decide**,
--   see the measurement in R1 of proofs/probes/marcus-statement-skeleton.lean and in proofs/API-NOTES.md)
example : Rat.zoneQ (1 : ℚ) (3 / 4) = Zone.normal := by norm_num [Rat.zoneQ]
example : ¬ InvertedRegion ((1 : ℚ) : ℝ) (((3 : ℚ) / 4 : ℚ) : ℝ) := by
  show ¬ (((1 : ℚ) : ℝ) < (((3 : ℚ) / 4 : ℚ) : ℝ))   -- first show the unfolded form (see correction (3))
  rw [← Rat.zoneQ_inverted_iff]
  norm_num [Rat.zoneQ]

-- Shape example (I6: deciding "does not conform")
example : ¬ InvertedDescriptor 1 (-1/2) 1 1 :=
  descriptor_fails_of_nonpos_lam (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Shape example (I7: the non-physical branch satisfies the description but the rate is non-positive ⇒ the instance is rejected)
example : InvertedDescriptor (-1) (-1) 1 1 :=
  inverted_descriptor_holds_of_neg (by norm_num) (by norm_num) (by norm_num)
-- ⚠️ The passage below **does not hold as originally planned** (refuted by the measurement of the M5b owner):
--   `intro h; have := h 0; norm_num [rate, barrier] at this` gets stuck at
--   `h0 : Real.exp (1/4) < 0 ⊢ False` — `norm_num` reduced the hypothesis but **does not recognise the positivity of `Real.exp`**, so no contradiction can be derived.
-- A workable version (already past the gate):
example : ¬ (∀ x, 0 < rate (-1) (-1) 1 1 x) := by
  intro h
  have h0 := h 0
  have hb : barrier (-1) 0 = -(1 / 4) := by norm_num [barrier]
  rw [rate, hb] at h0
  norm_num at h0
  linarith [Real.exp_pos (1 / 4)]
```

### 8.3 Literature parameter table (the input of M5) — already backfilled (`proofs/LITERATURE.md` §candidate table of instance parameters)

> **⚠️ Quantitative warning (it fixes the boundary of the instance-layer wording and must be observed)**: substituting `lam=1.2` and `T=298.15 K` into the classical formula
> gives `x=2.0 → ΔG‡=0.1333` eV and `x=2.4 → ΔG‡=0.30` eV, with the relative rate falling from `5.6×10⁻³` to `8.5×10⁻⁶`
> (**about 5 orders of magnitude**), whereas **experiment drops only about 2 orders of magnitude** — i.e. **the classical formula falls too fast in the inverted region** (this is exactly
> the motivation for quantum vibrational corrections / Bixon–Jortner, see §1.3 and §14).
> Hence the conclusion of the instance layer may only be stated as: **"this system lies in the inverted region, and the classical Marcus model satisfies the inverted-region description at this (lam, x, T, A)"**;
> it must **not** be stated as "the inverted-region rate of this system decreases with the driving force" (that would be a claim about experiment, whose strictness the literature does not support).
>
> **Quantitative comparison using the literature's per-compound data (the sharpest evidence)**: within the same MCC series,
> with `x: 1.23 → 2.40` eV (`lam = 1.20` eV, `T = 296 K` ⇒ `k_BT = 25.51` meV),
> **the classical formula predicts a rate drop of 5.1 orders of magnitude** (`7.86×10⁻⁶`), while **the measurement drops only 1.46 orders of magnitude** (`3.5×10⁻²`)
> — the classical formula **falls too fast by about 3.6 orders of magnitude** (the pre-exponential factors are approximately equal; `2×10⁹` is the instrumental upper limit, so the measured drop is a lower bound and the direction is unchanged).
> This is exactly why quantum vibrational corrections exist (the smooth curve of Nobel Fig. 8 includes `ω = 1500 cm⁻¹`), and it is the price of listing them as "explicitly out of scope" in §1.3.

Convention `x := -ΔG°`; **the region decision uses only (lam, x) and is independent of T and A**. Only entries marked `已核实` (verified) enter Lean:

| System (sources: Marcus Nobel Lecture 1992 figures/text and C&EN 1984-06-04 62(23):42–44; each entry located in `proofs/LITERATURE.md`) | `lam`/eV | `x = -ΔG°`/eV | measured `k`/s⁻¹ | decision |
|---|---|---|---|---|
| MCC biphenyl–androstane–2-naphthyl (10 Å, pulse radiolysis) | 1.20 | 0.05 | ≈ 1.5×10⁶ | **deep normal region** |
| MCC same (optimal/barrierless point) | 1.20 | 1.23 | ≳ 2×10⁹ (instrumental upper limit) | **near the optimal/barrierless point**; formally still **strictly inside the inverted region** (model `ΔG‡ = 0.0001875` eV ≈ literature 0.0002 eV ⇒ `x > lam` holds strictly) |
| MCC same (2-(5,6-dichlorobenzoquinonyl)) | 1.20 | 2.40 | ≈ 7×10⁷ | **clearly in the inverted region** |
| MCC same (read off the left branch of Nobel Fig. 8) | 1.20 | 0.60 | — | **normal region** |
| Photosynthetic reaction centre BPh⁻→BChl₂⁺ back transfer | 0.25 | 1.10 | — | **inverted region** (`x ≫ lam`) |

> **Treatment of temperature (literature correction)**: the C&EN caption says **296 K**, and the caption says THF while the text says MTHF (**the true temperature of the original was not verified**).
> ⇒ the instance layer must **not treat some particular temperature as an experimental fact**: `T` is an **explicit premise `0 < T`** (the region decision and the monotonicity are independent of the concrete value of `T`);
> if some instance needs a concrete number, write "for this instance we take T = 296 K as a **modelling choice**".

Basic constants (**exact values**; after the 2019 SI both `k_B` and `e` are exact): `k_B·T(298.15 K) = 0.025693` eV.
The instance layer writes "for this instance we take T = 298.15 K as a **modelling choice**; only `0 < k_B*T` is needed" —
**do not claim that 298.15 K is the true temperature of some experiment** (the region decision and the monotonicity are independent of the concrete value of T).

Planning constraint: the literature is used only to **fix parameter values**, never to replace a proof; entries that are `仅量级` (order of magnitude only) **do not enter Lean**.
Every parameter is annotated with its verification status (`已核实` / `凭记忆待人类复核` / `仅量级`).

**The instance layer must explicitly assert the physical domain of definition** (a boundary raised by the verifier during the M1/M4b acceptance): if an instance uses `lamOuter`,
the instance theorem must explicitly carry the domain premises `0 < a1`, `0 < a2`, `a1 + a2 ≤ R`, etc. —
because the premises of `lamOuter_pos` do not mathematically rule out negative radii or a negative separation (the conclusion remains true),
so **the geometric conventions are not inside the Lean statement** and can only be asserted by the instance layer itself.

**Acceptance**: `check.sh --strict PhotoLean.Marcus.Instances` PASS; each item clean under `axioms.sh`;
**the verifier must confirm that the "decision" for every instance is really given by `decide` / theorem instantiation**, and not merely claimed in a comment.

---

## 9. Proof dependency graph (critical path in bold)

```text
M1 Basic ──► **M2 Barrier** ──► **M3 Rate** ──► **M4a Sharp** ──► M4b Reorg
   │
   ├──► M5a RatModel ──────────────┐
   └──────────────────────────────►┴──► M5b Instances
```

- Only M4a depends on M3; only M4b and I6/I7 of M5b depend on M4a.
- M5a (the ℚ decision layer) and M4b (the microscopic λ) **depend only on M1**; they are the two side branches running in parallel with the critical path.

---

## 10. Sprint order and parallel boundaries

**Principle**: tackle the least formalizable step first (critical-path method). The risk of this project is concentrated in two places:
(a) the name and direction of the monotonicity API for `Real.exp` (M3); (b) the division-by-zero convention at `λ = 0` in the necessity direction of sharpness (M4a).
**Both are scheduled at the very front**: Sprint 1 must push them through, rather than waiting for M2 to be all green.

| Sprint | Content | Owner (exclusive file) | Parallelism |
|---|---|---|---|
| **S0 (wrapped up)** | `plan.md` written to disk ✅, the statement skeleton `proofs/probes/marcus-statement-skeleton.lean` compiles (31 unfinished-proof placeholders / 0 errors) ✅, `git init` + baseline commit ✅, API calibration (`api_researcher`, in progress), literature parameters (`literature_researcher`, in progress) | lead | 3 tracks (lead + 2 researchers) |
| **S1** | M1 `Basic.lean` (start of the critical path); M4b `Reorg.lean` (**zero dependencies**, imports Mathlib only, can start together with Basic) | prover_a / prover_d | 2 parallel tracks (disjoint files) |
| **S2** | M2 `Barrier.lean` (critical path); the **core lemmas** of M3 `Rate.lean`: `rate_gt_of_barrier_lt` + `rate_pos` (depend on M1 only); M5a `RatModel.lean` (depends on M1 only) | prover_a / prover_b / prover_c | 3 tracks |
| **S3** | finishing M3 (the three rate theorems, depending on M2); I1–I3 of M5b `Instances.lean` (depending on M1+M5a) | prover_b / prover_c | 2 tracks |
| **S4** | M4a `Sharp.lean` (the `(⟸)` direction first, then the two necessity branches) | prover_a | 1 track (critical path) |
| **S5** | M4c `Compose.lean` (depends on Sharp+Reorg); I4–I7 of M5b (depend on the literature table + Sharp) | prover_d / prover_c | 2 tracks |
| **S6** | full acceptance + per-lemma commit review + experience-bank write-back + archiving of the literature/API logs | verifier + lead | — |

**Hard parallelism constraint**: one owner per file at a time; a cross-Sprint handover = verifier PASS + the lead updating
the owner column of `proofs/TASKS.md`. Any `BLOCKED` is immediately written back to `EXPERIENCE.md` (including the failed path).

**Engineering support (the lead's responsibility)**: the `defaultTargets` of `lakefile.toml` are extended with every delivered module at each milestone
(otherwise a bare `check.sh --strict` builds only `PhotoLean.Smoke` — **the scan covers the whole directory but the build does not**,
an acceptance loophole that must be plugged); the `proofs/probes/` directory is created together with S0.

---

## 11. Acceptance criteria (script level, not left to self-discipline)

For every theorem of every milestone, execute the four steps of contract §3 one by one:

```bash
proofs/scripts/lake build <Module>                            # 1. compile
proofs/scripts/check.sh --strict <Module>                     # 2. unfinished-proof-placeholder / custom-axiom scan + build
proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>   # 3. #print axioms contains only infrastructure axioms
git log -1 --oneline                                          # 4. feat(<area>): <lemma>
```

- **No step may be skipped**: `lake build` **returns 0 for both** unfinished-proof placeholders and custom axioms (see the first measured entry of `proofs/EXPERIENCE.md`).
- Extra requirement for M5: the decision evidence of an instance must be `by decide` or a theorem instantiation; the verifier re-examines each one.
- Extra requirement for M4a: the verifier independently re-examines the two necessity branches of `descriptor_sharp` (`λ = 0` and `λ < 0`).

---

## 12. mathlib adaptation checklist (handed to `api_researcher` to settle item by item → `proofs/API-NOTES.md`)

| Class | Checklist | Purpose |
|---|---|---|
| exp layer | `Real.exp_lt_exp` (**direction**), `Real.exp_le_exp`, `Real.exp_pos`, `Real.exp_neg`, `Real.exp_sub`, `Real.exp_zero`, `Real.exp_strictMono` | M3 core lemma, `rate_ratio` |
| division/order | `div_lt_div_of_pos_right`, `div_lt_div_iff_of_pos_right`, `div_lt_iff`, `lt_div_iff`, `div_pos`, `one_div_pos`, `neg_lt_neg_iff`, `div_eq_mul_inv` | M2/M4b |
| square monotonicity | `sq_lt_sq` (shape/absolute value), `pow_lt_pow_left₀`, `mul_self_lt_mul_self`, `sq_pos_of_ne_zero`, `sq_nonneg` | all of M2 |
| multiplication/order | `mul_lt_mul_of_pos_left`, `mul_pos`, `pos_of_mul_pos_right` | M3/M4a |
| ℚ layer | `Rat.cast_lt`, `Rat.cast_le`, `Rat.cast_pos`, `Rat.cast_inj`; whether `by decide` can compute `(1:ℚ) < 3` | M5a transfer lemma |
| tactics | `positivity`, `nlinarith`, `norm_num`, `ring_nf`, `field_simp`, `gcongr` | all |

**Rule**: every item of this table must be checked off by `api_researcher` after an actual `#check` measurement in
`proofs/probes/marcus-*-api.lean`; **a name that has not been measured may not appear in a proof**.

---

## 13. Key references and explicit physical approximations

**References** (already backfilled by `literature_researcher`; item-by-item verification in `proofs/LITERATURE.md`):
**Marcus 1960** (Discuss. Faraday Soc. 29, p.28 §(v): **the first proposal of the inverted region**),
**Marcus 1956** (Eq. (38) p.974: the barrier formula; p.971: the explicit definition of `D_op = n²` ⇒ this formalization's direct use of `nSq` is **faithful** rather than a simplification),
Marcus 1992 Nobel Lecture (Eq. (5b) p.78, the printed barrier formula; Eq. (6)/(7)),
Miller–Calcaterra–Closs 1984 (**DOI 10.1021/ja00322a058**, JACS 106(10) 3047–3049: experimental evidence for the inverted region).
⚠️ **Full text not obtained** (equation numbers may not be cited): Marcus & Sutin 1985 (Elsevier paywalled), Marcus 1964 (403) —
the simplified work-term expression is supported only by secondary sources, but the conclusion is unaffected (we adopt `w_r = w_p = 0`,
a simplification that was verified verbatim from 1992 Eq. (5b)).
⚠️ **Attribution correction**: `(4πλk_BT)^(-1/2)` is **not** in Marcus 1956 (1956 has `k = Z·exp(-ΔF*/kT)`, with `Z` = collision number).

**Physical approximations that must be made explicit (theorem premises, not hidden in definitions)**:

| # | Approximation | Form in Lean |
|---|---|---|
| 1 | Parabolic (harmonic) potential-energy surfaces, single reaction coordinate | the definition of `barrier` itself (declared in the plan) |
| 2 | Classical nuclear motion (no nuclear tunnelling) | the rate takes the Arrhenius form `A·exp(-ΔG‡/(kBT))` |
| 3 | Condon approximation / electronic coupling independent of the nuclear coordinates | the pre-exponential factor `A` is independent of the driving force `x` (the definition of `rate`) |
| 4 | Positive temperature, `k_B > 0` | **the delivered statements actually use the product form** `hkT : 0 < kB * T` (see `Rate.lean`/`Sharp.lean`); the physical reading `0 < kB ∧ 0 < T` is **stronger**, so using the product is a **weaker** premise ⇒ a stronger conclusion. ⚠️ This also means that the non-physical assignment `kB < 0 ∧ T < 0` **formally** satisfies that premise as well (in the sharp characterization the `⟺` is stated only over `A`, `lam`; see the precision note in §7.1) |
| 5 | The rate constant is positive (positive pre-exponential factor) | theorem premise `0 < A` (**M4a proves that it cannot be dropped**) |
| 6 | The reorganization energy is positive | theorem premise `0 < λ`, **derived** in M4b from `λ_in + λ_out` and positivity of the Pekar factor |
| 7 | Two-sphere continuum model for the outer-sphere reorganization energy | the definition of `lamOuter` + premises `0 < nSq`, `0 < εs`, `1/εs < 1/nSq`, `hgeom` |
| 8 | **work terms set to zero**: `w_r = w_p = 0` (the review-level complete expression contains `w_r, w_p`; this formalization implicitly sets them to 0) | written explicitly into the documentation and the theorem comments; keeping them later would require new premises |
| 9 | The pre-exponential factor is independent of the driving force | the definition of `rate` (`A` does not depend on `x`). **Robustness remark**: if one instead used the TST pre-exponential factor `(4·π·lam·τ)^(-1/2)·κ·ν`, it is merely a **positive** factor independent of `x` ⇒ all monotonicity and sharpness conclusions are **unchanged** (literature §appendix) |
| 10 | **The decision at `lam = 0` relies on Lean's division-by-zero convention `x / 0 = 0`** | **a formal convention, not a physical fact**: this convention makes `barrier 0 x = 0` (hence `rate ≡ A`, see `barrier_zero_lam`), and the `lam = 0` necessity branch of M4a (`sharp_lam_pos_of_eq`) rests on it. If sharpness is presented externally as a "physical conclusion", this item must be declared at the same time — a boundary raised by the verifier during the M2 acceptance (finding D) |

---

## 14. Next stops after completion (preview; outside the scope of M1–M5; ordering rationale in `proofs/LITERATURE.md` §ordering of the inexpressible list)

**Priority (by "impact on M1–M5 × implementation cost")**:
① **Franck–Condon factors / vibrational overlap integrals** — zero impact on M1–M5, but the immediate prerequisite of quantum corrections,
and mathlib already has reusable `Lp`/Hilbert-space/special-function foundations ⇒ **low cost, high benefit; do it first**;
② the Marcus cross relation — formally an algebraic identity over `Real.sqrt` (**expressible**), but the real obstacle is that it relies on a "same `lam`" assumption
⇒ if it is done at all, it must be written as a **premise** rather than a theorem (**the cheapest item and the one most likely to yield an over-strong claim**);
③ Fermi golden rule + infinite summation over the vibrational heat bath — requires building a partition-function layer (absent from mathlib) after ①;
④ exponential decay of the electronic coupling / superexchange — no application layer for quantum-mechanical spectral theory;
⑤ **first-principles derivation of solvent electrostatics — recommended to be excluded permanently** (no PDE/boundary-value-problem library in mathlib; keeping `lamOuter` as a definition is the right call).

**Dimensional warning**: mathlib has no unit system, so **dimensional errors are not caught by the kernel** —
they can only be checked by comments at the instance layer and by human eyes on `#check` (§13).


- **Quantum vibrational corrections**: Bixon–Jortner-type rate (the vibrational-mode sum makes the inverted region saturate) — it needs infinite series and a
  vibrational partition function, and it is the next step for "why the inverted region is weakened in experiment".
- **Quantifying the temperature dependence**: the full thermodynamic form of `rate_ratio` and explicit expressions for the activation parameters.
- **The Marcus cross relation** and the exponential decay of the electronic coupling (`V(R) = V₀ exp(-β(R-R₀))`).
