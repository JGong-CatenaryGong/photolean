# RESULTS.md — Formalizing the Marcus inverted region: machine-checkable answers to a three-part request

> *English translation of `theories/Marcus/RESULTS.md`. The Chinese original at `theories/Marcus/RESULTS.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

> This file is the **answer to a human question** (it is not the engine's leaf data plane). For the contract and the plan see `proofs/ENGINE.yml`
> and `theories/Marcus/plan.md`; the authoritative source of status is `theories/Marcus/TASKS.md`; acceptance evidence is produced by `proofs/scripts/*.sh`.
>
> Question: *"How can the Marcus inverted-region theory be formalized into a theory that can be proved or verified with Lean?
> This work falls into three parts: first, turn the Marcus inverted region into a formal description;
> second, prove this description, or find the conditions under which it holds;
> third, plug some instances into this formalized theory and decide whether each instance conforms to the description of the Marcus inverted region."*
>
> This document answers these three parts point by point, and **every conclusion can be re-checked by a command inside the repository.**

---

## Summary (read this section first)

| Your question | Answer | Re-checkable evidence |
|---|---|---|
| ① How do we turn the inverted region into a formal description? | `PhotoLean/Marcus/Basic.lean`: the barrier `(lam-x)²/(4·lam)`, the rate `A·exp(-ΔG‡/(kB·T))`, the region predicates, the **descriptor predicate** `InvertedDescriptor`, and the decidable classifiers `Zone`/`zone` (§1) | `marcus-fidelity.py`: **51/51 verbatim agreement** with the authoritative statements |
| ② Does this description hold? What are the conditions for it to hold? | **It holds, and the condition is sharp**: `(the rate is everywhere positive ∧ descriptor) ⟺ 0 < A ∧ 0 < lam` (`descriptor_sharp`). A microscopic chain is also given: `lam = lamIn + lamOut`, positivity of the Pekar factor, and the geometric factor derivable from "the two spheres do not overlap" ⇒ the descriptor holds (§2) | All 70 theorems pass `check.sh --strict`; `marcus-all-axioms.lean` is **70/70 axiom-clean** (0 unfinished proofs / 0 custom axioms) |
| ③ Do the instances conform once substituted? | **The literature MCC system (`lam=1.20` eV) and the photosynthetic reaction center (`0.25` eV) conform under the classical model**: region decision + instantiation of the descriptor operator + **rate comparison `rate(2.40) < rate(1.23)`** (and independent of temperature); non-physical parameters are judged **non-conforming / inadmissible** (§3) | Every instance is a **named theorem**; the lead independently recomputed each of them in Python |
| Boundary (must be reported together) | In the inverted region the classical formula **falls too fast by about 3.6 orders of magnitude** (predicted 5.1 vs measured 1.46) ⇒ the instance conclusions only claim that the "**classical model**" satisfies the descriptor; they do not claim to predict the measured rates (§3.4, §4) | The model numbers and the measured literature rates are shown side by side and can be recomputed |

**Scale** (**Marcus-theory scope**; snapshot at the closing commit `6ebcff3`, 2026-09-20 — the point at which every verifier verdict was recorded): 8 modules / **70 theorems** (12 declarations + 70 theorems = 82 delivered declarations); **47 per-lemma commits** in the contract template (reproduce with `git log --oneline --grep='^feat(' -- PhotoLean/Marcus | wc -l`).

> **Counting convention**: this file cites **theory-scoped** numbers only (modules / theorems / commits) and does **not** quote repository-wide commit totals — this repository hosts several theories side by side under `theories/`, so a repository-wide total keeps growing as the other theories advance and would make this file age badly. For the same reason the `45/45` / `51/51`-style counts above each carry their own timestamp.
Zero unfinished proofs, zero custom axioms.

**Three-layer acceptance (one command per layer, all re-runnable)**:

| Layer | Command | Result |
|---|---|---|
| Build + whole-tree scan | `proofs/scripts/check.sh --strict` | **verdict: PASS** (`clean`) |
| Statement fidelity | `python3 theories/Marcus/probes/marcus-fidelity.py` | **51/51 verbatim agreement, 0 discrepancies** (this checker has itself been validated in the reverse direction) |
| Axiom discipline | `proofs/scripts/lake env lean theories/Marcus/probes/marcus-all-axioms.lean` | **70/70 pass, 0 error**: 69 × `[propext, Classical.choice, Quot.sound]` + 1 × `[propext]` |

**Independent acceptance (verifier, a read-only role, milestone by milestone)**: **all 8 module groups have passed** —
M1 · M2 · M3 · **M4a (the main theorem)** · M4b (including added items) · **M4c** · M5a (including the numeric bridge) · **M5b (judged simultaneously by two independent verifiers)**.
The verdicts and the itemized evidence are in the "acceptance record" table of `theories/Marcus/TASKS.md`; the task board has **45 rows all done / 0 rows awaiting acceptance**.

**Known deviations (registered truthfully, nothing concealed)**:
1. **`barrier_nonneg` has no separate commit** — its content was absorbed into `c000996` by an accident during one of the lead's `git add -A` runs; this is registered on the task board and in the experience bank, and **no make-up commit was fabricated**.
2. **Commit granularity of M5b** — 31 theorems are packed into 6 commits (2/4/12/4/4/5), which does not satisfy the iron rule of "one commit per lemma" (dispatch allowed "semantic batches", but that conflicts with the iron rule).
3. **The 31 theorems of `Instances.lean` are not in the authoritative skeleton** — the skeleton is the authority for **theory statements**, whereas the instance-judgment theorems are the **evidence layer** with concrete parameters (plan §8.2/§8.3 specifies their shape, not each statement). The fidelity check (51/51) therefore **does not cover these 31**; they were checked item by item against the plan by two independent verifiers, and additionally cross-validated at the definition level.
   Arithmetic: 82 delivered declarations = 12 definitions + 70 theorems; the 51 skeleton statements (12 definitions + 39 theorems) match them verbatim, and **the remaining 31 are exactly the instance theorems of `Instances.lean`** (31 + 51 = 82 — nothing missing, nothing extra).
4. **Six statements that were outside the skeleton and have now been backfilled** — the four necessity kernels of `Sharp.lean` (`sharp_A_pos` / `sharp_lam_pos_of_lt` / `sharp_lam_pos_of_eq` / `sharp_lam_pos`, i.e. the three-branch decomposition) and the two numeric bridges of `RatModel.lean` (`barrierQ_cast` / `barrierQ_zero_lam`): they were **both outside the skeleton and unnamed by the two items above** (the source of an earlier accounting gap in this file). They were **backfilled into the skeleton on 2026-09-20** (45 → 51 statements); after backfilling they match the delivered signatures **verbatim**, so the fidelity check now covers them.

---

## 0. One-sentence conclusion

The classical Marcus inverted region is formalized as "**monotonicity of the rate over a parabolic barrier**", and its **condition for holding is sharp**:

```
(∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T   ⟺   0 < A ∧ 0 < lam
```

That is: **as long as the pre-exponential factor is positive and the reorganization energy is positive** (positive temperature being an explicit physical premise), "the larger the driving force, the smaller the rate" holds in the inverted region; **no item can be dropped** — this is not our assertion but a proved equivalence, in which "positivity of the rate" must be **conjoined into the left-hand side** for it to be a necessary and sufficient condition (see the planning-time discovery and the counterexample in §2.3).

**Zero unfinished proofs, zero custom axioms**: the `#print axioms` of every delivered theorem contains only
`propext` / `Classical.choice` / `Quot.sound`. The verdict is executed by a script, not self-reported by the model.

---

## 1. Part one: turning the "Marcus inverted region" into a formal description

**Carrier**: elementary algebra over `ℝ` plus one real-analysis tool (monotonicity of `Real.exp`). No new kernel objects are built, no new axioms introduced.

### 1.1 Objects of the description layer (`PhotoLean/Marcus/Basic.lean`)

| Formal object | Definition | Physical meaning |
|---|---|---|
| `barrier lam x := (lam - x)^2 / (4*lam)` | barrier | `ΔG‡ = (λ - x)²/(4λ)`, where `x := -ΔG°` is the driving force and `lam := λ` is the reorganization energy |
| `rate A lam kB T x := A * Real.exp (-(barrier lam x) / (kB*T))` | rate | Arrhenius/Eyring type; `A` the pre-exponential factor, `kB*T` the thermal energy |
| `InvertedRegion lam x := lam < x` | inverted region | the driving force exceeds the reorganization energy |
| `NormalRegion lam x := x < lam` | normal region | the driving force is smaller than the reorganization energy |
| `InvertedDescriptor A lam kB T := ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate … x₂ < rate … x₁` | **inverted-region descriptor** | inside the inverted region the rate is **strictly decreasing** in the driving force |
| `NormalDescriptor` | dual predicate | inside the normal region the rate is **strictly increasing** in the driving force |
| `Zone` (`normal`/`barrierless`/`inverted`) + `zone : ℝ → ℝ → Zone` | region classifier | classifies `(lam, x)` into the three regions (`x = lam` is the barrierless point) |

**Three key design decisions** (all driven by measurement, not by stylistic preference):
1. **The description is written as a predicate, not as "a theorem about one curve"** — because "finding the conditions for it to hold" requires `¬ InvertedDescriptor` (counterexample decision) and conjunction (positivity), and the predicate form makes both expressible; the classifier in turn turns "deciding which region an instance belongs to" into a **computable equality**.
2. **All Lean identifiers are ASCII** (`lam` rather than `λ`) — in Lean 4, `λ` is the lambda keyword and **cannot be used as an identifier** (a measured parse error).
3. **The division-by-zero convention is declared explicitly** — `barrier 0 x = 0` (because Lean takes `x/0 = 0`). This single convention creates the degenerate branch `lam = 0`, which is the branch most easily missed in the "sharpness" proof (see §2.3).

### 1.2 The decision layer (`PhotoLean/Marcus/RatModel.lean`)

The order on `ℝ` is not computable (it requires `Classical`), so a **computable** copy of the classifier is made over `ℚ`:

```lean
def zoneQ (lam x : ℚ) : Zone := if x < lam then .normal else if x = lam then .barrierless else .inverted
theorem zoneQ_eq_zone (lam x : ℚ) : zoneQ lam x = zone (lam : ℝ) (x : ℝ)   -- transfer lemma
```

**The transfer lemma is the only bridge that makes "instance decisions" binding on the `ℝ` theory**: the decision value computed by the kernel over `ℚ` is carried by it up to the `ℝ` theorem layer. Measured boundary (`proofs/API-NOTES.md`): `decide` works on **integer** literals, but on **rational** literals **containing division/decimals** it gets stuck in `Rat`'s gcd reduction → `norm_num` must be used.

---

## 2. Part two: proving the description and finding the conditions under which it holds

### 2.1 Barrier algebra (`PhotoLean/Marcus/Barrier.lean`, 9 items)

The **complete monotonicity picture** of `barrier` (three signs of `lam` × two regions):

| Case | Conclusion | Theorem |
|---|---|---|
| `0 < lam`, inverted region | the barrier is **strictly increasing** (the algebraic core of the inverted region) | `barrier_mono_of_pos` |
| `0 < lam`, normal region | the barrier is **strictly decreasing** | `barrier_antitone_of_pos` |
| `lam < 0`, inverted region | the direction is **reversed**: the barrier decreases (a necessary branch for sharpness) | `barrier_antitone_of_neg` |
| `lam = 0` | the division-by-zero convention ⇒ the barrier is identically zero (the other necessary branch) | `barrier_zero_lam` |
| `0 < lam` | a **global minimum** at `lam` (the barrierless point) + parabolic symmetry | `barrier_min_at_lam`, `barrier_symm` |
| all | nonnegativity, zero at `lam`, exhaustiveness of the four cases | `barrier_nonneg`, `barrier_at_lam`, `barrier_mono_cases` |

### 2.2 The rate layer (`PhotoLean/Marcus/Rate.lean`, 6 items)

The **only real-analysis risk** in the whole project is isolated in a single lemma:

```lean
theorem rate_gt_of_barrier_lt (hA : 0 < A) (hkT : 0 < kB * T) (h : barrier lam x < barrier lam y) :
    rate A lam kB T y < rate A lam kB T x
```

The other five are all combinations of "barrier monotonicity + this lemma": `rate_pos` (the rate is positive), `normal_rate_increases` (the rate rises in the normal region),
`inverted_rate_decreases` (**the rate falls in the inverted region**), `rate_peak_at_lam` (the peak is at `x = lam`),
`rate_ratio` (the exponential form of the suppression factor, a stretch item).

### 2.3 The condition for it to hold: a sharp characterization (`PhotoLean/Marcus/Sharp.lean`, 9 items)

**Main theorem**:

```lean
theorem descriptor_sharp {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (A lam : ℝ) :
    ((∀ x : ℝ, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ↔ 0 < A ∧ 0 < lam
```

**Planning-time discovery (the physical core of this project)**: if one writes only `InvertedDescriptor` (without the positivity conjunct),
it **cannot** imply `lam > 0` — counterexample `A < 0 ∧ lam < 0 ∧ kB*T > 0`: `lam<0` makes the barrier **decreasing** in the inverted region,
so `exp(-Φ/(kBT))` is increasing and, multiplied by a negative `A`, becomes **strictly decreasing** ⇒ the descriptor holds, **but the rate is negative**.
Hence "positivity of the rate" must be conjoined into the characterization. This counterexample is kept as a theorem, as evidence:

```lean
theorem inverted_descriptor_holds_of_neg (hA : A < 0) (hkT : 0 < kB * T) (hlam : lam < 0) :
    InvertedDescriptor A lam kB T          -- the descriptor holds (but the rate is non-positive ⇒ inadmissible)
```

**The three-branch structure of necessity** (checkable item by item; the `lam = 0` branch is covered **separately** and is never confused with the `lam < 0` branch):

| Branch | Core | Mechanism |
|---|---|---|
| rate positive ⇒ `A > 0` | `sharp_A_pos` | at `x = lam` we have `0 < A * exp(…)` and `exp > 0` |
| `lam < 0` ⇒ contradiction | `sharp_lam_pos_of_lt` | decreasing barrier ⇒ increasing rate, conflicting with the decrease required by the descriptor |
| `lam = 0` ⇒ contradiction | `sharp_lam_pos_of_eq` | the division-by-zero convention ⇒ the rate is identically `A` ⇒ we get `A < A` (**with no positivity premise at all in the signature**) |
| assembly | `sharp_lam_pos` | `rcases lt_trichotomy lam 0` on the three true branches |

The proof term printed by `#print` confirms that all three branches occur in the term; the instantiation `¬ InvertedDescriptor 1 0 1 1`
at `lam = 0` is produced by the kernel and necessarily passes through the middle branch. Companions: `inverted_descriptor_holds`, `normal_descriptor_holds`,
`descriptor_fails_of_nonpos_lam` (`lam ≤ 0` ⇒ the descriptor fails).

### 2.4 Making the condition "microscopic" (`PhotoLean/Marcus/Reorg.lean` + `Compose.lean`)

Downgrading `lam > 0` from an **assumption** to a **derivation**:

```
lam = lamIn + lamOut
lamOut = dE² · (1/(2·a1) + 1/(2·a2) - 1/R) · (1/nSq - 1/epsS)      -- two-sphere continuum (Pekar form)
```
- `lamInner_nonneg` / `lamInner_pos` / `lam_total_pos`: the inner part is nonnegative (it may be zero);
- `lamOuter_pos`: **positivity of the Pekar factor** (`1/epsS < 1/nSq` ⟺ `n² < ε_s`) **plus** positivity of the geometric factor ⇒ the outer part is positive;
- `hgeom_of_nonoverlap`: positivity of the geometric factor can in fact **be derived from "the two spheres do not overlap"** (`a1 + a2 ≤ R` ⇒ `1/R < 1/(2a1)+1/(2a2)`),
  i.e. an assumption is turned into a **derivation**;
- `descriptor_holds_of_microscopic`: microscopic positivity ⇒ the premises of the main theorem hold ⇒ **the inverted-region descriptor holds**.

**Honest boundary**: the additivity of `lam = lamIn + lamOut` is a **modeling assumption** (coming from splitting the coordinate set into an inner and an outer part plus factorizing the partition function);
it is not a theorem. The Pekar formula is given as a **definition/premise**, and no first-principles derivation of solvent electrostatics is attempted (see §5).

### 2.5 Acceptance (script-level, not self-reported)

```bash
proofs/scripts/check.sh --strict <Module>                     # build + whole-tree scan for unfinished proofs / assumed axioms
proofs/scripts/axioms.sh <Module> <fully.qualified.theorem>   # #print axioms contains only infrastructure axioms
```
Returning 0 from `lake build` **does not** constitute a pass (unfinished proofs and custom axioms both return 0); the three layers (build + scan + `#print axioms`) must
all be in place and executed independently by a role that **does not write proofs**. The verifier verdicts and evidence for each milestone are in the "acceptance record" table of `theories/Marcus/TASKS.md`.

---

## 3. Part three: substituting instances and deciding

### 3.1 Decision mechanism (three independent chains of evidence)

| Chain | Form | Use |
|---|---|---|
| kernel computation | `by decide` (integer arguments) / `norm_num [Rat.zoneQ]` (containing division) | region decision at the `ℚ` layer |
| transfer lemma | `Rat.zoneQ_eq_zone`, `zoneQ_inverted_iff`, `normalRegion_of_zoneQ_normal`, `not_invertedRegion_of_zoneQ_normal` | carry the decision up to the `ℝ` theorem layer |
| theorem instantiation | `inverted_descriptor_holds`, `descriptor_fails_of_nonpos_lam`, `inverted_rate_decreases` … | decide whether an instance **satisfies the descriptor** |

### 3.2 Instances and their verdicts (`PhotoLean/Marcus/Instances.lean`)

| # | Instance | Verdict | Evidence |
|---|---|---|---|
| I1 | `lam = 1, x = 3` (pure numbers) | **in the inverted region** | `decide` computes `zoneQ` + transfer lemma |
| I2 | `lam = 1, x = 3/4` | **not in the inverted region** (normal region) | `norm_num [zoneQ]` + the lemma excluding the inverted region |
| I3 | the barrierless point of the literature MCC series, `lam = 1.20, x = 1.23` | **in the inverted region** (on the boundary side); and `barrier 1.20 1.23 = 0.0001875` **agrees with `ΔG‡ ≈ 0.0002 eV` in the literature** | `norm_num [barrier]` + transfer lemma |
| I4 | the highly exergonic branch of the literature MCC series: `x = 2.40` (and `2.00`) | **clearly in the inverted region** | literature parameters + transfer lemma |
| I5 | the normal branch of the literature MCC series: `x = 0.60` | **not in the inverted region** (normal region) | as above + the lemma excluding the inverted region |
| I6 | the literature photosynthetic reaction center: `lam = 0.25, x = 1.10` | **deep in the inverted region** (`x ≫ lam`) | as above |
| I7 | non-physical parameters `lam = -1/2` | **does not satisfy the inverted-region descriptor** | `inst_I7_nonpos_lam_not_descriptor` (an instantiation of `descriptor_fails_of_nonpos_lam`) |
| I7′ | non-physical branch `A = -1 ∧ lam = -1` | **inadmissible** | `inst_I7_unphysical_descriptor` (the descriptor **holds formally**) + `inst_I7_unphysical_rate_not_pos` (the rate is not positive: `rate … 0 = -exp(1/4) < 0`) + the summary verdict `inst_I7_unphysical_not_admissible` — this is checkable evidence that the **positivity premise cannot be dropped** |

> Every instance is a **named theorem** (each can be checked individually by `axioms.sh`), not a claim in a comment.

### 3.2b "Descriptor-operator instantiation" of the literature parameters (the most direct "does it satisfy the descriptor" decision)

| Theorem | Content | Basis |
|---|---|---|
| `inst_I4_mcc_descriptor_any_kT` | for **any** `kBT > 0`, the inverted-region descriptor **holds** at the MCC parameters `lam = 1.20` | instantiation of `inverted_descriptor_holds` |
| `inst_I4_mcc_descriptor` | as above (the concrete corollary with `kB = T = 1`) | as above |
| `inst_I4_mcc_admissible` | the above instance is **admissible** (the descriptor holds ∧ the rate is everywhere positive) | as above + `rate_pos` |
| `inst_I6_rc_descriptor_any_kT` | the descriptor holds at the photosynthetic reaction center `lam = 0.25` (any `kBT > 0`) | as above |
| `inst_I4_mcc_rate_drop` | **the signature conclusion of the inverted region**: `rate(1.20, 2.40) < rate(1.20, 1.23)` (**independent of `kBT`**) | instantiation of `inverted_rate_decreases` |
| `inst_I5_mcc_rate_rise` | normal region: `rate(1.20, 0.60) < rate(1.20, 1.20)` (rising up to `x = lam`) | instantiation of `normal_rate_increases` |
| `inst_I3_rate_peak` | peak position: `rate(1.20, 2.40) ≤ rate(1.20, 1.20)` | instantiation of `rate_peak_at_lam` |

> **`kBT` is a universally quantified variable, not a claim in a comment** — writing `kBT > 0` as an explicit premise of the theorem makes
> "**the decision is independent of temperature**" **part of the statement** (which is exactly what answers the literature's reservation that the temperature of the original work was not verified).

### 3.3 Literature parameters (checkable sources)

`lam = 1.20` eV (Miller–Calcaterra–Closs biphenyl–androstane–acceptor radical anion, 10 Å, `lam_s = 0.75 + lam_v = 0.45`);
`x = 1.23 / 2.00 / 2.40 / 0.60` eV; photosynthetic reaction center `lam = 0.25, x = 1.10` eV.
Item-by-item locations (figure/page/DOI) are in `theories/Marcus/LITERATURE.md`. The region decision **uses only `(lam, x)` and is independent of `T` and `A`**,
so `T` is an explicit modeling choice rather than an "experimental fact" (the temperature of the original work was not verified).

### 3.3b The lead's independent numerical cross-check (independent of any deliverer's self-report)

Computing directly from the definitions in Python (`ΔG‡ = (λ-x)²/(4λ)`, `k ∝ exp(-ΔG‡/k_BT)`), and comparing item by item with the Lean theorems:

| `x` at `λ = 1.20` eV | model `ΔG‡` / eV | `k/k(x=1.23)` (`k_BT = 1`) | corresponding Lean theorem | measured `k` / s⁻¹ in the literature |
|---|---|---|---|---|
| 0.60 | 0.075000 | 0.9277 | `inst_I5_mcc_rate_rise` (`rate(0.60) < rate(1.20)`) ✓ | — |
| 1.23 | **0.0001875** | 1 (reference point) | `inst_I3_barrier_value` (what Lean proves is exactly `0.0001875`) ✓ | ≳ 2×10⁹ (instrument limit) |
| 2.00 | 0.133333 | 0.8753 | `inst_I4_mcc_rate_drop_x200` ✓ | — |
| 2.40 | 0.300000 | 0.7410 | `inst_I4_mcc_rate_drop` (`rate(2.40) < rate(1.23)`) ✓ | ≈ 7×10⁷ |

`barrier 1.20 1.23 = 0.0001875` agrees with `ΔG‡ ≈ 0.0002 eV` from the literature (the optimal/barrierless point).

**Definition-level cross-validation (`theories/Marcus/probes/marcus-lead-crosscheck.lean`, which calls none of the delivered instance theorems)**:
the same batch of conclusions was **re-derived independently** — directly using `Real.exp_lt_exp` plus the barrier values (`norm_num [barrier]`) one proves
`rate(2.40) < rate(1.23)` (for any `kBT > 0`) and `rate(0.60) < rate(1.20)`,
as well as `barrier 1.20 1.23 = 0.0001875`, `barrier 1.20 2.40 = 0.3`, `barrier 1.20 2.00 = 2/15`, `barrier 1.20 0.60 = 0.075`.
In this way the conclusions at the instance layer do not depend on a "call chain": rather, **two independent paths lead to the same conclusion**.

**Quantitative comparison (`k_BT = 0.02551` eV @ 296 K)**: the classical model predicts `k(2.40)/k(1.23) = 7.87×10⁻⁶`
(**a drop of 5.1 orders of magnitude**); the measured literature value is `7×10⁷ / 2×10⁹ = 3.50×10⁻²` (**a drop of 1.46 orders of magnitude**).
⇒ the classical formula **falls too fast by about 3.6 orders of magnitude** (independently recomputed by the lead, in agreement with `literature_researcher`'s result).

### 3.4 ⚠️ Bounds on the wording of the instance layer (must be reported together with the conclusions)

Using the **per-compound measured rates** from the same body of literature for a quantitative comparison: for `x: 1.23 → 2.40` eV (`lam = 1.20` eV, `T = 296 K`),
**the classical formula predicts a rate drop of 5.1 orders of magnitude, while the measurement drops by only 1.46 orders of magnitude** — the classical formula **falls too fast by about 3.6 orders of magnitude**.
Therefore the verdict on an instance may **only** be phrased as:

> "the system lies in the inverted region, and the **classical Marcus model** satisfies the inverted-region descriptor at this `(lam, x, T, A)`",

and **must not** be phrased as "the inverted-region rate of this system decreases with the driving force" (that would be an assertion about experiment, and the literature does not support its strictness).
This is precisely the reason why quantum vibrational corrections (of Bixon–Jortner type) exist, and it is the part this project **explicitly does not do**.

---

## 4. What is explicitly not claimed (honest-boundary list)

1. **No claim to predict measured rates**: we only claim that the classical model satisfies the inverted-region descriptor at the given parameters (the quantitative comparison in §3.4).
2. **No claim about quantum effects**: no nuclear tunneling, no sum over vibrational modes; under the classical model the inverted region is a **strictly monotonically decreasing** regime.
3. **No competing reaction channels**: only a single mechanism is characterized (the original paper carries its own disclaimer: "unless a more favourable reaction mechanism is found").
4. **The `lam = 0` branch depends on the division-by-zero convention**: `x/0 = 0` is a **formal convention** in Lean, not a physical fact (already listed as item 10 of §13 of `theories/Marcus/plan.md`).
5. **Geometric conventions are not in the Lean statements**: the premises of `lamOuter_pos` do not mathematically exclude negative radii or negative separations ⇒ if the instance layer uses `lamOuter`,
   it must **explicitly assert the physical domain**.
6. **`zone_trichotomy` is weak**: it holds for any function `ℝ→ℝ→Zone`; what really pins down the semantics are the three `zone_eq_*_iff` lemmas
   (exhaustive and consistent). Documentation must not overstate the role of the former.
7. **Dimensions are not checked by the kernel**: mathlib has no unit system, so unit errors can only be caught by comments on instances and human review.

---

## 5. How to re-check (anyone can re-run)

```bash
cd <repo>
proofs/scripts/check.sh --strict                # whole-tree scan + build (should output verdict: PASS)
proofs/scripts/lake env lean theories/Marcus/probes/marcus-all-axioms.lean      # ★ one command that health-checks the axioms of all theorems
proofs/scripts/axioms.sh PhotoLean.Marcus.Sharp PhotoLean.Marcus.descriptor_sharp   # the axioms of a single theorem
proofs/scripts/lake env lean theories/Marcus/probes/marcus-statement-skeleton.lean           # the authoritative statements
```

**Statement fidelity (one command for the whole project)**: `python3 theories/Marcus/probes/marcus-fidelity.py` —
it compares **every declaration in the delivered files that appears in the authoritative skeleton** word for word against `marcus-statement-skeleton.lean`:
**51/51 agree, 0 discrepancies** (31 auxiliary declarations are not in the authoritative set — all of them in `Instances.lean`, i.e. the instance/evidence layer — and do not count as discrepancies).
This checker has been **validated in the reverse direction** (deliberately changing the conclusion `<` of `inverted_rate_decreases` into `≤` ⇒ it was caught and printed the comparison;
after restoring, it is back to 51/51) — a checker that cannot fail is worthless.

**Structural audit (is every definition/inductive constrained by at least one theorem?)** — one run of `python3 theories/Marcus/probes/marcus-name-audit.py`: all **12** `def`s/`inductive`s currently have references, so there is **no unconstrained definition**:
`barrier` (33), `rate` (29), `Zone` (20), `zoneQ` (18), `InvertedRegion` (17), `InvertedDescriptor` (16), `zone` (11), `lamInner` (6), `NormalRegion` (5), `lamOuter` (4), `barrierQ` (3), `NormalDescriptor` (1 — its own descriptor theorem).
During delivery this audit caught the **only** unconstrained definition, `barrierQ` (the M3+M5a verifiers found the same problem independently, as finding (b)); adding the numeric bridge `barrierQ_cast : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam:ℝ) (x:ℝ)` together with the degenerate point `barrierQ_zero_lam` closed the gap.

**Full health-check result (2026-09-20, 8 modules / 70 theorems)**: one run of `marcus-all-axioms.lean` outputs **70 lines of
`depends on axioms`, 0 error**; of these, **69 are exactly `[propext, Classical.choice, Quot.sound]`**,
and 1 (`inst_I1_zoneQ`) **depends only on `[propext]`** (a subset of the allowed set). **No `sorryAx`, no custom axioms,
no `Lean.ofReduceBool`** (that is, no `native_decide`). This probe is generated automatically by a script from the source tree, including `namespace` resolution,
and can be regenerated after new theorems are added.
The authoritative statements are `theories/Marcus/probes/marcus-statement-skeleton.lean` (all statements compile there first);
the signatures of `PhotoLean/Marcus/*.lean` are **verbatim identical** to it (at each milestone the verifier compared them mechanically with a script).

> **Concurrency note**: the scan of `check.sh --strict` covers the whole `PhotoLean/` tree. If someone is writing files at the same time, running the full gate bare may produce
> **transient FAIL/PASS**; the stable channel is the per-module `check.sh --strict <Module>`, and the final verdict must be re-run on a **frozen commit**.
