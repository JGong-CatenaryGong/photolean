# theories/BEP/plan.md — PhotoLean formalization plan: the Bell–Evans–Polanyi principle (B1–B5)

> Project: turn the **Bell–Evans–Polanyi (BEP) principle** into a *machine-checked* theorem set
> inside the equal-curvature two-parabola (Marcus-type) model of an elementary reaction step that
> this repository already uses for `PhotoLean/Marcus` (rates, inverted region) and
> `PhotoLean/Hammond` (transition-state structure).
> Target system: Lean 4.17.0 + mathlib v4.17.0 (`MODULE_PREFIX=PhotoLean`, see `proofs/ENGINE.yml`).
> Status: **draft for human confirmation** (layout + B1–B5); statement skeleton in preparation
> (`theories/BEP/probes/bep-statement-skeleton.lean`, owned by `api_researcher`). No proof work
> starts before the skeleton compiles.
> Authority: contract `proofs/ENGINE.yml`; board `theories/BEP/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/BEP/LITERATURE.md`.
> **Statement authority**: `theories/BEP/probes/bep-statement-skeleton.lean` — delivered signatures
> must match it word for word.
> Language policy: this file and every other proof-process artifact are **English**; the only
> bilingual file is `theories/BEP/RESULTS.md`.

---

## 1. Overall goal and boundaries

### 1.1 The physical claim being formalized

The empirical BEP principle says: for a **family of related elementary steps** (same bond being
made/broken, same mechanism, varying substituent), the activation barrier is *affine in the driving
force*,

```text
Ea  ≈  Ea₀ + α · (driving force),        α ∈ [0,1]      (Evans–Polanyi / Bell / Semenov)
```

with the slope `α` (transfer coefficient, Brønsted coefficient β, Leffler coefficient) empirically
near `1/2` for symmetric families and complementary between the two directions of the same step
(`α_f + α_r = 1`, the Brønsted relation). It is a **linear free-energy relation**, i.e. an
*approximation* with a definite domain of validity — not an identity.

This plan formalizes exactly that: the BEP *description* (B1), the *laws and their exact validity
conditions* (B2–B4), and *instance verdicts* decided by the kernel (B5).

### 1.2 The model (chosen, not derived) and the one structural subtlety

Same model as `PhotoLean/Hammond/Basic.lean`: reaction coordinate `q`, reactant well at `q = 0`,
product well at `q = 1`, harmonic surfaces of **equal** curvature `2λ`, transition state = the
**classical crossing point**. With driving force `x = -ΔG°` (exergonic: `x > 0`):

```text
Ea(x)   = (λ - x)² / (4λ)  =  λ/4 - x/2 + x²/(4λ)          barrier
q‡(x)   = (λ - x) / (2λ)                                    transition-state coordinate (Hammond)
```

**The subtlety this plan is built around.** The model barrier is a *parabola* in the driving force:
it is affine **only** when the quadratic remainder vanishes. So the honest formalization of BEP is
not "prove the line" but:

1. **BEP is a first-order (linear-response) law**: the tangent line at thermoneutrality is
   `bepLine λ x = λ/4 - x/2` (slope exactly `1/2` — Evans–Polanyi's empirical half), and the
   **exact violation is the quadratic remainder `x²/(4λ)`** (§5);
2. **the slope of that line is not a fit parameter but a model quantity**: `α = 1/2 - x/(2λ)`,
   which equals the transition-state coordinate `q‡` (the Leffler/Brønsted identification, §5) —
   so the *measured* BEP slope is the *structural* TS position;
3. **the description is exactly true only in the degenerate model** `λ = 0` (no barrier, no
   driving-force dependence) — i.e. exact BEP carries no content and conformance must be stated
   with a **tolerance and a window** (§6). The sharp region is the reorganization-energy radius
   `w* = 2√(λ·tol)`: inside it the linear law holds within `tol`, outside it the kernel exhibits a
   violation;
4. **the Evans–Polanyi bounds `0 ≤ α ≤ 1` have a sharp regime**: `α ∈ [0,1] ⟺ -λ ≤ x ≤ λ ⟺` the
   crossing point lies between the two wells `⟺` **neither direction of the step is in the Marcus
   inverted region** (§7) — a theorem that ties BEP to the already-delivered `PhotoLean/Marcus`
   theory instead of to a molecule's presumed virtue. **Naming caveat (literature round 1, §R1.7(iv))**:
   the phrase "Evans–Polanyi bounds" is a *model-side naming convention*; no source read in
   `theories/BEP/LITERATURE.md` states `0 ≤ α ≤ 1` as a law of chemical families — the literature
   analogue is the electrochemical transfer-coefficient bound (Inzelt p. 36), and documented series
   with a Brønsted coefficient outside `(0,1)` exist. The delivered statements are about the *model*
   coefficient `transfer`, and `RESULTS.md` must present them that way;
5. **a best-possible linear law exists and is not the tangent line**: on a symmetric window the
   minimax affine law is the tangent line shifted by `w²/(8λ)`, whose worst-case violation
   `w²/(8λ)` is *exactly half* the tangent line's `w²/(4λ)` (§6.4). This is the quantitative answer
   to "what is the best BEP line for this family?" — with a three-point equioscillation lower bound,
   not a fit.

### 1.3 Human request → milestones

| Human request | Milestone | Deliverable |
|---|---|---|
| ① turn BEP into a formal description | **B1** (description layer) | `PhotoLean/BEP/Basic.lean`: barrier, BEP line, exact defect, transfer coefficient and its reverse, observable secant slope, tolerance radius, minimax line, bound/window/exactness predicates, decidable regime classifier `epZone`, plus the nine `epZone` ↔ regime equivalences |
| ② prove the description / find its conditions | **B2** (law layer) | `PhotoLean/BEP/Criterion.lean`: the exact expansion, the exact defect law, thermoneutrality (`α = 1/2`, defect `0`), the mean-value identity (observable secant = coefficient at the window midpoint), the barrier-reversal identity, antitone barrier, non-negativity, non-vacuity |
| ②b the *sharp* conditions | **B3 + B4** (sharp + microscopic) | `PhotoLean/BEP/Sharp.lean`: `EPBounds ⟺ -λ ≤ x ≤ λ`, exactness `⟺ λ = 0`, non-affinity for every `λ ≠ 0` on any nontrivial window, the radius theorem `⟺ w ≤ 2√(λ·tol)`, λ-monotonicity of the defect, the minimax pair (attainment + optimality), hypothesis-necessity witnesses, an explicit tolerance failure. `PhotoLean/BEP/Compose.lean`: microscopic `λ = λ_in + λ_out` (Pekar-type), radius growth, and the cross-module bridges to `Marcus`/`Hammond` (`eact = Marcus.barrier`, `transfer = Hammond.tsCoord`, bounds ⟺ no inverted direction) |
| ③ plug in instances and decide conformance | **B5** (instances & verdicts) | `PhotoLean/BEP/RatModel.lean` (computable ℚ verdict layer: rational barrier/defect/coefficient/secant, two-point observable slope `α_obs`, two-point reorganization-energy solver `λ̂`, `decide`-checkable window conformance, verdict classifier, ℝ↔ℚ transfer lemmas) and `PhotoLean/BEP/Instances.lean` (kernel-checked verdicts I1–I11, including literature-sourced families and counterexample families) |

### 1.4 Explicit non-goals (scope control)

- **Not deriving the model.** That a real family is described by one scalar driving force, equal
  curvature `2λ` held fixed across the family, a classical crossing point as TS, and the Marcus
  reorganization form of `λ`, are **modeling assumptions** and appear as explicit premises or as
  documented scope limits (§13).
- **No claim that BEP is a law of nature.** The formalized content is: *conditional on the model*,
  the linear-free-energy description has exactly these properties and exactly this validity region.
  The empirical exceptions (curved BEP plots, inverted-region families, diffusion control,
  tunneling, family heterogeneity) are the *reason* for the tolerance/window formulation, and the
  counterexample instances of B5 are model realizations of them.
- **No quantum nuclear dynamics** (tunneling, recrossing), **no electronic structure**, **no
  surface catalysis coverage effects**, **no temperature/prefactor dependence**.
- **No attempt to fit literature data inside Lean.** The instance layer decides arithmetic verdicts
  about *literature-derived numbers* (provenance recorded in `theories/BEP/LITERATURE.md`); it does
  not model the experiments. Instances taken from the literature are marked `literature`; families
  constructed in the model to exhibit a regime are marked `model-constructed`.
- **No `sorry`, no custom `axiom`** in delivered files (enforced by `proofs/scripts/check.sh --strict`
  and `axioms.sh`).

---

## 2. Conventions and symbol table

| symbol | Lean name | meaning | convention |
|---|---|---|---|
| `lam` | `lam : ℝ` | reorganization energy (equal-curvature parameter) | physical: `0 < lam`; `lam = 0` and `lam < 0` are classified and used as counterexamples |
| `x` | `x : ℝ` | driving force `x = -ΔG°` | exergonic: `x > 0`; **same convention as `Marcus`/`Hammond`** |
| `Ea` | `eact lam x` | forward activation barrier | `(lam - x)^2 / (4*lam)` |
| BEP line | `bepLine lam x` | tangent/linear-free-energy law at `x = 0` | `lam/4 - x/2` |
| defect | `bepDefect lam x` | exact violation of the line law | `= x^2/(4*lam)` when `lam ≠ 0` |
| `α` | `transfer lam x` | BEP/Brønsted/Leffler coefficient of the forward direction | **linear-response form** `1/2 - x/(2*lam)` (so `α = q‡` and `α(0) = 1/2` are theorems, not definitions) |
| `α_rev` | `reverseTransfer lam x` | coefficient of the reverse direction (driving force `-x`) | `1/2 + x/(2*lam)` |
| observed slope | `secSlope lam x h` | finite difference of barrier data over the window `[x, x+h]` | `(eact lam x - eact lam (x+h))/h` |
| tolerance radius | `bepRadius lam tol` | half-width of the window on which the line law holds within `tol` | `2 * Real.sqrt (lam * tol)` |
| best line | `bepBestLine lam w x` | minimax affine law on a symmetric window of half-width `w` | `lam/4 + w^2/(8*lam) - x/2` |

Empirical convention warning (to be confirmed by `theories/BEP/LITERATURE.md`): the classical
Evans–Polanyi plot is `Ea` against **ΔH** (or ΔE), while the model variable is **ΔG°**; the passage
from one to the other assumes the family's `TΔS` is constant/harmless — a premise recorded in §13
and never silently used.

---

## 3. Layout and contract (must be reported to the human)

- Theory artifacts live under `theories/BEP/` as requested: `plan.md` (this file), `TASKS.md`,
  `LITERATURE.md`, `probes/`, `RESULTS.md` (bilingual).
- Lean sources live under `PhotoLean/BEP/` because the contract's `SOURCE_DIRS="PhotoLean"` is the
  global scan/build range of the acceptance gate; a source outside it would be invisible to
  `check.sh --strict`. This mirrors the layout already recorded for `hammond`
  (`theories/hammond/TASKS.md`, "Layout decision").
- `proofs/ENGINE.yml` gains the additive multi-theory entries
  `THEORIES="Marcus hammond BEP"`, `PLAN_BEP`, `TASKS_BEP`, `LITERATURE_BEP`, `PROBES_BEP`,
  `RESULT_BEP`. Additive only: canonical Marcus leaves and the scan/build behaviour are unchanged.
- `lakefile.toml` `defaultTargets` gains one line **per delivered module** as soon as that module
  exists (adding a line for a nonexistent module breaks the bare `check.sh --strict`).
- Probes (`theories/BEP/probes/*.lean`) are outside `SOURCE_DIRS`, so the statement skeleton may
  carry placeholders; delivered modules may not.

---

## 4. B1 — description layer (`PhotoLean/BEP/Basic.lean`; owner `prover_a`; Sprint 1)

### 4.1 Definitions (18 declarations: 17 `def`s + the `EPZone` inductive)

```lean
namespace PhotoLean.BEP

/-- Forward activation barrier in the equal-curvature two-parabola model; `x = -ΔG°`. -/
noncomputable def eact (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)

/-- The Bell–Evans–Polanyi line: the linear free-energy law tangent at thermoneutrality. -/
noncomputable def bepLine (lam x : ℝ) : ℝ := lam / 4 - x / 2

/-- Exact violation of the BEP line law. -/
noncomputable def bepDefect (lam x : ℝ) : ℝ := eact lam x - bepLine lam x

/-- BEP / Brønsted / Leffler coefficient of the forward direction, in linear-response form. -/
noncomputable def transfer (lam x : ℝ) : ℝ := 1 / 2 - x / (2 * lam)

/-- Coefficient of the reverse direction of the same step (driving force `-x`). -/
noncomputable def reverseTransfer (lam x : ℝ) : ℝ := 1 / 2 + x / (2 * lam)

/-- Observable BEP slope: a finite difference of barrier data over the window `[x, x+h]`. -/
noncomputable def secSlope (lam x h : ℝ) : ℝ := (eact lam x - eact lam (x + h)) / h

/-- Half-width of the driving-force window on which the line law holds within `tol`. -/
noncomputable def bepRadius (lam tol : ℝ) : ℝ := 2 * Real.sqrt (lam * tol)

/-- Minimax affine BEP law on a symmetric window of half-width `w`. -/
noncomputable def bepBestLine (lam w x : ℝ) : ℝ := lam / 4 + w ^ 2 / (8 * lam) - x / 2

/-- Evans–Polanyi bounds on the transfer coefficient. -/
def EPBounds (lam x : ℝ) : Prop := 0 ≤ transfer lam x ∧ transfer lam x ≤ 1

/-- `eact` agrees with some affine function of the driving force on the set `s`. -/
def EPLinearOn (lam : ℝ) (s : Set ℝ) : Prop := ∃ c a : ℝ, ∀ x ∈ s, eact lam x = c + a * x

/-- The BEP line law holds exactly on every driving force. -/
def EPExact (lam : ℝ) : Prop := EPLinearOn lam Set.univ

/-- The line law holds on the window `[a,b]` within tolerance `tol`. -/
def EPConformsOnWindow (lam tol a b : ℝ) : Prop :=
  0 < lam ∧ 0 < tol ∧ ∀ x ∈ Set.Icc a b, |bepDefect lam x| ≤ tol

/-- Optimality form: no affine law does better than `w^2/(8λ)` on `[-w,w]`. -/
def EPBestOnWindow (lam w : ℝ) : Prop :=
  0 < lam ∧ 0 < w ∧ ∀ c a : ℝ, ∃ x ∈ Set.Icc (-w) w,
    w ^ 2 / (8 * lam) ≤ |eact lam x - (c + a * x)|

/-- Regimes of the transfer coefficient (decidable classifier). -/
inductive EPZone where
  | degenerate | unphysical | thermoneutral | exergonic | endergonic
  | atForwardLimit | atReverseLimit | beyondForward | beyondReverse
  deriving DecidableEq, Repr

/-- Regime classifier, in the style of `Hammond.hammondZone` / `Marcus.zone`. -/
noncomputable def epZone (lam x : ℝ) : EPZone :=
  if lam = 0 then EPZone.degenerate
  else if lam < 0 then EPZone.unphysical
  else if x = 0 then EPZone.thermoneutral
  else if x = lam then EPZone.atForwardLimit
  else if x = -lam then EPZone.atReverseLimit
  else if lam < x then EPZone.beyondForward
  else if x < -lam then EPZone.beyondReverse
  else if 0 < x then EPZone.exergonic
  else EPZone.endergonic

/-- Open regime in which the transfer coefficient is strictly inside `(0,1)`. -/
def EPRegime (lam x : ℝ) : Prop := -lam < x ∧ x < lam

/-- Pointwise conformance to the BEP description. -/
def EPConforms (lam x : ℝ) : Prop := 0 < lam ∧ EPBounds lam x

/-- The exact defect law of the model (the descriptor of the BEP description). -/
def EPDescriptor (lam : ℝ) : Prop := 0 < lam ∧ ∀ x : ℝ, bepDefect lam x = x ^ 2 / (4 * lam)
```

### 4.2 B1 theorems (13)

| # | statement | proof sketch |
|---|---|---|
| 1 | `eact_at_zero (hlam : lam ≠ 0) : eact lam 0 = lam / 4` | `unfold`, `div_eq_iff`, `ring` |
| 2 | `eact_at_lam (hlam : lam ≠ 0) : eact lam lam = 0` | `unfold`, `ring_nf` |
| 3 | `eact_zero_lam (x : ℝ) : eact 0 x = 0` | `unfold`, `div_zero`, `zero_mul` |
| 4 | `transfer_zero_lam (x : ℝ) : transfer 0 x = 1 / 2` | `unfold transfer`, `div_zero`, `sub_zero` — **corrected 2026-09-20** (kernel counterexample by `prover_a`): the linear-response body gives `x/(2*0) = 0`, hence `1/2`, not `0`; the old `= 0` row belonged to the discarded TS-coordinate body |
| 5 | `bepLine_at_zero : bepLine lam 0 = lam / 4` | `unfold`, `ring` |
| 6 | `secSlope_zero_h : secSlope lam x 0 = 0` | `div_zero` |
| 7 | `epZone_eq_degenerate_iff : epZone lam x = .degenerate ↔ lam = 0` | `unfold epZone`, `split_ifs` + `simp` |
| 8 | `epZone_eq_unphysical_iff (hlam : lam ≠ 0) : epZone lam x = .unphysical ↔ lam < 0` | as 7 |
| 9 | `epZone_eq_thermoneutral_iff (hlam : 0 < lam) : epZone lam x = .thermoneutral ↔ x = 0` | as 7 |
| 10 | `epZone_eq_exergonic_iff (hlam : 0 < lam) : epZone lam x = .exergonic ↔ 0 < x ∧ x < lam` | as 7 |
| 11 | `epZone_eq_endergonic_iff (hlam : 0 < lam) : epZone lam x = .endergonic ↔ -lam < x ∧ x < 0` | as 7 |
| 12 | `epZone_eq_atForwardLimit_iff (hlam : 0 < lam) : epZone lam x = .atForwardLimit ↔ x = lam` | as 7 |
| 13 | `epZone_eq_atReverseLimit_iff (hlam : 0 < lam) : epZone lam x = .atReverseLimit ↔ x = -lam` | as 7 |
| 14 | `epZone_eq_beyondForward_iff (hlam : 0 < lam) : epZone lam x = .beyondForward ↔ lam < x` | as 7 |
| 15 | `epZone_eq_beyondReverse_iff (hlam : 0 < lam) : epZone lam x = .beyondReverse ↔ x < -lam` | as 7 |

(Inherited lesson: a "trichotomy"-style exhaustiveness lemma carries little information; the
semantic content is carried by the `..._iff` lemmas, which B3 will pair with algebraic facts.)

---

## 5. B2 — law layer (`PhotoLean/BEP/Criterion.lean`; owner `prover_a`; Sprint 2)

| # | statement | proof sketch |
|---|---|---|
| 1 | `eact_expansion (hlam : lam ≠ 0) : eact lam x = lam/4 - x/2 + x^2/(4*lam)` | `field_simp`, `ring` |
| 2 | `bepDefect_eq (hlam : lam ≠ 0) : bepDefect lam x = x^2/(4*lam)` | 1 + `unfold bepDefect bepLine`, `ring` |
| 3 | `bepLine_exact_at_thermoneutrality (hlam : lam ≠ 0) : bepLine lam 0 = eact lam 0` | 1 at `x = 0` |
| 4 | `bepDefect_at_thermoneutrality (hlam : lam ≠ 0) : bepDefect lam 0 = 0` | 2 + `ring` |
| 5 | `transfer_eq_tsCoord (hlam : lam ≠ 0) : transfer lam x = (lam - x)/(2*lam)` | `field_simp`, `ring` — **the Leffler/Brønsted identification** |
| 6 | `transfer_thermoneutral : transfer lam 0 = 1/2` | `unfold`, `zero_div`, `sub_zero` |
| 7 | `reverseTransfer_thermoneutral : reverseTransfer lam 0 = 1/2` | as 6 |
| 8 | `transfer_add_reverse (hlam : lam ≠ 0) : transfer lam x + reverseTransfer lam x = 1` | `field_simp`, `ring` — **Bronsted complementarity** |
| 9 | `reverseTransfer_eq_transfer_neg : reverseTransfer lam x = transfer lam (-x)` | `unfold`, `ring` |
| 10 | `secSlope_eq_transfer_mid (hlam : lam ≠ 0) (hh : h ≠ 0) : secSlope lam x h = transfer lam (x + h/2)` | **mean-value identity**; `field_simp`, `ring` |
| 11 | `secSlope_midpoint_invariant (hlam) (hh : h ≠ 0) (hk : k ≠ 0) (hmid : x + h/2 = y + k/2) : secSlope lam x h = secSlope lam y k` | 10 twice |
| 12 | `eact_neg_eq_add (hlam : lam ≠ 0) : eact lam (-x) = eact lam x + x` | **barrier-reversal identity** (forward−reverse barrier = driving force); `ring` |
| 13 | `eact_antitone (hlam : 0 < lam) (h₁ : x₁ < x₂) (h₂ : x₂ ≤ lam) : eact lam x₂ < eact lam x₁` | `nlinarith` |
| 14 | `bepDefect_nonneg (hlam : 0 < lam) : 0 ≤ bepDefect lam x` | 2 + `sq_nonneg`, `div_nonneg` |
| 15 | `bepDefect_pos_iff (hlam : 0 < lam) : 0 < bepDefect lam x ↔ x ≠ 0` | 2 + `sq_pos_iff`, `div_pos` |
| 16 | `epDescriptor_holds (hlam : 0 < lam) : EPDescriptor lam` | 2 |
| 17 | `epDescriptor_conforms (h : EPDescriptor lam) (hx : x ≠ 0) : 0 < bepDefect lam x` | unpack `h` |
| 18 | `epConforms_iff_bounds (hlam : 0 < lam) : EPConforms lam x ↔ EPBounds lam x` | `unfold` |
| 19 | `exists_epDescriptor : ∃ lam : ℝ, EPDescriptor lam` | witness `lam = 1` |
| 20–26 | non-vacuity of every regime: `exists_thermoneutral`, `exists_exergonic`, `exists_endergonic`, `exists_atForwardLimit`, `exists_atReverseLimit`, `exists_beyondForward`, `exists_beyondReverse`, `exists_unphysical`, `exists_degenerate` (`∃ lam x, epZone lam x = …`) | explicit `⟨…, …⟩` + `norm_num` |

---

## 6. B3 — sharp conditions (`PhotoLean/BEP/Sharp.lean`; owner `prover_d`; Sprint 3)

### 6.1 The sharp iff statements

| # | statement | proof sketch |
|---|---|---|
| 1 | `epBounds_iff_region (hlam : 0 < lam) : EPBounds lam x ↔ -lam ≤ x ∧ x ≤ lam` | `unfold transfer EPBounds`; `div_le_iff` / `le_div_iff` + `linarith` |
| 2 | `epRegime_iff_strict (hlam : 0 < lam) : EPRegime lam x ↔ 0 < transfer lam x ∧ transfer lam x < 1` | as 1 |
| 3 | `transfer_at_lam (hlam : 0 < lam) : transfer lam lam = 0` | `field_simp`, `ring` |
| 4 | `transfer_at_neg_lam (hlam : 0 < lam) : transfer lam (-lam) = 1` | `field_simp`, `ring` |
| 5 | `not_epBounds_of_lt_neg (hlam : 0 < lam) (hx : x < -lam) : ¬ EPBounds lam x` | 1 + `linarith` (α > 1: the **reverse** direction is in the inverted region) |
| 6 | `not_epBounds_of_gt (hlam : 0 < lam) (hx : lam < x) : ¬ EPBounds lam x` | 1 + `linarith` (α < 0: the forward direction is in the inverted region) |
| 7 | `epExact_iff_degenerate : EPExact lam ↔ lam = 0` | (⇐) `lam = 0` ⇒ `eact 0 x = 0`, take `c = a = 0`; (⇒) if `lam ≠ 0`, the second difference at `0, 1/2, 1` is `1/(16λ) ≠ 0`, contradicting affinity |
| 8 | `not_epLinearOn_of_ne_zero (hlam : lam ≠ 0) (hab : a < b) : ¬ EPLinearOn lam (Set.Icc a b)` | second difference with spacing `h = (b-a)/2 > 0`: affine ⇒ zero, model ⇒ `h²/(2λ) ≠ 0` |
| 9 | `exists_conforms_fails : ∃ lam tol w, 0 < lam ∧ 0 < tol ∧ ¬ EPConformsOnWindow lam tol (-w) w` | witness `lam = 2, w = 1, tol = 1/16` (`1/8 > 1/16`) |

### 6.2 The tolerance/radius theorem (the quantitative validity condition)

| # | statement | proof sketch |
|---|---|---|
| 10 | `bepDefect_abs_eq (hlam : lam ≠ 0) : |bepDefect lam x| = x^2 / (4*|lam|)` | 5.2 + `abs_div`, `abs_pow` |
| 11 | `epConformsOnWindow_iff_radius (hlam : 0 < lam) (htol : 0 < tol) (hw : 0 ≤ w) : EPConformsOnWindow lam tol (-w) w ↔ w ≤ bepRadius lam tol` | on `[-w,w]`, `x²/(4λ) ≤ w²/(4λ)`; `w²/(4λ) ≤ tol ↔ w ≤ 2√(λ·tol)` via `Real.le_sqrt` / `Real.sq_sqrt` |
| 12 | `epConformsOnWindow_at_radius (hlam : 0 < lam) (htol : 0 < tol) : EPConformsOnWindow lam tol (-(bepRadius lam tol)) (bepRadius lam tol)` | the radius is attained, not an estimate |
| 13 | `epConformsOnWindow_mono (h) : a ≤ a' → b' ≤ b → EPConformsOnWindow lam tol a b → EPConformsOnWindow lam tol a' b'` | shrink window / keep tolerance |
| 14 | `epConformsOnWindow_symm : EPConformsOnWindow lam tol a b ↔ EPConformsOnWindow lam tol (-b) (-a)` | `|x²|` evenness |

### 6.3 Monotonicity in the reorganization energy (the "conditions under which it holds")

| # | statement | proof sketch |
|---|---|---|
| 15 | `bepDefect_antitone_lam (h0 : 0 < lam₁) (hle : lam₁ ≤ lam₂) (hx : x ≠ 0) : bepDefect lam₂ x ≤ bepDefect lam₁ x` | 5.2 twice + `div_le_div_of_nonneg_left` (larger λ ⇒ smaller violation) |
| 16 | `bepRadius_mono (h0 : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) (htol : 0 ≤ tol) : bepRadius lam₁ tol ≤ bepRadius lam₂ tol` | `Real.sqrt_le_sqrt`, `mul_le_mul_of_nonneg_right` |
| 17 | `epConformsOnWindow_mono_lam : (…) → EPConformsOnWindow lam₁ tol a b → EPConformsOnWindow lam₂ tol a b` | 15/16 |

### 6.4 The best BEP line (minimax block)

| # | statement | proof sketch |
|---|---|---|
| 18 | `bepBestLine_error (hlam : 0 < lam) (hw : 0 ≤ w) : ∀ x ∈ Set.Icc (-w) w, |eact lam x - bepBestLine lam w x| ≤ w^2/(8*lam)` | `|x²/(4λ) - w²/(8λ)| ≤ w²/(8λ) ↔ 0 ≤ x²/(4λ) ≤ w²/(4λ)` |
| 19 | `epBestOnWindow_holds (hlam : 0 < lam) (hw : 0 < w) : EPBestOnWindow lam w` | three-point equioscillation: `e(-w) + e(w) - 2e(0) = w²/(2λ)` for `e = eact - (c + a·x)` since the affine part cancels; `|e(-w)| + |e(w)| + 2|e(0)| ≥ w²/(2λ)` ⇒ some point has `|e| ≥ w²/(8λ)` |
| 20 | `bepLine_worst_case (hlam : 0 < lam) (hw : 0 ≤ w) : ∃ x ∈ Set.Icc (-w) w, |bepDefect lam x| = w^2/(4*lam)` | witness `x = w` |
| 21 | `bepBestLine_halves (hlam : 0 < lam) (hw : 0 < w) : w^2/(8*lam) = (w^2/(4*lam))/2 ∧ w^2/(8*lam) < w^2/(4*lam)` | `ring` + positivity — the best line halves the tangent line's worst case |

### 6.5 Hypothesis necessity (each premise exhibited as necessary)

| # | statement | proof sketch |
|---|---|---|
| 22 | `bepDefect_zero_lam_witness : bepDefect 0 1 = 1/2 ∧ ((1:ℝ)^2/(4*0)) = 0` | `norm_num` — the defect formula needs `lam ≠ 0` |
| 23 | `bepDefect_neg_lam_witness : bepDefect (-1) 1 = -(1/4)` | `norm_num` — positivity needs `0 < lam` |
| 24 | `bepDefect_sign_flips (hlam : lam < 0) (hx : x ≠ 0) : bepDefect lam x < 0` | 5.2 + `div_neg_of_pos_of_neg` — the sign of the violation *is* the sign of λ |
| 25 | `secSlope_needs_h_ne_zero : secSlope 1 0 0 = 0 ∧ transfer 1 0 ≠ 0` | witness: dropping `h ≠ 0` breaks the mean-value identity of 5.10 (`0 ≠ 1/2`) |

---

## 7. B4 — microscopic and cross-module layer (`PhotoLean/BEP/Compose.lean`; owner `prover_b`; Sprint 3)

Imports `PhotoLean.Marcus.Basic` and `PhotoLean.Hammond.Basic` (both delivered; no cycles).

| # | statement | proof sketch |
|---|---|---|
| 1 | `eact_eq_barrier : eact lam x = Marcus.barrier lam x` | `rfl` (identical bodies, independent statements) |
| 2 | `rate_eq_exp_neg_eact (h : Marcus.rate A lam kB T x = …) : Marcus.rate A lam kB T x = A * Real.exp (-(eact lam x)/(kB*T))` | 1 + `rfl`-rewrite — the BEP barrier *is* the Marcus barrier, so the BEP description constrains the delivered rate descriptor |
| 3 | `transfer_eq_tsCoord_bridge (hlam : lam ≠ 0) : transfer lam x = Hammond.tsCoord lam x` | cross-module form of 5.5 |
| 4 | `epBounds_iff_no_inverted_direction (hlam : 0 < lam) : EPBounds lam x ↔ ¬ (Marcus.InvertedRegion lam x ∨ Marcus.InvertedRegion lam (-x))` | 6.1 + `Marcus.InvertedRegion` unfolding (`lam < x`) |
| 5 | `epBounds_of_reactionRegion (hlam : 0 < lam) (h : Hammond.ReactionRegion lam x) : EPBounds lam x` | 6.1 + `linarith` |
| 6 | `epBounds_of_marcus_normal (hlam : 0 < lam) (h : Marcus.NormalRegion lam x) (hx : -lam ≤ x) : EPBounds lam x` | 6.1 |
| 7 | `epDescriptor_of_microscopic (hli : 0 < lamInner) (hlo : 0 < lamOuter) : EPDescriptor (lamInner + lamOuter)` | additivity + 5.2 |
| 8 | `bepDefect_le_of_microscopic (hli : 0 < lamInner) (hlo : 0 < lamOuter) (hx : x ≠ 0) : bepDefect (lamInner + lamOuter) x ≤ bepDefect lamInner x` | 6.15 with `lamInner ≤ lamInner + lamOuter` |
| 9 | `bepRadius_add (hli : 0 ≤ lamInner) (hlo : 0 ≤ lamOuter) (htol : 0 ≤ tol) : bepRadius lamInner tol ≤ bepRadius (lamInner + lamOuter) tol` | 6.16 |
| 10 | `epConformsOnWindow_of_microscopic (hli : 0 < lamInner) (hlo : 0 < lamOuter) (htol : 0 < tol) (hw : w ≤ bepRadius (lamInner + lamOuter) tol) : EPConformsOnWindow (lamInner + lamOuter) tol (-w) w` | 6.11/6.12 + 9 |
| 11 | `epConformsOnWindow_shrinks_with_inner (…) : EPConformsOnWindow lamInner tol (-w) w → EPConformsOnWindow (lamInner + lamOuter) tol (-w) w` | 7/8 |
| 12 | `transfer_complementary_microscopic (hlam : lamInner + lamOuter ≠ 0) : transfer (lamInner + lamOuter) x + reverseTransfer (lamInner + lamOuter) x = 1` | 5.8 at the composed `λ` |

**Physical reading of B4**: BEP's accuracy is a *microscopic* consequence — a larger total
reorganization energy (inner + outer, Pekar-type) shrinks the exact violation and widens the
tolerance window, and the Evans–Polanyi bounds fail **exactly** when one of the two directions lies
in the Marcus inverted region.

---

## 8. B5 — instances and verdicts

### 8.1 B5a computable decision layer (`PhotoLean/BEP/RatModel.lean`; owner `prover_c`; Sprint 2)

All in `ℚ`, computable; the ℝ predicates are reached by transfer lemmas (pattern of
`PhotoLean/Hammond/RatModel.lean`).

```lean
def qEact (lam x : ℚ) : ℚ := (lam - x) ^ 2 / (4 * lam)
def qBepLine (lam x : ℚ) : ℚ := lam / 4 - x / 2
def qBepDefect (lam x : ℚ) : ℚ := qEact lam x - qBepLine lam x
def qTransfer (lam x : ℚ) : ℚ := 1 / 2 - x / (2 * lam)
def qReverseTransfer (lam x : ℚ) : ℚ := 1 / 2 + x / (2 * lam)
def qSecSlope (lam x h : ℚ) : ℚ := (qEact lam x - qEact lam (x + h)) / h
/-- Two-point observable BEP slope from data `(x₁,Ea₁)`, `(x₂,Ea₂)`. -/
def qAlphaObs (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (ea₁ - ea₂) / (x₂ - x₁)
/-- Two-point reorganization-energy solver (the model's λ from two data points).
    Numerator `x₂² - x₁²` and the premise `lam ≠ 0` are **required**: the literal form
    `(x₁² - x₂²)/…` returns `-λ` (kernel counterexample, risk probe 2026-09-20), and `lam = 0`
    is a genuine exception (totalised division makes `eact 0 x` constant `0`, so the barrier
    equations stop implying the solver's linear relation). -/
def qLamOfPair (x₁ ea₁ x₂ ea₂ : ℚ) : ℚ := (x₂ ^ 2 - x₁ ^ 2) / (2 * (x₂ - x₁) - 4 * (ea₁ - ea₂))
/-- Window conformance, in squared form so that it is decided without square roots. -/
def qConformsWindow (lam tol w : ℚ) : Prop := 0 < lam ∧ 0 < tol ∧ w ^ 2 ≤ 4 * lam * tol
inductive EPQVerdict where
  | degenerate | unphysical | conforming | boundary | superLinear | subLinear
/-- Verdict on a *single* family point (the regime of its coefficient). -/
def epQVerdict (lam x : ℚ) : EPQVerdict := …
```

Theorems (13): `qEact_cast`, `qBepDefect_cast`, `qTransfer_cast`, `qSecSlope_cast`,
`qAlphaObs_cast`, `qLamOfPair_cast` (each `(↑(qX …) : ℝ) = X …`),
`qSecSlope_eq_qTransfer_mid (hlam : lam ≠ 0) (hh : h ≠ 0)`,
`qAlphaObs_eq_qTransfer_mid` (**two-point data → structural coefficient**: if the data come from the
model, the observed slope is the coefficient at the data midpoint),
`qLamOfPair_reconstructs (hlam : lam ≠ 0) (hx : x₁ ≠ x₂) (hden : 2*(x₂ - x₁) - 4*(ea₁ - ea₂) ≠ 0)
(h₁ : ea₁ = qEact lam x₁) (h₂ : ea₂ = qEact lam x₂) : qLamOfPair x₁ ea₁ x₂ ea₂ = lam`
(**two model-consistent data points determine λ uniquely**; the `lam ≠ 0` premise is necessary —
both this premise and the numerator sign were corrected by kernel counterexamples from the Sprint-0
risk probe, §11),
`epQVerdict_conforming_iff`, `epQVerdict_boundary_iff`, `epQVerdict_superLinear_iff`,
`epQVerdict_subLinear_iff`, `qConformsWindow_iff_radius_sq`.

### 8.2 B5b instance verdicts (`PhotoLean/BEP/Instances.lean`; owner `prover_c`; Sprint 4)

Every row is decided by the kernel (`decide` / `norm_num` on `ℚ`, then transported to the ℝ
statements through the §8.1 transfer lemmas). `provenance` is `model-constructed` or `literature`
(the latter quoting `theories/BEP/LITERATURE.md` with its data table and status flag).

| id | family | parameters | expected verdict | theorems |
|---|---|---|---|---|
| I1 | thermoneutral family | `λ = 2`, `x = 0` | conforming, `α = 1/2`, defect `0` | `inst_I1_zone/transfer/conforms` |
| I2 | mildly exergonic | `λ = 2`, `x = 1/2` | conforming, `α = 3/8` | `inst_I2_zone/transfer/conforms` |
| I3 | mildly endergonic | `λ = 2`, `x = -1/2` | conforming, `α = 5/8` | `inst_I3_zone/transfer/conforms` |
| I4 | forward barrierless limit | `λ = 2`, `x = 2` | boundary, `α = 0` | `inst_I4_zone/transfer/boundary` |
| I5 | reverse barrierless limit | `λ = 2`, `x = -2` | boundary, `α = 1` | `inst_I5_zone/transfer/boundary` |
| I6 | strongly exergonic (forward inverted region) | `λ = 2`, `x = 3` | **not conforming**, `α = -1/4 < 0` | `inst_I6_zone/transfer/notBounds` |
| I7 | strongly endergonic (reverse inverted region) | `λ = 2`, `x = -3` | **not conforming**, `α = 5/4 > 1` | `inst_I7_zone/transfer/notBounds` |
| I8 | degenerate family | `λ = 0`, `x = 1` | exact BEP, no content: barrier `0`, `α = 0` | `inst_I8_exact/trivial` |
| I9 | unphysical curvature | `λ = -2`, `x = 1` | **not conforming**, defect `< 0` | `inst_I9_unphysical/defect_negative` |
| I10 | tolerance threshold | `λ = 2`, `w = 1` | conforms at `tol = 1/8`, fails at `tol = 1/16` (`w* = 2√(λ·tol)`) | `inst_I10_conforms/fails` |
| I11 | literature families (≥ 2 data pairs each) | from `LITERATURE.md` | verdict computed per family (conforming / boundary / violating / model-inconsistent) | `inst_I11_<family>_slope/lam/verdict` |

Additional instance requirements:
- **I9 is the instructive row (lead numeric audit, 2026-09-20)**: for `λ = -2, x = 1` the transfer
  coefficient is `α = 3/4`, which lies **inside** `[0,1]` — so the Evans–Polanyi bounds alone do
  **not** detect an unphysical curvature; what detects it is the *sign* of the defect
  (`bepDefect (-2) 1 = -1/8 < 0`, against the exact law `x²/(4λ) = -1/8` with `λ < 0`). The
  descriptor `EPDescriptor` is strictly stronger than the bounds pair, and I9 exists to exhibit that.
- at least **one literature family whose verdict is "conforming"** and at least **one whose verdict
  is a documented violation or model-inconsistency** — a table of confirmations only would be a
  selection artifact and must be stated as such;
- every literature instance theorem names its provenance in a docstring (source + locus + status
  flag from `LITERATURE.md`) and states the verdict *about the model family instantiated by those
  numbers*, not about the experiment;
- a non-vacuity instance (`inst_nonvacuous`: both a conforming and a non-conforming family exist).

---

## 9. Sprint order, ownership, dependency graph

```text
Sprint 0  engine plumbing: theories/BEP/{plan,TASKS,LITERATURE,RESULTS}.md + probes/ + ENGINE.yml
          statement skeleton (api_researcher) + API log + literature round 1
Sprint 1  B1  Basic.lean      prover_a   (no deps)                 ── statement-first gate
Sprint 2  B2  Criterion.lean  prover_a   (deps B1)    ┐
          B5a RatModel.lean   prover_c   (deps B1)    ┴ concurrent, different files
Sprint 3  B3  Sharp.lean      prover_d   (deps B1,B2) ┐
          B4  Compose.lean    prover_b   (deps B1, Marcus, Hammond) ┴ concurrent
Sprint 4  B5b Instances.lean  prover_c   (deps B5a, B2, literature round 1)
Sprint 5  adversarial audit (prover_b, probes/bep-audit-*.lean) + verifier batches
```

- Ownership is per file and exclusive (one owner at a time): `Basic.lean`/`Criterion.lean` →
  `prover_a`; `Sharp.lean` → `prover_d`; `Compose.lean` → `prover_b`; `RatModel.lean` /
  `Instances.lean` → `prover_c`.
- Dependency graph is the only licence to parallelize: B1 is upstream of everything, so it lands
  first; B5a is deliberately independent of B2/B3 (it is pure rational arithmetic) so `prover_c`
  starts in Sprint 2.
- Riskiest-first: the two riskiest statements (the radius theorem with `Real.sqrt`, and the minimax
  lower bound) are scheduled in B3 with the fallbacks of §11 pre-registered.

---

## 10. Acceptance criteria (per lemma, read from the contract)

1. `proofs/scripts/lake build PhotoLean.BEP.<Module>` — exit 0.
2. `proofs/scripts/check.sh --strict PhotoLean.BEP.<Module>` — `verdict: PASS` (build + no
   `sorry`, no custom `axiom` anywhere under `PhotoLean/`).
3. `proofs/scripts/axioms.sh PhotoLean.BEP.<Module> PhotoLean.BEP.<fully.qualified.theorem>` —
   clean, only `propext Classical.choice Quot.sound`.
4. One commit per lemma: `feat(B<k>): <lemma>` (definitions: `feat(B<k>): <definition group>`).
5. Statement fidelity against `theories/BEP/probes/bep-statement-skeleton.lean` word for word
   (checked mechanically by a probe script, as in `theories/hammond/probes/hammond-fidelity.py`).
6. Board row flipped to `done` **only** after an independent verifier PASS, ticked by the lead.

---

## 11. Risk register and pre-registered fallbacks

| risk | why | fallback (pre-registered) |
|---|---|---|
| `Real.sqrt` API drift (`Real.le_sqrt`, `Real.sq_sqrt`, `Real.sqrt_le_sqrt`) | the radius theorem is the only statement needing `sqrt` on ℝ | `api_researcher` probes the names first; if a name is missing, the radius theorem is restated in **squared form** (`w^2 ≤ 4*λ*tol`) with `bepRadius` kept as a *defined* quantity only; the squared form is mathematically equivalent and keeps the sharpness content |
| minimax lower bound (abs-triangle + `nlinarith` over three points) | pure-estimate proof, easy to get stuck in `linarith` | keep `bepBestLine_error` (attainment) + `bepLine_worst_case` (the tangent line's exact worst case) and state the lower bound for the three points `-w, 0, w` explicitly (`∃ x ∈ {-w,0,w}, w²/(8λ) ≤ …`) — same content, no `push_neg` gymnastics |
| `if`-cascade classifier proofs (`split_ifs` nesting, 9 branches) | mechanical and error-prone; hammond's 7-branch version needed care | reduce the cascade to 7 branches by merging `atForwardLimit`/`atReverseLimit` into `boundary` if the iff lemmas resist; the *predicates* (6.1) carry the content either way |
| `decide` on `ℚ` comparisons | needs the decidable `ℚ` order instances; `norm_num` may be needed instead | pattern is already proven in `PhotoLean/Hammond/RatModel.lean`; `api_researcher` confirms with a probe before B5a starts |
| residual statement risk after the Sprint-0 probes | the probes found three false/ill-posed rows before delivery: `transfer_zero_lam`, the `qLamOfPair` numerator sign, and the missing `lam ≠ 0` premise of the two-point reconstruction | all three are corrected in this plan (§4.2 row 4, §8.1, §8.1 theorems); any further statement defect is handled the same way — fix the statement, record it here and in `API-NOTES.md`, never paper over it with a hypothesis that hides the flaw |
| literature numbers unavailable / unverifiable | the instance layer must not fabricate data | instances I11 fall back to `model-constructed` families and the table's provenance column is filled with `not-accessed`; RESULTS then states plainly that no literature family was verified (the honest failure mode) |
| `Marcus`/`Hammond` cross-module names drift | B4 imports both modules | names are already delivered and stable (frozen theories); `api_researcher` re-checks `Marcus.barrier`, `Marcus.InvertedRegion`, `Marcus.NormalRegion`, `Hammond.tsCoord`, `Hammond.ReactionRegion` in a probe |
| unequal-curvature generalization attempted | it is the physically more faithful model | **out of scope** (§1.4); recorded as §14 next station |

---

## 12. Deliverable declaration inventory (target)

| file | definitions | theorems | milestone |
|---|---|---|---|
| `PhotoLean/BEP/Basic.lean` | 17 defs + 1 inductive | 15 | B1 |
| `PhotoLean/BEP/Criterion.lean` | 0 | 20 | B2 |
| `PhotoLean/BEP/Sharp.lean` | 0 | 25 | B3 |
| `PhotoLean/BEP/Compose.lean` | 0 | 12 | B4 |
| `PhotoLean/BEP/RatModel.lean` | 10 defs + 1 inductive | 14 | B5a |
| `PhotoLean/BEP/Instances.lean` | 0 | 28 | B5b |
| **total** | **28 defs + 2 inductives** | **114** | |

(Targets, not promises: the delivered count is whatever passes the gate, and `RESULTS.md` reports
the measured numbers, never the planned ones.)

---

## 13. Honesty table — what is assumed, what is proved, what is out of scope

| item | status |
|---|---|
| one scalar reaction coordinate; crossing point = TS; equal curvature `2λ`; `λ` fixed across the family | **model assumption** (premise of every theorem) |
| `Ea = (λ-x)²/(4λ)` | definition inside the model; the literature locus for it is recorded in `LITERATURE.md` |
| exact defect law `bepDefect = x²/(4λ)` | **proved** (B2 §5.2), conditional on `λ ≠ 0` |
| `α = q‡` (Leffler/Brønsted identification) | **proved** (B2 §5.5) as an algebraic identity in the model |
| `α(0) = 1/2`, complementarity `α_f + α_r = 1`, barrier reversal | **proved** (B2) |
| `0 ≤ α ≤ 1 ⟺ -λ ≤ x ≤ λ ⟺` no direction in the inverted region | **proved** (B3 §6.1, B4 §7.4) — a statement about the *model* coefficient; the literature does not state it as a law of chemical families (naming caveat, §1.2 item 4 and `LITERATURE.md` §R1.7(iv)) |
| IUPAC's normative wording calls the BEP relation "sometimes observed within a series of closely related reactions" | **literature premise**: the formalization's tolerance/window formulation is the formal counterpart of "sometimes … within a series"; the glossary's relation is activation energy vs **enthalpy**, while the model is stated in **Gibbs** energy, hence the `ΔH ≈ ΔG°` caveat below |
| exact affinity ⟺ `λ = 0`; no affinity on any nontrivial window for `λ ≠ 0` | **proved** (B3 §6.1) |
| tolerance window `⟺ w ≤ 2√(λ·tol)`; best line and its `w²/(8λ)` bound | **proved** (B3 §6.2, §6.4) |
| monotonicity in `λ` (bigger reorganization ⇒ better linearity) | **proved** (B3 §6.3, B4) |
| the empirical BEP principle of real chemistry (ΔH-based, family-wise, with its exceptions) | **out of scope**: what is proved is a conditional statement *inside the model*; the literature record supplies the premises and the data, not the proof |
| `ΔH ≈ ΔG°` within a family (constant `TΔS`), same prefactor/entropy across the family | **literature-dependent premise**, recorded in `LITERATURE.md`; not used as a Lean hypothesis because the model is stated in `ΔG°` — the caveat is in this table and in `RESULTS.md` |
| tunneling, recrossing, diffusion control, electronic-structure detail, surface catalysis | **out of scope** (§1.4); the model realizations of these effects (barrierless limits, `α` outside `[0,1]`) are the counterexample instances |

---

## 14. Next stations (not in this plan)

1. **Unequal curvature** `λ_R ≠ λ_P`: the BEP slope acquires an extra factor and the defect stops
   being a pure square — the sharp iff statements must be re-derived (the crossing equation becomes
   quadratic in `q`).
2. **Entropy/prefactor corrections**: a temperature-dependent `Ea(T)` and a family-wise entropy term
   would make the ΔH/ΔG° distinction a theorem rather than a caveat.
3. **Curved-BEP families**: a model with a nonlinear cross-relation (e.g. a quartic correction to
   the surface) would let "BEP violation over a wide window" be an instance of a *different* model
   rather than of the tolerance parameter.
4. **Cross-theory dictionary**: a single module stating Marcus (rate) ⟺ Hammond (structure) ⟺ BEP
   (linear free-energy) as one equivalence chain, with each theory's own validity region as the
   bridge conditions.
