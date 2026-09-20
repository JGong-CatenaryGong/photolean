# theories/kasha/plan.md — PhotoLean formalization plan: Kasha's rule (K1–K5)

> Project: turn **Kasha's rule** ("luminescence is emitted only from the lowest excited state of a
> given multiplicity, whatever the excitation") into a *machine-checked* theorem set, as the fourth
> theory of this repository (after `Marcus`, `hammond` and `BEP`).
> Target system: Lean 4.17.0 + mathlib v4.17.0 (`MODULE_PREFIX=PhotoLean`, contract
> `proofs/ENGINE.yml`).
> Status: **Sprint 0 — plan landed, statements being calibrated.** This file is the plan of record;
> every delivered signature must match the statement authority
> `theories/kasha/probes/kasha-statement-skeleton.lean` word for word.
> Authority: contract `proofs/ENGINE.yml`; board `theories/kasha/TASKS.md`; experience bank
> `proofs/EXPERIENCE.md`; literature `theories/kasha/LITERATURE.md`.
> Human request (2026-09-20): ① turn Kasha's rule into a formal description; ② prove the theory or
> find the exact conditions under which it holds; ③ plug instances in and decide, by kernel
> computation, whether each instance conforms.
> Language policy: this file and every other proof-process artifact are **English**; the only
> bilingual file is `theories/kasha/RESULTS.md`.

---

## 1. Overall goal and boundaries

### 1.1 The physical claim being formalized

**Kasha's rule** (Kasha 1950) is the empirical generalization that for a molecule with several
excited electronic states of the same multiplicity, luminescence comes from the **lowest** of them
only: whatever state is initially populated, fluorescence is emitted from `S₁` (phosphorescence from
`T₁`). Its spectroscopic faces are:

* the **emission spectrum is independent of the excitation wavelength** (the same band shape is
  observed under excitation into `S₁`, `S₂`, `S₃`, …), and
* **Vavilov's rule**: the emission quantum yield is independent of the excitation wavelength.

The physical explanation quoted in the literature is a *rate inequality*: internal conversion and
vibrational relaxation between excited states of the same multiplicity (`Sₙ → Sₙ₋₁`) are orders of
magnitude faster than radiative decay from those states (`k_IC ≫ k_rad`), so the excitation is
funnelled to the lowest state before any photon can leave.

The rule has a documented domain of failure: azulene's anomalously large `S₂–S₁` gap slows its
`S₂ → S₁` internal conversion enough that `S₂` fluorescence competes; isolated gas-phase molecules
show resonance fluorescence from the initially prepared level; and other anti-Kasha emitters are
reported (`theories/kasha/LITERATURE.md`).

**Provenance and scope of the statement (literature round 1, `theories/kasha/LITERATURE.md`
§R1.1).** The canonical wording is quoted as *"The emitting electronic level of a given multiplicity
is the lowest excited level of that multiplicity"* (Kasha 1950, *Discuss. Faraday Soc.* **9**, 14–19
— the sentence is reached through del Valle & Catalán, *PCCP* **21**, 10061 (2019), because the 1950
body is behind a paywall; the record marks that evidence strength `secondary`). The scope qualifiers
the source states with it are binding on the model's docstrings: **complex molecules**, **condensed
phase**, **one photon per molecule**, **photostationary conditions**. Two further consequences of
that round are registered here because they bound what this formalization may claim:

* the tolerance `tol` is a **model choice, not a literature number** — no source read in the record
  prints a threshold for `k_IC ≫ k_rad` (§R1.3). The plan's working value `tol = 1/100` is therefore
  labelled as such wherever it appears, and K5b carries a row that makes the dependence explicit
  (I11t: the same azulene data conforms at `tol = 1/10` and violates at `tol = 1/100`). Historically
  the tolerance formulation is not an invention of this development: Vavilov's own 1927 paper states
  his rule with a **±8 %** tolerance (§R1.2);
* the model's rates are **measured quantities identified with model scalars** (`rad 1 ≡ Σk_r(S₂)`,
  `ic 1 ≡ Σk_nr(S₂)`), and that identification is a declared bridge (§R1.4.2), never a theorem.

This plan formalizes exactly that: the Kasha *description* (K1), the *laws and their exact validity
conditions* (K2, K3), the *composition and the cross-theory bridge* (K4), and *instance verdicts
decided by the kernel* (K5).

### 1.2 The model (chosen, not derived)

A finite **excited-state ladder**. Level `0` is the lowest excited state of the multiplicity under
consideration (`S₁` for fluorescence, `T₁` for phosphorescence); level `n ≥ 1` is the `n`-th state
above it (`S₂, S₃, …`). Each level `n` has two competing decay channels, described by rate
constants:

* `rad n ≥ 0` — radiative decay of level `n` (emission);
* `ic n ≥ 0` — **nonradiative** decay of level `n`: for `n ≥ 1` an internal conversion step
  `n → n-1` (electronic relaxation, the vibrationally-assisted funnel of the rule), and for `n = 0`
  the nonradiative decay of the lowest state to the ground state (internal conversion to `S₀`,
  intersystem crossing — any channel that does not emit).

The **branching probabilities** of level `n` are therefore `rad n / decay n` (emit) and
`ic n / decay n` (step down / lose), where `decay n = rad n + ic n > 0`. Competing exponential
clocks with these rates give exactly these branching probabilities (the standard embedded-jump-chain
fact of a continuous-time Markov chain). That fact is a **modelling premise** here: the model is
stated in terms of the branching probabilities, and the derivation of the branching ratio from
exponential clocks is *not* formalized (it is recorded as a scope limit in §13; the plan's stretch
item K4c probes whether the installed mathlib supports it).

The observables are the **time-integrated** yields of this cascade, i.e. the standard fluorescence
quantum yields. With excitation at level `N`:

```text
emitYield i N = (rad i / decay i) · ∏_{j=i+1..N} (ic j / decay j)      emission from level i
fluoYield N   = Σ_{i=0..N} emitYield i N                              total emission probability
upperYield N  = Σ_{i=1..N} emitYield i N                              emission from above the lowest state
specFrac i N  = emitYield i N / fluoYield N                           the (normalized) emission spectrum
```

Kasha's rule in this description is the statement `upperYield N = 0`, i.e. the emission spectrum is
supported on the lowest state only.

### 1.3 The structural subtlety this plan is built around

**Kasha's rule is not a theorem of the cascade model.** This is the honest core, and it is what
makes the formalization non-trivial:

1. **Exact form.** `upperYield N = 0` holds **iff every upper level is non-radiative**
   (`rad i = 0` for `1 ≤ i ≤ N`) — Theorem K2 `kashaRule_iff_rad_zero`. Every real excited state has
   a non-zero radiative rate, so the rule is *never exactly true of a real molecule*: it is an
   idealization. Exactly as with the BEP line law in `Marcus`/`BEP` theory, conformance must be
   stated **with a tolerance** (`KashaWithin tol N : upperYield N ≤ tol · fluoYield N`, the fraction
   of the emitted photons that do *not* come from the lowest state).
2. **Sharp tolerance form.** The tolerance form has an exact rate criterion — a **funnel-ratio
   threshold** (Theorem K3 `kashaWithin_one_iff_ratio` and its N-level form
   `kashaWithin_iff_ladderRatio`):

   ```text
   KashaWithin tol N   ⟺   (1 - tol)/tol  ≤  [rad 0 · cascade 0 N] / [upperYield N · decay 0]
   ```

   The literature's folklore inequality `k_IC ≫ k_rad` becomes a *number*: for a 1 % purity
   requirement (`tol = 1/100`) the threshold is `99`. That is the answer to part ② of the request:
   the exact condition under which Kasha's rule holds.
3. **The threshold does not lift levelwise.** It is tempting to guess that "internal conversion
   beats radiation at each level" (`rad i/decay i ≤ ic i/decay i` for every `i ≥ 1`) implies the
   rule. It does not: in the equal-rates ladder `rad 0 = ic 0 = … = ic 2 = 1`, `rad 1 = rad 2 = 1`
   the per-level inequality holds with ratio `1/2 ≤ 1/2` at both upper levels and yet the leak is
   `upperYield 2/fluoYield 2 = 3/4` (the plan's counterexample row `I11`, kernel-checked in K5b).
   The correct general statement is **aggregate**: the ladder is *exactly* equivalent to a two-level
   model in **effective** branching data (Theorem K4 `kashaWithin_iff_effective`), and it is the
   effective funnel ratio that the threshold tests. Why the aggregate differs: the leak accumulates
   multiplicatively down the ladder (`upperYield N+1 = radBranch (N+1) + icBranch (N+1)·upperYield N`,
   Theorem K2 `upperYield_succ`), and a *relative* purity criterion is not a per-level property.
   This is the mathematical content that a two-level-only formalization would miss.
4. **The Kasha–Vavilov equivalence needs a loss premise.** The two faces of the rule — spectral
   purity (Kasha) and excitation-independence of the yield (Vavilov) — are equivalent here
   (Theorem K2 `kashaRule_iff_vavilovUpTo`), **provided the lowest level has a loss channel**
   (`ic 0 > 0`). With no loss anywhere the total yield is `1` for every excitation level (Kasha's
   `1 - icBranch 0 · cascade 0 N = 1`), so Vavilov's rule holds trivially while Kasha's rule fails;
   the premise is explicit, and the degenerate model is a delivered witness (K3
   `vavilov_premise_necessary`).
5. **Anti-Kasha has a Marcus-shaped criterion.** If the `S₂ → S₁` internal-conversion rate is given
   by the Marcus-type rate law of this repository's `PhotoLean.Marcus` theory, with driving force
   equal to the energy gap and reorganization energy `λ_IC`, then the rule holds **iff the gap lies
   in an explicit window** around `λ_IC` (Theorem K4 `kashaWithin_one_marcus`): too small a gap
   (activation-controlled) and too large a gap (the Marcus **inverted** region) both give an
   anti-Kasha emitter. This is the model-side explanation of the azulene family and the cross-theory
   bridge of the plan. The identification of internal conversion with the *classical* Marcus form is
   a modelling premise with a literature caveat (the true gap law is exponential, Jortner); it is
   stated as an explicit hypothesis and recorded in `theories/kasha/LITERATURE.md`.

### 1.4 Human request → milestones

| Human request | Milestone | Deliverable |
|---|---|---|
| ① turn Kasha's rule into a formal description | **K1** (description layer) | `PhotoLean/Kasha/Basic.lean`: the ladder data and its standing physical premise bundle (`RateData`), branching probabilities, the cascade probability, level-resolved and total yields, the normalized spectrum, the Kasha margin/ratio, the predicates `KashaRule` / `KashaWithin` / `VavilovAt` / `VavilovUpTo` / `KashaDescriptor`, the decidable zone classifier `kashaZone` and its three equivalences |
| ② prove the description / find its exact validity conditions | **K2** (law layer) | `PhotoLean/Kasha/Criterion.lean`: the Markov recursion (yield and leak), probability conservation (`cascade 0 N + upperYield N = 1`), the closed form of the total yield, monotonicity, and the two exact criteria — `KashaRule ↔ rad = 0` above the lowest level, and the Kasha–Vavilov equivalence |
| ②b the *sharp* conditions | **K3** (sharp layer) | `PhotoLean/Kasha/Sharp.lean`: the funnel-ratio threshold (two-level exact `iff` in both the rate and the ratio presentation), the lossless-lowest-level form `k_IC/k_rad ≥ (1-tol)/tol`, monotonicity in the tolerance and in the internal-conversion rate, exactness at `tol = 0`, the threshold's **attainment** (sharpness), the counterexample `perLevel_criterion_insufficient`, and the necessity witnesses (each premise dropped ⇒ kernel-checked counterexample) |
| ②c the general-level and microscopic form | **K4** (composition and bridges) | `PhotoLean/Kasha/Compose.lean`: the block-splitting identity, the **effective two-level reduction** (`kashaWithin_iff_effective`, `kashaMargin_effective`, `ladderRatio_one`), the N-level threshold `kashaWithin_iff_ladderRatio`, and the Marcus bridge `kashaWithin_one_marcus` (+ the squared-gap corollary and the anti-Kasha corollary) |
| ③ plug in instances and decide | **K5** (instances and verdicts) | `PhotoLean/Kasha/RatModel.lean` (computable ℚ layer: rational yields, the ratio test, a three-valued verdict classifier, `norm_num`-checkable conformance, ℝ↔ℚ bridges) and `PhotoLean/Kasha/Instances.lean` (kernel-checked verdicts I1–I14: the model-constructed boundary rows, the equal-rates counterexample row, and the literature-sourced conforming and anti-Kasha families with their provenance) |

### 1.5 Explicit non-goals (scope control)

* **Not deriving the model.** That a molecule is described by a discrete ladder of electronic levels
  with a single scalar rate per channel, that the branching probabilities are those of competing
  exponential clocks, that the observables are the time-integrated yields, and that only the
  *lowest* state's `ic 0` channel is a loss to the ground state, are **modelling assumptions**; they
  appear as explicit premises or as documented scope limits (§13).
* **No claim that Kasha's rule is a law of nature.** The formalized content is: *conditional on the
  model*, the rule is equivalent to exactly these rate conditions. The empirical exceptions are the
  *reason* for the tolerance formulation, and the violation instances of K5 are model realizations
  of them.
* **No electronic structure, no Franck–Condon factors, no vibrational dynamics.** Vibronic coupling,
  the promoting modes, the energy-gap law's exponential form and the spin–orbit coupling that makes
  `ic 0` (intersystem crossing) possible are outside the model; they enter only as *numbers* in the
  instance layer, with provenance.
* **No time-resolved kinetics.** The plan does not formalize the master equation's solution
  `p_n(t)`: the yields are the time-integrated quantities of the cascade. The exponential-race
  derivation of the branching probabilities is a stretch item (K4c) *if* the installed mathlib
  supports it, otherwise a declared premise.
* **No temperature or solvent dependence** of the rate constants; they are parameters.
* **No attempt to fit literature data inside Lean.** The instance layer decides arithmetic verdicts
  about *literature-derived numbers* (provenance in `theories/kasha/LITERATURE.md`); rows with no
  first-hand numbers are marked `UNSUPPORTED` rather than guessed.
* **No unproved placeholder, no custom axiomatic declaration** in delivered files (enforced by
  `proofs/scripts/check.sh --strict` and `axioms.sh`).

---

## 2. Conventions and symbol table

| symbol | Lean name | meaning | convention |
|---|---|---|---|
| `n : ℕ` | level index | `0` = lowest excited state of the multiplicity (`S₁`/`T₁`); `n ≥ 1` = the `n`-th state above it | the ladder is truncated at the excitation level `N` |
| `rad` | `rad : ℕ → ℝ` | radiative rate of level `n` (s⁻¹) | physical: `0 ≤ rad`; `rad i = 0` for `i ≥ 1` is the exact-rule idealization |
| `ic` | `ic : ℕ → ℝ` | nonradiative rate of level `n`: internal conversion `n → n-1` for `n ≥ 1`, decay of the lowest state to the ground state for `n = 0` | physical: `0 ≤ ic`; `ic 0 > 0` is the **loss premise** of the Vavilov equivalence |
| `decay` | `decay rad ic n` | total decay rate `rad n + ic n` | premise `0 < decay rad ic n` wherever a branch is divided |
| `radBranch` | `radBranch rad ic n` | `rad n / decay n` — probability of emitting from level `n` | `∈ [0,1]` under `RateData` |
| `icBranch` | `icBranch rad ic n` | `ic n / decay n` — probability of stepping down (or losing) from level `n` | `radBranch + icBranch = 1` |
| `cascade` | `cascade rad ic i N` | `∏_{j=i+1..N} icBranch j` — probability of arriving at level `i` from level `N` without emitting | `= 1` when `i = N` |
| `emitYield` | `emitYield rad ic i N` | time-integrated yield of photons emitted from level `i` after excitation at `N` | `= radBranch i · cascade i N` |
| `fluoYield` | `fluoYield rad ic N` | total fluorescence quantum yield, excitation at `N` | `Σ_{i=0..N} emitYield i N` |
| `upperYield` | `upperYield rad ic N` | photons emitted from levels **above** the lowest (`Σ_{i=1..N}`) — the **leak** | `= 0` is Kasha's rule exactly |
| `specFrac` | `specFrac rad ic i N` | normalized emission spectrum entry | `Σ_i specFrac = 1` when `fluoYield ≠ 0` |
| `kashaMargin` | `kashaMargin rad ic N` | `emitYield 0 N / upperYield N` — funnel margin (N-level) | needs `upperYield > 0` |
| `funnelRatio` | `funnelRatio rad ic` | two-level funnel ratio `rad 0 · ic 1 / (rad 1 · decay 0)` | the literature `k_IC/k_rad`-shaped quantity |
| `ladderRatio` | `ladderRatio rad ic N` | N-level funnel ratio `rad 0 · cascade 0 N / (upperYield N · decay 0)` | `ladderRatio 1 = funnelRatio` |
| `RateData` | `RateData rad ic N : Prop` | the standing physical premise bundle (`0 < decay n` for `n ≤ N`, `0 ≤ rad`, `0 ≤ ic`) | an explicit hypothesis of every physical theorem |
| `KashaRule` | `KashaRule rad ic N : Prop` | `upperYield rad ic N = 0` | the exact rule |
| `KashaWithin` | `KashaWithin rad ic tol N : Prop` | `upperYield ≤ tol · fluoYield` | the tolerance form (`tol ∈ (0,1)` in practice) |
| `VavilovAt` | `VavilovAt rad ic N : Prop` | `fluoYield (N+1) = fluoYield N` | excitation at `N+1` vs `N` |
| `VavilovUpTo` | `VavilovUpTo rad ic N : Prop` | `∀ i < N, VavilovAt rad ic i` | |
| `KashaDescriptor` | `KashaDescriptor rad ic : Prop` | `∃ N, KashaRule rad ic N` | non-vacuity of the description |
| `KashaZone` | `KashaZone` (`pure` / `withinTol` / `violating`) | decidable regime classifier of a ladder at `(tol, N)` | |

---

## 3. Statement authority and inventory

**Authority**: `theories/kasha/probes/kasha-statement-skeleton.lean`. It lives under
`theories/kasha/probes/` — outside `SOURCE_DIRS` (`PhotoLean`) — because the source tree has zero
tolerance for the unfinished-proof placeholder keyword; the file's placeholders are the calibrated
signatures and its compilation at 0 error is the Sprint-0 gate. *Statement-first*: no proof work
starts before it compiles, and every delivered declaration matches it word for word (mechanical
check: `theories/BEP/probes/bep-fidelity.py --theory kasha`, which is theory-generic).

Planned inventory — **measured from the compiled skeleton** (`sha256
b645cbfbf61ecf08a7c5dbe3a5e5f8f8874e50cbc806e994ea53823dbf63aa17`, `lake env lean`, exit 0):

| milestone | module | content (declarations) |
|---|---|---|
| K1 | `PhotoLean/Kasha/Basic.lean` | 17 definitions + 2 structures/inductives + 25 theorems = **44** |
| K2 | `PhotoLean/Kasha/Criterion.lean` | 22 theorems (laws) = **22** |
| K3 | `PhotoLean/Kasha/Sharp.lean` | 15 theorems (sharp conditions + necessity witnesses) = **15** |
| K4 | `PhotoLean/Kasha/Compose.lean` | 4 definitions + 16 theorems = **20** |
| K5a | `PhotoLean/Kasha/RatModel.lean` | 16 definitions + 1 inductive + 12 theorems = **29** |
| K5b | `PhotoLean/Kasha/Instances.lean` | 14 model-constructed rows (I1–I9 with their sub-rows, I13, I14) + 6 literature rows (I10, I11, I11-alt, I11-alt2, I11t, I15) = **20** |
| **total** | | **150 declarations** (110 theorems + 37 definitions + 3 structures/inductives); I12 was dropped by the literature round's negative result (§8.2) |

The literature rows (I10–I12) are **deliberately absent** from the Sprint-0 skeleton: their Lean
literals must be transcribed from `theories/kasha/LITERATURE.md` and may not be guessed. Appending
them changes the skeleton, so it is recorded in `proofs/API-NOTES.md` and reflected in this table
before K5b is dispatched.

---

## 4. K1 — description layer (`PhotoLean/Kasha/Basic.lean`)

### 4.1 Definitions (§4.1)

```lean
structure RateData (rad ic : ℕ → ℝ) (N : ℕ) : Prop where
  decay_pos  : ∀ n, n ≤ N → 0 < decay rad ic n
  rad_nonneg : ∀ n, 0 ≤ rad n
  ic_nonneg  : ∀ n, 0 ≤ ic n

noncomputable def decay       (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n
noncomputable def radBranch   (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n / decay rad ic n
noncomputable def icBranch    (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := ic n / decay rad ic n
noncomputable def cascade     (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := ∏ j ∈ Finset.Icc (i+1) N, icBranch rad ic j
noncomputable def emitYield   (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := radBranch rad ic i * cascade rad ic i N
noncomputable def fluoYield   (rad ic : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range (N+1), emitYield rad ic i N
noncomputable def upperYield  (rad ic : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N
noncomputable def specFrac    (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := emitYield rad ic i N / fluoYield rad ic N
noncomputable def kashaMargin (rad ic : ℕ → ℝ) (N : ℕ) : ℝ := emitYield rad ic 0 N / upperYield rad ic N
noncomputable def funnelRatio (rad ic : ℕ → ℝ) : ℝ := rad 0 * ic 1 / (rad 1 * decay rad ic 0)
noncomputable def ladderRatio (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  rad 0 * cascade rad ic 0 N / (upperYield rad ic N * decay rad ic 0)

def KashaRule      (rad ic : ℕ → ℝ) (N : ℕ) : Prop := upperYield rad ic N = 0
def KashaWithin    (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : Prop :=
  upperYield rad ic N ≤ tol * fluoYield rad ic N
def VavilovAt      (rad ic : ℕ → ℝ) (N : ℕ) : Prop := fluoYield rad ic (N+1) = fluoYield rad ic N
def VavilovUpTo    (rad ic : ℕ → ℝ) (N : ℕ) : Prop := ∀ i, i < N → VavilovAt rad ic i
def KashaDescriptor (rad ic : ℕ → ℝ) : Prop := ∃ N, KashaRule rad ic N

inductive KashaZone where
  | pure      -- no emission from above the lowest state: the exact rule
  | withinTol -- emission from above the lowest state within the relative tolerance
  | violating -- emission from above the lowest state beyond the tolerance

noncomputable def kashaZone (rad ic : ℕ → ℝ) (tol : ℝ) (N : ℕ) : KashaZone :=
  if upperYield rad ic N = 0 then KashaZone.pure
  else if upperYield rad ic N ≤ tol * fluoYield rad ic N then KashaZone.withinTol
  else KashaZone.violating
```

`ladderRatio` is defined here (K1) rather than in K4 because it is the description's central
quantity (it *is* the N-level threshold variable); K4 proves its criterion and its two-level
specialization.

### 4.2 Theorems (§4.2)

| # | statement | sketch |
|---|---|---|
| 1 | `decay_eq_rad_add_ic (rad ic n) : decay rad ic n = rad n + ic n` | `rfl` |
| 2 | `radBranch_add_icBranch (h : decay rad ic n ≠ 0) : radBranch rad ic n + icBranch rad ic n = 1` | unfold, `field_simp`, `ring` |
| 3 | `radBranch_nonneg (h : RateData rad ic N) (hn : n ≤ N) : 0 ≤ radBranch rad ic n` | `div_nonneg` with `decay_pos` |
| 4 | `icBranch_nonneg (h : RateData rad ic N) (hn : n ≤ N) : 0 ≤ icBranch rad ic n` | same |
| 5 | `radBranch_le_one (h : RateData rad ic N) (hn : n ≤ N) : radBranch rad ic n ≤ 1` | from 2 |
| 6 | `icBranch_le_one (h : RateData rad ic N) (hn : n ≤ N) : icBranch rad ic n ≤ 1` | from 2 |
| 7 | `cascade_self (rad ic i) : cascade rad ic i i = 1` | `Finset.Icc_self`, product of one term |
| 8 | `cascade_nonneg (h : RateData rad ic N) (h1 : i ≤ N) : 0 ≤ cascade rad ic i N` | `Finset.prod_nonneg` with 3 |
| 9 | `cascade_le_one (h : RateData rad ic N) (h1 : i ≤ N) : cascade rad ic i N ≤ 1` | `Finset.prod_le_one` with 3 |
| 10 | `emitYield_self (rad ic i) : emitYield rad ic i i = radBranch rad ic i` | 7 |
| 11 | `emitYield_nonneg (h : RateData rad ic N) (h1 : i ≤ N) : 0 ≤ emitYield rad ic i N` | 3, 8 |
| 12 | `emitYield_le_radBranch (h : RateData rad ic N) (h1 : i ≤ N) : emitYield rad ic i N ≤ radBranch rad ic i` | 9, 3 |
| 13 | `fluoYield_eq_low_add_upper (h : RateData rad ic N) : fluoYield rad ic N = emitYield rad ic 0 N + upperYield rad ic N` | `range (N+1)` = `{0} ∪ Icc 1 N` |
| 14 | `fluoYield_zero (rad ic) : fluoYield rad ic 0 = radBranch rad ic 0` | `range 1 = {0}`, `Icc 1 0 = ∅` |
| 15 | `upperYield_zero (rad ic) : upperYield rad ic 0 = 0` | `Icc 1 0 = ∅` |
| 16 | `fluoYield_nonneg (h : RateData rad ic N) : 0 ≤ fluoYield rad ic N` | 11 |
| 17 | `upperYield_nonneg (h : RateData rad ic N) : 0 ≤ upperYield rad ic N` | 11 |
| 18 | `upperYield_le_fluoYield (h : RateData rad ic N) : upperYield rad ic N ≤ fluoYield rad ic N` | 13, 11 |
| 19 | `kashaRule_iff_upperYield_zero (rad ic N) : KashaRule rad ic N ↔ upperYield rad ic N = 0` | definitional |
| 20 | `specFrac_sum (h : fluoYield rad ic N ≠ 0) : ∑ i ∈ Finset.range (N+1), specFrac rad ic i N = 1` | `Finset.sum_div`, `Finset.sum_range_succ` |
| 21 | `kashaWithin_iff_specFrac (h : fluoYield rad ic N ≠ 0) : KashaWithin rad ic tol N ↔ 1 - specFrac rad ic 0 N ≤ tol` | 20, 13 |
| 22 | `kashaZone_eq_pure_iff (h : RateData rad ic N) : kashaZone rad ic tol N = KashaZone.pure ↔ KashaRule rad ic N` | `split_ifs` |
| 23 | `kashaZone_eq_withinTol_iff (h : RateData rad ic N) : kashaZone rad ic tol N = KashaZone.withinTol ↔ ¬ KashaRule rad ic N ∧ KashaWithin rad ic tol N` | `split_ifs` |
| 24 | `kashaZone_eq_violating_iff (h : RateData rad ic N) (htol : 0 < tol) : kashaZone rad ic tol N = KashaZone.violating ↔ ¬ KashaWithin rad ic tol N` | `split_ifs` — **statement corrected 2026-09-20**, see the correction log in §3.1 |
| 25 | `kashaRule_of_rad_zero (h : RateData rad ic N) (hzero : ∀ i, 1 ≤ i → i ≤ N → rad i = 0) : KashaRule rad ic N` | each `emitYield i N = 0` |
| 26 | `KashaZone` + `kashaZone` + `RateData` are the 3 non-theorem declarations of the table above | |

(Note: the theorem rows carry the milestone's proof obligations; the table above lists every
declaration of `Basic.lean`, definitions included in §4.1.)

### 3.1 Statement-correction log (the authority changes only through this log)

| date | row | what was wrong | correction | evidence |
|---|---|---|---|---|
| 2026-09-20 | K1 #24 `kashaZone_eq_violating_iff` | as first handed over (no premise on `tol`) the row is **false**: the classifier tests the vanishing leak first, so `upperYield = 0` parks it in `pure`, while `¬ KashaWithin` can still hold when `tol < 0`. `RateData` bounds `decay`/`rad`/`ic`, never `tol` | added the tolerance premise `(htol : 0 < tol)` (the physical range, plan §2); no other K1 row is affected — prover_a audited all 25 and the other two classifier rows are true with no positivity premise | kernel-checked counterexample `theories/kasha/probes/kasha-k1-counterexample.lean` (witness `rad ≡ 1`, `ic ≡ 1`, `N = 0`, `tol = -1`), raised by prover_a while delivering K1 |
| 2026-09-20 | K5a `kashaQVerdict_eq_violating_iff` | the same shape defect in ℚ (`QRateData` bounds no tolerance) | added `(htol : 0 < tol)` in the same pass | same witness, restated in ℚ (the row is delivered by K5a; the ℝ-side probe is the evidence) |
| 2026-09-20 | K3 #2 `kashaWithin_one_iff_ratio` | as first handed over (no premise on the sign of `decay rad ic 1`) the row is **false**: the rate-form criterion of the sibling row #1 is equivalent to the ratio form only after multiplying by the *positive* factor `decay 1`; if `decay 1 < 0` the cross multiplication flips the inequality, and `funnelRatio` can be negative while the rule holds | added `(h1 : 0 < decay rad ic 1)`, matching sibling row #1 | kernel counterexample in `theories/kasha/probes/kasha-risk-probe.lean` (`risk_kashaWithin_one_iff_ratio_refuted`, witness `rad = (1,1,0,…)`, `ic = (1,-3,0,…)`, `tol = 1/2`), raised by prover_b's Sprint-0 risk probe |
| 2026-09-20 | K3 #9 `not_kashaWithin_one_of_ratio_lt` | it is the strict side of the same (false) equivalence, so it fails on the same witness | added `(h1 : 0 < decay rad ic 1)` in the same pass | same probe file |
| 2026-09-20 | K5a `kashaWithinQ_iff_funnelRatioQ` | the ℚ twin of K3 #2, with the same defect found **independently** | added `(h1 : 0 < decayQ rad ic 1)` | kernel counterexample in `theories/kasha/probes/kasha-rat-probe.lean` (`probe_criterion_premises_insufficient`, witness `rad = twoRad 1 1`, `ic = twoIc 0 (-1)`, `tol = 1/2`), raised by prover_c |

| 2026-09-20 | plan §5.1 #12, §5.2 #21, §7.2 #8/#9/#11/#12/#13/#14 | **plan-sketch ↔ authority reconciliation** (found by verifier run 2, finding 2): **eight** rows of the plan's sketches differ from the delivered signatures — **seven strengthened**, **one weakened by dropping an unneeded premise** (`hN : 0 < N` in K2 #12, true at `N = 0` too). The seven additions: `htol : 0 ≤ tol` (K2 #21), `hpos` (K4 #8), `h0 : 0 < decay rad ic 0` (K4 #9, #11), `hr0 : 0 < rad 0` (K4 #12, #13, #14 — genuinely needed for the `Real.log` step); six of the eight rows are K4 rows. None of the seven is a mathematical defect: the authority is the source of truth and was proved as delivered | the plan's tables are corrected in place to the delivered signatures, so plan and authority agree row by row; the `Compose.lean` header's claim of "nothing added" is replaced by a pointer to this entry | verifier run 2 report (batch K2/K4/K5a), reproduced in the board's acceptance record |

Correction-log lesson (recorded for the engine): **three of the five correction rows — i.e. three of
the three distinct defects — are the same
mistake in different clothes** — a statement whose premises do not carry the sign of a quantity the
proof must divide by (the tolerance `tol`, then the total decay `decay 1`). The Sprint-0 risk probe
is what caught it before any delivered file carried the false form; `#print axioms`-clean probes are
cheap, admitted false statements are not.

---

## 5. K2 — law layer (`PhotoLean/Kasha/Criterion.lean`)

The laws of the cascade. The two headline rows are the exact rule (§5.1) and its equivalence with
Vavilov's rule (§5.2).

### 5.1 Cascade and yield laws

| # | statement | sketch |
|---|---|---|
| 1 | `cascade_succ (h : i ≤ N) : cascade rad ic i (N+1) = icBranch rad ic (N+1) * cascade rad ic i N` | `Finset.Icc_succ_right`, `Finset.prod_insert` |
| 2 | `emitYield_succ (h : i ≤ N) : emitYield rad ic i (N+1) = icBranch rad ic (N+1) * emitYield rad ic i N` | 1 |
| 3 | `emitYield_succ_self (rad ic N) : emitYield rad ic (N+1) (N+1) = radBranch rad ic (N+1)` | `cascade_self` |
| 4 | `fluoYield_succ (h : RateData rad ic (N+1)) : fluoYield rad ic (N+1) = radBranch rad ic (N+1) + icBranch rad ic (N+1) * fluoYield rad ic N` | split `range (N+2)`, 2, 3 — **the Markov recursion** |
| 5 | `upperYield_succ (h : RateData rad ic (N+1)) : upperYield rad ic (N+1) = radBranch rad ic (N+1) + icBranch rad ic (N+1) * upperYield rad ic N` | same |
| 6 | `cascade_add_upperYield (h : RateData rad ic N) : cascade rad ic 0 N + upperYield rad ic N = 1` | induction on `N` from 4/5 — **probability conservation** |
| 7 | `fluoYield_eq_one_sub_loss (h : RateData rad ic N) : fluoYield rad ic N = 1 - icBranch rad ic 0 * cascade rad ic 0 N` | 6, 13 |
| 8 | `fluoYield_le_one (h : RateData rad ic N) : fluoYield rad ic N ≤ 1` | 7, 3/4 |
| 9 | `fluoYield_mono_succ (h : RateData rad ic (N+1)) : fluoYield rad ic N ≤ fluoYield rad ic (N+1)` | 4: difference `= radBranch (N+1)·(1 - fluoYield N)` |
| 10 | `fluoYield_lt_succ_of_rad_pos (h : RateData rad ic (N+1)) (hr : 0 < rad (N+1)) (h1 : fluoYield rad ic N < 1) : fluoYield rad ic N < fluoYield rad ic (N+1)` | 4, 9 with strictness |
| 11 | `fluoYield_eq_iff_rad_zero (h : RateData rad ic (N+1)) (h1 : fluoYield rad ic N < 1) : fluoYield rad ic (N+1) = fluoYield rad ic N ↔ rad (N+1) = 0` | 4: difference `= radBranch (N+1)·(1 - fluoYield N)` |
| 12 | `fluoYield_lt_one_iff_loss (h : RateData rad ic N) : fluoYield rad ic N < 1 ↔ 0 < icBranch rad ic 0 * cascade rad ic 0 N` | 7 — the delivered row **drops** the draft's `(hN : 0 < N)`, which the identity does not need (it is true at `N = 0` as well); reconciled in §3.1 |

### 5.2 The exact rule and the Kasha–Vavilov equivalence

| # | statement | sketch |
|---|---|---|
| 13 | `upperYield_eq_zero_iff (h : RateData rad ic N) : upperYield rad ic N = 0 ↔ ∀ i, 1 ≤ i → i ≤ N → emitYield rad ic i N = 0` | `Finset.sum_eq_zero_iff_of_nonneg` with 11 |
| 14 | **`kashaRule_iff_rad_zero`** `(h : RateData rad ic N) : KashaRule rad ic N ↔ ∀ i, 1 ≤ i → i ≤ N → rad i = 0` | 13 + `radBranch i ≠ 0` (from 3, `decay_pos`) + `cascade i N ≠ 0` |
| 15 | `not_kashaRule_of_rad_pos (h : RateData rad ic N) (h1 : 1 ≤ i) (h2 : i ≤ N) (hr : 0 < rad i) : ¬ KashaRule rad ic N` | 14 |
| 16 | **`vavilovAt_iff_rad_zero`** `(h : RateData rad ic (N+1)) (h1 : fluoYield rad ic N < 1) : VavilovAt rad ic N ↔ rad (N+1) = 0` | 11 |
| 17 | `vavilovUpTo_iff_rad_zero (h : RateData rad ic N) (h1 : ∀ i, i < N → fluoYield rad ic i < 1) : VavilovUpTo rad ic N ↔ ∀ i, i < N → rad (i+1) = 0` | 16, `∀ i < N` reindexing |
| 18 | **`kashaRule_iff_vavilovUpTo`** `(h : RateData rad ic N) (hloss : 0 < ic 0) : KashaRule rad ic N ↔ VavilovUpTo rad ic N` | 14, 17, 12 — the **Kasha–Vavilov equivalence**; `hloss` makes every `fluoYield i < 1` |
| 19 | `not_kasha_universal : ∃ rad ic N, RateData rad ic N ∧ ¬ KashaRule rad ic N` | witness `rad 0 = 1, rad 1 = 1, ic 0 = 1, ic 1 = 1`, `N = 1` — **the rule is not a theorem of the model** |
| 20 | `kashaDescriptor_nonvacuous : ∃ rad ic, KashaDescriptor rad ic` | witness `rad 0 = 1`, `rad n = 0` (`n ≥ 1`), `ic n = 1` |
| 21 | `kashaWithin_of_kashaRule (h : RateData rad ic N) (htol : 0 ≤ tol) (hK : KashaRule rad ic N) : KashaWithin rad ic tol N` | 18, `0 ≤ tol·fluoYield`; the delivered row carries the two premises the draft left implicit (reconciled in §3.1) |
| 22 | `upperYield_le_sum_radBranch (h : RateData rad ic N) : upperYield rad ic N ≤ ∑ i ∈ Finset.Icc 1 N, radBranch rad ic i` | 12 |

---

## 6. K3 — sharp conditions (`PhotoLean/Kasha/Sharp.lean`)

The exact tolerance criterion (the answer to ②) and its sharpness. All rows carry the standing
positivity premises explicitly.

### 6.1 The threshold

| # | statement | sketch |
|---|---|---|
| 1 | **`kashaWithin_one_iff_rates`** `(h0 : 0 < decay rad ic 0) (h1 : 0 < decay rad ic 1) : KashaWithin rad ic tol 1 ↔ rad 1 * decay rad ic 0 * (1 - tol) ≤ tol * (rad 0 * ic 1)` | unfold the two-level sums (`Icc 1 1 = {1}`, `cascade 1 1 = 1`, `cascade 0 1 = icBranch 1`), multiply by `decay 1 * decay 0 > 0` |
| 2 | **`kashaWithin_one_iff_ratio`** `(h0 : 0 < decay rad ic 0) (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) : KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ funnelRatio rad ic` | 1 divided by `tol · rad 1 · decay 0 > 0` — **statement corrected 2026-09-20**, see §3.1 |
| 3 | **`kashaWithin_one_iff_ic_ratio`** `(hic0 : ic 0 = 0) (hr0 : rad 0 ≠ 0) (htol : 0 < tol) (h1 : 0 < decay rad ic 1) (hr : 0 < rad 1) : KashaWithin rad ic tol 1 ↔ (1 - tol) / tol ≤ ic 1 / rad 1` | 2 with `decay 0 = rad 0` — the literature form `k_IC/k_rad ≥ (1-tol)/tol` (for `tol = 1/100`: `≥ 99`) |
| 4 | `funnelRatio_eq_ladderRatio_one (h : decay rad ic 1 ≠ 0) : funnelRatio rad ic = ladderRatio rad ic 1` | unfold both |
| 5 | `kashaWithin_iff_margin (h : RateData rad ic N) (hu : 0 < upperYield rad ic N) (htol : 0 < tol) : KashaWithin rad ic tol N ↔ 1 - tol ≤ tol * kashaMargin rad ic N` | 13 of K1, divide by `upperYield > 0` |
| 6 | `kashaWithin_mono_tol (h : RateData rad ic N) (h : tol ≤ tol') : KashaWithin rad ic tol N → KashaWithin rad ic tol' N` | 18 of K1 + `mul_le_mul_of_nonneg_right` |
| 7 | `kashaWithin_zero_iff (h : RateData rad ic N) : KashaWithin rad ic 0 N ↔ KashaRule rad ic N` | `0 * fluoYield = 0`, `upperYield_nonneg` |
| 8 | `kashaWithin_one_mono_ic (h : RateData rad ic 1) (h' : RateData rad' ic' 1) (hrad : ∀ n, rad' n = rad n) (hic0 : ic' 0 = ic 0) (hic : ic 1 ≤ ic' 1) : KashaWithin rad ic tol 1 → KashaWithin rad' ic' tol 1` | the rate criterion 1 is monotone in `ic 1`. **Correction to this sketch (delivered as stated, 2026-09-20):** the sketch implicitly assumed `0 ≤ tol`; the row carries no tolerance premise and is still true, but for `tol · rad 0 < 0` the rate form forces `rad 1 = 0` and `ic 1 = 0`, hence `decay 1 = 0` against `RateData` — the implication holds vacuously on that branch. prover_b proved it as stated and documented the branch in the module header; **adding `0 ≤ tol` would weaken the row, so the authority is unchanged** |

### 6.2 Sharpness, attainment, and the counterexample

| # | statement | sketch |
|---|---|---|
| 9 | `not_kashaWithin_one_of_ratio_lt (h0 : 0 < decay rad ic 0) (h1 : 0 < decay rad ic 1) (htol : 0 < tol) (hr : 0 < rad 1) (h : funnelRatio rad ic < (1 - tol) / tol) : ¬ KashaWithin rad ic tol 1` | contrapositive of 2 — **statement corrected 2026-09-20** in the same pass, see §3.1 |
| 10 | **`kashaThreshold_attained`** `(h0 : 0 < tol) (h1 : tol < 1) : ∃ rad ic, KashaWithin rad ic tol 1 ∧ (∀ tol' : ℝ, 0 < tol' → tol' < tol → ¬ KashaWithin rad ic tol' 1)` | witness `rad 0 = 1, rad 1 = tol, ic 0 = 0, ic 1 = 1 - tol` (`funnelRatio = (1-tol)/tol` exactly) — **the threshold is attained and cannot be improved** |
| 11 | ~~`kashaWithin_one_witness`~~ — **not in the authority**: its content landed in K5b as row I1 (same constants); the sketch row is kept here as the plan's provenance and marked as carried by I1 | `norm_num`-style two-level computation (funnel ratio `= 100 ≥ 99`) |
| 12 | ~~`kashaWithin_one_negative`~~ — **not in the authority**: its content landed in K5b as row I2 (same constants), and I3b carries the below-threshold variant | funnel ratio `= 10 < 99` |
| 13 | **`perLevel_criterion_insufficient`** `: ∃ rad ic, RateData rad ic 2 ∧ (∀ i, 1 ≤ i → i ≤ 2 → rad i * decay rad ic (i-1) ≤ ic i * decay rad ic i) ∧ ¬ KashaWithin rad ic (1/2) 2` | witness `rad = fun n => 1`, `ic = fun n => 1` — **the levelwise "k_IC ≥ k_rad" criterion is false**; the general criterion is the aggregate one of K4 |
| 14 | `vavilov_premise_necessary : ∃ rad ic N, RateData rad ic N ∧ rad (N+1) ≠ 0 ∧ VavilovAt rad ic N` | witness `rad = fun n => 1`, `ic = fun n => 0` — with no loss channel `fluoYield ≡ 1` and Vavilov holds trivially while Kasha fails |
| 15 | ~~`exact_rule_only_at_zero_rad`~~ — **dropped from the sketch**: it is a re-export of K2 #14 in the sharp layer's narrative and the authority does not carry it (no duplicate statements across modules) | K2 #14 is where the content lives |
| 16 | `kashaWithin_one_sharp_boundary (h0 : 0 < tol) (h1 : tol < 1) : ∃ rad ic, funnelRatio rad ic = (1 - tol) / tol ∧ KashaWithin rad ic tol 1` | the boundary case of 2 is attained (equality ⇒ conformance) |
| 17 | `upperYield_le_sum_radBranch` — K2 #22 re-export in the sharp layer's bound block? **no**: the plan keeps a bound of the *relative* leak instead: `leak_le_of_radBranch_le (h : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ) (hN : 0 < N) : upperYield rad ic N ≤ θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N` | 12 of K1 |
| 18 | `kashaWithin_of_uniform_branch (h : ∀ i, 1 ≤ i → i ≤ N → radBranch rad ic i ≤ θ) (hθ : θ * ∑ i ∈ Finset.Icc 1 N, cascade rad ic i N ≤ tol * fluoYield rad ic N) : KashaWithin rad ic tol N` | 17 |

### 6.3 The documented finding of this milestone

K3 #13 is a *negative* mathematical result about the naive generalization: "internal conversion
faster than radiation at every level" does **not** imply Kasha conformance. The plan records it as a
finding (experience bank + `RESULTS.md` §3), because it is the reason the general criterion has to be
stated through K4's effective reduction. The literature's `k_IC ≫ k_rad` slogan is a *two-level*
statement, and the model says it must be applied to the ladder's **effective** upper level.

---

## 7. K4 — composition and bridges (`PhotoLean/Kasha/Compose.lean`)

### 7.1 Definitions (§7.1)

```lean
-- effective two-level data of the ladder at excitation level N: the whole upper block
-- collapses to one level whose branches are the block's totals
noncomputable def effRad (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then rad 0 else if n = 1 then upperYield rad ic N else 0
noncomputable def effIc (rad ic : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n => if n = 0 then ic 0 else if n = 1 then cascade rad ic 0 N else 0

noncomputable def marcusIC (A lam kB T x : ℝ) : ℝ := A * Real.exp (-(PhotoLean.Marcus.barrier lam x) / (kB * T))
noncomputable def kashaGapThreshold (A rad0 dec0 rad1 tol : ℝ) : ℝ :=
  A * rad0 * tol / (rad1 * dec0 * (1 - tol))
```

### 7.2 Theorems (§7.2)

| # | statement | sketch |
|---|---|---|
| 1 | `cascade_compose (h1 : i ≤ M) (h2 : M ≤ N) : cascade rad ic i N = cascade rad ic i M * cascade rad ic M N` | split `Icc (i+1) N` at `M` |
| 2 | `emitYield_compose (h) : emitYield rad ic i N = cascade rad ic M N * emitYield rad ic i M` | 1 (`i ≤ M ≤ N`) |
| 3 | `effDecay_zero (rad ic N) : decay (effRad rad ic N) (effIc rad ic N) 0 = decay rad ic 0` | `if`-reduction |
| 4 | `effDecay_one (rad ic N) : decay (effRad rad ic N) (effIc rad ic N) 1 = upperYield rad ic N + cascade rad ic 0 N` | `if`-reduction |
| 5 | `effUpperYield_one (h : RateData rad ic N) : upperYield (effRad rad ic N) (effIc rad ic N) 1 = upperYield rad ic N / (upperYield rad ic N + cascade rad ic 0 N)` | `Icc 1 1`, `cascade_self` |
| 6 | `effEmitYield_zero_one (h) : emitYield (effRad …) (effIc …) 0 1 = emitYield rad ic 0 N / (upperYield rad ic N + cascade rad ic 0 N)` | unfold with 3, 4 |
| 7 | **`kashaMargin_effective`** `(h : RateData rad ic N) (hu : 0 < upperYield rad ic N) : kashaMargin (effRad rad ic N) (effIc rad ic N) 1 = kashaMargin rad ic N` | 5, 6 — **the ladder's margin is a two-level margin** |
| 8 | **`kashaWithin_iff_effective`** `(h : RateData rad ic N) (hpos : 0 < upperYield rad ic N + cascade rad ic 0 N) : KashaWithin rad ic tol N ↔ KashaWithin (effRad rad ic N) (effIc rad ic N) tol 1` | `fluoYield = low + upper`, multiply by `1/(u+C) > 0` — **every ladder is a two-level model in disguise** |
| 9 | **`kashaWithin_iff_ladderRatio`** `(h : RateData rad ic N) (hu : 0 < upperYield rad ic N) (htol : 0 < tol) (h0 : 0 < decay rad ic 0) : KashaWithin rad ic tol N ↔ (1 - tol) / tol ≤ ladderRatio rad ic N` | 7, 8, K3 #2 — **the N-level threshold**, the general answer to ② |
| 10 | `ladderRatio_one (h : decay rad ic 1 ≠ 0) : ladderRatio rad ic 1 = funnelRatio rad ic` | unfold |
| 11 | `not_kashaWithin_of_ladderRatio_lt (h : RateData rad ic N) (hu : 0 < upperYield rad ic N) (htol : 0 < tol) (h0 : 0 < decay rad ic 0) (hlt : ladderRatio rad ic N < (1 - tol)/tol) : ¬ KashaWithin rad ic tol N` | 9 |
| 12 | **`kashaWithin_one_marcus`** `(h : RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : ic 1 = marcusIC A lam kB T x) : KashaWithin rad ic tol 1 ↔ (lam - x)^2 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol)` | K3 #1 + `Real.exp`/`Real.log` monotonicity, then multiply by `4·lam > 0`; the gap `x` is the `S₂–S₁` energy gap, `barrier` is `PhotoLean.Marcus.barrier` |
| 13 | **`not_kashaWithin_of_gap_far`** `(h : RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : ic 1 = marcusIC A lam kB T x) (hfar : …) : ¬ KashaWithin rad ic tol 1` | 12 (the anti-Kasha direction: the gap is outside the window) |
| 14 | `kashaWindow_halfWidth` `(h : RateData rad ic 1) (htol0 : 0 < tol) (htol1 : tol < 1) (hA : 0 < A) (hlam : 0 < lam) (hkT : 0 < kB * T) (hr0 : 0 < rad 0) (hr1 : 0 < rad 1) (hic : …) (h0 : 0 ≤ 4 * lam * (kB * T) * Real.log (kashaGapThreshold …)) : KashaWithin rad ic tol 1 ↔ \|lam - x\| ≤ Real.sqrt (4 * lam * (kB * T) * Real.log (kashaGapThreshold …))` | 12 + the `sqrt` recipe of `theories/BEP/probes/bep-api-abs-sqrt.lean` (the API-notes recipe; the absolute-value route is the one that worked there) |
| 15 | `kashaGapThreshold_pos (hA : 0 < A) (hr0 : 0 < rad 0) (htol : 0 < tol) (hdec : 0 < decay rad ic 0) (hr1 : 0 < rad 1) (htol1 : tol < 1) : 0 < kashaGapThreshold A (rad 0) (decay rad ic 0) (rad 1) tol` | `div_pos`, `mul_pos` |
| 16 | `marcusIC_pos (hA : 0 < A) : 0 < marcusIC A lam kB T x` | `Real.exp_pos` |

**K4b — closed 2026-09-20 (outcome: stays a declared premise).** The exponential-race derivation of
the branching probability (`ic n / decay n` from two competing exponential clocks) was probed in
`theories/kasha/probes/kasha-api-race.lean`. The outcome is a **typed statement with no bounded proof
in budget**: `(expMeasure a).prod (expMeasure b) {p | p.1 < p.2} = ofReal (a/(a+b))` elaborates, and
the supporting pieces (`expMeasure r (Ioi x) = ofReal (exp (-(r*x)))`, `∫ x in Ioi 0, exp (-(c*x)) = 1/c`,
`expMeasure r = volume.withDensity (exponentialPDF r)`) are kernel-checked, but the missing bridge
(`iIndepFun` ↔ `Measure.prod`), the density-measure and `Ioi 0` bookkeeping, the `ofReal`
integrability conditions and the `s < 0` a.e. split amount to roughly a hundred lines of measure
theory — a sprint of its own, out of scope here. The row therefore stays **out** of the statement
authority, the branching probability stays a declared modelling premise (§13.5), and the negative
result is recorded in `proofs/API-NOTES.md` §kasha (f) and in `proofs/EXPERIENCE.md`. **No delivered
statement depends on a failed probe.**

**K4c (bridge bookkeeping)**: the Marcus bridge is a *model-side* conditional statement. The
docstring of `kashaWithin_one_marcus` must carry the literature caveat from
`theories/kasha/LITERATURE.md` (the classical strong-coupling Marcus form is not the general
energy-gap law; Jortner's exponential form and the promoting-mode/franck-condon factors are outside
the model), and `RESULTS.md` must present it as such.

---

## 8. K5 — instances and verdicts

### 8.1 K5a — computable rational verdict layer (`PhotoLean/Kasha/RatModel.lean`)

The ℚ mirror of K1's definitions (same bodies, `ℚ` instead of `ℝ`), so that instance verdicts are
kernel computations:

```lean
def decayQ (rad ic : ℕ → ℚ) (n : ℕ) : ℚ := rad n + ic n
def radBranchQ / icBranchQ / cascadeQ / emitYieldQ / fluoYieldQ / upperYieldQ / specFracQ
def funnelRatioQ (rad ic : ℕ → ℚ) : ℚ := rad 0 * ic 1 / (rad 1 * decayQ rad ic 0)
def ladderRatioQ (rad ic : ℕ → ℚ) (N : ℕ) : ℚ := rad 0 * cascadeQ rad ic 0 N / (upperYieldQ rad ic N * decayQ rad ic 0)
def KashaWithinQ (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : Prop := upperYieldQ rad ic N ≤ tol * fluoYieldQ rad ic N
def QRateData (rad ic : ℕ → ℚ) (N : ℕ) : Prop := (∀ n, n ≤ N → 0 < decayQ rad ic n) ∧ (∀ n, 0 ≤ rad n) ∧ (∀ n, 0 ≤ ic n)
inductive KashaQVerdict where
  | pure | withinTol | violating
def kashaQVerdict (rad ic : ℕ → ℚ) (tol : ℚ) (N : ℕ) : KashaQVerdict := …
```

Theorems: the cast bridges (one per definition, `Rat.cast_*` family; `ℚ`-side strictness lemmas so
that a verdict computed in ℚ transfers to ℝ), the three classifier equivalences
(`kashaQVerdict_eq_pure_iff`, `_withinTol_iff`, `_violating_iff` — the third carries the corrected
tolerance premise `0 < tol`, see §3.1), the ℚ criterion
(`kashaWithinQ_iff_funnelRatioQ` — carries the corrected premise `0 < decayQ rad ic 1`, §3.1), and
two witness/negative-control rows pinning the recipe. **Trap
recorded in the API log**: `by decide` does not close ℚ goals containing `/`-literals
(`Rat.blt` → `Int.decNonneg` does not reduce) and `native_decide` is banned
(`Lean.ofReduceBool` is outside `ALLOWED_AXIOMS`) — verdicts are closed by `norm_num`, exactly as in
BEP's K5.

### 8.2 K5b — instance rows (`PhotoLean/Kasha/Instances.lean`, I1–I14)

Each row is a kernel-checked verdict on concrete rational rate data. Rows marked `literature` carry
the source's printed numbers with provenance in `theories/kasha/LITERATURE.md`; rows marked
`model-constructed` are model realizations of a regime and are labelled as such (never presented as
data). Planned rows:

| row | kind | content | what it decides |
|---|---|---|---|
| I1 | model-constructed | two-level ladder `rad 0 = rad 1 = 1`, `ic 0 = 0`, `ic 1 = 100` | `KashaWithin 1/100 1` (the literature threshold 99 is met) |
| I2 | model-constructed | same with `ic 1 = 10` | `¬ KashaWithin 1/100 1` (the anti-Kasha control at the same tolerance) |
| I3 | model-constructed | the boundary ladder `ic 1 = 99` | `KashaWithin 1/100 1` with equality |
| I3b | model-constructed | one unit below (`ic 1 = 9899/100`) | the boundary is sharp: `¬ KashaWithin 1/100 1` |
| I4, I5 | model-constructed | the `N = 1` values `fluoYieldQ = 1`, `upperYieldQ = 1/101` | the recursion of K2 #4/#5 at concrete rationals |
| I6 | model-constructed | the `N = 2` value `fluoYieldQ = 7/8` for the equal-rates ladder with `ic 0 = 1` | the recursion at `N = 2` |
| I7, I7b | model-constructed | the equal-rates ladder (`rad n = ic n = 1`, `N = 2`): leak `3/4`, and `¬ KashaWithin 1/2 2` while every level satisfies `rad ≤ ic` | K3 #13's counterexample at concrete numbers |
| I8, I8b | model-constructed | no-loss ladder (`rad ≡ 1`, `ic ≡ 0`, `N = 1`) | `VavilovAt` holds and `KashaRule` fails — K3 #14's witness |
| I9 | model-constructed | the verdict classifier on the I2 data | `kashaQVerdict = violating` |
| I13 | summary | the I1/I2 verdicts as one conjunction | the row inventory is reproducible |
| I14 | non-vacuity | both verdict kinds occur among the model-constructed rows | the layer is not one-sided |
| I10 | literature | 4,6,8-trimethylazulene in cyclohexane: `rad 1 = 33`, `ic 1 = 67000` (units `10⁶ s⁻¹`; 1995 thesis Table 3.3 p. 126) | `KashaWithinQ 1/100 1` (ratio ≈ 2030 ≥ 99) |
| I11 | literature | parent azulene in cyclohexane: `rad 1 = 35`, `ic 1 = 720` (thesis Table 3.1 p. 115) | `¬ KashaWithinQ 1/100 1` (ratio ≈ 20.6) |
| I11-alt | literature | azulene via the **printed quantum yield** route: `Φ_Fl = 2.42 %` ⇒ `rad 1 = 242`, `ic 1 = 9758` (*Chem. Sci.* 2026 Table 2/3) | `¬ KashaWithinQ 1/100 1` (ratio ≈ 40.3) |
| I11-alt2 | literature | azulene, peer-reviewed experimental rates: `k_r(S₂) = 2.3×10⁷`, `k_IC(S₂→S₁) = 5.3×10⁸ s⁻¹` (Veys & Escudero, *JPCA* **124**, 7228 (2020) Table 2) | `¬ KashaWithinQ 1/100 1` (ratio ≈ 23.0) |
| I11t | literature | the **same** I11 data at two tolerances | `¬ KashaWithinQ 1/100 1 ∧ KashaWithinQ 1/10 1` — conformance is tolerance-relative, and `tol = 1/100` is the model's choice (§R1.3/§R1.6) |
| I15 | literature summary | the two azulene-family rows at one tolerance | the methylated derivative conforms while the parent violates, at `tol = 1/100` |
| ~~I12~~ | — | **dropped 2026-09-20**: the literature round found **no** second anti-Kasha molecule with first-hand numbers (§R1.6); ovalene is excluded because its S₁/S₂ populations are thermal (gap ≈ 1200 cm⁻¹), i.e. a different mechanism (§R1.5) | — |

Row names are fixed by the statement authority; the literature rows' *numbers* are transcribed from
`theories/kasha/LITERATURE.md` and their docstrings carry the source locus, the unit (s⁻¹) and the
evidence strength. **A literature row whose numbers are not first-hand is dropped, not guessed** —
the row then becomes `UNSUPPORTED` in the literature record and the drop is reported in
`RESULTS.md`.

---

## 9. Sprint order, ownership, and dispatch

Ownership is exclusive per file. The dependency graph is: K1 → {K2, K3, K4, K5a} → K5b; K4's Marcus
bridge additionally consumes `PhotoLean.Marcus.Basic` (`barrier`) — an already delivered module, no
new dependency.

| sprint | owner | deliverable | gate |
|---|---|---|---|
| 0 | lead | `theories/kasha/{plan.md,TASKS.md,LITERATURE.md,RESULTS.md,probes/}`, contract `THEORIES` extension, statement skeleton compiling | `check.sh --strict` PASS on the data plane; `lake env lean` on the skeleton, 0 errors |
| 0 | api_researcher | API calibration for the K1–K5 statement list + risk probes (`theories/kasha/probes/kasha-api-*.lean`), `proofs/API-NOTES.md` §kasha | probes compile, 0 warnings |
| 0 | literature_researcher | `theories/kasha/LITERATURE.md` round 1 (canonical statement, rate inequalities, instance numbers, gap-law caveat) | record lands with provenance |
| 1 | prover_a | K1 `Basic.lean` (critical path — everything imports it) | `check.sh --strict PhotoLean.Kasha.Basic` |
| 2 | prover_a | K2 `Criterion.lean` | `check.sh --strict PhotoLean.Kasha.Criterion` |
| 2 | prover_b | K3 `Sharp.lean` | `check.sh --strict PhotoLean.Kasha.Sharp` |
| 2 | prover_c | K5a `RatModel.lean` | `check.sh --strict PhotoLean.Kasha.RatModel` |
| 2 | prover_d | K4 `Compose.lean` (dependent on K1+K3 statements; the K3 *statements* are in the skeleton, so the file can be written against the skeleton and compiled once K3 lands) | `check.sh --strict PhotoLean.Kasha.Compose` |
| 3 | prover_c | K5b `Instances.lean` | `check.sh --strict PhotoLean.Kasha.Instances` |
| 3 | verifier | independent acceptance of K1–K5b (build + strict scan + `#print axioms` + fidelity + instance cross-check) | PASS/FAIL report |
| 3 | lead | board ticking, `RESULTS.md` (bilingual), experience-bank round, commits | frozen-state audit |

Parallelism discipline: because everything imports K1, Sprint 1 is a single-owner critical path;
Sprints 2–3 fan out. No two owners on one file, ever. A worker that finds a statement defect stops
and reports to the lead (statement changes go through the skeleton and are recorded in the API log).

---

## 10. Risks and mitigations

| risk | why it is a risk | mitigation |
|---|---|---|
| **Finset index bookkeeping** (`Icc`/`range` splits) | the cascade sums/products over `Icc (i+1) N` and `range (N+1)` need index surgery (`Icc_succ_right`, `sum_range_succ`, disjoint unions at `0` and at `M`) | api_researcher calibrates the exact lemma names first; prover_a's K1 lands the six index lemmas (`cascade_self`, `cascade_succ`, `fluoYield_eq_low_add_upper`, `fluoYield_succ`, `upperYield_succ`, `cascade_compose`) before any dependent work |
| **`Real.log`/`Real.sqrt` bridge** | K4 #12–#14 combine `exp`/`log` monotonicity with a square/sqrt step | the `sqrt` recipe is **already calibrated** in `theories/BEP/probes/bep-api-abs-sqrt.lean` (two independent routes) and `proofs/API-NOTES.md`; K4 #12 (the squared, log-only form) is primary and #14 is the corollary — if #14 fails its probe, #12/#13 stand alone and the deferral is recorded (never a placeholder) |
| **ℚ verdict computation** | `by decide` fails on `/`-bearing ℚ goals; `native_decide` is banned | use `norm_num` (BEP's measured recipe), keep every instance row to `norm_num`-sized arithmetic |
| **Statement drift vs. the plan** | BEP's experience: the dispatch text is not the authority | the skeleton is generated *from this plan* in one pass and compiled before any prover starts; `bep-fidelity.py --theory kasha` makes drift mechanically checkable |
| **The Marcus bridge overstates the physics** | the classical Marcus form is not the general gap law | the identification is an explicit hypothesis (`hic`), the caveat is in the docstring and in `RESULTS.md`, and the literature record carries the limit |
| **Literature rows without first-hand numbers** | BEP's F4 row had to be dropped after the fact | the literature round is asked for per-point data *with page references*; rows without them are dropped (`UNSUPPORTED`) before the instance layer is written |
| **K5b depends on K5a and on the literature round** | two dependencies | K5b is Sprint 3, after both land; the model-constructed rows (I1–I9) do not depend on the literature at all |

---

## 11. Acceptance criteria and gate commands

Every milestone row is accepted only when all four gates pass on a frozen tree (contract
`proofs/ENGINE.yml`):

```bash
proofs/scripts/lake build PhotoLean.Kasha.<Module>                       # 1. compiles
proofs/scripts/check.sh --strict PhotoLean.Kasha.<Module>                # 2. build + placeholder/axiom scan
proofs/scripts/axioms.sh PhotoLean.Kasha.<Module> PhotoLean.Kasha.<name> # 3. #print axioms → only propext, Classical.choice, Quot.sound
git log -1 --oneline                                                     # 4. commit format feat(<area>): <lemma>
```

* `lake build` succeeding is **not** acceptance; the strict scan and `#print axioms` are, and the
  verifier runs them independently (the writing role never self-certifies).
* `lakefile.toml`'s `defaultTargets` gains one line per delivered module. **Registered deviation
  (lead, 2026-09-20):** the line lands in a *separate, lead-owned* commit, not "in the same commit as
  the module" as first written here, because `lakefile.toml` is lead-owned and the workers are
  forbidden to edit it. The rule's purpose — no delivered module outside the build — is enforced by
  the lead immediately after each module lands, and the final frozen-state run of
  `proofs/scripts/check.sh --strict` (bare) is the check that it was.
* Milestone acceptance uses the scoped fidelity report: `python3 theories/BEP/probes/bep-fidelity.py
  --theory kasha --milestone <K1…K5b>` (added 2026-09-20 in response to verifier finding MEDIUM-6 —
  the unscoped checker's headline number grows while a milestone is being verified, so it cannot serve
  as that milestone's criterion).
* One commit per lemma, `feat(K<n>): <lemma>`; documentation commits use `docs(...)`.
* Closeout: a frozen-state audit of `RESULTS.md`/plan/board/literature — every number in those files
  must be a measured value from the delivered tree, and a verdict is only recorded from an audit
  report that exists (the BEP closeout's rule).

---

## 12. Honesty table — what is assumed, what is proved

| claim | status |
|---|---|
| the ladder model, its two channels per level, and the observables | **modelling assumption** (this plan's §1.2, §13) |
| the branching probabilities are those of competing exponential clocks | **modelling assumption** (probe K4b closed 2026-09-20: the statement types but its bounded proof is out of budget — `theories/kasha/probes/kasha-api-race.lean`, API-NOTES §kasha (f)) |
| the time-integrated yields are the observables of Kasha/Vavilov spectroscopy | **modelling assumption** (no time-resolved kinetics) |
| `KashaRule ⟺ rad = 0` above the lowest level (K2 #14) | **theorem** |
| `KashaRule ⟺ VavilovUpTo` with `ic 0 > 0` (K2 #18) | **theorem** (the loss premise is explicit) |
| the sharp tolerance threshold (K3 #1–#3, K4 #9) | **theorem**, with the `RateData` positivity premises explicit |
| the threshold is attained and cannot be improved (K3 #10) | **theorem** |
| the levelwise `k_IC ≥ k_rad` criterion is insufficient (K3 #13) | **theorem** (counterexample) |
| the Marcus gap window (K4 #12–#14) | **theorem conditional on the explicit `hic` hypothesis**, whose physical identification is a literature-caveated modelling premise |
| instance verdicts (K5b) | **kernel computations** about the stated rational data; literature rows are only as good as the numbers in `theories/kasha/LITERATURE.md` |
| `KashaWithin` is defined for every `tol : ℝ` | exposure, not unsoundness (verifier finding LOW-7): every criterion row carries `0 < tol` explicitly, and the honesty table notes that a row without it would silently read a non-physical tolerance |
| `kashaMargin` is `0/0`-degenerate exactly when the rule holds | exposure, not unsoundness (verifier finding LOW-7): totalized division makes the margin `0` on the branch it is named for, so the margin is only consumed under `0 < upperYield` — that premise is explicit in K3 #5 and K4 #7/#9 |

---

## 13. Scope limits (registered, not hidden)

1. The number of levels is finite and the ladder is truncated at the excitation level;
   above-`N` levels are not modelled.
2. Vibrational manifolds, vibronic coupling and Franck–Condon factors are not modelled: `ic n` is a
   black-box rate constant.
3. Spin multiplicity is a *scope choice*, not a modelled quantity: the ladder of one multiplicity is
   modelled at a time (`S₁` for fluorescence); intersystem crossing enters only as part of the
   lowest level's loss channel `ic 0`.
4. No temperature, solvent, concentration or aggregation dependence; no radiative or non-radiative
   transfer between molecules.
5. The yields are time-integrated probabilities; no rate equations, no transients, no collisions,
   no re-excitation.
6. The Marcus bridge (K4) is conditional and classical; the general energy-gap law's exponential
   form is out of scope. **Attribution requirement (literature round 1, §R1.7)**: the hypothesis
   `hic : ic 1 = marcusIC …` may only be presented as the *single-effective-mode, strong-coupling /
   classical high-temperature limit* of the radiationless-transition rate (sources recorded in
   `theories/kasha/LITERATURE.md` §R1.7.3: Jang, *JCP* **155**, 164106 (2021) for the two assumptions
   behind the gap law; Bozzi & Rocha, *JCTC* **19**, 2316, and Sutcliffe–Cagan–Hadt, *JACS* **146**,
   15506, for the Marcus-type limits); the delivered docstrings and `RESULTS.md` must say so.
7. **No global monotonicity claim about nonradiative rates and the energy gap.** The literature round
   found first-hand evidence *against* a monotone global statement — in the azulene family two
   channels with nearly equal gaps (14 010 vs 14 370 cm⁻¹) differ by about four orders of magnitude
   (§R1.4, §R1.8) — so `ic n` stays an unstructured scalar per level. A statement of the form "the IC
   rate decreases with the gap" must not be added, and the Marcus bridge (K4) is *per channel*: its
   `lam`, `A` are parameters of the `S₂ → S₁` channel it models, not of the molecule.
7. Instances are arithmetic verdicts about printed numbers, not fits; `UNSUPPORTED` marks are
   reported rather than filled with guesses.

---

## 14. Leaves

| leaf | path |
|---|---|
| plan (this file) | `theories/kasha/plan.md` |
| board | `theories/kasha/TASKS.md` |
| literature record | `theories/kasha/LITERATURE.md` |
| statement authority + probes | `theories/kasha/probes/` |
| bilingual deliverable | `theories/kasha/RESULTS.md` |
| Lean sources | `PhotoLean/Kasha/{Basic,Criterion,Sharp,Compose,RatModel,Instances}.lean` |
| source artifacts | `theories/kasha/literature/` (README + the Birks 1976 NIST text; size policy in the README) |
| API calibration (shared) | `proofs/API-NOTES.md` §kasha |
| experience bank (shared) | `proofs/EXPERIENCE.md` |
