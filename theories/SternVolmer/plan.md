# theories/SternVolmer/plan.md — PhotoLean formalization plan: Stern–Volmer quenching and the D1 identifiability adjudication (SV1–SV4)

> Status: **Phase 1 (statement formalization)** — the statement inventory of §4 is the frozen
> design; the statement authority `probes/SternVolmer-statement-skeleton.lean` transcribes it
> verbatim with placeholder proof bodies. No proof work in Phase 1.
> Authority: contract `proofs/ENGINE.yml`; board `theories/SternVolmer/TASKS.md`.
> Batch: the photophysics subgraph (human request 2026-09-22), group A (rate-cascade basis);
> home of adjudication target **D1** (static vs dynamic quenching — the Stern–Volmer
> identifiability boundary).

---

## 1. Overall goal and boundaries

### 1.1 The claim being adjudicated

Stern–Volmer analysis plots `I₀/I` against the quencher concentration `[Q]`. **Dynamic**
(collisional) quenching adds a concentration-dependent decay channel `kq·[Q]` to the excited
state, giving `I₀/I = τ₀/τ = 1 + kq·τ₀·[Q]`. **Static** quenching (ground-state complexation)
removes a fraction of fluorophores from the observed population, giving `I₀/I = 1 + Ka·[Q]` while
the lifetime of the remaining (free) fluorophores is unchanged. Both plots are *linear* — and the
literature routinely reads "linear Stern–Volmer plot" as "dynamic quenching". **D1 decides this
conflation**: (i) both mechanisms give exactly linear intensity plots (two theorems); (ii) the
intensity-only observation map is **not injective** on the mechanism space — a dynamic and a
static parameter set give pointwise-identical intensity curves at every concentration (the
conflation witness); (iii) the exact identifiability boundary is the lifetime channel: within the
two-mechanism model space, "lifetime ratio tracks intensity ratio" holds **iff** the mechanism is
dynamic (with `Ka > 0` load-bearing); (iv) coexistence is positively witnessed by *upward
curvature* (a nonzero second difference), which no single mechanism produces.

### 1.2 The model (chosen, not derived)

One excited state with intrinsic decay `k0 = kr + knr` (radiative + nonradiative), quencher
concentration `q : ℝ`. Intensity is proportional to the fluorescence quantum yield
`kr / decay`; lifetime is the inverse decay. Static quenching removes emitters by the
association isotherm `free fraction = 1/(1 + Ka·q)` — the linearized-binding form. Everything is
algebraic over ℝ with totalized division; every positivity premise is explicit (engine rule 3,
weakest-premise standard).

### 1.3 Explicit non-goals

* No diffusion theory (kq is a parameter; the Smoluchowski derivation is out of scope).
* No sphere-of-action / exponential static models (registered as future extensions; the
  adjudication needs the two textbook forms only).
* No time-resolved decay profiles — the lifetime enters through its ratio only.

---

## 2. Conventions and symbols

`k0 > 0` intrinsic total decay; `kq ≥ 0` dynamic quenching constant; `Ka ≥ 0` static association
constant; `q` concentration. `KSV k0 kq := kq / k0` — the Stern–Volmer constant (= `kq·τ₀`).
`Mech := dyn | stat` — the mechanism tag of the two-mechanism model space. Namespace
`PhotoLean.SternVolmer`; the rational decision layer lives in `PhotoLean.SternVolmer.Rat`.

## 3. Statement authority and inventory

The authority is `probes/SternVolmer-statement-skeleton.lean` (Phase-1 placeholder bodies;
sha256 recorded on the board once compiling).

### 3.1 Statement-correction log

* **Entry 3 (SV-I4, 2026-09-23, Phase-3 vacuity audit, verifier run 1 finding
  M3)** — `mixed_witness` was re-frozen: the tautological third conjunct `0 < 1` (no model
  object) is replaced by the model-tied second difference
  `svRatioBoth 2 1 1 (0 + 1) - 2 * svRatioBoth 2 1 1 0 + svRatioBoth 2 1 1 (0 - 1) = 1` — the
  SV-C9 value `2·KSV·Ka·h² = 1` read off the model object itself.
* **Entry 4 (SV-C10, 2026-09-23, Phase-3 premise audit)** — `d1_verdict` drops the unconsumed
  `hkq : 0 < kq` and weakens `hk0 : 0 < k0` to `hk0 : k0 ≠ 0` (the coincidence and linearity
  conjuncts need exactly `k0 ≠ 0` under totalized division; the boundary conjunct needs nothing
  on `k0` after entry 2).

* **Entry 1 (SV-R1, 2026-09-22, found while proving; re-freeze executed by the lead)** — the four
  cast-coherence rows were **vacuous as first frozen**: a `Rat.`-prefixed declaration elaborates
  its type inside the `Rat` namespace, so the unqualified right-hand side (`svRatioDyn` etc.)
  resolved to the ℚ shadow and each row became the identity `↑x = ↑x`, closable by `rfl` —
  contradicting the row's own docstring, the §4 text and the Phase-1 api probe (which measured the
  shape in an unnamed `example`, i.e. in the outer namespace, hence the intended reading).
  Evidence: `#print` before the fix showed `@Rat.cast (Rat.svRatioDyn a b q)` on both sides.
  **Fix**: fully-qualified right-hand sides (`PhotoLean.SternVolmer.svRatioDyn (a : ℝ) (b : ℝ)
  (q : ℝ)` etc.), delivered proofs by fully-qualified `unfold` + `norm_cast`; `#print` after the
  fix shows the real bridge; the transitional `rat_*_cast_real` workaround rows were removed.
  Authority sha256 is now `d4b129c125254d8e9a9c26243a3d6596183942086136fae97a6fc98735aa0baf`.

## 4. Statement inventory

Module plan (Phase 2): `Basic.lean` (SV-B), `Criterion.lean` (SV-C, the D1 core), `RatModel.lean`
(SV-R), `Instances.lean` (SV-I).

**SV-B (description layer, all definitions):**

* SV-B1 `dynDecay (k0 kq q : ℝ) : ℝ := k0 + kq * q` — decay rate under dynamic quenching.
* SV-B2 `svRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0` — the dynamic intensity ratio
  `I₀/I` (yield ratio `kr/decay(q)` over `kr/decay(0)`).
* SV-B3 `tauRatioDyn (k0 kq q : ℝ) : ℝ := dynDecay k0 kq q / k0` — the dynamic lifetime ratio
  `τ₀/τ`; the identical body **is** the physical claim of the dynamic mechanism (both observables
  are the decay ratio), registered here and in the SV-C1 docstring.
* SV-B4 `svRatioStat (Ka q : ℝ) : ℝ := 1 + Ka * q` — the static intensity ratio (inverse free
  fraction).
* SV-B5 `tauRatioStat (Ka q : ℝ) : ℝ := 1` — the static lifetime ratio: the observed (free)
  fluorophores decay unchanged.
* SV-B6 `KSV (k0 kq : ℝ) : ℝ := kq / k0` — the Stern–Volmer constant.
* SV-B7 `svRatioBoth (k0 kq Ka q : ℝ) : ℝ := svRatioDyn k0 kq q * svRatioStat Ka q` — combined
  mechanism (dynamic quenching of the free fraction).
* SV-B8 `inductive Mech | dyn | stat`; `svRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ` and
  `tauRatioOf (m : Mech) (k0 kq Ka q : ℝ) : ℝ` — the mechanism-tagged observation pair.
* SV-B9 `LifetimeTracks (m : Mech) (k0 kq Ka : ℝ) : Prop :=
  ∀ q, 0 < q → tauRatioOf m k0 kq Ka q = svRatioOf m k0 kq Ka q` — the discriminating
  observable: the lifetime ratio tracks the intensity ratio at every positive concentration.

**SV-C (laws + the D1 core):**

* SV-C1 `dyn_lifetime_tracks_intensity (k0 kq : ℝ) : ∀ q, tauRatioDyn k0 kq q = svRatioDyn k0 kq q`
  — definitional (the identical bodies); the content is the contrast SV-C2.
* SV-C2 `stat_lifetime_flat (Ka : ℝ) : ∀ q, tauRatioStat Ka q = 1` and
  `stat_lifetime_separates (hKa : 0 < Ka) (hq : 0 < q) :
  tauRatioStat Ka q ≠ svRatioStat Ka q`.
* SV-C3 `svRatioDyn_linear (hk0 : k0 ≠ 0) : svRatioDyn k0 kq q = 1 + KSV k0 kq * q` — the dynamic
  plot is exactly linear with slope `KSV`, intercept `1`.
* SV-C4 `svRatioStat_linear (Ka q : ℝ) : svRatioStat Ka q = 1 + Ka * q` — the static plot is
  exactly linear with slope `Ka`, intercept `1` (definitional; registered so that "both linear"
  is a theorem pair, not a slogan).
* SV-C5 `svRatioDyn_at_zero (hk0 : k0 ≠ 0) : svRatioDyn k0 kq 0 = 1`;
  `svRatioStat_at_zero (Ka : ℝ) : svRatioStat Ka 0 = 1`.
* SV-C6 `svRatioDyn_strictMono_q (hk0 : 0 < k0) (hkq : 0 < kq) (h : q₁ < q₂) :
  svRatioDyn k0 kq q₁ < svRatioDyn k0 kq q₂`; `svRatioStat_strictMono_q (hKa : 0 < Ka)
  (h : q₁ < q₂) : svRatioStat Ka q₁ < svRatioStat Ka q₂`.
* SV-C7 (**D1a, the conflation**) `intensity_curve_coincidence {k0 kq Ka : ℝ} (hk0 : k0 ≠ 0)
  (hK : KSV k0 kq = Ka) : ∀ q, svRatioDyn k0 kq q = svRatioStat Ka q` — matched parameters give
  pointwise-identical intensity plots at **every** concentration: the intensity-only observation
  map is not injective on the mechanism space.
* SV-C8 (**D1b, the boundary**) `lifetimeTracks_iff_dyn {k0 kq Ka : ℝ} (hk0 : 0 < k0)
  (hKa : 0 < Ka) : ∀ m : Mech, (LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn)` — within the
  two-mechanism model space, lifetime-tracking decides the mechanism exactly. (Weakest-premise
  note: no hypothesis on `kq` — at `kq = 0` the dynamic plot is flat and tracking still holds;
  `0 < Ka` is load-bearing — at `Ka = 0` the static plot is flat and tracking holds there too.)
* SV-C9 (**D1c, coexistence is positively witnessed**) `svRatioBoth_eq (hk0 : k0 ≠ 0) :
  svRatioBoth k0 kq Ka q = 1 + (KSV k0 kq + Ka) * q + KSV k0 kq * Ka * q ^ 2`;
  `svRatioBoth_secondDifference (hk0 : k0 ≠ 0) (x h : ℝ) :
  svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x + svRatioBoth k0 kq Ka (x - h)
    = 2 * KSV k0 kq * Ka * h ^ 2`;
  `svRatioDyn_secondDifference (hk0 : k0 ≠ 0) (x h : ℝ) :
  svRatioDyn k0 kq (x + h) - 2 * svRatioDyn k0 kq x + svRatioDyn k0 kq (x - h) = 0`;
  `svRatioStat_secondDifference (Ka x h : ℝ) :
  svRatioStat Ka (x + h) - 2 * svRatioStat Ka x + svRatioStat Ka (x - h) = 0`;
  `curvature_witnesses_coexistence (hk0 : 0 < k0) (hkq : 0 < kq) (hKa : 0 < Ka) (hh : h ≠ 0) :
  0 < svRatioBoth k0 kq Ka (x + h) - 2 * svRatioBoth k0 kq Ka x + svRatioBoth k0 kq Ka (x - h)`.
* SV-C10 (**D1 verdict**) `d1_verdict (hk0 : 0 < k0) (hkq : 0 < kq) (hKa : 0 < Ka)` — one row
  with the three conjuncts: both plots linear (SV-C3/C4 at the parameters), the coincidence
  (SV-C7 at `Ka = KSV k0 kq` — instantiated by `refl`/the hypothesis chain), and the boundary
  (SV-C8). The persistence explanation is prose in RESULTS (Phase 3): routine practice measures
  intensity only; lifetime resolution is a separate experiment.

**SV-R (rational decision layer):**

* SV-R1 `Rat.svRatioDyn`, `Rat.svRatioStat`, `Rat.tauRatioDyn`, `Rat.tauRatioStat` over `ℚ` +
  cast-coherence rows (`(Rat.svRatioDyn a b q : ℝ) = svRatioDyn a b q` etc.).
* SV-R2 `inductive SVZone | dynLike | statLike | mixedLike | inconsistent` and
  `svZoneQ (slopeI slopeTau : ℚ) : SVZone` — classify a measured slope pair: equal positive
  slopes ↦ `dynLike`; zero lifetime slope with positive intensity slope ↦ `statLike`;
  `0 < slopeTau < slopeI` ↦ `mixedLike`; otherwise `inconsistent`.
* SV-R3 zone-correctness rows at rational witnesses (four `decide`/`rfl` verdicts).

**SV-I (named instances):**

* SV-I1 `oxygenDynamic : ℝ × ℝ := (2, 2)` (k0, kq; representative) — dynamic model, verdict:
  zone `dynLike` at the measured slopes.
* SV-I2 `complexStatic : ℝ := 1` (Ka; representative) — static model, verdict `statLike`.
* SV-I3 (**the D1 conflation witness pair**) `conflation_witness : ∀ q : ℝ,
  svRatioDyn 2 2 q = svRatioStat 1 q` — kernel-checked pointwise coincidence; the two named
  mechanisms are intensity-indistinguishable.
* SV-I4 `mixed_witness`: at `k0 = 2, kq = 1, Ka = 1`, `svZoneQ` on the exact slopes returns
  `mixedLike` and the second difference at `(0, 1)` is `1 > 0` (decide at ℚ).

## 5. Proof routes

Everything is field algebra + `ring`/`field_simp`/`norm_num`; monotonicity rows by
`add_lt_add_left`/`mul_lt_mul_of_pos_left`; SV-C8 by cases on `m` (`LifetimeTracks dyn` holds by
SV-C1; `¬ LifetimeTracks stat` instantiates at `q = 1`). No `Real.exp`, no `Finset` — the lightest
module of the batch; ideal Phase-2 warm-up.

## 6. Sprint order, ownership, dispatch

Sprint SV0 (Phase 1) → SV1 `Basic` → SV2 `Criterion` (D1 — the batch's other headline) →
SV3 `RatModel` → SV4 `Instances`. Owner: prover_c.

## 7. Acceptance criteria and gate commands

    proofs/scripts/lake build PhotoLean.SternVolmer.Basic   (etc. per module)
    proofs/scripts/check.sh --strict PhotoLean.SternVolmer.Criterion
    proofs/scripts/axioms.sh PhotoLean.SternVolmer.Criterion PhotoLean.SternVolmer.d1_verdict
    python3 theories/BEP/probes/bep-fidelity.py --theory SternVolmer

## 8. Risks and mitigations

* The `LifetimeTracks` universal is over all positive `q`: the static refutation instantiates at
  `q = 1` (or any `q > 0`) — no decidability issue arises since the existential side is explicit.
* `svZoneQ` must be total: the `inconsistent` branch absorbs the non-physical slope pairs —
  register that classification is a *data* classifier, not a mechanism theorem.

## 9. Honesty table

| # | Assumed (declared premise) | Proved (theorem) |
|---|---|---|
| 1 | Intensity ∝ fluorescence yield; lifetime = inverse total decay | SV-C1..C10 |
| 2 | Static model = linearized binding isotherm `1/(1+Ka·q)` | — |
| 3 | `kq`, `Ka` are free parameters (no diffusion/binding theory derived) | — |
| 4 | Named instances are representative rational models (LITERATURE) | their zone verdicts |

## 10. Edge candidates (toward the 7 delivered nodes + the 8 batch siblings)

* **QuantumYield — composition (machine target)**: dynamic quenching *is* the added parallel
  channel of `QuantumYield.yieldOf_cons_*`; the SV ratio equals the yield ratio.
* **Kasha — composition (machine target)**: dynamic quenching adds to `ic 0` (level-0 loss) of
  the ladder; `fluoYield 0` under quenching tracks the SV ratio.
* **FluorPhos — composition (machine target)**: quenching enters `s1Decay`; the φF/φP ratio is
  quencher-invariant (one row: the ratio law cancels `k0 + kq·q`).
* **Einstein — one-way via QuantumYield**: the intensity is `A·population`; registered through
  QY, no direct row.
* **Forster — look-alike (N-class candidate)**: FRET quenching shares the "added channel" shape
  but the control variable differs (`R⁶` vs `[Q]`); no theorem transfers — register the shape.
* **Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor / KashaVavilov (except the
  §-stretch row) / EnergyGapLaw / StokesShift / ICvsISC**: no edge (no energetic surface, no
  curvature, no cascade structure in the SV layer) — absence drafts registered.

## 11. Position in the repository

Second theory of the batch; self-contained (`Mathlib` only at the Basic layer); D1 is registered
into `PhotoLean/Relations.lean` in Phase 3 as the second adjudicated conflation (identifiability
flavor).
