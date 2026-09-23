# theories/EnergyGapLaw/LITERATURE.md — literature record: the Englman–Jortner gap law, the classical Marcus rate, and the experimental gap-law series

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page)
> and a **reading status**; every entry carries the only column that matters for formalization —
> *what the source licenses as an explicit Lean premise, a declared physical approximation, a
> scope limit, or a statement change to `theories/EnergyGapLaw/plan.md`*. Statuses:
> `verified (first-hand abstract/full text read here)` / `verified (Crossref bibliographic)` /
> `verified (reused first-hand record of Marcus)` / `bibliographic-only`.
>
> **Seed correction (loud):** the seed's venue guess "J. Mol. Struct. 1970?" for Englman–Jortner
> **fails verification**. The checkable locus is *Molecular Physics* **18**(2), 145–164 (1970),
> DOI `10.1080/00268977000100171` (S1). No J. Mol. Struct. publication of this title exists in
> Crossref.

## S1 — Englman & Jortner 1970, the energy-gap law itself (with a companion account)

| field | content |
|---|---|
| source | R. Englman & J. Jortner, "The energy gap law for radiationless transitions in large molecules", *Molecular Physics* **18**(2), 145–164 (1970), DOI `10.1080/00268977000100171` [verified: Crossref record read 2026-09-23 — authors, venue, volume/issue, pages, year all match]. Companion short account: R. Englman & J. Jortner, "The energy gap law for non-radiative decay in large molecules", *J. Luminescence* **1–2**, 134–142 (1970), DOI `10.1016/0022-2313(70)90029-3` [verified: Crossref]. |
| claim (as used) | The nonradiative rate of an electronic relaxation in a large molecule falls off approximately exponentially with the electronic energy gap: `log k_nr ≈ const − γ·ΔE`, with a slope `γ` that depends only weakly (logarithmically) on the gap, in the weak-coupling regime with one dominant accepting vibration. The quantum prefactor (commonly quoted as `C²√(2π)/(ℏ√(2λℏω))`) is gap-independent up to slow factors. **Content-level grading:** the affine form and the weak slope-dependence are the standard, consistently cited content of the paper; the exact equation numbers and the printed prefactor form were **not** read first-hand (Taylor & Francis full text paywalled) — graded `bibliographic-only` at formula level. |
| **formalizable implication** | *Explicit Lean premises:* none beyond the model's own — `0 < A` (prefactor), `0 < lam`, `0 < kB * T` — exactly as carried on the EG-C/EG-S rows; EG-C1's weakest premise `lam ≠ 0` is licensed because the exact log law is pure algebra. *Declared approximations (never proved):* the classical (high-temperature) limit of the accepting mode — under it the exact log-rate is the **quadratic** `log A − (λ−x)²/(4λk_BT)` (EG-C1), so the affine Englman–Jortner "law" is formalized as the **tangent** `eglTangent` with the exact quadratic defect `−(x−x*)²/(4λk_BT)` (EG-S1/S2/S2a), and `not_affine_on_window` (EG-S3) is the sharp statement that no affine law is exact on any interval; the gap-independent prefactor folded into `A` (plan §1.3) matches the source's gap-independence claim. *Not expressible over installed mathlib:* the quantum vibronic progression (Poisson-weighted displaced-oscillator FC factors, the `ℏω` quantum) and hence the original `γ(ΔE)` formula — mathlib has no harmonic-oscillator eigenbasis/overlap-integral layer (same blocker as Marcus record, unexpressible-item #1); registered as plan §1.3 non-goal. |
| impact on plan statements | **None** — plan §1.1 already frames the exact law as quadratic, the affine law as its tangent with exact defect, and the decrease direction as an inverted-regime statement. One **confirmation** worth recording: the quantum Englman–Jortner law decreases monotonically for *all* gaps (no normal-region reversal — vibronic channels remove the turnover), so the classical model's EG-C3 reversal is a *model* phenomenon; plan §1.1 already says exactly this ("the gap law is an inverted-regime law"), no edit needed. |
| status | `verified (Crossref bibliographic)` for the locus; `bibliographic-only` for the formula-level content |

## S2 — the classical rate the law is read on: Marcus 1956/1960/1964 (reused first-hand records)

| field | content |
|---|---|
| source | Marcus, *J. Chem. Phys.* **24**(5), 966–978 (1956), DOI `10.1063/1.1742723`; Marcus, *Discuss. Faraday Soc.* **29**, 21–31 (1960), DOI `10.1039/df9602900021` (first statement of the inverted region, p. 28 §(v)); Marcus, *Annu. Rev. Phys. Chem.* **15**, 155–196 (1964), DOI `10.1146/annurev.pc.15.100164.001103`; Marcus Nobel Lecture 1992, pp. 78/82/84. Record: `theories/Marcus/LITERATURE.md`, entries of 2026-09-20 (local PDFs and rendered figure pages under `theories/Marcus/literature/`). |
| claim (as used) | The classical two-parabola rate is `k = A·exp(−ΔG*/k_BT)` with `ΔG* = (λ−x)²/(4λ)`, `x = −ΔG°`; the rate increases with the gap in the normal region (`x < λ`), is barrierless at `x = λ`, and decreases strictly in the inverted region (`λ < x`). The Marcus round also verified the **sharpness analysis** (record "附"): strict decrease on the inverted region holds iff `0 < A·λ/τ` — the positivity premises are load-bearing (counterexample `λ=−1, τ=1, A=−1` gives strict decrease with `A < 0`). |
| **formalizable implication** | *Explicit Lean premises:* `0 < A`, `0 < lam`, `0 < kB * T` on every order-sensitive row (EG-C2/C3, EG-S2..S4); `lam ≠ 0` suffices for the pure-algebra rows (EG-C1, EG-C4) — the weakest-premise standard of the batch. *Declared approximations:* classical nuclear motion; single scalar driving force with work terms `w_r = w_p = 0`; prefactor `A` positive and gap-independent (Marcus record §7: any TST prefactor enters as a positive x-independent factor, so no monotonicity content is lost — this is the license for folding the Englman–Jortner prefactor into `A`). *Not expressible:* the electrostatic derivation of `λ` (Pekar factor) — stays a definition, as in Marcus. |
| impact on plan statements | **None.** The plan's conventions (`x = −ΔG°`, inverted region `λ < x`) match the original sources exactly (Marcus record correction #4: never write `ΔG° > λ`). The load-bearing-positivity finding is already embodied in the EG rows' premise lists. |
| status | `verified (reused first-hand record of Marcus)` |

## S3 — the experimental gap-law series: aromatic-hydrocarbon triplet decay (Siebrand II)

| field | content |
|---|---|
| source | W. Siebrand, "Radiationless Transitions in Polyatomic Molecules. II. Triplet-Ground-State Transitions in Aromatic Hydrocarbons", *J. Chem. Phys.* **47**(7), 2411–2422 (1967), DOI `10.1063/1.1703324` [abstract read first-hand via Crossref, 2026-09-23]. (This is the "Siebrand recurrences" series the seed pointed at; Part I is Siebrand, *J. Chem. Phys.* **46**, 440–447 (1967), DOI `10.1063/1.1840685` [Crossref citation metadata: volume 46, first page 440, year 1967 verified; issue number and end page not independently verified].) |
| claim (as used) | From the abstract (first-hand): across aromatic hydrocarbons the triplet-state nonradiative decay obeys an empirical relation between triplet energy and triplet lifetime — an experimental gap-law series; the purely radiative triplet lifetime is ≈ 30 s for most of the series, and **the Franck–Condon factor is the only parameter in the nonradiative rate that varies considerably** across the series. Crucially: "No satisfactory theoretical representation of the empirical formula could be obtained on the basis of a **harmonic-oscillator** description … introduction of **anharmonicity** leads to excellent agreement." |
| **formalizable implication** | *Explicit Lean premises:* the per-series data licenses the instance design `aromaticSeries` (EG-I1) — one `(lam, A, kB·T)` per series, gaps varying — as a **representative rational model**, never as fitted data. *Declared approximations:* the classical two-parabola (harmonic!) law is a model of the gap dependence; Siebrand's own abstract records that harmonic models fail the series quantitatively — so no instance row may claim agreement with measured lifetimes, and the plan's honesty-table row 1/4 wording is exactly the required discipline. *Not expressible:* anharmonic accepting modes (CH/CD stretches), the isotope rule — no vibronic layer in mathlib (as S1). |
| impact on plan statements | **None** — plan §9 row 4 already labels the named instances "representative rational models". This source supplies the *reason* that label is mandatory: the harmonic model is documented to fail the real series quantitatively (direction survives; magnitudes do not). |
| status | `verified (first-hand abstract read here)` for the abstract content; full text not fetched (AIP paywall) |

## S4 — why the classical quadratic falls too fast: quantum flattening of the gap law

| field | content |
|---|---|
| source | M. Bixon & J. Jortner, "Intramolecular Radiationless Transitions", *J. Chem. Phys.* **48**(2), 715–726 (1968), DOI `10.1063/1.1668703` [Crossref-verified; content not read]; Marcus Nobel Lecture 1992, p. 84 Fig. 8 (smooth curve with `ω = 1500 cm⁻¹` quantum correction) [verified by image reading in the Marcus round]; the classical-vs-measured comparison arithmetic on the Miller–Calcaterra–Closs series (classical inverted-branch drop ~5.1 orders vs measured ~1.46 orders) [repo's own arithmetic, `theories/Marcus/LITERATURE.md` 2026-09-20, labeled as such]. |
| claim (as used) | Quantum vibrational channels (high-frequency accepting modes) flatten the gap-law falloff: the classical quadratic model decreases **too steeply** in the inverted region, by orders of magnitude against experiment. |
| **formalizable implication** | *Explicit Lean premises:* none. *Declared approximations:* EG-S4 (`eglTangent_slope_strictAnti` — the classical tangent slope steepens **linearly** with the reference gap) is a classical-model artifact; the quantum Englman–Jortner slope grows only weakly (logarithmically, S1). The theory's theorems are statements **about the model**, never about measured rates — this is the wording discipline every EG row's docstring must keep. *Not expressible:* the Poisson-weighted vibronic sum (as S1). |
| impact on plan statements | **None.** Reinforces plan §9 row 1 ("Classical two-parabola Marcus rate for the nonradiative channel (no quantum FC factor)"). |
| status | `verified (reused first-hand record of Marcus)` for the figure and the arithmetic; `bibliographic-only` for Bixon–Jortner content |

## S5 — registered, not first-hand this round

| source | status | note |
|---|---|---|
| Englman–Jortner 1970 full text (T&F) | `bibliographic-only` | paywalled; the prefactor form quoted in plan §1.3 (`C²√(2π)/(ℏ√(2λℏω))`) is the standard quoted form but its equation locus in the paper is **unverified** — the plan only folds it into `A`, so nothing load-bearing depends on it. |
| Henry & Kasha, *Annu. Rev. Phys. Chem.* **19**, 161–192 (1968), DOI `10.1146/annurev.pc.19.100168.001113` | `bibliographic-only` | the canonical review of radiationless transitions (surfaced as a Crossref reference of S1); a candidate upgrade for the review-of-series slot — not read. |
| Englman–Jortner, *J. Luminescence* **1–2**, 134–142 (1970) | `verified (Crossref bibliographic)` | companion account; registered for completeness, content not read. |

## Statement-impact summary

**None** — no statement in `theories/EnergyGapLaw/plan.md` §4 contradicts any verified source; the plan's
"exact quadratic + tangent with defect + inverted-regime direction" framing is precisely what the
literature supports for the classical model.

Two advisory notes (neither is a literature contradiction):

1. **EG-I3 draft arithmetic**: at `lam = 1/2`, `kB·T = 1/40`, `x* = 3/2`, `x = 2` the defect is
   `−(1/2)²/(4·(1/2)·(1/40)) = −(1/4)/(1/20) = −5`, not `−20` as the plan's parenthetical draft
   computes. The plan already mandates probe recomputation before freezing; the frozen row should
   state `lnRate 2 = eglTangent 2 − 5`. (Arithmetic check only — not a literature item.)
2. **Seed correction**: Englman–Jortner 1970 is *Molecular Physics* **18**(2), 145–164 — any
   citation of "J. Mol. Struct." would be wrong; no plan file contains that string, so no edit is
   required anywhere.
