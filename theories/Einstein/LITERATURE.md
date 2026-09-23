# theories/Einstein/LITERATURE.md — literature record: the Einstein A/B coefficients, the oscillator-strength chain, and the Strickler–Berg relation

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / arXiv id /
> printed page) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as an explicit premise, a declared approximation,
> or a scope limit*. Statuses: `verified (first-hand read here)` /
> `verified (metadata+abstract, Crossref-deposited)` / `bibliographic-only`.
>
> Seed-verification duty from the lead: confirm the Einstein 1917 citation *and its English
> translation source*. Result: the citation is correct, with one nuance worth registering
> (E1/E2) — the paper was **first published in 1916** (Mitteilungen der Physikalischen
> Gesellschaft Zürich **18**, 47–62); the canonical citation is the 1917 *Physikalische
> Zeitschrift* printing. The standard English translation "On the Quantum Theory of Radiation"
> is CPAE Vol. 6, Doc. 38 (Princeton University Press), reprinted in ter Haar's *The Old
> Quantum Theory* (Pergamon, 1967).

**STATEMENT-IMPACT FLAGS (read first):** none — every statement in the frozen inventory
(`theories/Einstein/plan.md` §4) checked against the verified sources is consistent,
including the `8πhν³/c³` factor (frequency-based convention, E3 eq. 15), the degeneracy
relation `g₁B₁₂ = g₂B₂₁` (E2/E3 eq. 13), and the two collected-constant legs
(`Cf`, `Ci`) whose *per-transition, convention-dependent* anatomy is registered below as
honesty content, not as a statement defect.

## E1 — Einstein 1917 (the source of the A/B relations)

| field | content |
|---|---|
| source | A. Einstein, "Zur Quantentheorie der Strahlung", *Physikalische Zeitschrift* **18**, 121–128 (1917) — received 3 March 1917, published 15 March 1917. **Seed nuance (correction-grade)**: this is a reprinting; the paper first appeared as *Mitteilungen der Physikalischen Gesellschaft Zürich* **18**, 47–62 (1916). English translation: "On the Quantum Theory of Radiation", *The Collected Papers of Albert Einstein*, Vol. 6, Doc. 38 (Princeton University Press); also reprinted in D. ter Haar, *The Old Quantum Theory* (Pergamon, 1967), pp. 167–183. |
| verification | No DOI exists (pre-DOI journal). The venue/pages are corroborated by two independent deposited records read here: (i) Strickler & Berg 1962's Crossref-deposited reference list — "first-page 121, volume 18, year 1917, journal-title Physik. Z." (the first reference of E4); (ii) Straumann's article E2 (read first-hand), which states the full publication history quoted above and cites the translation locus "CPAE, Vol. 6, Doc. 38". The ter Haar locus is widely cataloged but was not opened here (`bibliographic-only`). |
| claim as used | The paper defines the three coefficients (spontaneous emission `A`, induced absorption/emission `B₁₂`, `B₂₁`) and derives the two relations between them — the content the plan formalizes as *conversion definitions* (EB-B1/EB-B2/EB-B3) plus invertibility theorems (EB-C). |
| **formalizable implication** | Einstein's *derivation* (statistical equilibrium with the Planck radiation density, via the Rayleigh–Jeans correspondence limit and Wien's displacement law — see E2) is **physics, not formalized**: the plan takes the relations as definitions of the conversions. What the literature forces into the statements: (i) the A↔B conversion factor is **positive** (`h, c, ν > 0` premises in EB-C1); (ii) the degeneracy relation needs **positive degeneracies** (`0 < g1`, `0 < g2` premises in EB-C3/EB-C4) so the swap `g₂/g₁` is invertible — the plan's `degeneracy_roundtrip` consumes exactly these. The blackbody-radiation content behind `8πhν³/c³` is a registered non-goal (plan §1.3). |
| status | `verified (bibliographic loci cross-checked)` — original German text not read here; content corroborated by E2/E3 |

## E2 — Straumann on the 1916/1917 paper (read first-hand)

| field | content |
|---|---|
| source | N. Straumann, "Einstein in 1916: 'On the Quantum Theory of Radiation'", **arXiv:1703.08176** (2017), read via the ar5iv full-text HTML |
| locus | §"Derivation of the Planck distribution" and the Brownian-motion section. Verbatim points read: Einstein "described the statistical laws for these processes by three coefficients (the famous A- and B-coefficients) and **established two relations between these coefficients** on the basis of his earlier correspondence argument in the classical Rayleigh–Jeans limit and Wien's displacement law"; and, used mid-derivation: "With Einstein's relation **g_m B^n_m = g_n B^m_n** from the first part of the paper…". Footnote 1 gives the publication history (1916 Mitteilungen first; Phys. Z. 18:121–128, received 3 March 1917). Reference [1] is the CPAE Vol. 6 Doc. 38 translation locus. |
| claim as used | Independent expert confirmation of the two relations' *content* and of their derivation's logical locus (statistical, not algebraic). |
| **formalizable implication** | Confirms that `g₁B₁₂ = g₂B₂₁` (EB-C3's `detailed_balance`) is the historically correct orientation of the degeneracy factor: the population weighting `g_n e^{-E_n/kT}` appears on the absorption side, forcing `g_m B^n_m = g_n B^m_n` in Straumann's index convention — equivalent to the plan's `b12OfB21 g1 g2 B21 = (g2/g1)·B21` with `1` lower, `2` upper. No statement change. The thermodynamic-equilibrium *premise* of Einstein's argument is a physical assumption of the model class; the Lean theory never quantifies over radiation fields. |
| status | `verified (first-hand read here)` — full text read |

## E3 — Hilborn's coefficient-relations review (the textbook chain; read first-hand)

| field | content |
|---|---|
| source | R. C. Hilborn, "Einstein coefficients, cross sections, f values, dipole moments, and all that", *Am. J. Phys.* **50**, 982–986 (1982); revised version **arXiv:physics/0202029** (2002), DOI `10.48550/arXiv.physics/0202029` |
| locus | arXiv abstract page read (confirms authorship, venue, revision note); the arXiv PDF was downloaded and the equations read in context. Verbatim equation record: eq. (9) `A21 = 1/t_spon` (A is the reciprocal of the spontaneous radiative lifetime when 2→1 is the only channel; general case `1/t_spon = Σᵢ A2ᵢ`); eq. (12) `B21 = (π²c³/ℏω³₂₁)A21` (per-angular-frequency convention); eq. (13) `B12 = (g2/g1)B21`; eq. (15) (Yariv form, per-frequency convention) `B21f = c³A21/(8πhf³)`, i.e. **`A21 = (8πhf³/c³)B21f`**; eq. (33) **`f12 = (g2/g1)·2πε₀mc³A21/(ω²₂₁e²)`**; §V defines `f` via the classical oscillator rate. Hilborn's standing warning (text between eqs. 12–16): different radiation-density conventions (per angular frequency / per frequency / per wavenumber) give *different* A–B prefactors — Herzberg, Yariv and Mihalas are quoted differing by factors of `c` and `2π`. |
| claim as used | The single checkable locus for the whole EB chain: `A = (8πhν³/c³)B` (frequency convention — the plan's `radFactor`), `g₁B₁₂ = g₂B₂₁`, `f ∝ (g₂/g₁)·A`, and `τ_rad = 1/A` (EB-B6/EB-C8's premise). |
| **formalizable implication** | (i) EB-B1's `radFactor h c ν := 8·π·h·ν³/c³` is confirmed as the **per-frequency** convention (Hilborn eq. 15); the theory thereby *chooses* a convention — the alternative prefactors (Herzberg/Mihalas) are registered here so that the collected `K` is never misread as convention-free. This is a **declared modelling choice**, not a premise Lean can discharge. (ii) EB-B4's `fOfA Cf g1 g2 A := Cf·(g2/g1)·A` matches eq. (33) with `Cf = 2πε₀mc³/(ω²₂₁e²) > 0` — **note for the honesty table**: `Cf` is *per-transition* (it carries `ω₂₁⁻²`), not a universal constant; the frozen statements only consume `Cf ≠ 0` / `0 < Cf`, so no statement change — but RESULTS should not call `Cf` universal. (iii) `0 < h`, `0 < c`, `0 < ν` (EB-C1) are exactly the positivity premises the physical factor requires; `Real.pi_pos` covers `π`. (iv) Nothing in this source needs measure theory or spectroscopy infrastructure — all legs are field algebra over `ℝ`, matching the plan's proof routes (§5). |
| status | `verified (first-hand read here)` — equations read from the arXiv PDF |

## E4 — Strickler & Berg 1962 (the radiative-rate/integrated-absorption leg)

| field | content |
|---|---|
| source | S. J. Strickler & R. A. Berg, "Relationship between Absorption Intensity and Fluorescence Lifetime of Molecules", *J. Chem. Phys.* **37**(4), 814–822 (1962); DOI `10.1063/1.1733166` |
| verification | Crossref record read in full, **including the deposited abstract**: the paper derives the modified formula `1/τ₀ = 2.880×10⁻⁹ · n² · ⟨ν̃_f⁻³⟩_Av⁻¹ · (g_l/g_u) · ∫ε d(ln ν̃)`, "valid for broad molecular bands when the transition is strongly allowed"; calculated vs. measured lifetimes agree within experimental error for a number of organic molecules; "limitations ... for weak or forbidden transitions" are discussed by the authors. Its reference [1] is the Einstein 1917 Phys. Z. citation (used in E1). |
| claim as used | The radiative rate is proportional to the integrated absorption with a collected positive constant — the plan's EB-B5 `aOfInt Ci I := Ci·I` — with the degeneracy ratio `g_l/g_u` and the refractive index `n²` folded into `Ci`. |
| **formalizable implication** | (i) The shape `rate = Ci·(integrated absorption)` with `0 < Ci` is confirmed; EB-C5's round trip consumes only `Ci ≠ 0`. (ii) **Declared, never proved**: the "strongly allowed transition" restriction and the frequency-moment correction `⟨ν̃_f⁻³⟩` are physical approximations *inside* `Ci`; the theory's registered non-goal "the constants' internal structure is not unfolded" (plan §1.3/§9) is exactly the right formalization posture — the literature itself presents the prefactor as semi-empirical (the `2.880×10⁻⁹` figure is unit-convention-laden). (iii) Same per-transition caveat as E3: `Ci` hides `n²`, the degeneracy ratio, and band-moment factors — positive per transition, not universal. |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text not read here |

## E5 — not first-hand this round (registered, not hidden)

| source | status | note |
|---|---|---|
| D. ter Haar, *The Old Quantum Theory* (Pergamon, 1967), pp. 167–183 | `bibliographic-only` | The reprinted English translation of E1; widely cataloged, not opened here. The CPAE Vol. 6 Doc. 38 translation locus is independently attested by E2's reference list. |
| Einstein 1916, "Strahlungs-Emission und -Absorption nach der Quantentheorie", *Verh. Dtsch. Phys. Ges.* **18**, 318–323 (CPAE Vol. 6, Doc. 34) | `bibliographic-only` | The predecessor note with the first A/B derivation; not needed for the statement layer, registered for completeness. |

## Statement-impact summary

**No statement in the frozen inventory (`plan.md` §4) contradicts any verified source.** Row by row:

* EB-B1 (`radFactor = 8πhν³/c³`): confirmed, per-frequency convention (E3 eq. 15; convention-dependence of the prefactor registered as a declared modelling choice). No change.
* EB-B2/EB-C2 (A↔B invertibility with `K ≠ 0`): content licensed by E1/E3; the only premise needed is nonzeroness/positivity, present. No change.
* EB-B3/EB-C3 (`B₁₂ = (g₂/g₁)B₂₁`, `detailed_balance`): confirmed orientation of the degeneracy factor (E2's `g_m B^n_m = g_n B^m_n`, E3 eq. 13). No change.
* EB-B4/EB-C4 (`fOfA` with collected `Cf`): confirmed by E3 eq. (33); honesty note — `Cf` is per-transition (∝ `ω⁻²`), not universal; statements consume only `Cf ≠ 0` / `0 < Cf`. No change.
* EB-B5/EB-C5 (Strickler–Berg leg with collected `Ci`): confirmed shape by E4's deposited abstract; the "strongly allowed" restriction stays a declared approximation. No change.
* EB-B6/EB-C8 (`tauR = 1/A`, `yield_radiative`): `A = 1/τ_spon` confirmed (E3 eq. 9, single-channel case — matching the plan's two-channel yield row, whose nonradiative channel is added explicitly). No change.
* EB-R2 (rational surrogates): the plan's own registration that the physical `radFactor` contains `π` (hence the ℚ layer tests algebra at surrogates) is consistent with E3's prefactor anatomy. No change.

Seed corrections registered (neither affects any statement): (i) the 1917 Phys. Z. paper is a reprinting of a 1916 Mitteilungen (PGZ) publication (E1/E2); (ii) the translation locus is CPAE Vol. 6 Doc. 38 (attested), with ter Haar 1967 as the widely-cited reprint (`bibliographic-only`).
