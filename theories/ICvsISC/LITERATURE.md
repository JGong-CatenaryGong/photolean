# theories/ICvsISC/LITERATURE.md — literature record: El-Sayed's rule, the spin-orbit prefactor, and the first-hand rate scale

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / printed page)
> and a **reading status**; every entry carries the only column that matters for formalization —
> *what the source licenses as an explicit Lean premise, a declared physical approximation, a
> scope limit, or a statement change to `theories/ICvsISC/plan.md`*. Statuses:
> `verified (first-hand abstract/full text read here)` / `verified (Crossref bibliographic)` /
> `verified (reused first-hand record of Marcus)` / `bibliographic-only`.

## S1 — El-Sayed 1963: the orbital dependence of the spin-orbit coupling (the rule's origin)

| field | content |
|---|---|
| source | M. A. El-Sayed, "Spin–Orbit Coupling and the Radiationless Processes in Nitrogen Heterocyclics", *J. Chem. Phys.* **38**(12), 2834–2838 (1963), DOI `10.1063/1.1733610` [abstract read first-hand via Crossref, 2026-09-23 — authors, venue, volume/issue, pages, year all match]. |
| claim (as used) | From the abstract (first-hand): to first order there is **no spin-orbit coupling between singlet and triplet states of the same configuration** for (n,π*) states of nitrogen heterocyclics; the squared ratio of the spin-orbit matrix elements `|⟨S(n,π*)\|H_SO\|T(n,π*)⟩ / ⟨S(π,π*)\|H_SO\|T(π,π*)⟩|²` has an **upper value of 10⁻³**; the enhanced intersystem crossing in molecules with lowest (n,π*) singlets is attributed to an `S(n,π*) → T(π,π*)` process rather than same-configuration ISC. This is the origin of what is now called **El-Sayed's rule**: ISC is fast between states of different orbital type, slow between states of the same type. |
| **formalizable implication** | *Explicit Lean premises:* the abstract licenses the *shape* of the ISC rate — a **squared** coupling `HSO ^ 2` multiplying an otherwise Marcus-like rate (FC-B3) — and the design decision that `FCData` carries **no sign premise on `HSO`** (the amplitude enters squared; FC-B4). The instance scale is licensed too: a squared-coupling discount of 10⁻³ corresponds to `HSO` of order 1/30, so FC-I1's representative `HSO = 1/10` sits at the mild-discount (El-Sayed-favored) end — representative, never fitted. *Declared approximations (never proved):* the golden-rule rate form `rate ∝ \|coupling\|² × FC factor` for both channels; **El-Sayed's rule itself is a valuation of the parameter `HSO` per molecule — a parameter premise, never derived** (plan §1.2 and §9 row 2 — exactly the required honesty). *Not expressible over installed mathlib:* first-order perturbation theory of the spin-orbit operator, orbital classifications (n,π*) vs (π,π*) — no quantum-mechanical operator layer exists in mathlib; the rule can never become a theorem here. |
| impact on plan statements | **None.** The source confirms the plan's central design choice (parameter `HSO`, squared, no derivation) is the faithful formalization of the literature. |
| status | `verified (first-hand abstract read here)` |

## S2 — El-Sayed 1968: the review that canonized the rule

| field | content |
|---|---|
| source | M. A. El-Sayed, "Triplet state. Its radiative and nonradiative properties", *Acc. Chem. Res.* **1**(1), 8–16 (1968), DOI `10.1021/ar50001a002` [verified: Crossref record read 2026-09-23 — author, venue, volume/issue, pages, year all match; full text not read]. |
| claim (as used) | The standard review statement of the orbital-type dependence of ISC rates (El-Sayed's rule as community practice): intersystem crossing between states of different orbital character outpaces ISC between states of the same character, controlling phosphorescence vs fluorescence competition in aromatics and carbonyls. |
| **formalizable implication** | *Explicit Lean premises:* none new. *Declared approximations:* reinforces that the rule enters the theory **only** as the parameter `HSO` — a review-level empirical regularity is exactly the kind of claim that must be declared, never proved (the kernel has nothing to prove it with). *Not expressible:* as S1. |
| impact on plan statements | **None.** |
| status | `verified (Crossref bibliographic)`; content `bibliographic-only` |

## S3 — the competition picture: the triplet-state review (Lower & El-Sayed 1966)

| field | content |
|---|---|
| source | S. K. Lower & M. A. El-Sayed, "The Triplet State and Molecular Electronic Processes in Organic Molecules", *Chem. Rev.* **66**(2), 199–241 (1966), DOI `10.1021/cr60240a004` [verified: Crossref record read 2026-09-23 — authors, venue, volume/issue, pages, year all match; full text not read]. |
| claim (as used) | The standard review of triplet-state photophysics: radiative and nonradiative channels (fluorescence, phosphorescence, IC, ISC) compete as parallel first-order rates, and the fate of the excited state is read off their relative magnitudes — the competition framing this theory formalizes as `iscRate / icRate` (FC-C1..C3). |
| **formalizable implication** | *Explicit Lean premises:* the `FCData` positivity bundle (`0 < AI`, `0 < AS`, `0 < lamI`, `0 < lamS`, `0 < kB * T`) — positivity is what makes the ratio and its log well-defined (FC-C1/C2) and the crossover an exact iff (FC-C3); `0 < HSO` on the log/crossover rows, `HSO < 1` on the spin-discount row (FC-C4). *Declared approximations:* both channels are classical two-parabola Marcus rates over their own `(lam, x)` — the FC-factor reading licensed by the Marcus record (S6); no hot ISC, no reverse channels (plan §1.3). *Not expressible:* the review's tabulated per-molecule rates enter only as instance motivation — representative rational models, never data rows (plan §9 row 4). |
| impact on plan statements | **None.** |
| status | `verified (Crossref bibliographic)`; content `bibliographic-only` |

## S4 — the first-hand number set I: the spin-prohibition factor in aromatics (Siebrand–Williams III)

| field | content |
|---|---|
| source | W. Siebrand & D. F. Williams, "Radiationless Transitions in Polyatomic Molecules. III. Anharmonicity, Isotope Effects, and Singlet-to-Ground-State Transitions in Aromatic Hydrocarbons", *J. Chem. Phys.* **49**(4), 1860–1871 (1968), DOI `10.1063/1.1670318` [abstract read first-hand via Crossref, 2026-09-23]. |
| claim (as used) | From the abstract (first-hand): internal-conversion rate constants between closely spaced same-multiplicity levels are **10¹³–10¹⁴ s⁻¹**; comparison with triplet–ground-state transition rates "indicates a **spin-prohibition factor of 10⁸**" for the aromatic hydrocarbons studied. This is the first-hand anchor for the prefactor hierarchy the theory encodes: same-spin FC-limited rates vs spin-forbidden rates differ by orders of magnitude in the prefactor alone. |
| **formalizable implication** | *Explicit Lean premises:* none — the 10⁸ factor itself is **not** a premise and must never become one; it motivates only the *scale separation* that makes the spin-discount theorem (FC-C4: with `AI = AS` and `0 < HSO < 1`, an ISC win forces a strictly lower ISC barrier) the physically interesting row. *Declared approximations:* `HSO` collects the entire spin prohibition into one dimensionless amplitude; for pure aromatics the first-hand scale is `HSO² ~ 10⁻⁸` (HSO ~ 10⁻⁴), far below FC-I1's `1/10` — the instance is registered as the El-Sayed-favored class, not the aromatic-hydrocarbon class. *Not expressible:* the anharmonic accepting-mode analysis behind the numbers (no vibronic layer, as in EnergyGapLaw S1). |
| impact on plan statements | **None.** The instance docstrings should name their class (FC-I1 = El-Sayed-favored mild discount; a pure-aromatic instance would need `HSO ~ 10⁻⁴`), but no statement changes. |
| status | `verified (first-hand abstract read here)` |

## S5 — the first-hand number set II: El-Sayed-favored ISC in aromatic carbonyls (Dym–Hochstrasser 1969)

| field | content |
|---|---|
| source | S. Dym & R. M. Hochstrasser, "Spin–Orbit Coupling and Radiationless Transitions in Aromatic Ketones", *J. Chem. Phys.* **51**(6), 2458–2468 (1969), DOI `10.1063/1.1672367` [abstract read first-hand via Crossref, 2026-09-23]. |
| claim (as used) | From the abstract (first-hand): for benzophenone the intersystem-mixing rate is calculated at about **10¹¹ s⁻¹** (from uncertainty broadening of the triplet origin), and the ISC mechanism in aromatic ketones involves direct coupling of (n,π*) singlet and triplet states of mixed character — the El-Sayed-favored situation, with ISC fast enough to outcompete fluorescence entirely. This is the carbonyl-side number set the seed asked to verify. |
| **formalizable implication** | *Explicit Lean premises:* none. *Declared approximations:* confirms the instance reading that El-Sayed-favored channels carry a mild spin discount (HSO of order 10⁻¹ as a representative value) and that whether ISC then wins is decided by the **barrier comparison** — exactly FC-C7 (unit coupling, equal prefactors: the race is the barrier ordering). *Not expressible:* the Zeeman/polarization spectroscopy behind the mechanism assignment. |
| impact on plan statements | **None.** |
| status | `verified (first-hand abstract read here)` |

## S6 — the classical FC factor both channels share (reused first-hand records)

| field | content |
|---|---|
| source | Marcus, *J. Chem. Phys.* **24**(5), 966–978 (1956), DOI `10.1063/1.1742723`; Marcus, *Annu. Rev. Phys. Chem.* **15**, 155–196 (1964), DOI `10.1146/annurev.pc.15.100164.001103`; Marcus Nobel Lecture 1992 pp. 78/82 [record: `theories/Marcus/LITERATURE.md`, 2026-09-20, first-hand]. |
| claim (as used) | The classical Franck–Condon factor of a nonradiative transition between equal-curvature parabolas is the Arrhenius factor over the crossing barrier `(λ−x)²/(4λ)` — the form `fcBarrier` (FC-B1) copies and `cert_fcBarrier`/`cert_icRate` pin to the kernel and to `PhotoLean.Marcus.rate`. |
| **formalizable implication** | *Explicit Lean premises:* `0 < lamI`, `0 < lamS`, `0 < kB * T` (in the `FCData` bundle) — load-bearing per the Marcus sharpness analysis (strict order statements fail without positivity); `lamI ≠ 0`, `lamS ≠ 0` suffice for the pure-algebra row FC-C6 (weakest-premise standard). *Declared approximations:* classical nuclear motion, gap-independent prefactors, work terms ignored — inherited from the Marcus record unchanged. *Not expressible:* quantum FC factors for either channel (as EnergyGapLaw S1). |
| impact on plan statements | **None.** |
| status | `verified (reused first-hand record of Marcus)` |

## S7 — registered, not first-hand this round

| source | status | note |
|---|---|---|
| El-Sayed 1968 and Lower–El-Sayed 1966 full texts | `bibliographic-only` | ACS paywall; bibliographic records Crossref-verified (S2/S3). No plan row depends on their page-level content. |
| El-Sayed, *Acc. Chem. Res.* **4**(1), 23–31 (1971), DOI `10.1021/ar50037a004` | `verified (Crossref bibliographic)` | follow-up review (phosphorescence microwave double resonance); surfaced during verification, registered for completeness, not read. |
| Lim & Yu, *J. Chem. Phys.* **45**(12), 4742–4743 (1966), DOI `10.1063/1.1727567` | `verified (Crossref bibliographic)` | vibronic mixing between (n,π*) and (π,π*) states — the refinement of the first-order rule; registered as the standard caveat, not read. |

## Statement-impact summary

**None** — no statement in `theories/ICvsISC/plan.md` §4 contradicts any verified source. The two
first-hand number sets (spin-prohibition factor 10⁸ in aromatics, S4; ISC ≈ 10¹¹ s⁻¹ in aromatic
ketones, S5) bracket the instance design exactly as the plan draws it: `HSO` is a per-class
parameter (never derived), and the competition theorems are about barrier orderings against a spin
discount.

One advisory note (not a literature contradiction): **FC-I2 draft arithmetic** — at
`lamI = 1, xI = 3/2` the IC barrier is `(1−3/2)²/4 = 1/16`; at `lamS = 2, xS = 3/2` the ISC barrier
is `(2−3/2)²/(4·2) = 1/32`, **not** `1/16` as the plan's parenthetical draft wonders — so the pure
FC race is `1/32 < 1/16` and ISC wins under FC-C7. The plan already mandates probe recomputation
before the row is frozen; the frozen row should state `1/32 < 1/16`.
