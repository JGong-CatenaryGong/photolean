# theories/kasha/LITERATURE.md — literature record: Kasha's rule (opening stub)

> Owner: `literature_researcher`. Every entry must carry a checkable source, its conclusion, and a
> **formalizable implication** (which assumptions become explicit Lean premises, which are physical
> approximations that must be declared rather than proved, which cannot be expressed in the installed
> mathlib, and how the plan's statements are affected).
> Status: **stub** — round 1 in progress. This file is English; the only bilingual file of this
> theory is `theories/kasha/RESULTS.md`.

---

## §R0. Scope of the survey (why these questions)

The theory formalizes Kasha's rule (emission from the lowest excited state of a given multiplicity)
inside a finite excited-state cascade model. The literature round must settle:

1. **The canonical statement of Kasha's rule** (original source, exact wording, scope: which
   molecules/phases, the "of a given multiplicity" qualifier) — so the formal predicate is not a
   caricature.
2. **Vavilov's rule** and the Kasha–Vavilov relation (independence of the emission quantum yield
   from the excitation wavelength) — the second face of the same condition.
3. **Which rate inequalities the literature actually asserts** (internal conversion versus radiative
   rates; the "k_IC >> k_rad" form) and with what numbers — these become the tolerance threshold of
   the sharp criterion, with provenance.
4. **First-hand rate data for instances**: at least one conforming family (e.g. benzene, naphthalene,
   anthracene, pyrene) and at least one anti-Kasha family (e.g. azulene's S₂ emission, gas-phase
   isolated molecules showing resonance fluorescence, thioketones) with per-point data and page
   references, or an explicit `UNSUPPORTED` mark where the numbers are not first-hand.
5. **The energy-gap law / Marcus-type radiationless-transition form** for internal conversion — the
   input needed by the plan's Marcus bridge (K4b): is the quadratic driving-force form used in the
   literature for radiationless transitions, and under what stated limits?

## §R1. Round 1 — in progress

<!-- Findings land here, one `## §R1.<n>` block per round, each with source / conclusion /
     formalizable implication. Do not delete failed or negative findings: they are the asset. -->
