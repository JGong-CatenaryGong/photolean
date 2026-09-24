# theories/RACI/LITERATURE.md — literature record: Restricted Access to a Conical Intersection (RACI) ⇒ aggregation-induced emission (AIE)

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / Crossref record /
> ADS bibcode / printed page) and a **reading status**; every entry carries the only column that
> matters for formalization — *what the source licenses as an explicit premise, a declared
> approximation, or a scope limit*. Statuses: `verified (first-hand read here)` /
> `verified (metadata+abstract, Crossref-deposited)` / `bibliographic-only`.
>
> Statement inventory audited against: the delivered modules `PhotoLean/RACI/*.lean`
> (TwoState, Branching, Seam, Accessibility, Torsion, Barrier, LandauZener, Jablonski,
> JablonskiRatios, GeometricPhase, Main), milestones M1–M4 + M1* + M6 + the M4+ ratio
> generalizations.

**STATEMENT-IMPACT FLAGS (read first): none.** No delivered statement contradicts any verified
source. Two **seed bibliographic corrections** (do not propagate the seed's errors into the plan):

1. The seed conflated two different papers. The 2001 AIE *discovery* paper in Chem. Commun. is
   **Luo et al., "Aggregation-induced emission of 1-methyl-1,2,3,4,5-pentaphenylsilole",
   Chem. Commun. 2001, (18), 1740–1741, DOI `10.1039/B105159H`** — first author Luo, not Tang;
   the seed's author list matches neither this paper nor any other. The title the seed gave
   ("Aggregation-induced emission: the whole is more brilliant than the parts") belongs to the
   **2014 *Advanced Materials* review** by Mei, Hong, Lam, Qin, Tang, Tang
   (DOI `10.1002/adma.201401356`). Both are recorded (R1a, R1b).
2. The phrase "restricted access to a conical intersection" is **not** the coinage of the
   Angew. 2020 paper in the repository (Guan et al. — its abstract speaks of a conical
   intersection reached by ultrafast cyclization, blocked in the solid, but never uses the
   phrase). The terminology appears as the title of **Peng, Ruiz-Barragan, Li, Li & Blancafort,
   J. Mater. Chem. C 4, 2802–2810 (2016), DOI `10.1039/C5TC03322E`**, built on the precursor
   CI model of **Li & Blancafort, Chem. Commun. 49, 5966–5968 (2013), DOI `10.1039/C3CC41730A`**
   (R2b). The ChemLean source repository's own plan cites exactly these two.

## R1a — the AIE discovery paper (2001) — *seed-corrected*

| field | content |
|---|---|
| source | J. Luo, Z. Xie, J. W. Y. Lam, L. Cheng, H. Chen, C. Qiu, H. S. Kwok, X. Zhan, Y. Liu, D. Zhu, B. Z. Tang, "Aggregation-induced emission of 1-methyl-1,2,3,4,5-pentaphenylsilole", *Chem. Commun.* **2001**(18), 1740–1741; DOI `10.1039/B105159H` |
| verification | Crossref record read at `api.crossref.org/works/10.1039/b105159h`: title, venue (Chemical Communications, RSC), issue 18, pages 1740–1741, year 2001, full author list — all match this row (8104 citations recorded). **Seed correction**: the discovery paper's first author is Luo and its title is the silole one; the seed's author list and title do not match any single paper (see R1b). Independently corroborated by the deposited reference lists of Li & Blancafort 2013 (R2b, ref cit17: "Luo 2001, page 1740, Chem. Commun.") and Guan et al. 2020 (R2, ref e_1_2_6_11_2). |
| claim as used | Some non-emissive solutions (silole derivatives) become strongly emissive as aggregates — the experimental phenomenon AIE that the RACI theory explains: aggregation turns on fluorescence. |
| **formalizable implication** | This paper fixes the *target predicate* only: there exist phases `sol`/`agg` with `Φ_agg > Φ_sol`. It licenses no Lean premise beyond the reading of `Φ` as a fluorescence quantum yield (a declared two-channel Jablonski reading, R7/R8 of the rate algebra below). Nothing about mechanism is taken from it; the mechanistic content is R2/R2b. |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text not read here |

## R1b — the review bearing the seed's title; the RIM unification (2014) — *seed-corrected*

| field | content |
|---|---|
| source | J. Mei, Y. Hong, J. W. Y. Lam, A. Qin, Y. Tang, B. Z. Tang, "Aggregation-Induced Emission: The Whole Is More Brilliant than the Parts", *Adv. Mater.* **26**(31), 5429–5479 (2014); DOI `10.1002/adma.201401356` |
| verification | Crossref record read (title, authors, volume 26, issue 31, pages 5429–5479, August 2014). Deposited abstract read: AIE = luminogens non-emissive in good solvents but luminescent when clustered; "we … unify the restriction of intramolecular motions (RIM) as the main cause for the AIE effects". Cited as ref cit3 in Peng et al. 2016 (R2b's deposited reference list) — independent corroboration. |
| claim as used | The community's umbrella mechanism is RIM (restriction of intramolecular motion). RACI is the *geometrically specific* sharpening of RIM: not motion in general but access to the conical intersection is what must be restricted. The formalization is on the RACI side: it formalizes the gap-raising mechanism (M2: constraint raises the minimal accessible gap from 0 to 2δ), not generic RIM. |
| **formalizable implication** | Explains the modelling posture: the theory does **not** formalize "motion" (no vibrational modes, no friction, no diffusion — none expressible or needed here); it formalizes one scalar surrogate, the torsion coordinate θ with an excluded window `|θ| < δ`. The identification "aggregate phase = `|θ| ≥ δ` window" (`Allowed δ` in `Torsion.lean`) is thereby a **declared modelling approximation**, never a theorem — the literature (RIM as an umbrella, RACI as its CI sharpening) is exactly what justifies declaring rather than proving it. |
| status | `verified (metadata+abstract, Crossref-deposited)` |

## R2 — the RACI mechanism paper in the repository (2020)

| field | content |
|---|---|
| source | J. Guan, R. Wei, A. Prlj, J. Peng, K.-H. Lin, J. Liu, H. Han, C. Corminboeuf, D. Zhao, Z. Yu, J. Zheng, "Direct Observation of Aggregation-Induced Emission Mechanism", *Angew. Chem. Int. Ed.* **59**(35), 14903–14909 (2020); DOI `10.1002/anie.202004318` (received 2020-03-24; PDF and SI present in the source repository `[local path removed]`) |
| verification | Crossref record read: title, all eleven authors, volume 59, issue 35, pages 14903–14909, published 2020 — all match. Deposited abstract read: frequency/polarization-resolved ultrafast UV/IR spectroscopy on tetraphenylethylene (TPE) observes Woodward–Hoffmann cyclic intermediates in dilute solution but not in the solid; "the ultrafast cyclization provides an efficient nonradiative relaxation pathway through crossing a conical intersection"; without it, "the electronic excitation is preserved in the molecular solids and the molecule fluoresces efficiently". **Terminology check**: the phrase "restricted access to a conical intersection" does *not* appear in the deposited abstract; the RACI coinage is R2b. |
| claim as used | The physical content behind M2–M4: in solution a CI-mediated ultrafast nonradiative channel exists; in the aggregate the pathway is geometrically inaccessible, so excitations decay radiatively instead. This is the empirical warrant for `torsion_blocks_ci` (M2.2: no admissible FC→CI path under the constraint) feeding `raci_emission_enhancement` (M4.2). |
| **formalizable implication** | (i) The paper's "pathway blocked in the solid" is formalized as *nonexistence of an admissible continuous path* (`BlockedBelow`, proven from `0 < δ`, `δ < θ0`, `FC ⊆ {θ | θ0 ≤ θ}`, `conicalSet M ⊆ {0}` and path continuity via IVT) — the explicit premises are exactly the constraint window and the endpoint separation. (ii) **Declared, never proved**: the two-state truncation (TPE's real photophysics involves more states), the reduction of the nuclear configuration space to a single torsion coordinate ℝ (cf. R3b: a *minimal* isomerization picture already needs ≥2 coordinates and 3 states), the linear gap model `gap = 2|θ|` (`torsionH`), and the energy-field reading of `below_energy` (M2 proves blocking for *all* ε, i.e. purely geometrically — stronger than the physical claim, which is energetic accessibility). (iii) Not expressible over installed mathlib: ultrafast wavepacket dynamics through the CI; ab-initio PES data. Neither enters any statement. |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text PDF on disk in the source repo, not re-read this round |

## R2b — the RACI coinage: the CI model for AIE (2013) and its named form (2016) — *seed addition*

| field | content |
|---|---|
| source | (i) Q. Li & L. Blancafort, "A conical intersection model to explain aggregation induced emission in diphenyl dibenzofulvene", *Chem. Commun.* **49**(53), 5966–5968 (2013), DOI `10.1039/C3CC41730A`. (ii) X.-L. Peng, S. Ruiz-Barragan, Z.-S. Li, Q.-S. Li, L. Blancafort, "Restricted access to a conical intersection to explain aggregation induced emission in dimethyl tetraphenylsilole", *J. Mater. Chem. C* **4**(14), 2802–2810 (2016), DOI `10.1039/C5TC03322E` |
| verification | Both Crossref records read: (i) title, authors, volume 49, issue 53, page 5966, 2013; its deposited reference list independently corroborates R1a (Luo 2001, page 1740). (ii) title, authors, volume 4, issue 14, pages 2802–2810, 2016 (received 2015-10-14); **deposited abstract read verbatim**: "Aggregation-induced emission of dimethyl tetraphenylsilole is due to restricted access to a conical intersection. The intersection allows for radiationless decay in solution but is not reachable in the aggregate phase." — this is the first source carrying the RACI phrase as its title; the acronym "RACI" in bare form is later community usage (not pinned to a single verifiable first occurrence here — registered, not hidden). |
| claim as used | The RACI hypothesis in its original computational form: the S₁/S₀ CI is reachable along the relaxation path in solution but unreachable in the aggregate, cutting the CI-mediated radiationless decay. This is precisely the implication `constraint ⇒ minimal accessible gap ↑` (M2/M4.3) with the aggregate modelled by the excluded torsion window. |
| **formalizable implication** | Licenses the *direction* of the formalized implication and nothing more: the papers' content is quantum-chemical (MECI optimizations, PES scans) and none of it is a Lean premise. What they fix for us is the statement shape `BlockedBelow` + `accessGap univ < accessGap (Allowed δ)` and the reading of `knr` as a CI-channel rate. **Declared, never proved**: that the physical aggregate actually realizes the `|θ| ≥ δ` window (steric/packing argument, outside the model); that `knr` decreases *specifically through the CI channel* (the M4+ generalization `quantumYield_gt_of_channel_ratios` records exactly this channel decomposition `knr = kCI + kOther` with `kOther` not increasing — an explicit premise, matching the literature's caveat that other quenching channels may coexist). |
| status | `verified (metadata+abstract, Crossref-deposited)` for both |

## R3 — conical-intersection reviews (the CI algebra context for M1)

| field | content |
|---|---|
| source | (i) W. Domcke, D. R. Yarkony, H. Köppel (eds.), *Conical Intersections: Electronic Structure, Dynamics and Spectroscopy*, Advanced Series in Physical Chemistry **Vol. 15**, World Scientific, July 2004; book DOI `10.1142/5406`, ISBN 9789812386724; chapter of record: D. R. Yarkony, "Conical Intersections: Their Description and Consequences", pp. 41–127, DOI `10.1142/9789812565464_0002`. (ii) B. G. Levine & T. J. Martínez, "Isomerization Through Conical Intersections", *Annu. Rev. Phys. Chem.* **58**, 613–634 (2007), DOI `10.1146/annurev.physchem.57.032905.104612` |
| verification | (i) Crossref book record read (title, editors, publisher World Scientific, series "Advanced Series in Physical Chemistry", 2004-07); the volume number 15 is corroborated by the ADS bibcode of Yarkony's chapter (`2004AdSPC..15...41Y`). (ii) Crossref record read: title, authors, volume 58, pages 613–634, 2007; deposited abstract read: "a minimal picture of the reaction mechanism requires the consideration of at least two molecular coordinates and three electronic states"; emphasis on conical intersections and charge transfer in photoisomerization. |
| claim as used | Standard CI theory: a degeneracy of two real Born–Oppenheimer surfaces needs two independent conditions (the branching plane coordinates: gradient-difference g and derivative-coupling h directions); near a CI the splitting is linear in the branching-plane displacement (the double cone); CIs are the funnels for ultrafast nonradiative decay. This is the content of M1 (discriminant algebra), M1.3 (codimension 2), M1.4 (`linearized_gap`: `e.1 − e.2 = 2|t|·√(gv² + hv²)`), and M1* (local seam). |
| **formalizable implication** | (i) Explicit Lean premises licensed: the **2×2 real symmetric** structure (`h_symm`), continuity of the Hamiltonian family (`h_cont`), and for the codimension statements **surjectivity of the degeneracy map's derivative** (`hreg`) plus finite-dimensionality; for M1* additionally **C¹ of the matrix elements** (`ContDiffAt ℝ 1 …`) and `CompleteSpace X`. (ii) **Declared, never proved**: the Born–Oppenheimer separation itself; the two-state truncation (R3b's abstract is the standing warning — 2 coordinates × 3 states is already the physical minimum, while the model uses 1 coordinate × 2 states; the formalization is the *algebraic core*, not the full picture); the linearization about the CI. (iii) Not expressible over installed mathlib: the **global** CI seam as an embedded codimension-2 submanifold (M1* delivers the *local* slice via `ImplicitFunctionData`; a global submanifold statement would need atlas machinery over degenerate loci where regularity fails — registered scope limit); derivative couplings as vector fields; any wavepacket dynamics. |
| status | (i) `verified (metadata, Crossref-deposited)`; (ii) `verified (metadata+abstract, Crossref-deposited)` — neither full text read here |

## R4 — the von Neumann–Wigner noncrossing rule (1929) and the codimension caveat

| field | content |
|---|---|
| source | J. von Neumann & E. P. Wigner, "Über merkwürdige diskrete Eigenwerte. Über das Verhalten von Eigenwerten bei adiabatischen Prozessen", *Phys. Z.* **30**, 467–470 (1929); ADS bibcode `1929PhyZ...30..467V`. Checkable secondary locus (read first-hand here): L. N. Trefethen, "Eigenvalue Repulsion" (Short Stories), *Notices Amer. Math. Soc.* **73**(6), 484– (2026), DOI `10.1090/noti3356` |
| verification | Primary: bibliographic locus corroborated by two independent Crossref-deposited reference lists — Longuet-Higgins 1975 (R5, ref p_9: "Z. Physik 30, 467, 1929") and Berry 1984 (R6, ref p_26: "Von Neumann J. & Wigner E. P. 1929 Phys. Z. 30 467-470") — and by the ADS record (title/volume/page match). The journal predates Crossref registration; no DOI. Secondary: Trefethen's note read first-hand (PDF): "the set of real symmetric 2×2 matrices is of dimension 3, whereas the set … whose eigenvalues are equal is of dimension just 1 … Thus the codimension is 2 … For complex Hermitian matrices the effect is even stronger, with a (real) codimension of 3"; n×n generalization `(n²+n)/2 − 2` and `n² − 3`. **This is exactly the seed's caveat, confirmed**: real symmetric → codim 2, complex Hermitian → codim 3. |
| claim as used | Degeneracies of a real symmetric two-level Hamiltonian occur at codimension 2 of the parameter space — the mathematical content of M1.3 (`finrank_branching_eq_two`: for a surjective continuous linear degeneracy map `F : Y →L[ℝ] ℝ×ℝ`, `finrank ℝ (ker F)ᗮ = 2`) and its M1* upgrade (local codim-2 seam slice). |
| **formalizable implication** | (i) The explicit premises are: real-symmetric structure (the whole theory is over ℝ — *consistent with the caveat*: codim 2 is the real-symmetric count; a Hermitian version would be codim 3 and is a registered non-goal), surjectivity (`hreg`), finite-dimensionality and inner-product structure on the parameter space. (ii) Note the formalization states the codimension **linearly** (dimension of the orthogonal complement of ker F), which is the mathematically load-bearing form; the "codimension of a submanifold" reading exists only locally via M1* and only under the regularity premise. (iii) Not expressible: the n×n degenerate-locus stratification (needs the full symmetric-matrix degeneracy stratification, not in mathlib); any statement about *complex Hermitian* families (codim 3) — the modules are ℝ-only by design. |
| status | primary `bibliographic-only` (two independent deposited reference lists + ADS record); codimension content `verified (first-hand read here)` via the Trefethen locus |

## R5 — the Longuet–Higgins sign theorem (1975)

| field | content |
|---|---|
| source | H. C. Longuet-Higgins, "The intersection of potential energy surfaces in polyatomic molecules", *Proc. R. Soc. Lond. A* **344**(1637), 147–156 (1975); DOI `10.1098/rspa.1975.0095` |
| verification | Crossref record read: author, title, volume 344, issue 1637, pages 147–156, published 1975-06-24. Deposited abstract read: "It is proved that if the wave function of a given electronic state changes sign when transported adiabatically round a loop in nuclear configuration space, then the state must become degenerate with another one at some point within the loop." |
| claim as used | The sign-change (monodromy −1) of a real electronic eigenfunction around a loop encircling a CI — formalized as M6.3 (`loop_monodromy`: `loopLowerVec (t + 2π) = − loopLowerVec t`) on the canonical loop `H(t) = [[cos t, sin t],[sin t, −cos t]]`, with M6.4 certifying the loop stays in the non-degenerate annulus (gap ≡ 2). |
| **formalizable implication** | (i) The delivered theorems are the *model direction*: an explicit eigenvector (`loopLowerVec`, proved an eigenvector of eigenvalue −1 in M6.1, unit norm in M6.2) flips sign after one turn — a finite ℝ² computation needing only trigonometric lemmas (`Real.sin_add_pi`, `Real.cos_add_pi`). (ii) The **converse direction** of Longuet-Higgins (sign change ⟹ degeneracy inside the loop) is *not* formalized — it would need a continuity/topological argument over the disk bounded by the loop (a 2D intermediate-value/degree argument for the degeneracy map `(a−d, b)`); registered as a possible future statement, currently **not claimed** by any module. (iii) Declared approximation: the loop model is the linearized CI model of M1.4, not an ab-initio surface. (iv) Not expressible over installed mathlib: the general statement for arbitrary C¹ Hamiltonian families and arbitrary loops (would need homotopy/degree theory glue beyond current mathlib usage here). |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text not read here |

## R6 — Berry phase context (1984)

| field | content |
|---|---|
| source | M. V. Berry, "Quantal phase factors accompanying adiabatic changes", *Proc. R. Soc. Lond. A* **392**(1802), 45–57 (1984); DOI `10.1098/rspa.1984.0023` |
| verification | Crossref record read: author, title, volume 392, issue 1802, pages 45–57, 1984. Deposited abstract read, key clause: "If C lies near a degeneracy of Ĥ, γ(C) takes a simple form which **includes as a special case the sign change of eigenfunctions of real symmetric matrices round a degeneracy**." Its deposited reference list corroborates R5 (`10.1098/rspa.1975.0095`) and R4 (Phys. Z. 30, 467–470, 1929). |
| claim as used | The M6 monodromy is the ℝ-valued shadow of the Berry phase: for a real symmetric Hamiltonian the geometric phase around a CI reduces to the Longuet–Higgins sign (−1 = exp(iπ)). |
| **formalizable implication** | (i) Licenses reading M6's `−1` as `exp(iπ)` — a remark, not a premise. (ii) Explicit premise boundary: everything delivered is over ℝ with an *explicit* eigenvector; no adiabatic transport operator, no connection, no curvature is defined in the modules. (iii) Not expressible over installed mathlib: the Berry phase as holonomy of a complex line bundle (principal-bundle/connection infrastructure not present); the adiabatic theorem itself. Both are registered non-goals; M6's scope is exactly the sign computation. |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text not read here |

## R7 — Landau–Zener sources (1932) and the collected-constant rate form

| field | content |
|---|---|
| source | (i) L. D. Landau, "Zur Theorie der Energieübertragung. II", *Phys. Z. Sowjetunion* **2**, 46–51 (1932) — no Crossref DOI (journal not deposited). (ii) C. Zener, "Non-adiabatic crossing of energy levels", *Proc. R. Soc. Lond. A* **137**(833), 696–702 (1932), DOI `10.1098/rspa.1932.0165`. Checkable review locus: S. N. Shevchenko, S. Ashhab, F. Nori, "Landau–Zener–Stückelberg interferometry", *Phys. Rep.* **492**(1), 1–30 (2010), DOI `10.1016/j.physrep.2010.03.002` |
| verification | (ii) Crossref record read: author, title, volume 137, issue 833, pages 696–702, 1932; deposited abstract read (level crossing of polar/homopolar molecular states — the avoided-crossing problem). (i) bibliographic locus corroborated by two independent Crossref-deposited reference lists: Shevchenko et al. 2010 (ref b81: "Landau, Phys. Z. Sowjetunion, vol. 2, first-page 46, 1932") and arXiv:2005.03284's reference list read here (ref [1]: "L. D. Landau, Zur Theorie der Energieübertragung. II, Physikalische Zeitschrift der Sowjetunion 2, 46 (1932)"); end page 51 is the standard cataloguing (registered, not independently re-verified). Review locus: Crossref record read (title, authors, volume 492, issue 1, pages 1–30, 2010). |
| claim as used | The two-state nonadiabatic transition probability across an avoided crossing is exponential in (minus) the squared coupling over the sweep rate: the standard form `P = exp(−2π V² / (ℏ·v·s))` (v the sweep velocity, s the diabatic slope difference). The formalization uses `lzProbability c a = exp(−(c·a))` with `c = c0/(v·F)` and `a = Δ²` — i.e. `2π/ℏ` (and the factor 4 between V and the minimal gap Δ = 2V) are **collected into the constant `c0`**, and only the strict antitonicity in `Δ²` is proved (M3.2: `lz_probability_antitone_in_gap`, explicit premises `0 < v`, `0 < F`, `0 < c0`, `0 ≤ Δ1`, `Δ1 < Δ2`). |
| **formalizable implication** | (i) Explicit Lean premises: positivity of every collected constant and of the sweep parameters; non-negativity of the smaller gap. (ii) **Declared, never proved**: the LZ regime itself (linear-in-time diabatic energies, constant coupling, exact solution of the driven two-level problem — none of which is modeled); the identification of the minimal adiabatic gap with `2V`; the use of an LZ form for the CI-mediated rate at all (a physical ansatz, cf. R2b's computational context). (iii) Not expressible over installed mathlib: the derivation of the formula from the time-dependent Schrödinger equation (special-function asymptotics, no infrastructure); time-dependent quantum dynamics generally. The barrier form `A·exp(−(β·B))` (M3.3, `barrierRate_antitone`, premises `0 < A`, `0 < β`) is likewise a *declared* Arrhenius/gap-rate shape — no transition-state theory is modeled. |
| status | (ii) `verified (metadata+abstract, Crossref-deposited)`; (i) `bibliographic-only` (two independent deposited reference lists); review locus `verified (metadata, Crossref-deposited)` |

## Registered, not load-bearing

| source | status | note |
|---|---|---|
| R. Crespo-Otero & L. Blancafort, "A Global Potential Energy Surface Approach to the Photophysics of AIEgens", *Handbook of Aggregation-Induced Emission*, 411–454 (2022), DOI `10.1002/9781119643098.ch14` | `bibliographic-only` | Cited in the ChemLean source plan; PES-level review of AIEgen photophysics. Not opened here; no statement depends on it. |
| P.-A. Yin, Q. Ou, Z. Shuai, "Computational Design Strategy for AIE Luminogens: Modulating the S₁/S₀ MECI of Anthracene Derivatives", *J. Chem. Theory Comput.* **21**, 4992–5002 (2025), DOI `10.1021/acs.jctc.5c00231` | `bibliographic-only` | Cited in the ChemLean source plan; modern computational RACI usage. Not opened here; no statement depends on it. |

## Statement-impact summary

**No delivered statement in `PhotoLean/RACI/` contradicts any verified source.** Row by row:

* M1 (`discr_eq_zero_iff_ci`, `degenerate_iff_discr_zero`, `ci_iff_degenerate`): pure 2×2 real symmetric algebra; consistent with R3/R4's CI algebra. No change.
* M1.3/M1* (`finrank_branching_eq_two`, `Fex` instance, `conicalSet_locally_slice`, `conicalSet_local_codim_two`): codimension 2 for a *real* family under a *surjectivity* premise — matches R4's caveat exactly (real symmetric → 2; the complex Hermitian codim-3 case is out of scope by design, not contradicted). No change.
* M2 (`exists_cross_forbidden`, `torsion_blocks_ci`, `torsionH` facts): the blocking direction (aggregate constraint ⇒ no CI access) matches R2/R2b; the formalization proves the stronger *all-ε* geometric blocking, which entails the physical (energetic) claim. No change.
* M3 (`barrierRate_antitone`, `lz_antitone`, `lz_probability_antitone_in_gap`, `lorentzian_antitone_on_norm`): only antitonicity is claimed; the physical rate forms (Arrhenius, LZ) are declared shapes with collected constants — consistent with R7. No change.
* M4/M4+ (`raci_emission_enhancement`, `quantumYield_gt_iff_ratio_lt`, `aie_iff_mul`, channel-ratio forms): the conclusion shape `Φ_agg > Φ_sol` matches R1a/R1b/R2; the equality-of-radiative-rates premise (`kr_agg = kr_free`) is an explicit hypothesis, and the ratio/channel generalizations correctly weaken it — matching the literature's caveat that only the *competition* `knr/kr` matters. No change.
* M6 (`loopLowerVec_eigen`, `loopLowerVec_sq_sum`, `loop_monodromy`, `loop_gap`): the model sign theorem matches R5/R6 (Berry's abstract names the real-symmetric sign change as a special case). The converse (sign change ⟹ enclosed degeneracy) is *not* claimed by any delivered statement — correctly, since it is unformalized. No change.

Seed corrections applied (recorded at the top of this file): (1) R1a/R1b replace the conflated seed item 1; (2) R2b supplies the RACI coinage that seed item 2 misattributed to the 2020 paper.
