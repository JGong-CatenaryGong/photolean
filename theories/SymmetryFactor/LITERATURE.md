# theories/SymmetryFactor/LITERATURE.md — literature record: the β = 1/2 practice, its warning record, and what is formalizable

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / arXiv id /
> printed page) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as a premise, a verdict, or a scope limit*. Statuses:
> `verified (first-hand read here)` / `verified (reused first-hand record of <theory>)` /
> `delegated` / `bibliographic-only`.
>
> The round had one job (H1 plan task L1): find a **first-hand practice locus** — a printed source
> that performs or endorses the identification "transfer coefficient / symmetry factor = 0.5"
> *without* the equal-force-constants condition — because the adjudication is only a **false
> equivalence** if the equivalence was on record as assumed. The pre-registered decision rule
> (H1 plan §3): L1 succeeds → H1∃ crossed; L1 fails → the deliverable is honestly retitled
> "boundary of an IUPAC-warned identification" and H1∃ stays open. **L1 succeeded** (S1 below).

## S1 — the practice locus (first-hand, read in full-text HTML 2026-09-21)

| field | content |
|---|---|
| source | L. Cabras, V. Oancea, A. Salvadori, "A novel two-mechanism model for all solid state Li-ion batteries: review and comparisons", **arXiv:2104.05424** (preprint; journal status not verified — graded honestly as a preprint) |
| locus | §2.1, prose immediately after eq. (8) (the Butler–Volmer interface condition of the reviewed Fabre et al. thin-film battery model); read via the ar5iv full-text HTML |
| verbatim | "with `s` either `a/e` or `e/c` and **α the so-called anodic (cathodic) charge transfer coefficient, usually both taken to be equal to 0.5**" |
| conclusion | A modelling-review paper documents — and adopts without qualification — the working value α(anodic) = α(cathodic) = 0.5 for the Butler–Volmer charge-transfer coefficient, in a review of battery models whose own eq. (8) puts α and 1−α on the two branches (the same additive structure as this repository's `transfer + reverseTransfer = 1`). No force-constant condition, no derivation of the value: it is *the usual value*. |
| **formalizable implication** | This is the "treated as interchangeable" side of the H1 pair: the unqualified reading is formalized as `BetaHalfReading kr kp := tsCoordZero kr kp = 1/2` asserted **for the model class** (positive curvatures). The kernel verdict `betaHalf_iff_equalForceConstants` decides it: the reading holds exactly on the equal-curvature diagonal, and fails at every unequal pair — witness `(1,4) ↦ 2/3`. The source licenses the *verdict target*, not a physical claim. |
| status | `verified (first-hand read here)` — full text retrieved and the sentence read in context; being a preprint, it is a **practice locus**, not an authority recommendation (the authority side is S2) |

## S2 — the warning record (first-hand, reused record of the BEP round-1g)

| field | content |
|---|---|
| source | IUPAC Technical Report 2014, *Pure Appl. Chem.* **86**(2), 245–258; DOI `10.1515/pac-2014-5026`; open copy read first-hand in the BEP round via Universidad de Alicante RUA DSpace 7 (record: `theories/BEP/LITERATURE.md` §R1.17 and `proofs/EXPERIENCE.md` 2026-09-20 round-1g) |
| loci | printed **pp. 255–256**: equating the Butler–Volmer symmetry factor with the observable transfer coefficient "needs an extra premise"; the report predicts "**large deviations of β from 0.5**" when the two force constants differ (citing Fletcher 2009's conversion formula). Printed **p. 257**: "The numerical value of the transfer coefficient α **can by no means be assumed**; it can only be obtained by measuring the Tafel slope"; complementarity is `αc + αa = n/ν` (eq. (43)) — the repository's `transfer + reverseTransfer = 1` is its single-electron special case. Printed **p. 259** (Recommendations, `10.1515/pac-2014-5025`): the observable definition α = (RT/F)(dE/d ln|j|)⁻¹ |
| conclusion | The standards body itself documents that (i) the β = α identification requires conditions, (ii) β deviates from 1/2 exactly when the force constants are unequal, (iii) α is measurable-not-assumable. |
| **formalizable implication** | The warning's *content* is what F2 turns into a theorem: the deviation regime is exactly `kr ≠ kp`, and its boundary is the iff `BetaHalfReading kr kp ↔ kr = kp`. The theory does **not** formalize the observable (Tafel-slope) definition — that is the kinetic reading, out of scope (plan §1.3); the structural reading is the Leffler/Hammond side, tied to the delivered E1 at equal curvature. |
| status | `verified (reused first-hand record)` — printed pages were read in the BEP round; not re-read here |

## S3 — coverage-dependence of the observable (first-hand, reused record of BEP round-1g)

| field | content |
|---|---|
| source | Shinagawa, Garcia-Esparza & Takanabe, *Sci. Rep.* **5**:13801 (2015); DOI `10.1038/srep13801`; OA (PMC4642571); printed pp. 5–6 read first-hand in the BEP round |
| conclusion | "The Tafel slopes used to evaluate the rate determining steps generally assume extreme coverage… the slopes are coverage-dependent"; "the same Tafel slopes can be obtained for different elementary steps with varied coverages". |
| **formalizable implication** | Independent first-hand evidence that the *observable* α is not a model constant — it motivates keeping the adjudication model-internal (verdicts about declared models, never about measured electrodes) and is cited in the RESULTS honesty section. |
| status | `verified (reused first-hand record)` |

## S4 — why the symmetric picture dominates (first-hand, reused record of hammond S34)

| field | content |
|---|---|
| source | Marcus, Nobel Lecture 1992, printed pp. 79/81 (journal version *Rev. Mod. Phys.* **65**, 599–610 (1993), DOI `10.1103/RevModPhys.65.599`); record: `theories/hammond/LITERATURE.md` S34 |
| conclusion | Marcus's own statement of the model's approximations, including "I introduced a '**symmetrization**' approximation for the vibrational part of the potential energy surface" — the equal-curvature picture is a declared approximation of the standard model, not a fact about every reaction. |
| **formalizable implication** | Explains the persistence half of the verdict: the conflated reading is a theorem **of the symmetrized model** (`betaHalf_holds_in_kernel`), which is the model every textbook draws — the kernel certificate tying `tsCoordZero lam lam` to `Kernel.tsCoord lam 0` is exactly this tie. |
| status | `verified (reused first-hand record)` |

## S5 — not first-hand this round (registered, not hidden)

| source | status | note |
|---|---|---|
| Fletcher 2009 (the "conversion formula" between β and α) | `delegated` | H1-plan task L2 (upgrade to first-hand) **not done this round** — out of budget; the verdict does not depend on it (S2 carries the warning record with printed pages). Registered as open. |
| IUPAC Gold Book entries "symmetry factor" / "transfer coefficient" | `not accessed` | `goldbook.iupac.org` returned HTTP 403 to this environment (same measurement as hammond S49's attempt); the older H02734 record there is already cited in `theories/hammond/LITERATURE.md` S49 with its own status. Not used as a load-bearing locus. |
| Butler (1924) / Erdey-Grúz & Volmer (1930) originals | `bibliographic-only` | the historical origin of the 1/2 value; not accessed (paywalled/scan); S1 + S2 suffice for the practice-plus-warning pair. |

## Round summary

L1 **succeeded at the first full-text source fetched** (S1); with S2's printed warning the pair
"practice locus + warning record + kernel verdict with exact boundary" is complete, so under the
pre-registered decision rule the milestone delivers the **H1∃ crossing** (an adjudicated
conflation), not the fallback. One honest grading note carried into RESULTS: S1 is a preprint and a
*review* of models — it documents modelling practice, which is exactly the kind of locus the
criterion asked for ("performs or endorses … without the condition"), but the paper should cite it
as practice evidence alongside IUPAC's warning, never as IUPAC's endorsement.
