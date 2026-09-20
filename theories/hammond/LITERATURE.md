# theories/hammond/LITERATURE.md — literature record: the Hammond postulate in the two-parabola model

> Maintained by `literature_researcher` (engine leaf `LITERATURE` for the second theory; the sibling
> record is `theories/Marcus/LITERATURE.md`). Contract: `proofs/ENGINE.yml`. Language: English.
> Every entry carries a **Formalizable implication** — the only part of a survey that the
> formalization can consume — and an explicit **Impact** on `theories/hammond/plan.md`.

---

## 0. Purpose, reading rules, notation, status vocabulary

### 0.1 Purpose

For every source this record answers one question: **what does this let us *state*, and what must we
*assume explicitly* in Lean?** Concretely, per source:

1. which hypotheses become **explicit Lean premises** (positivity, non-degeneracy, parameter
   inequalities…);
2. which steps are **physical approximations** that must be *declared* rather than proved;
3. which claims **cannot be expressed** in the installed mathlib (Lean 4.17.0 + mathlib), and what
   blocks them.

### 0.2 Rule (non-negotiable)

**Literature fixes statements and premises; it never replaces proof.** No citation below is used as a
substitute for a kernel step. Quotes are kept to the minimum needed to fix wording (short, decisive
sentences with page/equation loci); no abstract dumps, no PDF text pasted, no full paper read into
context — PDFs were piped through `pdftotext` and only grepped, or read as rendered images.

### 0.3 Theory under formalization (per `theories/hammond/plan.md`, milestones H1–H5)

Reaction coordinate `q`; reactant well at `q = 0`, product well at `q = 1`; **harmonic surfaces of
equal curvature** `2λ`:

```
reactantSurface lam q     = lam * q^2
productSurface  lam dG q  = lam * (q - 1)^2 + dG      -- dG = ΔG°  (exergonic: dG < 0)
x                         = -ΔG°                      -- driving force (exergonic: x > 0)
tsCoord lam x             = (lam - x) / (2 * lam)     -- crossing point q‡
gapReactant lam x         = (lam - x)^2 / (4 * lam)   -- forward barrier
gapProduct  lam x         = (lam + x)^2 / (4 * lam)   -- reverse barrier
lefflerSecant  lam x1 x2  = -(gapReactant lam x2 - gapReactant lam x1) / (x2 - x1)
```

Planned claims (the lead's brief and plan H1–H5): **(a)** `tsCoord` strictly decreasing in `x` iff
`λ > 0`; **(b)** energy–structure correspondence ("TS closest in structure ⟺ closest in energy",
equivalent to `gapReactant < gapProduct ↔ 0 < x`); **(c)** the Leffler/Brønsted coefficient measured
from barrier data equals the TS coordinate at the secant midpoint and satisfies `0 < α < 1` iff
`-λ < x < λ`; **(d)** for `x > λ` (Marcus inverted region) `q‡ < 0`, `α < 0`, and the
structural-resemblance reading leaves its domain; **(e)** kernel-checked verdicts for literature
`(λ, x)` pairs.

### 0.4 Notation and sign conventions (declare these in Lean docstrings)

| symbol here | meaning | source notation | trap to record |
|---|---|---|---|
| `q`, `q‡` | scalar reaction coordinate; crossing coordinate | `n` / `n*` = "degree-of-reaction parameter" and its value at the barrier maximum (Marcus 1968, symbol list p. 899) | Marcus's `n` is *his* structural parameter; our `q` is a coordinate, not a bond order |
| `λ` | reorganization energy, product of the two-parabola model | Marcus: `λ = λ_o + λ_i` (Nobel 1992 Eq. (6), printed p. 78); modern: `λ_out + λ_in`; `λ = λ_R + λ_P` in cross-relations | `λ` vs **`λ/4` = intrinsic barrier**: Cohen & Marcus 1968 write the barrier as `ΔF* = (λ/4)[1 + ΔF°'/λ]²` and call `ΔF_0* = λ/4`; Marcus 1968's abstract writes `ΔF* = λ(1 + ΔF°'/λ)²/4`; Denisov 2012 Eq. (2) writes the same identity with their `E_r` in the slot of `λ/4` |
| `x` | driving force `= -ΔG°` (exergonic `x > 0`) | `-ΔG°`, `-ΔF°′`; Nobel Fig. 8 axis is labelled `-ΔG° (eV)` | in the inverted region `ΔG°` is **negative**: never write `ΔG° > λ` (it means the normal region) |
| `α` | Leffler/Brønsted coefficient as a *barrier-data observable* (`lefflerSecant`) | Marcus 1968: "local Brønsted slope `α`"; Cohen & Marcus 1968: "instantaneous slope"; IUPAC: `δΔ‡G = α δΔ_rG°`; Nobel 1992 p. 85: "slope of 1/2" | Marcus's `α` is the *slope*; the electrode "transfer coefficient" is a different object (and in arXiv:2511.01909 `α` is a tunneling parameter — do not conflate) |
| `Δ`, `ΔF°′`, `ΔG°` | standard free energy of reaction | Marcus 1968 abstract writes `α = (1 + Δ/λ)/2` with `Δ` standing for `ΔF°′` (**our reading** of the abstract's own context — flagged, not verbatim) | one must state which `Δ` is meant |

### 0.5 Verification-status vocabulary

| status | meaning |
|---|---|
| `verified` | read in this survey by the author of this record; the medium is named (full text / abstract / figure image / text-layer grep) |
| `verified (delegated read)` | the text and locus were reported by a delegated surveyor of this survey; the bibliographic record was re-checked against Crossref here, the text was **not** re-read here |
| `verified (abstract-level)` | the quoted sentence is from the publisher's abstract as mirrored in a repository record; body not read |
| `verified (sibling record)` | already read and recorded in `theories/Marcus/LITERATURE.md` (local PDF present there); not re-read here |
| `recalled-needs-check` | from prior knowledge, **not** read in a retrieved source during this survey |
| `order-of-magnitude` | only a title / citation list / rough value; **no locus** may be quoted |
| `not-accessed` | the source exists (Crossref-verified) but its text could not be retrieved (paywall/403); **no claim is attributed to it** |

### 0.6 Anti-patterns (forbidden; same discipline as the sibling record)

- pasting large excerpts or abstracts instead of a formalizable implication;
- using a literature conclusion in place of a proof step ("the literature says it is monotone");
- attributing a sentence to a source that was only cited second-hand or whose text was blocked
  (every such item is marked `recalled-needs-check` / `order-of-magnitude` / `not-accessed`);
- promoting an *algebraic consequence of a model* into an *empirical law* (see §4.2, the
  `α < 0 ⟺ inverted region` question — **no source states it**; it is a theorem of the model).

---

## 1. Source table

### 1.1 Sources

| # | Source (short) | DOI / URL | What it fixes for us | Status |
|---|---|---|---|---|
| S1 | Hammond, *J. Am. Chem. Soc.* **77**(2), 334–338 (1955), "A Correlation of Reaction Rates" | `10.1021/ja01607a027` | The postulate's **verbatim** wording and its two consequences (§2); the "closest in energy" question; his own footnote that the postulate is about **potential** energy and that entropic changes are uncontrolled | `verified` (full text, OCR of the printed article; no OA copy exists) |
| S2 | Hammond, "This Week's Citation Classic" commentary, *Current Contents/PC&ES* 1985, p. 16 (ISI) | `garfield.library.upenn.edu/classics1985/A1985ANX0100001.pdf` | The author's own later verdict: the rules "contain conceptual weaknesses", the "most egregious" being the tacit assumption of *similar potential functions* for all bonds; warning against abusing TS theory | `verified` (full text) |
| S3 | Leffler, *Science* **117**(3039), 340–341 (1953), "Parameters for the Description of Transition States" | `10.1126/science.117.3039.340` | The historical priority of the α-as-structure idea (α relating rate to equilibrium change) | **`not-accessed`** (paywalled; Crossref + PubMed record verified, no OA copy: Unpaywall `is_oa=false`, Semantic Scholar `CLOSED`); the *content* is carried by S4/S5 |
| S4 | Perrin et al., IUPAC "Glossary of terms used in physical organic chemistry (IUPAC Recommendations 2021)", *Pure Appl. Chem.* **94**(4), 353–534 (2022) | `10.1515/pac-2018-1010` (manuscript PDF: `iupac.org/wp-content/uploads/2021/05/PAC-REC-18-10-10.R6_PR20210507.pdf`) | The **normative** definitions: "Hammond postulate (Hammond-Leffler principle)" (a *Hypothesis*); "Leffler's relation / Leffler's assumption" (`α` = "approximate measure of the fractional displacement of the TS", with "**many exceptions**"); "anti-Hammond effect"; the parallel(Hammond)/perpendicular(anti-Hammond) decomposition attributed to Thornton; the "Marcus equation" entry | `verified` (full text; entries quoted in §2.3, §5.1) |
| S5 | Leffler & Grunwald, *Rates and Equilibria of Organic Reactions*, Wiley (1963) | cited as ref. [109] of S4 | The book locus to which IUPAC attaches the `α`-as-fractional-displacement interpretation | `not-accessed` (cited via S4 only) |
| S6 | Marcus, *J. Chem. Phys.* **24**(5), 966–978 (1956) | `10.1063/1.1742723` | The two-parabola derivation and the barrier formula (Eq. (38), printed p. 974); rate written as collision number × exponential (Eq. (44), p. 975) | `verified (sibling record)`; local PDF `theories/Marcus/literature/Marcus1956_ET_theory_I.pdf`. **Full-text grep: "slope" 0, "alpha" 0, "Bronsted" 0, "inverted" 0 hits** — 1956 contains **no** α formula and **no** inverted region |
| S7 | Marcus, *Discuss. Faraday Soc.* **29**, 21–31 (1960) | `10.1039/df9602900021` | The **first** statement of the inverted region: item "(v) Possibility of 'inverted' chemical behaviour" | `verified` (local PDF `Marcus1960_Faraday_inverted_region.pdf`, printed p. 28; quote in §4.1). **Full-text grep: no `slope`, no `Brønsted`, no `α`** |
| S8 | Marcus, Nobel Lecture 1992, "Electron Transfer Reactions in Chemistry: Theory and Experiment", *Chemistry 1992* (Nobel Foundation), printed pp. 71–89 | local PDF `theories/Marcus/literature/Marcus1992_nobel_lecture.pdf` | Printed loci for: barrier Eq. (5b) (p. 78), `λ = λ_o + λ_i` Eq. (6) (p. 78), inverted region + the **Brønsted/Tafel-plot** analogy (p. 82), slope 1/2 (p. 85), Fig. 8 annotation `λ_s = 0.75`/`λ_v = 0.45` eV/`ω = 1500 cm⁻¹` (p. 84), reaction-centre numbers `0.25 eV`/`~1.1 eV` (p. 88), atom/proton/methyl-transfer scope limit (p. 90) | `verified` (text layer + rendered Fig. 8 PNG read here). **"Hammond" 0 hits, "Leffler" 0 hits** |
| S9 | Cohen & Marcus, *J. Phys. Chem.* **72**(12), 4249–4256 (1968), "On the slope of free energy plots in chemical kinetics" | `10.1021/j100858a052` | **The α formula as an observable slope**, applied to experiment: instantaneous slope of the `ΔF*` vs `ΔF°′` plot `= (1/2)[1 + ΔF°′/(4ΔF_0*)]`, applied to Brønsted-slope data of **16 proton- and atom-transfer series**, "experimental results are consistent with this equation, but more data are needed" | `verified (abstract-level)` (CaltechAUTHORS record `adpqk-tcp81`, abstract reproduced) |
| S10 | Marcus, *J. Phys. Chem.* **72**(3), 891–899 (1968), "Theoretical relations among rate constants, barriers, and Broensted slopes of chemical reactions" | `10.1021/j100849a019` | "local Brønsted slope `α` … `α = (1 + Δ/λ)/2`"; barrier with work term `ΔF* = w^r + λ(1 + ΔF°′/λ)²/4`; the "degree-of-reaction parameter" `n`, `n*`; `λ` constant across a series "as a conjecture"; Appendix II: the two-parabola picture is a **projection** of a many-dimensional surface, and for bond-breaking atom/proton transfers the **inverted effect is removed** | `verified (abstract-level)` for the abstract (CaltechAUTHORS `xnks4-y0h56`) + `verified (delegated read)` for the Appendix II/III and symbol-list quotes (§3.2, §4.4, §5.2) |
| S11 | Marcus, *J. Am. Chem. Soc.* **91**(26), 7224–7225 (1969), "Unusual slopes of free energy plots in kinetics" | `10.1021/ja01054a003` | Primary-adjacent identification **slope of the barrier-vs-driving-force plot ↔ position of the TS along the reaction coordinate**, and application to experimental "unusual Brønsted coefficients" | `verified (abstract-level)` (CaltechAUTHORS `wew6q-35t88`) |
| S12 | Marcus & Sutin, *Biochim. Biophys. Acta (BBA) — Reviews on Bioenergetics* **811**(3), 265–322 (1985), "Electron transfers in chemistry and biology" | **`10.1016/0304-4173(85)90014-X`** | The standard review-level statement of the unified theory (work terms, cross-relation, inverted region) | `not-accessed` (paywalled). **⚠ The DOI `10.1016/0005-2728(85)90039-9` returns 404 at Crossref and at doi.org — do not use it** |
| S13 | Sutin, "Theory of Electron Transfer Reactions: Insights and Hindsights", *Prog. Inorg. Chem.* **30**, 441–498 (1983) | `10.1002/9780470166314.ch9` | Review-level treatment of the inverted region; identified for citation only | `not-accessed` |
| S14 | García-Padilla & Qiu, *Chem. Sci.* **16**(37), 17494–17505 (2025), "The global kinetic–thermodynamic relationship derived from first principles" | `10.1039/d5sc04829j` (OA, PMC12406046) | **The closest published form** of "the inverted region is where Brønsted slopes go negative" (quotes in §4.1); "the gradient at `E_eq` is always equal to 0.5"; the two-parabola model "assuming both reactants and products distort identically and quadratically" fixes the thermoneutral slope at 0.5, "which often does not hold"; causes of non-monotonic response: asynchronicity, intersystem crossing | `verified` (OA full text read here) |
| S15 | Villegas-Escobar, "Is the Brønsted coefficient a robust measure of the position of the transition state?", *Chem. Phys.* (2026), art. 113488 | `10.1016/j.chemphys.2026.113488` (preprint `10.2139/ssrn.6719541`) | **Equality of the Brønsted coefficient with the TS position is exact only under the symmetric (equal-curvature) approximation** and diverges systematically with asymmetry; "the Brønsted coefficient is not a general descriptor of transition-state structure" | `verified (delegated read)` (abstract); bibliographic record re-checked here |
| S16 | Denisov, Shestakov & Denisova, "Transition state geometry in radical hydrogen atom abstraction", *Russ. Chem. Rev.* **81**(12), 1117–1132 (2012) | `10.1070/RC2012v081n12ABEH004275` (free PDF `russchemrev.org/RCR4275pdf`) | The intersecting-parabolas model **makes the postulate quantitative** (§IV, p. 1123); "the TS configuration always differs from that of both reactants and products" (p. 1124); the barrier identity `ΔG‡ = E_r(1 + ΔG/(4E_r))²` (Eq. (2)) | `verified` (full text read here; free PDF's text layer garbles equations — prose quoted only) |
| S17 | Denisov, "The Hammond postulate: A quantitative interpretation", *Russ. J. Phys. Chem. B* **2**(4), 343–349 (2008) | `10.1134/s1990793108030020` | The thermoneutral TS position depends on force constants and bond lengths when the reaction centre is **asymmetric**; the structural dependence on `ΔH` is linear only over a bounded range, nonlinear in the Morse-curve model | `verified (delegated read)` (abstract) |
| S18 | Cremer & Kraka, "Verification and Quantification of the Hammond–Leffler Postulate", *Revista Processos Químicos* **6**(11), 27–30 (2012) | `10.19142/rpq.v6i11.152` | Computational test of the postulate: "This has not led to a general verification of the HLP"; reaction-path regions are "often … not centered at the TS"; quantification via path curvature for ~150 reactions, 19 of type `XHn + H2` at CCSD(T)/cc-pV5Z | `verified` (full text read here) |
| S19 | Bochet & Harvey, "Is there a photochemical Hammond postulate?", *Chem. Sci.* **12**(2), 599–605 (2021) | `10.1039/D0SC04370B` (OA, PMC8178980) | "So far, **no systematic studies** on the validity of the Hammond postulate for photochemical reactions are available"; "there are currently **no guiding principles like the HP in photochemistry**"; credits Leffler's priority (1953) and uses "Hammond–Leffler postulate" | `verified` (OA full text read here) |
| S20 | Boeije & Olivucci, *Chem. Soc. Rev.* **52**, 2643–2687 (2023) | `10.1039/D2CS00719C` | The photochemical bottleneck is not a point but an **intersection space (a seam)** | `verified (delegated read)` (abstract) |
| S21 | Buck, Beck & Winter, *J. Am. Chem. Soc.* **136**(25), 8933–8940 (2014) | `10.1021/ja501777r` | Documented **inversion of substrate preference** between thermal and photochemical reactions: "switching from transition-state control in thermal heterolysis reactions to conical intersection control" | `verified (delegated read)` (abstract) |
| S22 | Ben-Nun, Molnár, Schulten & Martínez, *PNAS* **99**(4), 1769–1773 (2002) | `10.1073/pnas.032658099` | "energetic considerations cannot explain the observed bond selectivity … origin … is the shape (topography) of the potential energy surfaces in the vicinity of points of true degeneracy" | `verified (delegated read)` (abstract) |
| S23 | Migliore, Polizzi, Therien & Beratan, *Chem. Rev.* **114**(7), 3381–3465 (2014) | `10.1021/cr4006654` (OA, PMC4317057) | Peer-reviewed OA anchor that "`Q_t` is closer to the equilibrium geometry of the precursor complex … agree[s] with … the Hammond postulate", **conditional on `λ` being constant across the series** ("Equations 6.23 and 6.24 hold if the reorganization energy is constant for a reaction series … Otherwise, eq 6.24 is replaced by 6.25 where `∂λ/∂ΔG_R°` … describes the variation in the intrinsic barrier") | `verified` (OA full text read here) |
| S24 | Qiu, "Exceptions, Paradoxes, and Their Resolutions in Chemical Reactivity", *J. Org. Chem.* **89**(22), 16307–16316 (2024) | `10.1021/acs.joc.4c02246` (OA, PMC11574852) | "between different intrinsic reactivities, the Hammond postulate is no longer relevant" (fixed-intrinsic-barrier premise); catalogue of exception types incl. dynamics/tunneling/recrossing references | `verified` (OA full text read here) |
| S25 | Koeppl & Kresge, "Marcus rate theory and the relationship between Brønsted exponents and energy of reaction", *J. Chem. Soc., Chem. Commun.* (11), 371–373 (1973) | `10.1039/C39730000371` | Realistic variation of bond strengths/reaction distances gives a **sigmoid Brønsted slope**, deviating from the Marcus prediction | `verified (delegated read)` (via S14's characterization) / bibliographic record re-checked here |
| S26 | Richard & Jencks, *J. Am. Chem. Soc.* **106**(5), 1396–1401 (1984) | `10.1021/ja00317a034` | Documented deviations of Brønsted slopes in general base catalysis (differential charge development, reactant–product asymmetry) | `verified (delegated read)` (via S14's characterization) / bibliographic record re-checked here |
| S27 | Espinosa et al., "Correlating Thermodynamic and Kinetic Hydricities of Rhenium Hydrides", *J. Am. Chem. Soc.* **144**(39), 17939–17954 (2022) | `10.1021/jacs.2c07192` | A **measured Brønsted α series** (hydride transfer) analysed with Marcus: "Brønsted α values were obtained … which enables the use of Marcus theory …"; with increasing driving force the reactions become "less sensitive … because there is less buildup of charge in the increasingly early transition state" | `verified (abstract-level)` |
| S28 | Silverman, "Marcus rate theory applied to enzymatic proton transfer", *Biochim. Biophys. Acta* **1458**(1), 88–103 (2000) | `10.1016/s0005-2728(00)00061-x` | Experimental proton-transfer series whose Brønsted plots are "of high curvature" and are fitted by Marcus theory (intrinsic barrier 1–2 kcal/mol; work terms 4–10 kcal/mol) | `verified (abstract-level)` |
| S29 | Miller, Calcaterra & Closs, *J. Am. Chem. Soc.* **106**(10), 3047–3049 (1984) | `10.1021/ja00322a058` | The experimental inverted-region data set reproduced as Nobel 1992 Fig. 8 — the provenance of the MCC `(λ, x)` instance pairs | `verified (sibling record)` + `verified` for the Fig. 8 annotation (image read) |
| S30 | Pu, Gao & Truhlar, *Chem. Rev.* **106**(8), 3140–3169 (2006); Carpenter, *Chem. Rev.* **113**(9), 7265–7286 (2013); JACS **131**, 3130–3131 (2009) | `10.1021/cr050308e`, `10.1021/cr300511u`, `10.1021/ja807666d` | Recrossing / transmission coefficient, non-statistical dynamics, and an explicit case of TST failure in an alkene hydroboration | bibliographic records `verified`; content `not-accessed` (cited as pointers via S24's reference list) |
| S31 | Kresge, "The Nitroalkane Anomaly", *Can. J. Chem.* **52**(10), 1897–1903 (1974); Agmon, "Is there a nitroalkane anomaly?", *J. Am. Chem. Soc.* **102**(7), 2164–2167 (1980) | `10.1139/v74-270`, `10.1021/ja00527a003` | The classic case of a Brønsted slope **outside** `(0,1)` — the mirror branch `x < -λ` of the model | bibliographic records `verified`; content `not-accessed` (403) → `recalled-needs-check` for any α value |
| S32 | Thornton, *J. Am. Chem. Soc.* **89**(12), 2915–2927 (1967); Steffa & Thornton, *J. Am. Chem. Soc.* **89**(24), 6149–6156 (1967) | `10.1021/ja00988a020`, `10.1021/ja01000a026` | Priority for the "perpendicular (anti-Hammond) effect" | bibliographic records `verified`; content `not-accessed` (the substance is carried by S4) |
| S33 | Agmon, "Quantitative Hammond postulate", *J. Chem. Soc., Faraday Trans. 2* **74**, 388 (1978) | `10.1039/f29787400388` | Title-level: the classical "quantitative Hammond" tradition | `order-of-magnitude` (content `not-accessed`, RSC blocked) |

### 1.2 Formalizable implications at a glance

| Premise / approximation that must be **explicit** in Lean | Where it lives | Forced by |
|---|---|---|
| `0 < lam` (positive curvature = reorganization energy) | every H2/H3 theorem signature (`hlam : 0 < lam`) | model consistency; S6/S7/S12 lineage; S4 "Hypothesis" framing |
| `lam ≠ 0` where only the crossing *identity* is at stake (`crossing_iff`, `tsCoord_neg`) | H1 signatures | algebra (division) — not physics |
| `x₁ ≠ x₂` (non-degenerate secant) | `lefflerSecant_eq_midpoint`, `lefflerSecant_mem_iff` | definition of a finite difference |
| `lam` **fixed across the compared pair/series** (intrinsic barrier constant) | implicit in `HammondDescriptor lam` / `lefflerSecant lam …`; must be documented | S23 ("hold if the reorganization energy is constant for a reaction series"), S24 ("between different intrinsic reactivities, the Hammond postulate is no longer relevant"), S10 ("assumed constant as a conjecture for a reaction series") |
| **equal curvature** of the two parabolas (symmetric case) | the definition of `productSurface` with the same `lam`; must be named as an assumption | S15 (exactness only in the symmetric approximation), S14 ("assuming both reactants and products distort identically and quadratically"), S17 (asymmetric centre ⇒ force-constant-dependent thermoneutral TS) |
| one scalar coordinate `q` = "molecular structure" | `reactantSurface`/`productSurface`/`tsCoord` docstrings | S10 Appendix II (parabola = a *profile* along a coordinate in many-dimensional configuration space; TS = distribution centred at the intersection) |
| the TS is the classical **crossing point** (static picture, no dynamics) | `crossing_iff`; H1 | S24/S30 pointers (recrossing, transmission coefficient), S19 (photochemistry has no such single-surface TS) |
| **no work terms** (`w_r = w_p = 0`) | absorbed into `ΔG°`; document it | S10 (`ΔF* = w^r + λ(1+ΔF°′/λ)²/4`), S12 |
| classical nuclei (no tunneling), no electronic-structure input | out of scope; document it | S24's tunneling references; S8 p. 82 context |
| the model applies to **ET-type** reactions (reorganization not dominated by bond rupture/formation) for the inverted-region verdict | instance layer documentation | S10 Appendix II, S8 p. 90 (both quoted in §4.4) |
| `λ = 0` branch uses Lean's `x / 0 = 0` **convention** | `tsCoord_zero_lam`, sharpness witnesses | formal, not physical (already plan §13 row 5) |

| Claim that **cannot** be expressed in the installed mathlib | Blocker |
|---|---|
| "molecular structure", bond lengths/angles, *which* bond breaks — beyond the scalar `q` | no chemistry/geometry layer; only `ℝ`-arithmetic is used |
| many-dimensional PES, MERP, perpendicular/anti-Hammond effects | no multivariable Morse theory / saddle geometry application layer; model is 1-D by construction |
| entropy, partition functions, free-energy vs potential-energy conversion | no statistical-mechanics layer (and Hammond's own footnote S1: entropic changes are *uncontrolled* by the postulate) |
| rate constants, prefactors, TST, transmission coefficients, recrossing, tunneling | no reactive-flux / dynamics machinery; the project deliberately formalizes barriers only |
| conical intersections, seam dimensions, surface hopping | needs multivalued/vector-bundle-style PES layer; entirely out of scope |
| physical units (eV vs K vs J) | mathlib has no unit system; the instance layer must carry units in documentation only |

---

## 2. Hammond's postulate — verbatim wording (Q1)

### 2.1 What the 1955 paper literally says

**Source**: S1, `10.1021/ja01607a027`. **Locus**: printed **p. 334**, right column.
**Status**: `verified` (full-text OCR of the printed article; the paper is not open access, so the text
was read from a scanned copy of JACS 77, 334–338 and cross-checked against the wording quoted in S18,
S21 and S4 — the three agree word-for-word).

The statement of the postulate (the two sentences to quote):

> "If two states, as for example, a transition state and an unstable intermediate, occur consecutively
> during a reaction process and have nearly the same energy content, their interconversion will
> involve only a small reorganization of the molecular structures."

Immediately following, the operational consequence that the formalization actually uses:

> "The value of the postulate derives from its application to elementary processes which are either
> highly exothermic or highly endothermic. In highly exothermic steps it will be expected that the
> transition states will resemble reactants closely and in endothermic steps the products will provide
> the best models for the transition states."

Two further loci on the same page matter for our premises:

> (footnote 1) "It will be noticed that the postulate deals directly with potential energy rather than
> free energy relationships. Translational entropy changes and to some extent solvation entropies are
> essentially uncontrolled by the postulate."

> (Fig. 1 discussion) "In the first case, going from the reactants to the transition state involves
> little progress along the reaction coordinate and in the second the same is true of the conversion of
> the transition state to the product."

### 2.2 Does the original say the TS resembles the species to which it is "closest in energy"? — **No.**

**Clean negative, `verified`**: the phrases **"closest"**, **"close in"**, **"nearest"**, **"near in"**
occur **0 times** in the full text of Hammond 1955 (whole-document search of the OCR text of
pp. 334–338). The paper speaks of species with "nearly the same energy content" (in the *pair of
states* sense) and of reactants/products being "the best models", not of a "closest-in-energy"
species. The familiar sentence

> "the structure of the transition state resembles that of the species to which it is closest in energy"

is a **later paraphrase**, not Hammond's wording. Consequences for the plan:

- plan §1.1 quotes exactly that paraphrase as "Hammond's postulate" → it must be re-labelled as the
  standard modern paraphrase (or replaced by the 1955 wording above), otherwise the record would
  attribute to the 1955 paper a sentence it does not contain;
- the paraphrase is nonetheless a *faithful* reading of the two energy–structure links in the model:
  see §2.4, where the "closest in energy" reading and the "less stable species" reading are proved to
  coincide inside the equal-curvature two-parabola model.

### 2.3 The canonical modern wording (what to cite for the normative statement)

**Source**: S4, `10.1515/pac-2018-1010`. **Status**: `verified` (full text).

- Entry **"Hammond postulate (Hammond-Leffler principle)"**:
  > "**Hypothesis** that, when a transition state leading to a high-energy reaction intermediate (or
  > product) has nearly the same energy as that intermediate (or product), the two are interconverted
  > with only a small reorganization of molecular structure."
- **Note 1** (the naming issue):
  > "Essentially the same idea is sometimes referred to as 'Leffler's assumption', namely, that the
  > transition state bears a greater resemblance to the **less stable species** (reactant or reaction
  > intermediate/product). Many textbooks and physical organic chemists, however, express the idea in
  > Leffler's form (couched in terms of Gibbs energies) but attribute it to Hammond (whose original
  > conjecture concerns structure)."
- **Note 3** (the model-theoretic content):
  > "If a factor stabilizes a reaction intermediate (or reactant or product), then the position of the
  > transition state along the minimum-energy reaction path (MERP) for that elementary step moves away
  > from that intermediate … This behaviour is often called a **Hammond effect** and is simply a
  > consequence of adding a **linear perturbation to the parabola**."

S19 independently confirms the attribution history: "While best known as the Hammond postulate, Jack
Leffler proposed a similar idea two years before Hammond's paper was published."

### 2.4 Formalizable implication of §2

- **Explicit Lean premises**: none from §2 itself — the postulate is qualitative. What §2 fixes is the
  *statement* the model must realize: (i) energy proximity between consecutive states, (ii) "small
  reorganization of molecular structure" = small displacement along the coordinate.
- **Physical approximations to declare**:
  1. **"resemblance" = the scalar `q`** — Hammond's "small reorganization of the molecular structures"
     is replaced by "the TS sits at `q‡`, and `q‡` is compared with 0 and 1". This is the whole
     modeling bridge; literature supports it (S4 Note 3's "linear perturbation to the parabola",
     S16's "the intersecting parabolas model can make the postulate quantitative").
  2. **energy ≠ free energy**: Hammond's own footnote places the postulate on **potential** energy and
     declares translational/solvation entropy "uncontrolled"; our `λ` and `ΔG°` are free-energy-like
     quantities (Marcus's convention). The two must be reconciled by declaration, not proof.
  3. **which reading of "closer"**: the literature canonically says "**greater resemblance to the less
     stable species**" (S4), while the colloquial form says "closest in energy". In this model both
     readings are *equivalent* (proof sketch: `gapProduct - gapReactant = x` and
     `productSurface lam dG 1 - reactantSurface lam 0 = -x`, so
     `gapReactant < gapProduct ↔ x > 0 ↔ reactant well is the higher/less stable well`). **The
     equivalence of the two readings is exactly the content that the postulate contributes**; the
     model proves it, the postulate asserts it about molecules. Since the two readings can differ
     outside equal curvature (S15, S17), the plan should name the reading it uses.
- **Not expressible**: "molecular structures" themselves (bond lengths, angles, which bond), i.e. the
  literal content of the 1955 sentence, is not expressible; only the scalar coordinate is.
- **Impact**: plan §1.1 must (i) replace the "closest in energy" quotation by the 1955 wording or
  label it as a paraphrase (§9 item 1), and (ii) state which energy–structure link claim (b) uses.

---

## 3. The quantitative two-parabola statements (Q3)

### 3.1 Loci for the barrier formula

| statement | locus | status |
|---|---|---|
| barrier `ΔG‡ = (λ/4)(1 + ΔG°′/λ)²` (equivalent to `(λ - x)²/(4λ)`) | S8, **Eq. (5b), printed p. 78** | `verified (sibling record)` + re-checked text layer |
| `λ = λ_o + λ_i` (= `λ_out + λ_in`) | S8, **Eq. (6), printed p. 78** | `verified (sibling record)` |
| original two-parabola derivation (gas-phase/ET free-energy surfaces, no work terms) | S6, **Eq. (38), printed p. 974** | `verified (sibling record)` |
| barrier with explicit work term | S10: `ΔF* = w^r + λ(1 + ΔF°′/λ)²/4` (eq. (2) as read) | `verified (delegated read)`; abstract-level `verified` |
| `ΔG‡ = E_r(1 + ΔG/(4E_r))²` (their `E_r` in the `λ/4` slot) | S16, **Eq. (2)** | `verified` (prose/equation form; text layer garbles symbols) |
| inverted-region criterion: barrier "vanish[es] at `ΔG° = -λ`" and increases beyond | S8, **printed p. 82** | `verified` (text layer) |
| first statement of the inverted region | S7, **printed p. 28, item (v)** | `verified` (local PDF) |

### 3.2 The α formula (the decisive loci)

1. **Marcus 1968** (S10), abstract, `verified (abstract-level)`:
   > "(3) a calculation of the local Brønsted slope α from the intercept of the ΔF* vs. ΔF^0' plot,
   > **α = (1 + Δ/λ)/2**"
   with the abstract's `Δ` standing for `ΔF°′` (**our reading**, flagged in §0.4). With `x = -ΔG°`
   this is `α = (λ - x)/(2λ)` — **identical to `tsCoord`**.
2. **Cohen & Marcus 1968** (S9), abstract, `verified (abstract-level)`:
   > "the instantaneous slope of a `ΔF*` vs. `ΔF^0'` plot is calculated to be
   > `(1/2)[1 + (ΔF^0'/4 ΔF_0*)]`. Thus far the experimental results are consistent with this equation,
   > but more data are needed."
   Since `ΔF_0* = λ/4`, this is again `α = 1/2 + ΔF°′/(2λ) = (λ - x)/(2λ)`. **This same paper is the
   experimental comparison asked for in Q7** (16 proton- and atom-transfer reaction series).
3. **Marcus 1969** (S11), abstract, `verified (abstract-level)`: the slope ↔ TS-position identification
   plus "some recent experimental findings of **unusual Brønsted coefficients**".
4. **Marcus 1992** (S8), printed p. 85, `verified`:
   > "Another consequence of Eq. (5) is the linear dependence of [ln] k on `-ΔG°` with a slope of 1/2,
   > when `ΔG°` is small … Extensive verification of both these results has been obtained."
   (the text layer prints "l/2" for "1/2" — OCR artefact, flagged).
5. **The exactness caveat**: S15 — the identification is exact only under the symmetric
   (equal-curvature) approximation; with asymmetry the two quantities "diverge systematically".

### 3.3 Notation traps to record in Lean docstrings

- `λ` vs **intrinsic barrier `λ/4`** (see §0.4): S9/S10/S16 use three different printings of the same
  identity; only the value `λ` is a premise in Lean, but any docstring quoting them must map `4ΔF_0*`
  and `E_r` correctly.
- **Sign**: never write `ΔG° > λ` for the inverted region (that is the *normal* region); three correct
  forms: `ΔG° < -λ`, `-ΔG° > λ`, or `|ΔG°| > λ` given `ΔG° ≤ 0` (sibling record; S8 p. 82).
- **`α` in other fields**: the electrode transfer coefficient and the tunneling `α` of
  `arXiv:2511.01909` are different objects; the project's `α` is the Leffler/Brønsted slope of a
  reaction series (`lefflerSecant`, a finite difference of barrier data).

### 3.4 Formalizable implication and impact of §3

- The formula `α = (λ - x)/(2λ)` is available **as a primary-source statement** (S9, S10) — the plan may
  cite these two for the *shape* of the formula, and must cite **neither** for `α < 0 ⟺` inverted
  region (§4).
- **No new Lean premise is needed for the formula itself**; the premises are the equal-curvature model
  and `0 < lam`.
- **Impact on plan §1.1 attribution (must change)**: the current text says "the two-parabola
  realization **and the α formula** are **Marcus 1956**, *J. Chem. Phys.* **24**, 966 ff." The
  two-parabola realization and the barrier formula are indeed 1956 (Eq. (38), p. 974 — and the sibling
  record already records that 1956 contains no inverted region), but **the α formula is not in 1956**
  (0 hits for `slope`, `alpha`, `Bronsted` in the local 1956 PDF). Correct anchors: S10 and S9 for
  `α`, S6 for the barrier. See §9 item 2.

---

## 4. Inverted region, the sign of α, and the boundary of Hammond's validity (Q4)

### 4.1 What the literature does state

**(i) The criterion (primary, `verified`).** S7, printed p. 28, item:

> "(v) Possibility of 'inverted' chemical behaviour. If `ΔF°` becomes too negative, intersection of the
> two surfaces becomes possible only at high potential energies, unless in such cases a more favourable
> reaction mechanism is found."

S8, printed p. 82 (`verified`):

> "[the barrier] first decrease[s] as [`ΔG°`] is varied from 0 to some negative value, vanish[es] at
> `ΔG° = -λ`, and then increase[s] when [`ΔG°`] is made still more negative. **This initial decrease …
> is the expected trend in chemical reactions and is similar to the usual trend in 'Bronsted plots' of
> acid or base catalyzed reactions and in 'Tafel plots' of electrochemical reactions.** I termed that
> region … the 'normal' region. However, the prediction for the region where [ΔG° < -λ], the 'inverted
> region', was the unexpected behavior …"

This is **the strongest primary locus available**: Marcus himself says the sign of
`d(barrier)/d(-ΔG°)` *flips* at `ΔG° = -λ` and that this sign *is* the Brønsted-plot / Tafel-plot
slope. He does **not** use the symbol `α`, does not write `α < 0`, and never names Leffler here.

**(ii) The α formula that makes the identification algebra (primary).** S9 and S10 (§3.2). Together
with (i): `α(x) = (λ - x)/(2λ)` is positive for `x < λ`, zero at `x = λ`, negative for `x > λ`. The
last step is **our one-line algebra**, not a quotation.

**(iii) The closest published statement that the inverted region *is* the negative-slope regime
(modern, OA, `verified`).** S14:

> "While the kinetic–thermodynamic plots of some reactions exhibit observed slopes outside of the range
> 0–1 (such as the nitroalkane anomaly **or the Marcus inverted region**), these observed local
> gradients do not contradict our model but instead arise from parallel system-dependent effects. In
> most known examples, the disruption of the monotonicity of the kinetic–thermodynamic response occurs
> because of the **weakening of Hammond's postulate** … which sometimes results in the inverted
> region. Experimental evidence supports this, as in most observed inverted regions, the **inverted
> Brønsted slopes** vary significantly in magnitude, deviating from the expected
> **same-magnitude-inverse-sign** predicted by the quadratic equation in Fig. 1b. In fact … a
> non-monotonic energy response **cannot be compatible with Hammond's postulate**. In ET and many other
> reactions, **asynchronicity** is common, which limits the validity of Hammond's postulate for the
> particular reaction, while in **intersystem crossings** there is no required smooth interpolation of
> the potential energy surface."

Two distinct services: it treats the inverted region as the regime of *negative* ("inverted") Brønsted
slopes, and it states that the quadratic (equal-curvature, i.e. our model) equation predicts the
reverse-branch slope to be the **same magnitude with opposite sign** — which is precisely the model's
mirror symmetry `tsCoord lam (-x) = 1 - tsCoord lam x` (plan H1 `tsCoord_neg`) specialized to
`α(-x) = -α(x)` around `x = 0`.

**(iv) Experiments do compare measured α with the model slope (primary).** S9 (16 series,
"consistent … but more data are needed"), S27 (measured Brønsted α for hydride transfer, analysed with
Marcus), S28 (proton transfer, Brønsted plots "of high curvature" fitted by Marcus).

### 4.2 What the literature does NOT state — clean negatives (required deliverables)

`verified` negatives, from this survey (searches run and their outcomes):

- **No source states "inverted region ⟺ Brønsted/Leffler slope `α < 0`" as an identity.** Europe PMC
  full-text REST searches: `("Brønsted slope" OR "Brønsted coefficient") AND "inverted region"` → 3
  hits, none with the identification; `"alpha becomes negative"` → 0 hits;
  `"transfer coefficient" AND "inverted region" AND "Marcus"` → 6 hits, all using the *electrode*
  transfer coefficient; `"Bronsted plot" AND "inverted region"` → 1 hit (unrelated). Control query
  `"slope becomes negative"` → 43 hits, so the index is not blind to the phrase.
- **Marcus 1956 and Marcus 1960 contain no slope/α/Brønsted language at all** (grep of the local
  PDFs: 1956 → `slope` 0, `alpha` 0, `bronsted` 0, `inverted` 0; 1960 → `slope`/`bronsted` 0). The
  inverted-region paper S7 must **not** be cited for anything about α.
- **Marcus 1992 never names `α`, Leffler or the Brønsted coefficient as such** (`Hammond` 0 hits,
  `Leffler` 0 hits; `Bronsted` 1 hit, the p. 82 analogy quoted above).
- **No source found** that states `α → 0` as the reaction becomes strongly exergonic *and* `α → 1` in
  the endergonic direction **as an experimental finding with page-level data**; only the algebraic
  limits of `(λ - x)/(2λ)` and the qualitative hydride statement of S27.
- **No established "photochemical Hammond postulate"** exists (S19 is literally titled as a question:
  "no systematic studies … available"; "no guiding principles like the HP in photochemistry").
  Europe PMC `"anti-Hammond"` → 48 hits, all ground-state; `"Hammond postulate" AND "conical
  intersection"` → 1 unrelated hit.
- **`not-accessed` (so unread, not refuted)**: S3 (Leffler 1953 full text), S5, S12, S13, S30 content,
  S31 content, S32 content, S33 content, and S10's body equations (34)/(35).

### 4.3 What the formalization may therefore claim

| claim | licenses | must be labelled as |
|---|---|---|
| `tsCoord lam x < 0 ↔ Marcus.InvertedRegion lam x` (H2) | the criterion `x > λ` (S7 p. 28; S8 p. 82) + the definition `q‡ = (λ - x)/(2λ)` (S6/S8 Eq. (5b)) | **pure algebra + model definition** |
| `lefflerSecant lam x₁ x₂ < 0 ↔ Marcus.InvertedRegion lam ((x₁+x₂)/2)` (H2) | S9/S10 (slope formula) + the same criterion | **a theorem of the equal-curvature model**; the empirical reading ("inverted region ⇒ negative measured Brønsted slope") is *supported* by S14 and S9 but is **not** an identity in the literature |
| "the structural-resemblance reading fails / leaves its domain for `x > λ`" | S8 p. 82 (trend reversal), S14 ("weakening of Hammond's postulate", "cannot be compatible with Hammond's postulate"), S4 ("many exceptions") | **model-internal verdict + documented literature analogy**; phrase it as plan §13 row 7 already does ("outside the domain where the structural reading applies"), never as "the molecule violates Hammond" |

### 4.4 The scope boundary (this is the part that most affects the plan)

- **S8, printed p. 90** (`verified`):
  > "Since the transfer of these nuclei involves strong electronic interactions, it is not well
  > represented by intersecting parabolic free energy curves, and so a different theoretical approach
  > was needed. … The resulting simple expression for [`ΔG‡`] is similar to Eq. (5), when [`ΔG°`] is not
  > large (`< 1/2`), but **differs from it in not having any inverted region**."
  (said of atom, proton and methyl-group transfer).
- **S10, Appendix II, pp. 897–898** (`verified (delegated read)`): for a bond-breaking atom transfer the
  profile "rises to a maximum, like an Eckart barrier" so that "one can no longer … obtain the
  'inverted chemical effect' … and so the added equation (6) is imposed"; the effect "could again
  occur" only "when most of the reorganization is associated with coordinates not involved in bond
  rupture or formation". Same Appendix: the parabola is "a profile of the potential energy along a
  reaction coordinate in **many dimensional configuration space**", and the TS is a distribution of
  activated-complex configurations centred at the intersection.
- **S15**: with unequal curvature the α = TS-position identity "diverge[s] systematically"; the
  deviation depends on `ΔG` and the `λ` ratio.
- **S16**: the parabolic model makes the postulate quantitative, but "the TS configuration always
  differs from that of both reactants and products for any `ΔH` values" — i.e. no strict adherence.
- **S18**: computationally, "no … general verification of the HLP"; path regions are often not centred
  at the TS.

### 4.5 Formalizable implication and impact of §4

- **Explicit Lean premises**: `0 < lam`, `x > lam` (for the inverted branch), `x₁ ≠ x₂` for the secant
  form. Nothing about α needs a new premise; the identification is a theorem.
- **Physical approximations to declare** (in `RESULTS.md` wording and instance doc comments): (i) the
  parabola model applies to ET-type reactions; (ii) the inverted-region verdict is *inside* the model;
  (iii) equal curvature is what makes `α = q‡` exact; (iv) empirically, observed inverted-region
  slopes vary in magnitude rather than mirroring the normal branch (S14) — so the model's *symmetry*
  is the sharpest falsifiable prediction of this layer and should be documented as such.
- **Impact on plan**: add to §13 (anchors) the negative result of §4.2 explicitly — i.e. that the
  `α < 0 ⟺` inverted-region identification is a **model theorem**, with S8 p. 82 + S9/S10 as the
  statement-level support and S14 as the modern published analogue; and add the scope restriction of
  §4.4 to the instance layer (no H-transfer/proton-transfer instance may be given a `beyondReactant`
  verdict as a physical claim).

---

## 5. Exceptions, criticism, and limits (Q5)

### 5.1 Postulate-level

| item | source / locus | status | relevance |
|---|---|---|---|
| the authoritative definition calls it a **Hypothesis**; `α` is an "**approximate** measure of the fractional displacement of the TS along the MERP" and there are "**many exceptions**" | S4, entries "Hammond postulate (Hammond-Leffler principle)" and "Leffler's relation / Leffler's assumption" | `verified` | the single best citation for "heuristic, not theorem"; directly supports plan §13's wording rule |
| the Leffler form of the postulate (energy form, `δP‡ = α δP_P + (1-α) δP_R`) is attributed to Hammond by textbooks | S4, Note 1 | `verified` | the plan's attribution sentence should say "Hammond 1955 (structure form) / Leffler 1953 (energy form, prior)" |
| "**anti-Hammond effect**: If a structure lying off the minimum-energy reaction path (MERP) is stabilized, the position of the transition state moves toward that structure" | S4, entry "anti-Hammond effect" | `verified` | the model has **one** coordinate and cannot represent this branch: record it as structurally inexpressible |
| Thornton's rules: "stabilization of a structure located off the assumed MERP in a direction perpendicular to it shifts the transition state toward that more stabilized geometry (a perpendicular effect)"; the observed TS shift is the resultant of a **parallel (Hammond)** and a **perpendicular (anti-Hammond)** component | S4, entry "More O'Ferrall–Jencks diagram", Note 2 (attributed there to Thornton) | `verified` (substance via S4); S32 itself `not-accessed` | the plan's three resemblance predicates cover only the parallel branch; this must be declared, and Thornton 1967 cited only for priority |
| the postulate is qualitative; the intersecting-parabolas model is what makes it quantitative; the TS never coincides with either well | S16, §IV pp. 1123–1124 | `verified` | supports calling H2 "the quantitative Hammond postulate *inside the model*" |
| author's own retrospective: the rules "contain conceptual weaknesses, perhaps the most egregious of which is the **tacit assumption that there is a basic similarity among the potential functions for stretching and contracting all bonds**"; and a warning against abusing TS theory ("I wish that some of the citations had been omitted …") | S2, printed p. 16 | `verified` | **the equal-curvature/equal-force-constant assumption of our model is exactly what Hammond himself flagged as the weak point** — this is the strongest available justification for plan §13 row 2 and §1.3 |
| the intrinsic barrier can dominate over `ΔG°,` so rates may not track thermodynamic stability | S4, entry "Marcus equation" | `verified` | supports the fixed-`λ` premise (below) |
| "between different intrinsic reactivities, the Hammond postulate is no longer relevant" | S24 | `verified` | fixed-intrinsic-barrier premise |
| computational test: no general verification of the HLP; path regions often not centred at the TS; curvature-based quantification over ~150 reactions (19 `XHn + H2` at CCSD(T)/cc-pV5Z) | S18 | `verified` | shows the postulate is *tested*, not assumed, in the computational literature |
| organic exceptions are catalogued under "exceptions/paradoxes" | S24 | `verified` | pointer for RESULTS.md's honesty section |
| Pross 1995, pp. 177–182 (the source IUPAC attaches to the "many exceptions" note) | S4's ref. [287] | `not-accessed` | cite via S4 only |

### 5.2 Two-parabola-level (equal curvature, single coordinate, harmonicity)

| item | source / locus | status | relevance |
|---|---|---|---|
| `α` = TS position is **exact only in the symmetric (equal-curvature) approximation**; deviates systematically with asymmetry; "the Brønsted coefficient is not a general descriptor of transition-state structure" | S15, abstract | `verified (delegated read)` | forces the equal-curvature assumption to be named in plan §13 |
| Marcus theory "assuming both reactants and products distort identically and quadratically" implies a thermoneutral local slope fixed at 0.5, "which often does not hold"; "the gradient at `E_eq` is always equal to 0.5" | S14 | `verified` | same, from an OA source; also documents that our `q‡(x=0) = 1/2` is a model artefact |
| the two-parabola plot is a projection of a many-dimensional surface; the inverted effect is removed for bond-breaking transfers | S10, Appendix II, pp. 897–898 | `verified (delegated read)` | scope boundary + "single coordinate" caveat |
| force-constant-dependent thermoneutral TS position for asymmetric centres; linear `ΔH` range bounded; nonlinear in Morse-curve models | S17, abstract | `verified (delegated read)` | documents what replaces `tsCoord_zero = 1/2` |
| realistic variation of bond strengths/distances gives a sigmoid Brønsted slope deviating from Marcus | S25 | `verified (delegated read)` / biblio `verified` | the curvature-criticism anchor |
| Brønsted-slope deviations in general base catalysis (differential charge development, asymmetry) | S26 | `verified (delegated read)` / biblio `verified` | ditto |
| the correlation `α`–structure requires **`λ` constant across the series** | S23, S24, S10 | `verified` | new explicit premise (§8.2) |
| recrossing / transmission coefficient / non-statistical dynamics / explicit TST failure | S30 | content `not-accessed` (pointers) | the dynamics limitation (§7 rank 5) |

### 5.3 Photochemistry (the "no photochemical Hammond postulate" result)

- S19 (`verified`, OA): "So far, no systematic studies on the validity of the Hammond postulate for
  photochemical reactions are available"; after discussing Born–Oppenheimer breakdown: "there are
  currently no guiding principles like the HP in photochemistry to help predict the location and
  geometry of transition states"; the paper's conclusion *hopes* the HLP "can be extended to the
  excited state" and defers conical intersections to future work.
- S20 (`verified (delegated read)`): the bottleneck is "a full 'line' of transient structures … the
  intersection space (IS)" — a seam, not a point.
- S21, S22 (`verified (delegated read)`): preference inversion between thermal and photochemical
  pathways is attributed to a switch from **transition-state control to conical-intersection control**,
  and selectivity correlates with surface **topography**, not with energy differences.
- Consequence: photochemical cases are **not** "Hammond violations"; they are outside the model's
  domain of definition, and the plan must say so (today `RESULTS.md`/plan §1.3 do not mention
  photochemistry at all — the project name notwithstanding).

### 5.4 Formalizable implication of §5

- **No new Lean premises** (exceptions are not premises of a theorem; they bound the *reading* of it).
- **Approximations to declare** (extend plan §13's table): equal curvature; fixed `λ` across the
  compared series; single scalar coordinate as a projection; static crossing-point TS; no
  perpendicular (anti-Hammond) branch; no photochemistry/conical intersections.
- **Impact**: (i) plan §13's anchor list should add S4 (normative wording + exceptions), S15
  (equal-curvature exactness) and S2 (Hammond's own caveat); (ii) plan §13's assumption table should
  gain the fixed-`λ` row and the "projection onto one coordinate" row; (iii) `RESULTS.md` should state
  that no photochemical Hammond postulate exists (S19) as a scope statement, and that ground-state
  inverted-region instances are "outside the Hammond regime of the model", not "anti-Hammond".

---

## 6. Instance parameters (Q6)

Values are in eV; `x = -ΔG°`; `q‡ = α(x) = (λ - x)/(2λ)` (**our arithmetic** in the model, not a
literature value); zone names are the plan's `HZone` constructors. All values are decimal rationals,
so every row is expressible in the ℚ decision layer (H5a) exactly.

### 6.1 Table

| # | System | `λ`/eV | `x`/eV | `q‡ = α` | `HZone` | model verdict (structural) | source / locus | status |
|---|---|---|---|---|---|---|---|---|
| P1 | MCC series, acceptor = 2-naphthyl (k ≈ 1.5×10⁶ s⁻¹) | **1.20** | **0.05** | `23/48 ≈ 0.479` | `early` | conforms; reactant-like TS; `α ∈ (0,1)` | λ from Nobel Fig. 8 annotation; x from C&EN 1984-06-04 (secondary) as recorded in `theories/Marcus/LITERATURE.md` | λ: `verified` (Fig. 8 PNG read here); x: `verified (sibling record)` |
| P2 | MCC series, acceptor = 2-hexahydronaphthoquinonyl (barrierless point) | 1.20 | **1.23** | `-1/80 = -0.0125` | `beyondReactant` | **does not conform**: `x > λ` strictly; `q‡ < 0`, `α < 0` | same as P1 (C&EN 1984, secondary; "optimal/no-barrier point") | `verified (sibling record)` |
| P3 | MCC series, acceptor = 2-(5,6-dichlorobenzoquinonyl) (k ≈ 7×10⁷ s⁻¹) | 1.20 | **2.40** | `-1/2` | `beyondReactant` | **does not conform**; inverted region | same as P1 (+ Nobel Fig. 8 right-hand points) | `verified (sibling record)` |
| P4 | MCC series, left branch of Fig. 8 (read-off) | 1.20 | **0.60** | `1/4` | `early` | conforms; `α = 0.25` | Nobel 1992 **Fig. 8 axis** (printed p. 84) | `verified (sibling record)` (figure read-off) |
| P5 | MCC series, right branch of Fig. 8 (read-off) | 1.20 | **2.00** | `-1/3` | `beyondReactant` | **does not conform** | Nobel 1992 Fig. 8 axis | `verified (sibling record)` (figure read-off) |
| P6 | photosynthetic reaction centre, first step BChl₂* → BPh | ~**0.25** | ~**0.25** | `0` | `atReactant` | **boundary**: `x = λ`; `α = 0 ∉ (0,1)`; strict regime fails | Nobel 1992 **printed p. 88**: first transfer "only about 0.25 eV out of an overall excitation energy of BChl₂* of 1.38 eV"; "small λ (~0.25 eV)" | `verified` (local PDF text layer) |
| P7 | photosynthetic reaction centre, back transfer BPh⁻ → BChl₂⁺ (hole–electron recombination) | ~0.25 | ~**1.10** | `-17/10 = -1.7` | `beyondReactant` | **does not conform**; deeply inverted (`x ≫ λ`); `α < -1` | Nobel 1992 **printed p. 88**: "a very highly exothermic process (~1.1 eV)"; "small λ (~0.25 eV) … inverted region effect" | `verified` (local PDF text layer) |
| P8 | enzymatic proton transfer (silverman) — **no `x`** | `λ ≈ 4 × (1–2 kcal/mol) ≈ 0.17–0.35` (**our arithmetic** from "intrinsic barrier … 1 to 2 kcal/mol") | not reported | — | — | **not usable as a verdict** (no driving force) | S28, abstract | `verified (abstract-level)` for the intrinsic barrier; λ conversion is our arithmetic with a flag |
| P9 | rhenium hydride hydride-transfer series | not reported (abstract) | not reported | — | — | **not usable as a verdict**; documents that measured `α` values exist and decrease with driving force | S27, abstract | `verified (abstract-level)` |
| P10 | nitroalkane anomaly (classic `α` outside `(0,1)`) | not verified | not verified | — | — | **not usable**: mirrors the `x < -λ` branch, but no verified pair | S31 | biblio `verified`; content `not-accessed` |

### 6.2 Provenance notes (binding for the instance layer)

1. `λ = 1.20 eV` is the sum of the two numbers **printed inside Nobel 1992 Fig. 8**:
   `λ_s = 0.75 eV`, `λ_v = 0.45 eV`, `ω = 1500 cm⁻¹`. The rendered figure is on disk
   (`theories/Marcus/literature/Marcus1992_nobel_p84_fig8.png`) and was **read as an image** in this
   survey: the annotation, the axis `-ΔG° (eV)` with ticks 0.0/1.0/2.0 and the "Lower Limit" arrow are
   legible. This is the strongest provenance available in-project for the MCC pairs.
2. The MCC `x` values (0.05, 1.23, 2.40 eV) come from the **secondary** source C&EN 1984-06-04 (as
   recorded in the sibling record). The primary series is S29 (ACS, paywalled). A human with library
   access can re-check the same numbers in `Closs et al., J. Phys. Chem. 90, 3673–3683 (1986)`,
   `10.1021/j100407a039` (the full paper of the MCC series, containing the λ/solvent tables) — the
   sibling record already flags this as the double-check route.
3. The reaction-centre pair is a **modelling pair quoted inside a Nobel lecture**, not a fitted
   experimental value: both numbers appear in the same paragraph as `~`, and the lecture presents
   `λ ≈ 0.25 eV` as "small". Status `verified` as *quoted numbers*, `order-of-magnitude` as
   *measurements*.
4. **Reading rule** (already plan §13 row 7): a `beyondReactant` verdict means "the instance lies
   outside the Hammond regime **of the two-parabola model**". It does **not** mean that the molecule
   violates Hammond's postulate. For P3/P5/P7 the physical systems are the textbook inverted-region
   cases; the model's coordinate simply leaves the well interval.
5. **Scope restriction from §4.4**: P1–P7 are all **electron-transfer** parameter sets, which is
   exactly the regime where the two-parabola model is licensed. No proton-transfer/H-abstraction row
   may be given a `beyondReactant` verdict.
6. `T` and the prefactor `A` do **not** enter any structural verdict (as in the sibling record):
   only `(λ, x)` do. Keep `0 < kB*T`, `0 < A` as explicit premises where rates are mentioned at all —
   in this theory they are not.

### 6.3 Bottom line for the plan's instance table (plan §8.2)

- Usable rows with verified provenance: **P1, P2, P3, P4, P5, P6, P7** (rational literals:
  `6/5`, `1/20`, `123/100`, `12/5`, `3/5`, `2`, `1/4`, `11/10`).
- Verdicts: `early`/conforms for P1, P4; `atReactant` boundary for P6; `beyondReactant`/does-not-conform
  for P2, P3, P5, P7.
- The plan's I5 (`6/5, 1/20`), I6 (`6/5, 12/5`) and I7 (`1/4, 11/10`) reproduce **P1, P3, P7**
  exactly; plan I9's pair (`6/5`, `3/5 → 12/5`) reproduces the monotonicity instantiated at
  **P4 → P3**.
- **Arithmetic check of plan §8.2 as written**: for I6 (`lam = 6/5`, `x = 12/5`) the model gives
  `q‡ = α = (6/5 - 12/5)/(12/5) = -1/2`; the plan's row states `q‡ = -1/2` (correct) but also
  "`α = -1/8 < 0`" (**inconsistent with its own `lefflerSecant_eq_midpoint`**, which forces
  `α = q‡` at the secant midpoint). Either the `1/8` is a typo for `1/2` or a different `x`-pair was
  intended. This is a plan-level correction (§9 item 5); it does not change any verdict, since the
  zone (`beyondReactant`) and the sign (`α < 0`) are unaffected.

---

## 7. Non-formalizable list, ranked (Q8)

Ranked by **actual impact on the planned statements (a)–(e)** × the reuse value of the mathematics that
would be needed. Items are "not expressible, or unreasonably expensive, in the installed
Lean 4.17.0 + mathlib". **Claims (a)–(e) depend on none of them** — that is the point of the list.

| rank | item | impact on the planned claims | what would be needed |
|---|---|---|---|
| **1** | **"Molecular structure" itself** (bond lengths, angles, which bond breaks, charge distribution) — the literal content of Hammond's "small reorganization of the molecular structures" | **high for the *reading*, zero for the theorems**: the formalized `q‡` is a coordinate, not a structure. The gap must be bridged by an explicit modeling assumption (plan §13 row 1) | a chemistry/geometry layer (molecular graphs, internal coordinates, force fields); mathlib has no such thing and building it is a separate project |
| **2** | **Many-dimensional PES, MERP, perpendicular/anti-Hammond (Thornton) effects** | **high**: the model's three resemblance predicates cover only the parallel branch, so "resemblance" in the model is *a priori* blind to the anti-Hammond/Thornton channel (S4, S10) | multivariable Morse/saddle theory, path geometry, normal-mode decomposition; mathlib lacks an applied Morse-theory layer |
| **3** | **Equal curvature / equal force constants** | **decisive**: this is the premise that makes claims (b), (c) exact (S15, S14, S17). It is a *model assumption*, not a theorem; the plan must say so | unequal-curvature generalization is a next station (plan §14 ①); needs `Real.sqrt`/implicit-function work in mathlib (available but out of scope here) |
| **4** | **Entropy / free energy vs potential energy** (Hammond's own footnote: translational and solvation entropies "essentially uncontrolled") | **medium**: our `ΔG°` is a free-energy-like scalar; the postulate is stated for potential energy. The identification is an assumption | statistical mechanics / partition functions; mathlib has none |
| **5** | **Dynamics: recrossing, variational TS, transmission coefficient, non-statistical dynamics** | **low for (a)–(e)**, but it bounds the *interpretation* of "the TS is the crossing point" (S24/S30 pointers) | reactive-flux theory, Hamiltonian dynamics, trajectory ensembles; far beyond mathlib |
| **6** | **Quantum nuclear effects (tunneling), heavy-atom tunneling** | **low**: the structural claims are T-independent; tunneling affects rates only | path integrals / instanton calculus; not available |
| **7** | **Conical intersections, seam dimensions, excited-state surfaces, surface hopping** | **low for the present claims, but essential for the project's photochemical framing**: no "photochemical Hammond postulate" exists (S19), and the photochemical bottleneck is a seam (S20) | multivalued PES / vector-bundle-style geometry, nonadiabatic dynamics; entirely out of mathlib's scope |
| **8** | **Rate constants, prefactors, TST, and the barrier→rate map** | **zero** (this theory proves structural statements only; rate theorems live in `PhotoLean.Marcus.Rate`) | transition-state theory + partition functions; deliberately out of scope (plan §1.3) |
| **9** | **Work terms `w_r, w_p` and activity/dielectric corrections** | **low**: absorbed into `ΔG°` (S10's own eq. (2) shows what is dropped) | electrostatics/PDE layer; mathlib lacks it (sibling record item 2) |
| **10** | **Physical units and dimensional checking (eV/K/J, kcal/mol)** | **zero, but needs discipline**: `lam` and `x` are bare `ℝ`; a units error cannot be caught by the kernel | a unit system; mathlib has none (document units in every instance row, and keep the kcal→eV conversions flagged as ours) |
| **11** | **Experimental uncertainty** | **zero for the verdicts, medium for the "honest" reading**: `λ` and `ΔG°` are measured with error bars; verdicts are computed from point values | probability/error propagation; document as a modelling limitation |

---

## 8. Impact on `theories/hammond/plan.md` (statements (a)–(e))

### 8.1 Per planned claim

**(a) `HammondDescriptor` / `tsCoord_antitone` — "strictly decreasing in `x` iff `λ > 0`.**
- **Explicit premises**: `0 < lam` (must remain in every signature), and `a < b` for the two driving
  forces. The `iff` form additionally requires the two witnesses for `λ ≤ 0`
  (`tsCoord_zero_lam` + `tsCoord_increasing_of_neg`) — algebraic, no premise beyond `¬ 0 < lam`.
- **What the literature gives**: no source states this monotonicity as a theorem; it *is* the
  quantitative Hammond content of the model (S4 Note 3: "simply a consequence of adding a linear
  perturbation to the parabola"; S16 §IV). So (a) may be presented as "the model's Hammond
  descriptor", never as an empirical law.
- **Modeling assumptions (documented only)**: single scalar coordinate; equal curvature; `λ` fixed
  across the series compared; no perpendicular channel.
- **Impact**: none on the statement; the wording of §1.1 should cite S4/S16 for "the model realizes the
  postulate", and the fixed-`λ` premise should be added to §13.

**(b) `gap_compare_iff` — energy–structure correspondence.**
- **Explicit premises**: `0 < lam`.
- **Substance**: `gapProduct - gapReactant = x` (H1) gives
  `gapReactant < gapProduct ↔ 0 < x`. Because in the same model the reactant well is the *less stable*
  one exactly when `x > 0`, the two literature readings — "closer in energy to the TS" and "resembles
  the less stable species" (S4) — are **equivalent in this model**. Recording this equivalence is a
  genuine formalization contribution; outside equal curvature they need not agree (S15, S17).
- **Assumption to declare**: the identification "q‡ < 1/2 ⟺ *structurally* closer to the reactant"
  (i.e. that the scalar distance along `q` measures resemblance).
- **Impact**: plan §2.3 already treats the descriptor as a `Prop`; §13 should name the chosen reading of
  "closer" and note the equivalence result. No statement change.

**(c) `lefflerSecant_eq_midpoint` / `lefflerSecant_mem_iff` — α = TS coordinate, `α ∈ (0,1)` iff
`-λ < x < λ`.**
- **Explicit premises**: `0 < lam`, `x₁ ≠ x₂` (secant), and the **fixed-`λ`** condition for reading the
  secant as an "experimental α of a reaction series" (S23, S24, S10).
- **Literature check**: the "α measures the fractional displacement of the TS along the MERP" reading
  is normative (S4) but explicitly **approximate** with "**many exceptions**"; the equality is exact
  only in the equal-curvature model (S15). The plan's "exact" wording is therefore correct *only*
  qualified by "in this model" — plan §2.3 item 3 already says this; keep it and add the citation.
- **Impact**: statement unchanged; **documentation must add** the equal-curvature and fixed-`λ`
  premises, and RESULTS.md must not slide from "exact in the equal-curvature model" to "Hammond
  proved".

**(d) inverted region: `tsCoord lam x < 0 ↔ Marcus.InvertedRegion lam x`, `α < 0` iff inverted.**
- **Explicit premises**: `0 < lam`; `x > lam` (or the midpoint form for the secant).
- **Literature check** (§4): the criterion is primary (S7 p. 28; S8 p. 82); the α formula is primary
  (S9; S10); the *identification* is **not** stated verbatim anywhere (clean negative) and the modern
  published analogue is S14 ("inverted Brønsted slopes", "weakening of Hammond's postulate").
  Therefore the two H2 lemmas may be **proved**, but they must be labelled as **model theorems**
  (pure algebra on the model's definitions), not as literature results.
- **Additional boundary premise**: the inverted-region verdict is licensed only for ET-type parameter
  sets; for bond-breaking atom/proton/methyl transfers Marcus removes the inverted effect (S8 p. 90;
  S10 Appendix II). This does not change the Lean statements — it changes what the project may *say*
  about them, and it forbids H-transfer instances in H5.
- **Impact**: documentation-only for the statements; **but** plan §13's anchor list should record the
  negative result, and §8.2's instance set must stay ET-only (it does).

**(e) instance verdicts.**
- **Explicit premises**: `0 < lam` (each instance's λ must be positive to be a model instance at all);
  rational literals.
- **Provenance**: §6.1 — P1–P7 usable, with the status split (λ = 1.20 eV verified from the Fig. 8
  annotation read as an image; MCC `x` values secondary; RC pair quoted in the Nobel lecture at `~`).
- **Impact**: (i) `λ = 1.20` must be documented as `λ_s + λ_v` from Fig. 8, not as a fitted value;
  (ii) the RC `(0.25, 1.10)` pair is a *quoted modelling* pair — keep the `~` in the doc comment;
  (iii) fix the I6 α typo (§6.3, §9 item 5); (iv) no H-transfer/proton-transfer instance.

### 8.2 Premise register to add to plan §13 (documentation, no signature changes)

1. `λ` (equivalently the intrinsic barrier) is **fixed** across the family compared by
   `HammondDescriptor` / read off by `lefflerSecant` — S23, S24, S10.
2. **Equal curvature** (identical force constants for both parabolas) is what makes claims (b) and (c)
   exact — S15, S14, S17, S2 (Hammond's own "tacit assumption").
3. `q` is a **projection** onto one reaction coordinate of a many-dimensional configuration-space
   surface, and the TS is a distribution centred at the intersection — S10 Appendix II/III.
4. The structural claims are **domain-restricted to ET-type reactions**; for bond-breaking
   atom/proton/methyl transfers the inverted effect is removed in Marcus's own treatment — S8 p. 90,
   S10 Appendix II.
5. **No photochemical Hammond postulate** exists; photochemical selectivity is controlled by conical
   intersections/topography — S19, S20, S21, S22.
6. The postulate is a **Hypothesis**, and its α-form has "many exceptions" — S4 (wording rule backed by
   the authority of the IUPAC glossary).
7. Hammond's own footnote: the postulate concerns **potential** energy and leaves translational/
   solvation entropy uncontrolled — S1 (p. 334, footnote 1); our `ΔG°` is free-energy-like.

### 8.3 Wording rules that follow

- Never write "this molecule obeys/violates Hammond's postulate" (plan §13 already forbids it); the
  literature supports the prohibition (S4 "many exceptions"; S14 "weakening").
- Never write `α < 0 ⟺ inverted region` as a *literature* statement; write "in the model, the inverted
  region is exactly where the Leffler coefficient is negative (H2), the model-level analogue of the
  negative ('inverted') Brønsted slopes reported for inverted regions (S14)".
- Do not cite Marcus 1956 or 1960 for α (zero occurrences); cite S9/S10 for α, and S8 p. 82 / S14 for
  the inverted-region slope picture.
- Do not attribute the sentence "the TS resembles the species to which it is closest in energy" to
  Hammond 1955 (§2.2).

---

## 9. Corrections and conflicts (relative to `plan.md` and to the brief)

1. **"closest in energy" is not Hammond 1955's wording** (§2.2). Plan §1.1 quotes it as the postulate.
   Fix: quote the p. 334 sentence, or label the paraphrase as such and cite S4 for the canonical
   "less stable species" form.
2. **The α formula is not Marcus 1956.** Plan §1.1 attributes "the two-parabola realization **and the
   α formula**" to Marcus 1956. The two-parabola realization and the barrier formula are 1956
   (Eq. (38), p. 974); the α formula belongs to **S9** (`10.1021/j100858a052`) and **S10**
   (`10.1021/j100849a019`), with S11 as the slope↔TS-position paper. The local 1956 PDF contains no
   `slope`, `alpha`, `Bronsted` or `inverted` string.
3. **DOI correction: Marcus & Sutin 1985** is `10.1016/0304-4173(85)90014-X` (BBA *Reviews on
   Bioenergetics* 811, 265–322). The DOI `10.1016/0005-2728(85)90039-9` returns **404 at Crossref and
   at doi.org** — verified twice. If plan §13 or RESULTS cites that DOI, it should be replaced.
4. **Marcus 1968 DOI (from my own dispatch brief, recorded for traceability)**:
   `10.1021/j100849a035` is a *different* paper (Bundschuh & Li, *J. Phys. Chem.* 72(3), 1001–1005);
   the correct DOI is **`10.1021/j100849a019`** (Crossref-verified).
5. **Plan §8.2, instance I6 arithmetic**: the row gives `q‡ = -1/2` (correct) and `α = -1/8 < 0`
   (inconsistent — `lefflerSecant_eq_midpoint` forces `α = q‡ = -1/2` at the midpoint of the pair
   used). Verdict and zone are unaffected (`beyondReactant`, `α < 0`); the number should be corrected
   to `-1/2` or the intended `x`-pair stated. This is our arithmetic on the plan's own definitions,
   not a literature claim.
6. **The `α < 0 ⟺` inverted-region identification is not in the literature** (§4.2). The plan's H2
   statements `tsCoord_lt_zero_iff_inverted` and `lefflerSecant_neg_iff_inverted` are therefore
   **model theorems**; §13/RESULTS must say so, with S8 p. 82, S9, S10 (statement level) and S14
   (modern published analogue) as the only support.
7. **Scope restriction that touches the instance layer**: the inverted-region verdict must not be
   applied to bond-breaking atom/proton/methyl transfer as a physical claim (S8 p. 90; S10 Appendix
   II). Plan §1.3/§13 do not currently say this.
8. **`not-accessed` items that must not be cited as authority until read**: S3 (Leffler 1953 — the
   plan's attribution of the α idea to Leffler 1953 is bibliographically correct and is corroborated by
   S4/S19, but its own text was not retrieved); S5, S12, S13, S30 (content), S31 (content), S32
   (content), S33 (content), and the printed eqs (34)/(35) of S10.
9. **Resolved open item of plan §14 ④ (`Empirical Brønsted α comparison`)**: a source **does** exist —
   S9 (Cohen & Marcus 1968: the model slope applied to Brønsted-slope data of 16 proton- and
   atom-transfer series, "consistent … but more data are needed"), with S27 and S28 as modern
   experimental series. The plan's fallback ("otherwise record as non-formalizable") need not be used;
   the comparison belongs in this record (§4.1 (iv)) and stays outside the kernel.

---

## 10. Search ledger (so the lead can re-run or extend)

- **Crossref REST** (`api.crossref.org/works/<DOI>`) — every DOI in §1 re-checked; the two DOI
  failures are recorded in §9 items 3–4.
- **CaltechAUTHORS** (`authors.library.caltech.edu/api/records…`) — the abstract-level loci for S9, S10,
  S11 (publisher abstracts reproduced there; the records carry no files).
- **Europe PMC REST** — OA full texts of S14 (`PMC12406046`), S24 (`PMC11574852`), S19 (`PMC8178980`),
  S23 (`PMC4317057`), plus the negative full-text searches of §4.2.
- **Local PDFs** (`theories/Marcus/literature/`) — S6, S7, S8, and the Fig. 8 rendered PNG, read by
  `pdftotext` greps and one image read; nothing was downloaded into the workspace for this record.
- **Primary scans** — S1 (Hammond 1955 full text via a scanned copy found by search) and S2 (Garfield
  Citation Classic PDF) were read as text; no copies were stored in the repo.
- **Blocked hosts (unread, not refuted)**: `pubs.acs.org` 403 (S3 abstract is available, but the 1955,
  1968, 1969, 1973, 2009 bodies are not; S9/S10/S11 abstracts came from CaltechAUTHORS instead),
  `science.org` 403 (S3), `goldbook.iupac.org` 403 (the Gold Book entry could not be read — S4's 2021
  PAC manuscript, same organization and open, was used instead), `cdnsciencepub.com` 403 (S31),
  `archive.org`/`osti.gov` timeouts, Elsevier/RSC paywalls (S12, S13, S33).
