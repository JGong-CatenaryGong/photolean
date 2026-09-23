# theories/Forster/LITERATURE.md — literature record: Förster resonance energy transfer, the κ² orientation factor, and the 2/3 convention

> Discipline (engine contract §5): every entry names a **checkable locus** (DOI / arXiv id /
> printed page) and a **reading status**; every entry carries the only column that matters for
> formalization — *what the source licenses as an explicit premise, a declared approximation,
> or a scope limit*. Statuses: `verified (first-hand read here)` /
> `verified (metadata+abstract, Crossref-deposited)` / `bibliographic-only`.
>
> This round had one critical job from the lead: **verify that the azimuthal parametrization**
> `κ² = (sinθ_D·sinθ_A·cosφ − 2·cosθ_D·cosθ_A)²` **is the standard spherical-geometry form** of
> the dipole–dipole orientation factor, i.e. that `cosθ_T = cosθ_D·cosθ_A + sinθ_D·sinθ_A·cosφ`
> with `θ_T` the angle between the dipoles. **Verified** (F5 below, equations read in context):
> the plan's FO-B1 is the standard form, since `cosθ_T − 3cosθ_D cosθ_A` rewrites as
> `sinθ_D sinθ_A cosφ − 2cosθ_D cosθ_A` by exactly that identity.

**STATEMENT-IMPACT (see the note at the end of this file) FLAGS (read first):** none against the frozen statement inventory
(`theories/Forster/plan.md` §4) — every statement checked against the verified sources is
consistent. One **prose-level** observation on plan §1.1 (not a statement): the clause
"overestimates `R₀⁶` by at most a factor `6` (at `κ² = 4`)" has the direction backwards in
words — at `κ² = 4` the *true* `R₀⁶` is `6×` the convention's, i.e. the convention
*under*estimates by at most `6×`; the unbounded *over*estimate occurs only toward the blind
spot `κ² → 0`. The frozen statement FO-C7 (`ratio ∈ Icc 0 6`) is direction-neutral and
correct; see the statement-impact summary.

## F1 — Förster's original paper (1948)

| field | content |
|---|---|
| source | Th. Förster, "Zwischenmolekulare Energiewanderung und Fluoreszenz", *Annalen der Physik* **437**(1–2), 55–75 (1948); received 1947-05-05; DOI `10.1002/andp.19484370105` |
| verification | Crossref metadata record read at `api.crossref.org/works/10.1002/andp.19484370105` (title, volume, pages, date, author all match; 7227 citations recorded). Deposited abstract (German) confirms: quantum-mechanical treatment of electronic-excitation transfer between like molecules in solution; the critical molecular distance is computable from the absorption/fluorescence spectra and the excitation lifetime; values 50 Å (fluorescein) and 80 Å (chlorophyll a). |
| claim as used | The transfer rate between a donor–acceptor pair follows the sixth-power distance law with a critical (Förster) radius set by the spectral overlap, the donor emission properties, and the refractive index — the content of FO-B2/FO-B3/FO-B5. |
| **formalizable implication** | The 1948 paper fixes the *statement shape* (`R₀` from spectra + lifetime), not Lean premises: it licenses `r0six C κ² Φ J n = C·κ²·Φ·J / n⁴` with a collected positive constant `C` — the paper's own prefactor (involving `ln 10`, Avogadro's number, `π`) is **not** unfolded in this theory (plan §1.2). Explicit premises required by the statements: `0 < C`, `0 < Φ`, `0 < J`, `0 < n`, `0 < tauD`, `0 < R`. The spectral-overlap integral `J` is a positive parameter (no overlap theory — plan §1.3 non-goal). |
| status | `verified (metadata+abstract, Crossref-deposited)` — full German text not read here; the English translation "Intermolecular energy migration and fluorescence" exists in Mielczarek, Greenbaum & Knox (eds.), *Biological Physics* (AIP, 1993) — cited in van der Meer 2002's Crossref-deposited reference list (page given there as 183); translation not opened here (`bibliographic-only`). Companion paper Förster 1949, *Z. Naturforsch.* **4a**, 321–327, DOI `10.1515/zna-1949-0501` — appears in Dale & Eisinger 1974's deposited reference list; `bibliographic-only`. |

## F2 — Dale & Eisinger 1974 (orientation factors, the seed source)

| field | content |
|---|---|
| source | R. E. Dale & J. Eisinger, "Intramolecular distances determined by energy transfer. Dependence on orientational freedom of donor and acceptor", *Biopolymers* **13**(8), 1573–1605 (1974); DOI `10.1002/bip.1974.360130807` |
| verification | Crossref record read (`api.crossref.org/works/10.1002/bip.1974.360130807`): title, authors, volume 13, issue 8, pages 1573–1605, August 1974 — all match. **Seed correction**: the often-guessed DOI `10.1002/bip.1974.360130802` belongs to a *different* paper in the same issue (Stevens, polyadenylic acid, pp. 1517–1533); the correct suffix is `...0807`. The deposited abstract was read: Förster transfer efficiency depends on the orientational freedom of D and A attached to a macromolecule; polarized emission measurements bound the D–A separation via maximum and minimum values of the orientation factor. |
| claim as used | The orientation factor is the dominant uncertainty in distance determination from transfer efficiency; the `κ² = 2/3` average is a *regime assumption* (dynamic averaging), not a constant of nature — the batch's κ² dependency analysis (FO-C7) is exactly this observation formalized. |
| **formalizable implication** | Licenses the *headline pair* FO-C7 as a statement about the ratio `r0six C κ² Φ J n / r0six C (2/3) Φ J n = κ²/(2/3) ∈ [0,6]`: the misestimate factor of a tabulated `R₀⁶` is bounded below by `0` and above by `6` — a pure consequence of `0 ≤ κ² ≤ 4` (FO-C1/FO-C2) plus positivity premises. The paper's own content (bounds from polarization data) is out of scope: no anisotropy theory is formalized. |
| status | `verified (metadata+abstract, Crossref-deposited)` — full text paywalled, not read |

## F3 — Dale, Eisinger & Blumberg 1979 (the κ² distribution classic)

| field | content |
|---|---|
| source | R. E. Dale, J. Eisinger & W. E. Blumberg, "The orientational freedom of molecular probes. The orientation factor in intramolecular energy transfer", *Biophysical Journal* **26**(2), 161–193 (1979); DOI `10.1016/S0006-3495(79)85243-1` |
| verification | Crossref record read (title, authors, volume 26, pages 161–193, 1979; 582 citations). Also deposited as reference BIB1 of van der Meer 2002 (F4) and CR10 of Cherny et al. 2009 (F6) — two independent citing records. |
| claim as used | The canonical analysis of the probability distribution of `κ²` under restricted orientational motion; the reference point for "how wrong can `2/3` be" — the static-averaging regime can push the effective `κ²` below `2/3` (cf. F5: values down to `0`). |
| **formalizable implication** | Supports the *distribution-free* formalization choice: this theory proves worst-case statements (`Icc 0 6`, the blind spot) instead of any distributional claim. A distributional statement (the `κ²` density under dynamic isotropy) is **not expressible** over installed mathlib scope — it needs probability measures on `SO(3)`/spheres; registered non-goal (plan §1.3). |
| status | `verified (metadata, Crossref-deposited)` — full text not read here |

## F4 — van der Meer 2002 (the "κ² problem" review, the seed source)

| field | content |
|---|---|
| source | B. W. van der Meer, "Kappa-squared: from nuisance to new sense", *Reviews in Molecular Biotechnology* **82**(3), 181–196 (2002); DOI `10.1016/S1389-0352(01)00037-X`; PubMed PMID 11999689 |
| verification | Crossref record read (title, author, volume 82, issue 3, pages 181–196, January 2002). **Seed correction**: the venue is *Reviews in Molecular Biotechnology* (ISSN 1389-0352), not *J. Biotechnology* as sometimes mis-transcribed (a *J. Biotechnol.* 82 issue exists with different content). Its deposited references independently corroborate F1 (Förster 1948), F3 (Dale et al. 1979), and the van der Meer–Coker–Chen book *Resonance Energy Transfer: Theory and Data* (VCH, 1994). |
| claim as used | The review devoted to the κ² uncertainty: `κ² ∈ [0, 4]`, `2/3` valid only under the dynamic isotropic averaging regime, and the orientation factor carries structural information when measured rather than assumed. |
| **formalizable implication** | Licenses the modelling posture of the whole theory: `κ²` is a *geometric parameter with a proved range* (FO-C1/FO-C2/FO-C3), the `2/3` value is a **declared convention** (FO-B6, never a theorem about physics), and the convention's failure mode is *witnessed* (FO-C8, the blind spot) rather than estimated. Nothing in the review demands new Lean premises beyond the positivity premises already in FO-C7/C8. |
| status | `verified (metadata, Crossref-deposited)` — abstract read via PubMed search record; full text not read here |

## F5 — the azimuthal parametrization, the range, and the 2/3 average (the critical verification; read in context)

| field | content |
|---|---|
| source | S. Bhuckory, PhD thesis (Université Paris-Saclay / HAL open archive), HAL id `tel-01548910`, deposited PDF `71236_BHUCKORY_2016_diffusion.pdf` (2016), §2 FRET review, **printed pp. 41–43** |
| locus | Read first-hand from the HAL PDF (`pdftotext`, equations 2.5–2.9 and surrounding prose). Verbatim: "**κ² = (cosθ_DA − 3cosθ_D cosθ_A)²** (2.7)" with "**cosθ_DA = sinθ_D sinθ_A cosφ + cosθ_D cosθ_A** (2.8)", where θ_D, θ_A are the angles of the donor/acceptor transition dipoles to the connecting vector **r** and φ is "the azimuth between the planes (M_D, r) and (M_A, r)". Prose: "Kappa square, κ², can range from 0 to 4 ... A value of 0 corresponds to perpendicular transition moments, collinear transition moments results when κ² = 4 and κ² = 1 for transition moments that are parallel." And: "We assume an average κ² = 2/3 when the orientations ... randomize within the lifetime of the excited state (dynamic averaging regime) ... the dynamic isotropic average of κ² = 2/3." The R₀ formula (eq. 2.5): `R₀⁶ = 9(ln10)·κ²·Φ_D·J(λ)/(128·π⁵·N_A·n⁴)`. Also: assuming `2/3`, "since the sixth root is taken to calculate R₀, an error not exceeding 35% results". |
| claim as used | **This is the source the lead asked for**: the spherical-geometry identity decomposing the dipole–dipole angle (`cosθ_T = cosθ_D cosθ_A + sinθ_D sinθ_A cosφ`) and hence the azimuthal parametrization `κ² = (sinθ_D sinθ_A cosφ − 2cosθ_D cosθ_A)²` *is* the standard form — substituting (2.8) into (2.7) gives exactly the plan's FO-B1. (Honest grading: a PhD thesis *reproducing* the standard textbook statement — the canonical printed loci are Lakowicz and van der Meer–Coker–Chen, F8; the thesis is the accessible checkable locus, read in context.) |
| **formalizable implication** | (i) **FO-B1 is confirmed standard**; the three angles are independent parameters (plan §1.2) because θ_T *depends on* all three through the identity. (ii) The range witnesses match FO-C3: θ_D = θ_A = 0 (both dipoles along the separation) gives `(0 − 2)² = 4` ("collinear"); θ_D = π/2, θ_A = 0 gives `0` (a perpendicular configuration) — the plan's registered witnesses are consistent with the literature's extreme geometries. (iii) **The 2/3 question the lead posed**: the literature's value is the *continuous* dynamic-isotropic average `⟨κ²⟩ = 2/3` (this row; also F2/F4). The plan's FO-R2 instead computes the *exact average over the orthonormal frame* (nine axis-aligned dipole pairs, separation along an axis): values `4` (both dipoles along the separation axis), `1+1` (both along each of the two perpendicular axes), `0` (six mismatched pairs), sum `6`, average `6/9 = 2/3`. **The frame average agrees with the literature's continuous average exactly** — as it should, since κ² is a *quadratic* form in the direction cosines, and the axis frame reproduces the isotropic second moments (`⟨x_i²⟩ = 1/3`, `⟨x_i x_j⟩ = 0`) exactly. The Lean theory registers this as: the continuous average is a registered non-goal (needs measure theory on the rotation group — **not expressible** over installed mathlib scope); the frame average is a finite ℚ computation (`decide`), and its agreement with `2/3` is the consistency certificate, not a proof of the continuous claim. (iv) The "error not exceeding 35%" remark corroborates FO-C7's factor `6`: `6^{1/6} ≈ 1.348`, i.e. ≲ 35% error in `R₀` itself — the plan's `R⁶`-space factorization `∈ [0,6]` is the sixth power of that bound. |
| status | `verified (first-hand read here)` — full chapter read from the deposited PDF |

## F6 — the dot-product form in a working derivation (peer-reviewed, SI read first-hand)

| field | content |
|---|---|
| locus | SI §3 read first-hand: the orientation factor is computed from the dipole unit vectors **f**_D, **f**_A and the separation direction **r** via the dot-product identity `κ = (f_A·f_D) − 3(f_A·r̂)(f_D·r̂)` (typeset in the SI as `(fAfD) 3(fAr)(fDr)`), with the polar decompositions of the two dipoles around **r** — the same spherical geometry as F5's (2.8), used for a concrete Cy3/Cy5-on-DNA geometry. |
| claim as used | Peer-reviewed working evidence that the three-angle (polar + azimuthal) parametrization of the point-dipole coupling is the practitioners' standard form, not an idiosyncrasy of one textbook. |
| **formalizable implication** | Confirms the *geometric reading* behind FO-C2's proof route: `κ` is `(unit dipoles) · (I − 3 r̂ r̂ᵀ) · (unit dipole)`, so the bound `κ² ≤ 4` is a statement about unit vectors — the plan's elementary route (triangle inequality + ℝ² Cauchy–Schwarz, no rotations, no eigenvalues) is mathematically sufficient because only unit-vector algebra is involved. The **point-dipole approximation itself is a declared physical approximation, never a Lean premise to be discharged** (cf. F7). |
| status | `verified (first-hand read of SI)` — main text not needed for this row |

## F7 — the point-dipole approximation and the rate/efficiency shapes (review, read first-hand)

| field | content |
|---|---|
| source | S. Saini, G. Srinivas & B. Bagchi, "Distance and Orientation Dependence of Excitation Energy Transfer: From Molecular Systems to Metal Nanoparticles", *J. Phys. Chem. B* **113**(7), 1817–1832 (2009); DOI `10.1021/jp806536w` |
| locus | Feature Article, read first-hand via a full-text copy. §2: "Förster theory assumes the transition charge densities of donor and acceptor molecules are point dipoles and hence predicts a 1/R⁶ dependence"; the coupling `V_DA = κ·|μ_D||μ_A|/R³` (eq. 2.3); the rate `k_DA = k_rad·(R_F/R)⁶` (eq. 2.6) with `R_F` the separation at which the transfer rate equals the donor radiative rate; "κ² is the orientational factor which in EET experiments is generally assumed to be 2/3"; the efficiency as lifetimes `E_T = 1 − τ_DA/τ_D`; and the warning: "use of a preaveraged value of orientation factor in deducing the separation distance via Förster expression can lead to a wrong interpretation" (with the Eaton group's polyproline measurement: pre-averaging *overestimates* the rate when orientational motion is slower than transfer). §5–6: documented breakdown of the point-dipole approximation at separations comparable to molecular size. |
| claim as used | Confirms the *shape* of FO-B2/FO-B3/FO-C5/FO-C10 against a peer-reviewed source, and supplies the literature's own verdict that the two load-bearing approximations (point dipole, pre-averaged κ²) are exactly where the model fails — the two items the plan declares and never proves. |
| **formalizable implication** | (i) FO-C10's lifetime reading `E = 1 − τ_DA/τ_D` matches the literature form (here via rates: `1 − (1/(kD+kF))/(1/kD) = (kF/kD)/(kF/kD + 1)`), premises `0 < kD`, `0 ≤ kF`. (ii) FO-C5 (`fretEff R0 R0 = 1/2`) matches "the separation at which transfer rate equals radiative decay rate". (iii) **Declared, never proved**: the point-dipole approximation (the review documents its breakdown regime — extended dyes, nanoparticles, short distances) and the `2/3` pre-averaging convention (the review documents its overestimate regime). Neither is expressible as a Lean premise beyond "the model is declared", which is what plan §1.2/§9 do. |
| status | `verified (first-hand read here)` — full text read |

## F8 — not first-hand this round (registered, not hidden)

| source | status | note |
|---|---|---|
| van der Meer, Coker & Chen, *Resonance Energy Transfer: Theory and Data*, VCH 1994 | `bibliographic-only` | The standard data-book statement of the azimuthal κ² form; cited in F4's deposited reference list. Not accessed. |
| Förster 1949, *Z. Naturforsch.* **4a**, 321 | `bibliographic-only` | Companion experimental-theoretical paper; DOI `10.1515/zna-1949-0501` (De Gruyter page exists); not read. |
| IUPAC Gold Book entry "Förster-resonance-energy transfer" (FT07381) | `not accessed` | `goldbook.iupac.org` returned HTTP 403 to this environment — same measurement as the hammond round's attempt (AGENTS.md-registered behavior). Not used as a locus. |

## Statement-impact summary

**No statement in the frozen inventory (`plan.md` §4) contradicts any verified source.** Row by row:

* FO-B1 (azimuthal κ²): **confirmed standard** by F5 (eqs. 2.7–2.8 read in context) + F6. No change.
* FO-B2/FO-B3/FO-B5 (rate, efficiency, R₀⁶ proportionality): confirmed shapes by F1/F5/F7. No change.
* FO-C1/FO-C2 (0 ≤ κ² ≤ 4): confirmed range by F4/F5. No change.
* FO-C3 witnesses (κ² = 0 at θ_D = π/2, θ_A = 0; κ² = 4 at θ_D = θ_A = 0): confirmed against F5's extreme geometries. No change.
* FO-C7 (misestimate ratio ∈ [0,6]) and FO-C8 (blind spot): confirmed as the formalized content of the "κ² problem" (F2/F4/F7). No change.
* FO-R2 (frame average = 2/3): the literature's continuous dynamic-isotropic average is `2/3` (F5); the frame average **agrees exactly** (`6/9`), for the structural reason recorded in F5 (κ² quadratic in direction cosines). The continuous average stays a registered non-goal (no measure theory). No change.
* **Prose-level observation (no statement impact)**: plan §1.1's clause "overestimates `R₀⁶` by at most a factor `6` (at `κ² = 4`)" reads with the direction backwards in words — at `κ² = 4` the convention *under*estimates the true `R₀⁶` by the factor `6`; the unbounded *over*estimate is the blind-spot direction (`κ² → 0`). FO-C7's frozen statement (ratio `true/convention ∈ Icc 0 6`) is direction-neutral and correct; a one-line prose fix in §1.1 is recommended at the lead's next plan edit, but the statement authority is untouched.

---

**Correction (lead, 2026-09-23; verifier run 3 finding F6).** The statement-impact flag above
claiming that plan §1.1's over/under-estimate direction is "backwards in words" is a FALSE POSITIVE:
the frozen plan text is correct — the unbounded overestimate in ratio is at the blind spot
(`κ² → 0`), and at `κ² = 4` the convention *underestimates* the true `R₀⁶` by at most a factor 6
(which is what the plan says). No plan change was needed; the earlier wording amendment recorded in
the plan's §3.1 entry 4 predates this flag and remains as documentation of the sentence fix.
