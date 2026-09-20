# Literature Survey Record

> *English translation of `proofs/LITERATURE.md`. The Chinese original at `proofs/LITERATURE.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

> Maintained by `literature_researcher`. **Every entry must have a "formalizable implication" section** —
> that section is the only useful product of a literature survey for the formalization; an entry lacking
> it is considered invalid.

## Record format

```markdown
## YYYY-MM-DD — <short title> — literature_researcher
- Source: <DOI / arXiv id / title> (PDF stored in proofs/literature/)
- Conclusion: <the literature's core claim about the theory>
- Formalizable implication:
  - Can be made explicit as a Lean premise: <list>
  - Is a physical approximation (must be declared explicitly): <list>
  - Currently not expressible in mathlib: <list, with the obstacle explained>
- Impact: <whether the statements in plan.md need revision>
```

## Anti-patterns (forbidden)

- Quoting long passages of the original text or a whole abstract without giving the "formalizable
  implication";
- Substituting a literature conclusion for a proof ("the literature says it is monotone, so there is no
  need to prove it") — the literature is used only to **fix statements and premises**;
- Pouring the entire content of a PDF into the context. Record only conclusions and page/section
  locations.

## Verification-status vocabulary (project convention)

- `verified`: personally read this time in the sources obtained (Crossref / printed page / PDF body text).
- `from memory, pending human review`: written from prior knowledge, **not** read in the sources obtained
  this time.
- `order of magnitude only`: only an order of magnitude is given; no precise value is claimed.

---

<!-- records are appended below -->

## 2026-09-20 — Marcus 1956: the original form of the barrier formula and of the pre-exponential factor (the original theory) — literature_researcher

- Source: Marcus, R. A., "On the Theory of Oxidation-Reduction Reactions Involving Electron
  Transfer. I", *J. Chem. Phys.* **24**(5), 966–978 (1956). DOI `10.1063/1.1742723`
  [verified: Crossref (volume/issue/pages/year/authors all correct) + CaltechAUTHORS record page].
  Local PDF: `proofs/literature/Marcus1956_ET_theory_I.pdf` (1.4 MB).
- Conclusion:
  - From the "slight-overlap" assumption + the electrostatic free energy of non-equilibrium solvent
    polarization + variational minimization, one obtains the free energy `ΔF*` of the intermediate
    state X*: **this paper's Eq. (38), p. 974** (printed page).
  - Throughout, the rate is written as **collision number × exponential**: `k₁ = Z·exp(−ΔF*/kT)`
    (Eq. (44)) and `k_bimol ≈ Z·exp(−ΔF*/kT)` (Eq. (47)), p. 975–976, where `Z` is the collision number
    in solution.
    ⇒ **the 1956 original has no pre-exponential factor of the form `(4πλk_BT)^{-1/2}`**; that form comes
    from later transition-state-theory treatments (see record 7).
  - **The word "inverted" appears nowhere in the paper** (0 hits when searching the full text of this
    PDF) ⇒ the inverted-region prediction is **not** in the 1956 paper; it was first proposed in the
    1960 Faraday Discussion (see record 2).
  - Eq. (38) already contains the two-sphere outer reorganization energy structure:
    `(Δe)²·(1/(2a₁) + 1/(2a₂) − 1/R)·(1/D_op − 1/D_s)`, where `D_op` is the optical dielectric
    constant and `D_s` the static dielectric constant (see record 3).
- Formalizable implication:
  - Can be made explicit as Lean premises:
    - `0 < A` (in 1956, A = Z, the collision number, physically positive);
    - `0 < k_B*T`; two-sphere parameters `0 < a₁`, `0 < a₂`, `a₁ + a₂ ≤ R`;
    - `Δe ≠ 0`; `0 < D_op`, `D_op < D_s`.
  - Is a physical approximation (must be declared explicitly):
    - **slight overlap / non-adiabatic electron coupling**: the electron hopping probability is small, and
      the rate is controlled by nuclear-configuration fluctuations reaching the intersection of the
      surfaces;
    - **dielectric continuum approximation for the medium** (including non-equilibrium polarization);
    - **Franck–Condon constraint**: electron transfer takes place at the intersection of the two
      free-energy surfaces;
    - the pre-exponential factor is independent of the driving force (in 1956, A = Z).
  - Currently not expressible in mathlib:
    - the electrostatics derivation **preceding** Eq. (38) (construction of the non-equilibrium
      polarization free energy and its variational minimization).
      mathlib has no continuum electrostatics / PDE library ⇒ the Pekar formula can only be introduced as
      a **definition**, and **cannot** be derived in Lean.
- Impact: **recommend revising the attribution of references in plan.md**. If plan writes "the
  pre-exponential factor is taken to be `(4πλk_BT)^{-1/2}`", it **must not** cite Marcus 1956; that form
  should be attributed to Marcus 1964 or Marcus & Sutin 1985.
  However, this **does not change any x-monotonicity conclusion** (see the last item of record 7).

## 2026-09-20 — The original source and the exact sign convention of the inverted-region criterion (**guarding against a sign flip**) — literature_researcher

- Source:
  - Marcus, R. A., "Exchange reactions and electron transfer reactions including isotopic
    exchange. Theory of oxidation-reduction reactions involving electron transfer. Part 4.
    A statistical-mechanical basis for treating contributions from solvent, ligands, and
    inert salt", *Discuss. Faraday Soc.* **29**, 21–31 (1960). DOI `10.1039/df9602900021`
    [verified: Crossref]. ← **the paper in which the inverted region was first proposed**.
  - Marcus, R. A., "Chemical and Electrochemical Electron-Transfer Theory",
    *Annu. Rev. Phys. Chem.* **15**(1), 155–196 (1964). DOI `10.1146/annurev.pc.15.100164.001103`
    [verified: Crossref].
  - Marcus, R. A., Nobel Lecture 1992, "Electron Transfer Reactions in Chemistry: Theory and
    Experiment", *Chemistry 1992* (Nobel Foundation), printed pages 71–89.
    Local PDF: `proofs/literature/Marcus1992_nobel_lecture.pdf`;
    key-page renderings: `Marcus1992_nobel_p78_eq5.png` (p. 78, Eq. 5a/5b/6),
    `Marcus1992_nobel_p79_eq7.png` (p. 79, Eq. 7/8), `Marcus1992_nobel_p84_fig8.png` and
    `Marcus1992_nobel_p84_fig8_axis.png` (p. 84, Fig. 8).
    [verified: page-by-page reading of the images; the formulas are exactly as printed]
- Conclusion:

  **(exact wording as printed)**
  - **Nobel Lecture p. 78, Eq. (5b)**:
    ```
    ΔG* = (λ/4)·(1 + ΔG°′/λ)²
    ```
    where ΔG°′ is the standard free energy of the reaction (0 for a self-exchange reaction). This is
    **identical** to `(λ + ΔG°)²/(4λ)` — i.e. the classical textbook form.
  - **p. 78, Eq. (5a)**: `k = A·exp(−ΔG*/k_B T)`, where A depends on the reaction type
    (bimolecular / intramolecular).
  - **p. 78, Eq. (6)**: **`λ = λ_o + λ_i`** (solvational + vibrational).
    ⇒ **Marcus's own notation is λ_o / λ_i, i.e. the modern λ_out / λ_in** (synonymous).
  - **Exact wording of the inverted-region criterion (p. 82, section "The Inverted Region Effect")**:
    the activation free energy "first decrease as [ΔG°] is varied from 0 to some negative value,
    **vanish at ΔG° = −λ**, and then increase when [ΔG°] is made still more negative".
    ⇒ inverted region = **`ΔG° < −λ`** ⟺ **`−ΔG° > λ`**.
  - **The horizontal-axis label of p. 84, Fig. 8 is precisely `−ΔG° (eV)`**, with ticks `0.0` / `1.0` /
    `2.0` [verified: reading the figure].
- Formalizable implication:
  - Can be made explicit as Lean premises: **none**. `InvertedRegion` is a **definition**, not a
    premise: taking `x := −ΔG°`, we have `InvertedRegion λ x := λ < x`,
    `barrier λ x := (λ − x)^2 / (4*λ)`.
  - Is a physical approximation (must be declared explicitly): treating ΔG° as a **single scalar driving
    force** (absorbing the solvent electrochemical potential and all work terms into ΔG°, see record 7).
  - Currently not expressible in mathlib: **nothing**. This item is 100% expressible in mathlib.
- Impact:

  **Conclusion — plan's convention is correct and needs no revision; but one anti-pattern note must be
  added:**
  - ✅ plan's `x = −ΔG°`, `ΔG‡ = (λ−x)²/(4λ)`, inverted region `x > λ`
    **are fully consistent with the original literature**.
  - ⚠️ **Never write `ΔG° > λ`**. ΔG° is **negative** for exergonic reactions, and `ΔG° > λ > 0` actually
    falls in the **normal region** — the sign is exactly reversed. Three correct ways to write it:
    `ΔG° < −λ` / `−ΔG° > λ` / (only after `ΔG° ≤ 0` has been explicitly declared) `|ΔG°| > λ`.
  - ⚠️ Recommend writing a one-line chain of equivalences as a comment at the `InvertedRegion` definition
    in plan, so that later provers and reviewers do not misread it.

## 2026-09-20 — The original text of the **first proposal** of the inverted region (Marcus 1960 Faraday Discussion): verbatim quotation and page number — literature_researcher

- Source: Marcus, R. A., "Exchange reactions and electron transfer reactions including isotopic
  exchange. Theory of oxidation-reduction reactions involving electron transfer. Part 4.
  A statistical-mechanical basis for treating contributions from solvent, ligands, and
  inert salt", *Discuss. Faraday Soc.* **29**, 21–31 (1960). DOI `10.1039/df9602900021`
  [verified: Crossref].
  **Open-access full text**: CaltechAUTHORS `authors.library.caltech.edu/records/h2ztx-ee849`
  (file `df9602900021.pdf`). Local PDF: `proofs/literature/Marcus1960_Faraday_inverted_region.pdf`
  [verified: downloaded and its text layer extracted in this survey].
- Conclusion:
  - The **first proposal** of the inverted region is item **(v)** of the "list of predictions still to
    be tested" in section 4.4 of this paper, printed page **28**, with item title
    **"Possibility of 'inverted' chemical behaviour"**.
    Verbatim original text (**the only original sentence quoted in this report — two sentences in
    total**):
    > "If ΔF° becomes too negative, intersection of the two surfaces becomes possible only
    > at high potential energies … m² eventually increases with increasing −ΔF°, and the
    > rate constant decreases."
  - Key points: ① the criterion is phrased as **"ΔF° becomes too negative"** (`ΔF°` ≡ `ΔG°`, which is
    **negative** for exergonic reactions); ② the mechanism is that the barrier term `m²` grows as `−ΔF°`
    increases ⇒ the rate constant **decreases**.
    ⇒ **consistent** with the sign conclusion of record 2: inverted region = `ΔG° < −λ` ⟺ `−ΔG° > λ`.
  - Item **(ii)** of the same section is **the earliest form of the cross relation**:
    `k₁₂ ≈ (k₁k₂K)^½`, and the original **carries its own applicability condition**:
    "if ΔF° is not too large". ⚠️ plan §1.3 does not treat the cross relation; if it is ever done, then
    besides "same λ" it must also carry this restriction that `ΔF° must not be too large` (otherwise an
    overly strong claim would be made).
  - Item **(vi)** of the same section describes itself as "Analysis of assumptions made when electron
    transfers are interpreted in the terms of the Franck-Condon principle" (cf. ref. 8)
    — **the original itself acknowledges that the Franck–Condon interpretation is an assumption**, which
    directly supports items 1–3 of the approximation list in plan §13.
  - Item **(iv)** of the same section describes itself as "inert salt effects (subject to an assumed
    treatment of the ionic atmosphere as a continuous distribution)" — this is **the origin of the work
    terms**, and the original explicitly states that it is an **assumption** (see record 7).
- Formalizable implication:
  - Can be made explicit as Lean premises: **none** (the inverted region is a definition). But this paper
    makes explicit a **contextual premise** beyond the definition:
    "unless … a more favourable reaction mechanism is found" ⇒
    **this theorem does not apply to systems in which a competing reaction channel exists** (the original
    itself writes this disclaimer).
  - Is a physical approximation (must be declared explicitly): the three that the original acknowledges —
    ① the Franck–Condon interpretation is an assumption (item (vi)); ② the ionic atmosphere is treated as
    a continuous distribution (item (iv), i.e. the modelling basis of the work terms); ③ the reaction
    follows a single mechanism with no more favourable competing channel (item (v)).
  - Currently not expressible in mathlib: none.
- Impact:

  **Recommend adding one citation and one boundary declaration to plan.md:**
  - Recommend that plan §1.1 or §13 attribute the **first proposal of the inverted region** to
    **Marcus 1960, Discuss. Faraday Soc. 29, p. 28, §(v)** (**not** to 1956 — the word "inverted" appears
    nowhere in the 1956 paper, see record 1).
  - Recommend adding to plan §1.3 "explicitly out of scope" a boundary declaration (**grounded in the
    original text, not our invention**):
    > This formalization characterizes only the classical Marcus rate under a **single mechanism**; it
    > does not include competing reaction channels
    > (Marcus 1960 item (v) itself says: "unless … a more favourable reaction mechanism is found").

## 2026-09-20 — The Pekar factor and the two-sphere model of the outer reorganization energy λ_out (**λ>0 can be derived from geometry**) — literature_researcher

- Source:
  - Marcus 1956, **Eq. (38), p. 974** (same DOI as above) [verified: PDF body text]:
    `ΔF* = e₁*e₂*/(R·D_s) + m²·(Δe)²·(1/(2a₁) + 1/(2a₂) − 1/R)·(1/D_op − 1/D_s)`.
  - Marcus Nobel Lecture 1992, **Eq. (7), p. 79** (same as above) [verified: reading the image]:
    ```
    λ_o = (Δe)²·( 1/(2a₁) + 1/(2a₂) − 1/R )·( 1/D_op − 1/D_s )
    ```
    The original explains: `a₁, a₂` are the two ionic radii (including the inner coordination shell),
    `R` is the centre-to-centre distance of the reacting species, `D_op` the optical / `D_s` the static
    dielectric constant, and `Δe` the amount of charge transferred from one reactant to the other.
  - Marcus Nobel Lecture 1992, **Eq. (8), p. 79**: `λ_i = ½·Σ_j k_j·(Q'_j − Q''_j)²`,
    where `k_j := 2k'_j k''_j/(k'_j + k''_j)` is the **reduced force constant**. The original states that
    it introduces the **"symmetrization" approximation** (replacing the individual force constants of
    reactant and product by the reduced force constant) [verified: body text].
  - Marcus, R. A.; Sutin, N., "Electron transfers in chemistry and biology",
    *Biochim. Biophys. Acta (Reviews on Bioenergetics)* **811**(3), 265–322 (1985).
    DOI `10.1016/0304-4173(85)90014-X` [verified: Crossref + CaltechAUTHORS record page].
    (The full body text was not obtained this time, Elsevier paywall; equation numbers pending human
    review.)
  - The name "Pekar factor" and the form `1/ε_opt − 1/ε_st` are used in several papers
    [verified: for example ChemElectroChem 2021 uses `C = 1/ε_opt − 1/ε_st` and calls it the Pekar
    factor].
- Conclusion:
  - Write `G := 1/(2a₁) + 1/(2a₂) − 1/R` (**geometric factor**) and
    `P := 1/D_op − 1/D_s = 1/n² − 1/ε_s` (**Pekar factor**, `n` the refractive index, `ε_s` the static
    dielectric constant). Then `λ_out = (Δe)²·G·P`.
  - **Necessary and sufficient condition for `λ_out > 0`**: `Δe ≠ 0 ∧ P > 0 ∧ G > 0`.
    - `P > 0 ⟺ D_op < D_s ⟺ n² < ε_s`. This holds physically in all cases (the optical dielectric
      constant is always smaller than the static one, because only the electronic polarization responds
      at optical frequencies).
    - **`G > 0` can be derived from geometry; it need not be assumed**: if `0 < a₁`, `0 < a₂`,
      `a₁ + a₂ ≤ R` (the two spheres do not intersect = physically, they touch or are farther apart),
      then
      `1/R ≤ 1/(a₁+a₂)`, and
      `1/(2a₁) + 1/(2a₂) − 1/(a₁+a₂) = (a₁² + a₂²)/(2·a₁·a₂·(a₁+a₂)) > 0`.
      ⇒ `G ≥ G|_{R=a₁+a₂} > 0`.
- Formalizable implication:
  - Can be made explicit as Lean premises:
    `0 < a₁`, `0 < a₂`, `a₁ + a₂ ≤ R`, `Δe ≠ 0`, `0 < D_op`, `D_op < D_s`.
  - Can be made explicit as a **Lean theorem (the most important product of this record)**:
    ```lean
    lemma geometric_factor_pos {a₁ a₂ R : ℝ}
        (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hR : a₁ + a₂ ≤ R) :
        0 < 1/(2*a₁) + 1/(2*a₂) - 1/R
    ```
    Tactic hints: `one_div_le_one_div_of_le` gives `1/R ≤ 1/(a₁+a₂)`; move to
    `(a₁²+a₂²)/(2*a₁*a₂*(a₁+a₂)) > 0`, and after `field_simp` use `positivity` / `nlinarith`.
  - Can be made explicit as a **Lean theorem (inner part)**:
    `λ_in := (1/2) * ∑ j ∈ s, k j * (Q' j - Q'' j)^2`;
    `Finset.sum_nonneg` + `sq_nonneg` gives `0 ≤ λ_in`; strict positivity requires
    `∃ j ∈ s, 0 < k j ∧ Q' j ≠ Q'' j`.
  - Is a physical approximation (must be declared explicitly):
    - **two-sphere model + dielectric continuum approximation** (spherical cavity, bulk dielectric
      constant);
    - **the radii are unchanged by the reaction** (1956 p. 974 original: "radii … taken to be essentially
      unchanged by the reaction");
    - **the transferred charge is a single scalar Δe** (localized single-electron transfer);
    - **additivity `λ = λ_in + λ_out`**: Marcus himself writes `λ = λ_o + λ_i` (Nobel Eq. (6)), but
      additivity is a **modelling assumption** (decoupling of inner and outer coordinates + additive
      quadratic form), **not a theorem**.
      🎯 **the original source and the exact form of additivity have been verified**: **Marcus 1960,
      Discuss. Faraday Soc. 29, §3.3, p. 24–25** (local PDF
      `Marcus1960_Faraday_inverted_region.pdf`) **explicitly decomposes** the total set of coordinates
      `k` into `k_i` (coordinates internal to the coordination shell, "inner") and `k''` (all remaining
      coordinates, "outer"), and likewise separates the potential energy: `g_{k_i}` depends only on the
      internal coordinates, `g_o` only on `k''`.
      The corresponding partition function **factorizes** accordingly (the internal coordinates give a
      vibrational partition function `Q_vib`, the outer coordinates give `exp(−F_o(r)/kT)`).
      ⇒ **the real origin of additivity is "the potential energy is separable + each block is taken in
      the quadratic (harmonic) approximation"**; on the Lean side it should be written as an
      **explicitly declared approximation** (e.g. take `lam = lamIn + lamOut` as a definition and declare
      that "this is a consequence of the inner/outer coordinate-separability assumption"), and it
      **must not** be claimed to be derived from more basic principles.
    - **the "symmetrization" approximation** (reduced force constant) — stated by Marcus himself on
      Nobel Lecture p. 79.
  - Currently not expressible in mathlib:
    - **deriving** the Pekar formula from dielectric-continuum electrostatics (non-equilibrium
      polarization free-energy functional + variational principle) — one can only treat `λ_out` as a
      **definition**;
    - deriving the relation between `D_op` and the refractive index from a dispersion relation — not in
      mathlib.
      ⚠️ **but this step needs no derivation**: Marcus 1956 **p. 971** explicitly defines
      "optical dielectric constant `D_op` (i.e., **the square of the refractive index**)"
      [verified: PDF text layer]⇒ `D_op = n²` is a **given definition of the model**, and plan's
      `lamOuter` taking `nSq` directly as a parameter is **faithful**, not a simplification.
- Impact:

  **Recommend revising plan.md:**
  - **Recommend upgrading/downgrading `0 < λ` from an "assumption" to a "derivable conclusion"**:
    at the instance layer set `λ := λ_in + λ_out`; then `0 < λ` is **derived** from `0 ≤ λ_in` (a sum of
    squares) and `0 < λ_out` (from `Δe ≠ 0`, `D_op < D_s`, and the lemma `geometric_factor_pos`).
  - The abstract main theorems (M2/M3) **should still keep `0 < λ` as an explicit premise** (otherwise
    the abstract layer loses generality); plan should state that "the instance layer proves this premise
    from the concrete expressions for `λ_in, λ_out`".
  - **Recommend a separate lemma task for `geometric_factor_pos`**: it is the only geometric lemma in
    this plan that **genuinely needs inequalities**, and it **depends on no physical approximation**, so
    it has the lowest risk and can be started earliest.

## 2026-09-20 — Experimental evidence for the inverted region I: the (λ, −ΔG°) values of the Miller–Calcaterra–Closs 1984 series — literature_researcher

- Source:
  - Miller, J. R.; Calcaterra, L. T.; Closs, G. L., "Intramolecular long-distance electron
    transfer in radical anions. The effects of free energy and solvent on the reaction
    rates", *J. Am. Chem. Soc.* **106**(10), **3047–3049** (1984).
    DOI **`10.1021/ja00322a058`** [verified: Crossref].
  - Closs, G. L.; Calcaterra, L. T.; Green, N. J.; Penfield, K. W.; Miller, J. R.,
    "Distance, stereoelectronic effects, and the Marcus inverted region in intramolecular
    electron transfer in organic radical anions", *J. Phys. Chem.* **90**, 3673–3683 (1986).
    DOI `10.1021/j100407a039` [verified: Crossref]. (= the full-length version of the communication
    above)
  - Closs, G. L.; Miller, J. R., "Intramolecular Long-Distance Electron Transfer in Organic
    Molecules", *Science* **240**, 440–447 (1988). DOI `10.1126/science.240.4851.440`
    [verified: Crossref].
  - Marcus Nobel Lecture 1992, **p. 84, Fig. 8** (title "Experimental Confirmation of
    Inverted Region"; the caption names Miller et al.) [verified: reading the image].
  - Independent redrawing of the same figure (same parameters): Lokan, N. R., *Synthetic approaches
    towards novel bichromophoric systems for studying solvent-mediated electron transfer and electronic
    excitation energy transfer*, PhD thesis, UNSW Sydney (2000), Chapter 1, pp. 9–11,
    Fig. 1.6 / 1.7 / 1.8. DOI `10.26190/unsworks/7583` (`hdl.handle.net/1959.4/62022`)
    [verified: DataCite + PDF text layer].
  - Miller, J. R.; Peeples, J. A.; Schmitt, M. J.; Closs, G. L., "Long-distance
    fluorescence quenching by electron transfer in rigid solutions",
    *J. Am. Chem. Soc.* **104**(24), 6488–6493 (1982). DOI `10.1021/ja00388a002`
    [verified: Crossref]. (the MTHF glass series, **a different experiment from MCC 1984**)
  - **Secondary source for the per-compound values**: *Chem. Eng. News* **1984-06-04**, **62**(23),
    42–44, DOI `10.1021/cen-v062n023.p042` [verified: Crossref + the full text of that report
    (secondary)].
    ⚠️ **this is a news-type secondary source, not the original paper's table**; the tables of the
    originals (JACS 1984 / JPC 1986) are behind the ACS paywall. A human should check against the
    Table/Figure of `Closs et al. 1986, JPC 90:3673`.
  - Additional verified bibliographic entries (Crossref): Joran et al., *Nature* **327**, 508–511
    (1987), DOI `10.1038/327508a0`; Irvine et al., *Chem. Phys.* **104**, 315–324 (1986),
    DOI `10.1016/0301-0104(86)80175-6`; Barbara & Meyer, *J. Phys. Chem.* **100**, 13148–13168 (1996),
    DOI `10.1021/jp9605663`.
- Conclusion:

  **(the numbers)**
  - **System**: a D–bridge–A bichromophore; D = 4-biphenylyl (biphenyl radical anion),
    bridge = a rigid saturated hydrocarbon spacer (5α-androstane), fixed separation ≈ **10 Å**;
    A = a series of π-electron acceptors (8 of them, see below).
    Pulsed radiolysis prepares the radical anion in **fluid solution**.
    [verified: Lokan 2000 (UNSW thesis, DOI 10.26190/unsworks/7583) Ch. 1 p. 9; C&EN 1984 (secondary)]
  - **The 8 acceptors (in increasing order of −ΔG°)**: 2-naphthyl, 9-phenanthryl, 1-pyrenyl,
    2-hexahydronaphthoquinonyl, 2-naphthoquinonyl, 2-benzoquinonyl, 2-(5-chlorobenzoquinonyl),
    2-(5,6-dichlorobenzoquinonyl).
    [verified: C&EN 1984 (secondary)]
  - **The 3 compounds whose values were obtained** (same λ series):
    | A (acceptor) | −ΔG° / eV | k / s⁻¹ |
    |---|---|---|
    | 2-naphthyl | ≈ 0.05 | ≈ 1.5×10⁶ |
    | 2-hexahydronaphthoquinonyl | **1.23** (optimal) | ≳ 2×10⁹ (**instrumental upper limit**) |
    | 2-(5,6-dichlorobenzoquinonyl) | **2.40** | ≈ 7×10⁷ |
    [verified: C&EN 1984 (secondary)] the per-item values of the remaining 5 acceptors were **not obtained**.
  - **λ_s = 0.75 eV** (solvent/outer), **λ_v = 0.45 eV** (vibrational/inner),
    **ω = 1500 cm⁻¹** ⇒ **λ ≈ 1.20 eV**.
    [verified: annotation inside Nobel Fig. 8 (including ω) + UNSW Fig. 1.8 independently redrawing the
    same λ value]
  - **Solvent and temperature**: main solvent MTHF / THF, **≈ 296 K** (C&EN caption; the body text says
    "room temperature"); the second solvent is **isooctane** (**not** isopentane), in which the peak is
    shifted markedly to the left and some reactions are too fast to measure.
    ⚠️ **the true temperature in the original was not verified** (the caption says THF, the body text
    says MTHF — inconsistent in itself).
    [verified: C&EN 1984 (secondary)]
  - **Driving-force range**: `−ΔG°` from ≈ **0.05 eV to ≈ 2.4 eV** (axis ticks 0.0 / 1.0 / 2.0).
    [verified: per-compound values + reading Nobel Fig. 8]
  - **Rate range**: `k ≈ 1.5×10⁶ → ≳ 2×10⁹ s⁻¹` (intramolecular first-order rate constants).
    [verified: per-compound values + reading the vertical axis of Nobel Fig. 8]
  - **Qualitative behaviour**: k first rises with −ΔG° (normal region) → reaches a maximum at x ≈ λ →
    then falls (inverted region); the inverted-region drop is about **1.5 orders of magnitude**.
    [verified: read-off from the figure + per-compound values]
  - ⚠️ **Quantitative comparison (the key finding of this record)**: substituting λ = 1.2 eV,
    T = **296 K** (`k_B T = 25.51 meV`) into the classical formula, and comparing with experiment:

    | x = −ΔG° / eV | classical ΔG‡ / eV | classical ΔG‡/k_BT | classical k / k(peak) | measured k / k(peak) |
    |---|---|---|---|---|
    | 0.05 | 0.27552 | 10.80 | 2.0×10⁻⁵ | 7.5×10⁻⁴ |
    | 1.23 | 0.00019 | 0.007 | 1 | 1 (instrumental upper limit) |
    | 2.40 | 0.30000 | 11.76 | 7.9×10⁻⁶ | 3.5×10⁻² |

    ⇒ on the inverted branch, 1.23 → 2.40 eV: the classical prediction drops by **5.1 orders of
    magnitude**, while the measurement drops by only **1.46 orders of magnitude**
    ⇒ **in the inverted region the classical model falls off too fast by about 3.6 orders of
    magnitude**; this is the direct reason for the existence of the quantum vibrational correction
    (`ω = 1500 cm⁻¹`; the smooth curve of Nobel Fig. 8 includes this correction) (record 6).
    [the table is my own arithmetic; the formula and the parameters are all verified and the calculation
    can be re-checked. ⚠️ two premises: ① within the same series the pre-exponential factor `A` is
    approximately the same (the standard treatment in the literature); ② `2×10⁹ s⁻¹` is an instrumental
    upper limit ⇒ the **lower bound** on the measured drop is even smaller, and the direction of the
    conclusion is unchanged.]
- Formalizable implication:
  - Can be made explicit as Lean premises (instance layer):
    `λ = 1.2`, `x ∈ {0.05, 0.60, 1.23, 2.00, 2.40}`, `A > 0`, and
    **`0 < kB`, `0 < T` (take T as a premise; do not hard-code 296 or 298)**.
    Also needed is an **instance-field-style declaration**: "λ and −ΔG° are literature fit/measured
    values" — this is data, not a theorem.
  - **Region determination needs only (λ, x)**: `x < 1.2` ⇒ normal region; `x = 1.2` ⇒ no barrier;
    `x > 1.2` ⇒ inverted region. **Independent of T and A** — this makes the instance layer very clean.
  - Is a physical approximation (must be declared explicitly; **the most important warning this
    experiment gives for the formalization**):
    - **"the description holds" (the inverted-region rate strictly decreases with the driving force) is
      a proposition about the classical Marcus formula, not about the experimental curve.** The measured
      drop is "flattened" by the quantum correction; if "the description" were understood as "predicting
      the measured rate", then for real systems the proposition **is false**. plan must keep the two
      apart (see "Impact").
    - within a "series of homologues" the pre-exponential factor A is independent of x (the series has a
      fixed 10 Å separation, so the electronic coupling is approximately constant).
  - Currently not expressible in mathlib: **nothing**. Deciding `λ < x` is a pure real-number
    proposition. If "the measured rate" is to be written down, the data can only be hard-coded as a
    `List (ℝ × ℝ)` as **data** (not a theorem), and explicitly declared to be literature-measured
    values.
- Impact:

  **Recommend revising the wording of plan.md:**
  - The instance-layer theorem statement must read "**this system falls in the inverted region, and the
    classical Marcus description holds at this (λ,x,T,A)**", and **must not** read "the inverted-region
    rate of this system decreases with the driving force" (the latter is an assertion about experiment,
    whose strictness the literature explicitly refutes).
  - Recommend the M5 instance take `λ = 1.2` together with `x = 0.6` (deciding `¬ InvertedRegion`) +
    `x = 2.0` (deciding `InvertedRegion` and `StrictAntiOn` holds).

## 2026-09-20 — Experimental evidence for the inverted region II: porphyrin–quinones, geminate ion pairs, photosynthetic reaction centres — literature_researcher

- Source:
  - Wasielewski, M. R.; Niemczyk, M. P.; Svec, W. A.; Pewitt, E. B., *J. Am. Chem. Soc.*
    **107**(4), **1080–1082** (1985). DOI `10.1021/ja00290a066` [verified: Crossref].
  - Gould, I. R.; Ege, D.; Mattes, S. L.; Farid, S., "Return electron transfer within
    geminate radical ion pairs. Observation of the Marcus inverted region",
    *J. Am. Chem. Soc.* **109**(12), 3794–3796 (1987). DOI `10.1021/ja00246a055`
    [verified: Crossref].
  - McLendon, G.; Miller, J. R., "The dependence of biological electron transfer rates on
    exothermicity. The cytochrome c/cytochrome b₅ couple", *J. Am. Chem. Soc.*
    **107**(26), 7811–7816 (1985). DOI `10.1021/ja00312a002` [verified: Crossref].
  - Marcus Nobel Lecture 1992, **p. 88** (photosynthetic reaction centre) [verified: body text].
  - Lee, K. J., "The Marcus Inverted Region", UIUC Department of Chemistry literature seminar report,
    1988-02-25, printed pages 38–40. Local PDF:
    `proofs/literature/Lee1988_Marcus_inverted_region.pdf`
    [verified: PDF text layer; **secondary source**].
- Conclusion:
  - **Porphyrin–quinone (Wasielewski 1985)**: photoinduced charge separation and dark charge
    recombination rates vary with exergonicity; the radical-ion recombination rate **drops by about two
    orders of magnitude** as the driving force increases
    [verified: Lee 1988 report (secondary); **the concrete λ / −ΔG° values were not obtained from the
    original**].
  - **Geminate radical ion pairs (Gould/Farid 1987)**: cyano-substituted anthracene as acceptor,
    naphthalene derivatives / tolane / biphenyl as donors; the rate drops by nearly two orders of
    magnitude as −ΔG° increases
    [verified: Lee 1988 report (secondary); **the concrete values are unverified**].
  - **Biological systems (McLendon & Miller 1985, cyt c / cyt b₅)**: evidence for the inverted region in
    proteins. **The exact (λ, −ΔG°) values were not verified this time.**
  - **Photosynthetic reaction centre (Marcus Nobel Lecture p. 88)**: for the first step BChl₂→BPh,
    `−ΔG° ≈ 0.25 eV` (total excitation energy 1.38 eV) and λ is small; whereas the return step
    BPh⁻→BChl₂⁺ (hole–electron recombination) is highly exergonic, `−ΔG° ≈ 1.1 eV`, with
    **`λ ≈ 0.25 eV`** ⇒ **clearly in the inverted region** (x = 1.1 ≫ λ = 0.25). Marcus states explicitly
    that the inverted-region effect is the key to this step being suppressed.
    [verified: Nobel Lecture p. 88 body text]
  - **77 K MTHF glass series (Miller–Peeples–Schmitt–Closs 1982)**: biphenyl radical anion → 28
    different acceptors, with `β = 1.2 Å⁻¹` at the optimal driving force. **This is a different
    experiment from the fluid-solution series of MCC 1984** (different temperature, different
    mechanism); do not mix the two when citing.
    [verified: quotation in Lokan 2000 thesis Ch. 1 + Crossref]
- Formalizable implication:
  - Can be made explicit as Lean premises (the second instance layer): `λ = 0.25`, `x = 1.1` (eV) ⇒
    `InvertedRegion`; `0 < A`, `0 < k_B*T` ⇒ the description holds.
  - Is a physical approximation (must be declared explicitly): for biological systems ΔG° is estimated
    from **redox potential differences** and λ is given by **fitting** — **both are model-dependent
    derived quantities, not directly observable quantities**. The instance layer must annotate that "the
    parameters are taken from literature fits, not from first-principles calculations".
  - Currently not expressible in mathlib: estimating λ in a protein environment (needs
    Poisson–Boltzmann / continuum protein electrostatics) — not expressible; one can only take 0.25 eV
    as an externally given constant.
- Impact:
  - **Recommend that M5 include at least two independent systems** (organic series λ = 1.2 eV;
    photosynthetic reaction centre λ = 0.25 eV) to show that the definition is reusable, each with a
    normal-region counterexample.
  - ⚠️ **the Wasielewski page number 107:5562 given in the task statement does not agree with the
    Crossref-verified `107(4):1080–1082`**. If the 5562 paper really must be cited, it needs separate
    verification (it may be another paper from the same group). **Do not write 107:5562 before
    verification.**

## 2026-09-20 — Quantum vibrational correction: why the classical model gives a strictly monotone decrease — literature_researcher

- Source:
  - Siders, P.; Marcus, R. A., "Quantum effects for electron-transfer reactions in the
    'inverted region'", *J. Am. Chem. Soc.* **103**(4), 748–752 (1981).
    DOI `10.1021/ja00394a004` [verified: Crossref].
  - Siders, P.; Marcus, R. A., "Quantum effects in electron-transfer reactions",
    *J. Am. Chem. Soc.* **103**(4), 741–747 (1981). DOI `10.1021/ja00394a003`
    [verified: Crossref].
  - Marcus Nobel Lecture 1992, the annotation `ω = 1500 cm⁻¹` inside **Fig. 8** [verified: reading the
    image] — i.e. the mean vibrational quantum used in the quantum correction.
  - Bixon, M.; Jortner, J., "Intramolecular Radiationless Transitions",
    *J. Chem. Phys.* **48**(2), 715–726 (1968). DOI `10.1063/1.1668703`
    [verified: Crossref]. (= the original paper of the Bixon–Jortner energy-gap law)
  - Jortner, J., "Temperature dependent activation energy for electron transfer between
    biological molecules", *J. Chem. Phys.* **64**(12), 4860–4867 (1976).
    DOI `10.1063/1.432142` [verified: Crossref]. (quantized treatment of high-frequency vibrational
    modes)
  - Bixon, M.; Jortner, J., "Electron Transfer—from Isolated Molecules to Biomolecules",
    *Adv. Chem. Phys.* **106/107**, 35–202 (1999). DOI `10.1002/9780470141656.ch3`
    [verified: Crossref]. (review)
  - ⚠️ for the three papers above, **only the bibliographic information was verified; the body text was
    not read**; quantitative details concerning "saturation/plateau" are marked
    `from memory, pending human review`. But this record serves §1.3 "explicitly out of scope", for
    which only a directional attribution is needed.
- Conclusion: the classical treatment regards nuclear motion as purely classical degrees of freedom,
  giving `ΔG‡ = (λ−x)²/(4λ)`, which in the inverted region grows **quadratically and without bound**
  with x ⇒ the rate decreases strictly monotonically and extremely fast.
  After quantizing the high-frequency vibrational modes (`ω ≈ 1500 cm⁻¹`), electron transfer can be
  accompanied by vibrational excitation (Franck–Condon vibrational overlap factors), the barrier growth
  is diverted through "vibrational channels", and the inverted-region decline becomes gentler and tends
  to saturation/a plateau. This explains the comparison in record 4, where "the measured drop
  (~2 orders of magnitude) is far smaller than the classical prediction (~5 orders of magnitude)".
  [verified: figure and formulas; the mechanistic statement is review consensus]
- Formalizable implication:
  - Can be made explicit as Lean premises: **none** (this record enters no theorem's premises).
  - Is a physical approximation (must be declared explicitly): **classical nuclear motion / no nuclear
    tunnelling / vibrational modes negligible** — this is exactly the applicability condition of the
    classical Marcus formula, and it must go into plan's approximation list.
  - Currently not expressible in mathlib: the Fermi golden rule sum over a vibrational heat bath (needs
    the harmonic-oscillator Hilbert space + vibrational overlap integrals `⟨χ_i|χ_f⟩` + thermal
    averaging). **Explicitly excluded from scope.**
- Impact: **recommend hard-coding one item into plan.md §1.3 "explicitly out of scope"**:
  > This plan characterizes only the monotonicity of the **classical Marcus formula**
  > `ΔG‡ = (λ−x)²/(4λ)` in the inverted region; it does not characterize the saturation caused by
  > quantum vibrational corrections (Bixon–Jortner / Siders–Marcus), nor does it claim that the
  > classical formula can quantitatively reproduce the measured inverted-region drop.

## 2026-09-20 — Review-level complete barrier formula (with work terms): the approximation cost of this plan — literature_researcher

- Source:
  - Marcus, R. A.; Sutin, N., "Electron transfers in chemistry and biology",
    *Biochim. Biophys. Acta (Reviews on Bioenergetics)* **811**(3), 265–322 (1985).
    DOI `10.1016/0304-4173(85)90014-X` [verified: Crossref + CaltechAUTHORS record page].
    ⚠️ **the full body text was not obtained this time (Elsevier paywall); the equation numbers below
    are pending human review.**
  - Corroboration (secondary): the Lee 1988 report (same as record 5) gives
    `ΔG‡ ≈ w_r + (λ/4)·(1 + (ΔG° + w_p − w_r)/λ)²`,
    with the inverted-region condition written as `|ΔG° + w_p − w_r| > λ`. [verified: PDF text layer;
    but it is secondary]
- Conclusion: the review-level "complete" barrier formula contains **electrostatic work terms**:
  `ΔG‡ = w_r + (λ/4)·(1 + (ΔG° + w_p − w_r)/λ)²`,
  rate `k = κ·ρ·Z·exp(−ΔG‡/k_B T)`.
  When `w_r = w_p = 0` (neutral or zwitterionic pairs, or screening at high ionic strength) it reduces
  to `ΔG‡ = (λ + ΔG°)²/(4λ)`, the form adopted by this plan.
- Formalizable implication:
  - Can be made explicit as Lean premises: if the "with work terms" route is taken, then
    `w_r, w_p : ℝ` become **additional parameters**, and the inverted-region criterion becomes
    `λ < |ΔG° + w_p − w_r|` — in that case the "region" is **no longer determined by x alone**.
  - Is a physical approximation (must be declared explicitly): **ignoring the work terms
    (`w_r = w_p = 0`)** is the price paid for this plan's adoption of `ΔG‡ = (λ−x)²/(4λ)`, and **must be
    declared explicitly**.
  - Currently not expressible in mathlib: the Debye–Hückel / electrostatic screening expressions for the
    work terms; `κ` (electron transmission coefficient, needs the Landau–Zener formula); `ρ`
    (adiabatic/non-adiabatic factor).
- Impact:

  **Recommend revising plan.md:**
  - Recommend stating explicitly in plan §2.2 or §1.3:
    > the driving force is taken as `x = −ΔG°`, and **the work terms are explicitly declared to be
    > ignored** (`w_r = w_p = 0`) — this is a physical approximation, not a theorem.
  - Recommend also recording the extension cost in passing: if the work terms are added later, the
    `InvertedRegion` predicate must be changed to depend on `(ΔG°, w_r, w_p, λ)` instead of on `x` alone,
    **which would break the existing definition**; a sentence should be left in plan now.
  - **About the pre-exponential factor (clarification)**: the transition-state-theory form
    `A = (4πλk_B T)^{-1/2}·κ·ν_n` enters k only through a **positive factor that is independent of x**.
    Therefore plan's assumption that "the pre-exponential factor is independent of the driving force"
    **loses no x-monotonicity conclusion whatsoever**. Recommend writing this sentence into plan as an
    explanation of "why this approximation is harmless".

---

## Appendix: formalizable implication — the exact shape of the "sharp characterization" (for direct adoption by M2/M3/M4a)

> This section is a **formalization recommendation** derived from the sources listed above; it is not a
> literature conclusion.
> ⚠️ **an early version of this section gave an incorrect proposition; it has been corrected (the
> incorrect version is kept below as a warning).**
> The corrected F1/F2/F3 have been re-checked by **exhaustive numerical verification**: `λ ∈ {±0.5, ±1, ±2}`,
> `τ ∈ {±0.5, ±1, ±2, 0}`, `A ∈ {−2,−1,0,1,2}`, all combinations, 0 counterexamples in total.

**Notation** (exactly as in `plan.md` §2.2):
`barrier λ x := (λ - x)^2 / (4*λ)`, `rate λ τ A x := A * Real.exp (-(barrier λ x) / τ)`,
`desc λ τ A := StrictAntiOn (rate λ τ A) (Set.Ioi λ)` (= plan's `InvertedDescriptor`).
(The Lean division-by-zero convention `z/0 = 0` is in force throughout.)

### F1 (exact characterization of **`desc` alone**)

```
desc λ τ A   ↔   0 < A * λ / τ          -- equivalent integer form: 0 < A * λ * τ
```

**Mechanism**: `rate = A·exp(e(x))`, where `e(x) = -(x-λ)²/(4·λ·τ)`, hence
`e'(x) = -(x-λ)/(2·λ·τ)`. On `(λ,∞)` we have `x-λ > 0`, so `sign e' = -sign(λ·τ)`:

- `λ·τ > 0` ⇒ `e` strictly decreasing ⇒ `rate` strictly decreasing ⟺ `A > 0`;
- `λ·τ < 0` ⇒ `e` strictly increasing ⇒ `rate` strictly decreasing ⟺ `A < 0`;
- `λ·τ = 0` (including `λ = 0` or `τ = 0`) ⇒ `e ≡ 0` ⇒ `rate ≡ A` constant ⇒ **not** strictly decreasing.

⇒ **`desc` alone implies neither `A > 0` nor `λ > 0`.**

### F2 (characterization **after incorporating rate positivity**)

```
(∀ x : ℝ, 0 < rate λ τ A x) ∧ desc λ τ A   ↔   0 < A ∧ 0 < λ * τ
```

Because `Real.exp > 0` always holds, `(∀x, 0 < rate λ τ A x) ↔ 0 < A` (`A > 0` is the necessary and
sufficient condition).

### F3 (the shape of `plan.md` §7.1 `descriptor_sharp` — **checked word by word; the formulation is correct**)

plan takes `0 < kB`, `0 < T` as **explicit premises**, hence `0 < τ := kB*T`, and F2 degenerates to:

```
(∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T   ↔   0 < A ∧ 0 < lam
```

✅ This is **word-for-word identical** to the statement in `plan.md` §7.1 (lines 341–342) ⇒ **plan needs
no modification**.
✅ I7 in plan §7.1 (`A=-1, λ=-1, kB*T=1`) and the "discovered during planning" note in §7.1 have also been
re-checked and are **correct**.
**Key point**: the left-hand side of `⟺` **must** contain the conjunct `∀x, 0 < rate ...` (see the
counterexamples below).

### ⚠️ Typical miswritings (**these appeared in an early version of this document; kept as a warning**)

> ❌ **Miswriting A**: `desc λ τ A ↔ 0 < λ ∧ 0 < τ ∧ 0 < A`
>
> **Counterexample (constructed by the lead, re-checked)**: `λ = −1`, `τ = 1`, `A = −1`.
> `barrier (−1) x = −(x+1)²/4` is strictly **decreasing** on `(−1,∞)` ⇒ `−(barrier)/τ = (x+1)²/4` is
> strictly **increasing** ⇒ `exp` increasing ⇒ multiplied by the negative `A` ⇒ `rate` is strictly
> **decreasing** ⇒ `desc` **holds**, yet `A < 0`.
> ⇒ the item about `A` in the necessity direction **fails** (likewise `λ<0 ∧ τ<0 ∧ A>0` also makes `desc`
> hold).

> ❌ **Miswriting B**: `(∀x, 0<rate) ∧ desc ↔ 0 < A ∧ 0 < λ ∧ 0 < τ`
>
> **Counterexample (re-checked)**: `λ = −3/2`, `τ = −1`, `A = 1`.
> `rate = exp(−(x−λ)²/(4λτ))` is **positive everywhere** and **strictly decreasing** on `(λ,∞)`
> (`λτ = 3/2 > 0`, `A>0`), but `0 < λ` and `0 < τ` both **fail**.
> ⇒ **`τ > 0` can only be a premise, never a conclusion.** This is exactly why `plan.md` §7.1 puts
> `0<kB`, `0<T` in premise position (rather than writing them on the right-hand side of `⟺`) — that
> formulation is correct.

**Reusable lesson (recommended for `proofs/EXPERIENCE.md`)**:
the right-hand side of a "sharp characterization" `⟺` **must correspond one-to-one with the conjuncts of
the left-hand side**.
The sign information carried by `desc` contains only `sign(A·λ/τ)` (a single product),
so recovering the signs of the three parameters individually from `desc` **alone** is **impossible** —
one must take "rate positivity" (`0 < A`) as a left-hand conjunct in order to pin `A` down; the signs of
`λ` and `τ` can still only be premises. **First count the information content on the left, then write the
conjunction on the right.**

**Robustness of the pre-exponential factor**: if the TST pre-exponential factor
`A(λ,τ) = (4*π*λ*τ)^(-1/2) * κ * ν` is used instead, it contributes only a **positive factor independent
of `x`**, and the conclusion about `desc` and the necessity analysis are **all unchanged** (as long as
`λ>0, τ>0, κ>0, ν>0`).
⇒ plan's adoption of a "constant pre-exponential factor" loses no x-monotonicity conclusion.

---

## Candidate table of instance parameters (for M5)

> Convention: `x := −ΔG°` (positive for exergonic). Region determination: `x < λ` normal region;
> `x = λ` no barrier; `x > λ` inverted region.
> **The determination uses only (λ, x)**, independently of T and A.
> A row whose "Source" column is marked **(secondary)** = read from news / lecture notes / a thesis;
> **the original table was not obtained** (ACS paywall).
> A human can check item by item against the Table / Figure of
> `Closs et al. J. Phys. Chem. 1986, 90, 3673–3683` (DOI `10.1021/j100407a039`)
> — that paper is the **full-length version** of the MCC system and contains λ / solvent tables.

| System | λ / eV | −ΔG° / eV | T / K | Region determination | Source | Verification status |
|---|---|---|---|---|---|---|
| **MCC · A = 2-(5,6-dichlorobenzoquinonyl)** (biphenyl–5α-androstane–acceptor, 10 Å, pulsed radiolysis; k ≈ 7×10⁷ s⁻¹) | **1.20** (λ_s=0.75 + λ_v=0.45) | **2.40** | **296** | **inverted region** (2.40 > 1.20, ΔG‡ = 0.300 eV) | C&EN 1984-06-04, 62(23):42–44 (secondary, DOI `10.1021/cen-v062n023.p042`); consistent with the upper bound of Nobel Fig. 8 | `verified` |
| **MCC · A = 2-hexahydronaphthoquinonyl** (k ≳ 2×10⁹ s⁻¹, instrumental upper limit) | 1.20 | **1.23** (optimal / barrierless point) | 296 | **boundary** (x ≈ λ, ΔG‡ = 1.9×10⁻⁴ eV) | same as above (secondary); Lokan 2000 thesis Ch.1 p.10 body text | `verified` |
| **MCC · A = 2-naphthyl** (k ≈ 1.5×10⁶ s⁻¹) | 1.20 | **0.05** | 296 | **deep normal region** (0.05 ≪ 1.20, ΔG‡ = 0.276 eV) | same as above (secondary) | `verified` |
| MCC (same series, read off the horizontal axis) | 1.20 | **2.00** | 296 | **inverted region** | Marcus Nobel Lecture 1992 **Fig. 8** horizontal axis (ticks 0.0/1.0/2.0 eV) | `verified` |
| MCC (same series, monotone rising left branch) | 1.20 | **0.60** | 296 | **normal region** | same as above (read off the left branch) | `verified` |
| The other 5 acceptors of the MCC series (9-phenanthryl, 1-pyrenyl, 2-naphthoquinonyl, 2-benzoquinonyl, 2-(5-chlorobenzoquinonyl)) | 1.20 | per-item values **not obtained** (only the increasing order is known) | 296 | undetermined | C&EN 1984 (secondary; gives only the sequence) | `order of magnitude only` |
| Photosynthetic reaction centre BPh⁻→BChl₂⁺ return transfer (hole–electron recombination) | **0.25** | **1.10** | modelling value | **inverted region** (1.10 ≫ 0.25) | Marcus Nobel Lecture 1992 p.88 body text | `verified` |
| Photosynthetic reaction centre BChl₂*→BPh first step | 0.25 | **0.25** (the body text gives ~0.25 eV) | modelling value | **boundary / near-optimal** (x ≈ λ) | Marcus Nobel Lecture 1992 p.88 body text | `verified` |
| Wasielewski porphyrin–quinone (photoinduced charge separation / dark recombination) | — | increases with exergonicity | — | inverted region (qualitative: drop of about 2 orders of magnitude) | Lee 1988 report (secondary); JACS 107(4):1080–1082 (1985) | `order of magnitude only` |
| Gould/Farid geminate radical ion pairs (cyanoanthracene acceptor) | — | increases with exergonicity | — | inverted region (qualitative: drop of nearly 2 orders of magnitude) | Lee 1988 report (secondary); JACS 109(12):3794–3796 (1987) | `order of magnitude only` |
| McLendon & Miller cyt c / cyt b₅ (proteins) | — | — | — | inverted region (qualitative) | JACS 107(26):7811–7816 (1985) | `order of magnitude only` |
| MCC non-polar solvent control (**isooctane**, **not** isopentane) | not obtained | peak shifted markedly to the left | — | — | C&EN 1984 (secondary): some reactions too fast to measure | `order of magnitude only` |
| Miller–Peeples–Schmitt–Closs MTHF glass (biphenyl anion → 28 acceptors) | — | near the optimal driving force | **77** | contains the inverted region; β = 1.2 Å⁻¹ | JACS 104(24):6488–6493 (1982) | `order of magnitude only` |

**⚠️ About T (for M5)**: C&EN (secondary) records the 1984 series as "MTHF at room temperature", and its
reproduced caption says **296 K**; **the true temperature of the original was not verified** (and the
caption says THF while the body text says MTHF, which is inconsistent in itself).
⇒ **recommend that M5 take T as an explicit premise `0 < T` and not hard-code a concrete temperature** —
the region determination depends only on `(λ, x)` and the monotonicity only on `0 < kB*T`, both of which
are independent of the concrete value of T.

**⚠️ About the verification status of `ω = 1500 cm⁻¹` (clarification)**: this value is **not** a secondary
paraphrase — it is printed directly in the **in-figure annotation of Marcus Nobel Lecture 1992 Fig. 8**
(local rendering `Marcus1992_nobel_p84_fig8.png`, in the same annotation block as λ_s / λ_v), and it was
confirmed this time by reading the image ⇒ its status is `verified (image read)`. That the second survey
route did not see this value is normal (it appears only inside that figure).

**🔬 Classical formula vs. measurement (arithmetic on the verified numbers of the table above, to back the
boundary declaration of §1.3)**: take λ = 1.20 eV, T = 296 K (`k_B T = 25.51 meV`). On the **inverted
branch** x: 1.23 → 2.40 eV: the classical formula predicts a rate drop of
`exp(−11.761)/exp(−0.0074) = 7.86×10⁻⁶` (**5.1 orders of magnitude**), while the measurement drops by only
`7×10⁷ / 2×10⁹ = 3.5×10⁻²` (**1.46 orders of magnitude**).
⇒ in the inverted region the classical formula **falls off too fast by about 3.6 orders of magnitude**.
(⚠️ two premises: ① within this series the pre-exponential factor `A` is approximately the same — this is
the standard treatment in the literature; ② 2×10⁹ s⁻¹ is an **instrumental upper limit**, so the true peak
rate may be higher, hence the **lower bound** on the measured drop is smaller and the direction of the
conclusion is unchanged. This is also exactly why the smooth curve of Nobel Fig. 8 includes the
`ω = 1500 cm⁻¹` quantum correction.)
**This arithmetic is my own calculation, not a literature conclusion**; the numbers themselves are marked
`verified`. **Implication**: M5 must not write "the description holds" as an assertion about the measured
rate (see the "Impact" column of the record "Experimental evidence for the inverted region I").

### Fundamental constants (to be written directly into Lean at the instance layer)

| Quantity | Value | Source | Verification status |
|---|---|---|---|
| `k_B` | `1.380 649 × 10⁻²³` J/K (**exact**) | NIST CODATA 2022, `physics.nist.gov/cgi-bin/cuu/Value?k` | `verified` |
| elementary charge `e` | `1.602 176 634 × 10⁻¹⁹` C (**exact**) | NIST CODATA, `physics.nist.gov/cgi-bin/cuu/Value?e` | `verified` |
| `k_B` (eV/K) | `8.617333262145 × 10⁻⁵` eV/K (**exact**, = k_B/e, both being exact SI values) | obtained by dividing the two rows above | `verified` (arithmetically consistent) |
| `k_B·T` at T = 298.15 K | **25.693 meV** (0.025693 eV) | obtained by multiplying the row above | `verified` (arithmetically consistent) |
| `k_B·T` at T = 77 K | **6.635 meV** | obtained by multiplying the row above | `verified` (arithmetically consistent) |

> ✅ Promoted from "from memory" to "verified": after the 2019 SI redefinition both `k_B` and `e` are
> **exact values**, so the eV/K representation of `k_B` and `k_B·T` are both **exact arithmetic results**,
> not measured values.

> Instance-layer recommendation: **do not claim 298.15 K as the true temperature of some experiment**.
> Write explicitly that "this instance takes T = 298.15 K as a modelling choice, needing only
> `0 < k_B*T`" — the region determination and the monotonicity are both independent of the concrete value
> of T.

---

## List of corrections and conflicts (relative to the assumptions of the task statement)

1. **The DOI `10.1021/ja00323a043` given in the task statement is not Miller–Calcaterra–Closs 1984.**
   Crossref verifies that this DOI = Mislow & Siegel, "Stereoisomerism and local chirality",
   *JACS* **106**(11), 3319–3328 (1984). **The correct DOI of MCC 1984 is
   `10.1021/ja00322a058`, *JACS* 106(10), 3047–3049.**
2. **The Wasielewski page number 107:5562 given in the task statement is unconfirmed.** Crossref verifies
   that the paper with the same title is *JACS* **107**(4), 1080–1082 (1985), DOI `10.1021/ja00290a066`.
   After a second independent check: **107:5562 is a different paper** (DOI `10.1021/ja00305a059`) and is
   **not the same paper** as "Dependence of rate constants for photoinduced charge separation and dark
   charge recombination on the free energy of reaction in restricted-distance porphyrin-quinone
   molecules". If it really must be cited, its content needs to be verified separately.
   (Also: the UIUC 1988 lecture notes print the pages of MCC 1984 as "106, 3074" — Crossref confirms this
   is a **typographical error**; the correct value is 106(10):3047–3049; this typo does not constitute a
   numerical conflict.)
3. **✅ No conflict: the original form of the classical barrier formula is indeed `(λ + ΔG°)²/(4λ)`.**
   Marcus's own printed form (Nobel Lecture 1992, Eq. (5b), p.78) is
   `ΔG* = (λ/4)(1 + ΔG°′/λ)²`, and the two are identical.
4. **✅ No conflict: the inverted-region criterion.** **Its original source is Marcus 1960, Discuss.
   Faraday Soc. 29, p.28 §(v)** (title "Possibility of 'inverted' chemical behaviour", original text
   "If ΔF° becomes too negative …"); the modern wording at Marcus Nobel Lecture 1992 p.82 is
   "vanish at ΔG° = −λ".
   The two agree ⇒ inverted region = `ΔG° < −λ` ⟺ `−ΔG° > λ`, consistent with this plan's `x > λ`
   (`x := −ΔG°`).
   **⚠️ But `ΔG° > λ` is a miswriting with the sign reversed** (see record 2 and the new record).
   **⚠️ The first proposal of the inverted region should be cited to 1960, not to 1956** (the word
   "inverted" appears nowhere in the 1956 paper).
5. **⚠️ Attribution of the pre-exponential factor**: `(4πλk_BT)^{-1/2}` **is not** in Marcus 1956
   (1956 has `k₁ = Z·exp(−ΔF*/kT)`, Eq. (44); `Z` = collision number, whose explicit form is given by
   Eq. (43)). The citation must be changed. This item was confirmed by independent checking against a
   second source.
6. **⚠️ Notation**: Marcus himself writes `λ = λ_o + λ_i` (solvational + vibrational);
   plan's `λ = λ_in + λ_out` is the synonymous modern notation.
7. **⚠️ work terms**: the review-level complete formula contains `w_r, w_p`; plan's form implicitly
   assumes `w_r = w_p = 0` and must declare this explicitly (record 7).
8. **⚠️ An early version of the "Appendix" section of this document gave an incorrect proposition**
   (corrected; the incorrect version is kept as a warning):
   it once read `desc λ τ A ↔ 0 < λ ∧ 0 < τ ∧ 0 < A`, whose **necessity fails**
   — the counterexample `λ = −1, τ = 1, A = −1` makes `desc` hold while `A < 0`.
   The correct characterizations are **`desc ↔ 0 < A·λ/τ`** (`desc` alone) and
   **`(∀x, 0<rate) ∧ desc ↔ 0 < A ∧ 0 < λ·τ`** (after incorporating rate positivity).
   ✅ **The `descriptor_sharp` statement in `plan.md` §7.1 is itself correct and needs no modification**
   (it takes `0<kB`, `0<T` as premises, and its left-hand side contains the positivity conjunct).
9. **✅ A point that can be strengthened (not a conflict, a recommendation)**: `lamOuter_pos` in
   `plan.md` §7.2 takes the geometric-factor inequality `hgeom : 1/R < 1/(2a₁) + 1/(2a₂)` as an
   **assumption**; record 3 of this document proves that it can be **derived** from `0 < a₁`, `0 < a₂`,
   `a₁ + a₂ ≤ R` (the corollary `geometric_factor_pos`).
   Recommend that M4b replace the two premises `hR` + `hgeom` by the single premise
   `hRge : a₁ + a₂ ≤ R`, making the solvent-side condition for "the inverted region exists" more basic
   (`a₁+a₂ ≤ R`, i.e. "the two spheres do not overlap", has a direct geometric meaning).

---

## Ordering of the inexpressible list (for direct adoption by `plan.md` §14 "next stop")

> Ordering criterion: **actual impact on the existing statements of M1–M5** (the larger, the earlier)
> × the reusability of the required mathematical foundations.
> All items are "currently inexpressible in mathlib or too expensive to express"; **M1–M5 depend on none of
> them**.

| Rank | Inexpressible item | Impact on M1–M5 | What mathematical foundations would be needed to do it in the future |
|---|---|---|---|
| **1** | **Franck–Condon factors / vibrational overlap integrals (the inner product of `χ_i` and `χ_f`)** | **Zero** (M1–M5 use only the classical parabolic barrier). But it is the **direct prerequisite** for "why the classical inverted region is weakened by experiment", and at the same time the common prerequisite of rank 3 | Eigenfunction systems of the one-dimensional harmonic oscillator in `L²(ℝ)` + orthogonality/completeness of Hermite polynomials + the Laguerre closed form of the overlap integral. mathlib already has `Lp`, Hilbert spaces and some special functions, but **does not have** the completeness theorem for the harmonic-oscillator eigenbasis ⇒ **it has to be built, and it is the most feasible of all the items** |
| **2** | **First-principles derivation of solvent continuum electrostatics (the origin of the Pekar formula)** | **Medium**: `lamOuter` is currently a **definition** (plan §7.2). If it were later changed to a "derivation", the statement of M4b would be upgraded from a "premise" to a "theorem" | Variational principle for non-equilibrium polarization + the boundary-value problem for the Poisson equation on a spherical cavity. mathlib **has no PDE / boundary-value-problem library**, and the construction cost far exceeds the benefit ⇒ **recommended to keep it a definition permanently** |
| **3** | **Fermi golden rule + infinite sum over a vibrational heat bath (Bixon–Jortner / Jortner energy-gap law)** | **Zero** (§1.3 has already excluded it); it is the main body of §14 item 1 | Series convergence + vibrational partition function (generating function) + thermal averaging. mathlib has series-convergence infrastructure but **no** statistical-mechanics / partition-function layer ⇒ it would have to be built after rank 1 is completed |
| **4** | **Exponential decay of the electronic coupling `V(R) = V₀·exp(−β(R−R₀))` and the superexchange mechanism** | **Zero** (§1.3 has already excluded it); belongs to §14 item 3 | Derivation of the effective coupling in a tight-binding model / perturbation theory. mathlib has no application layer for the spectral theory of quantum-mechanical operators ⇒ high construction cost |
| **5** | **Marcus cross relation `k₁₂ = √(k₁₁k₂₂K₁₂)`** | **Zero** (§1.3 has already excluded it) | Formally it is only an algebraic identity at the `Real.sqrt` level — **expressible**; the real obstacle is that it depends on the **physical assumption** that "the cross reaction and the self-exchange reactions have the same `λ`" ⇒ if it is done, it should be written as a **premise** rather than a provable theorem. **This is the cheapest of all the items, but it must be made clear that it is an assumption** |
| **6** | **Pre-exponential factors `κ` (Landau–Zener transmission coefficient), `ρ` (adiabatic factor)** | **Extremely low**: plan treats `A` as a positive constant (§13 item 9 has argued for the robustness of this approximation) | The Landau–Zener formula requires asymptotic analysis of a time-dependent two-level system (Stokes phenomenon / complex-time saddle points) ⇒ not in mathlib |
| **7** | **Physical units and dimensional checking (eV / K / J)** | **Zero, but requires discipline**: in Lean, `kB`, `T`, `lam`, `x`, `A` are all bare `ℝ`, and **dimensional errors will not be caught by the kernel** | mathlib **has no** physical unit system (something like `Unitful`) ⇒ one can only rely on documentation and instance comments. **Recommend that every M5 instance state its units**, and that a one-line unit-convention comment be written at the top of `Instances.lean` |

**Recommended ordering for `plan.md` §14**:
1. **Do rank 1 first (Franck–Condon factors)** — it is the common prerequisite of ranks 1 and 3, and
   mathlib's `Lp` / Fourier / special-function foundations are reusable, making it the only low-cost,
   high-benefit item among the "next stops".
2. **Rank 2 (first-principles derivation of solvent electrostatics) is recommended to be excluded
   permanently** — its cost/benefit ratio is the worst; keeping `lamOuter` as a definition is the correct
   engineering choice.
3. **Rank 5 (the cross relation) is the cheapest item**, but if it is done, the statement level must make
   clear that the "same `λ` assumption" is a **premise** rather than a theorem; otherwise a physically
   overly strong claim would be made.
