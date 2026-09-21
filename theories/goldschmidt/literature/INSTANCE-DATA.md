# theories/goldschmidt/literature/INSTANCE-DATA.md — printed numbers: radii, bands, per-compound `t` values

> Companion to `theories/goldschmidt/LITERATURE.md` (the authority; it names every source as `S<n>`
> and carries the formalizable implication of each). This file exists only to keep the *printed
> numbers* out of the record's main text.
> Language: English (contract `proofs/ENGINE.yml`; the only bilingual file is `RESULTS.md`).
> **Every row is a transcription of what a source prints — never a value this round computed.**
> Derived values appear only in a column explicitly labelled `derived (this round)`.
> Evidence vocabulary (identical to the record's): `first-hand` (the text was retrieved here and the
> passage searched locally) · `abstract-only` · `secondary` (read only as quoted by a named retrieved
> source) · `bibliographic-only` · `unverified`.
> Raw PDFs are **not** stored in this repository; scratch is `/tmp/goldschmidt/`. Nothing here is a
> new finding: look-up keys, statuses and loci are the record's.
> Date: **2026-09-21** (round 1).

---

## T1 — Band conventions actually printed (`t` = Goldschmidt tolerance factor)

The round's central negative: **the literature does not single out one band.** Row order follows the
record's §S-bands. "closed" = both edges printed with `≤`; "half-open" = the upper side is printed as
`t > x` with no upper edge at all — which is *not* a band.

| # | band as printed | status | source (record id) |
|---|---|---|---|
| 0 | ⭐ **`0.8 – 1.0`** — printed as *"durchwegs zwischen 0,8 und 1"*, with **corundum** below ≈ 0.8 and replacement "durch die **Aragonitstruktur**" above 1.0 | **first-hand via OCR** (primary text; band sentence corroborated by an index hit on the same scan) | **Goldschmidt, Barth, Lunde & Zachariasen 1926 (`S9`)**, printed pp. 79–80 |
| 1 | `0.8 ≤ t ≤ 1` | first-hand | Travis et al. 2016, *Chem. Sci.* **7** 4548 (`S3`) |
| 2 | `0.8 ≤ t ≤ 1.0` (closed) | first-hand | Kim et al. 2023, *Materials* **16** 6317 (`S4a`); Rafiu et al. 2026, *RSC Adv.* **16** 21833 |
| 3 | `0.80 ≤ t ≤ 1.00` | first-hand | Lim et al. 2024, *Energy Environ. Sci.* **17** 4390 |
| 4 | `0.75 < t < 1.0` | first-hand | Yentekakis et al. 2022, *Nanomaterials* **12** 1042 (`S4b`); Ramantani et al. 2021, *Nanomaterials* **11** 1931; Hadi et al. 2022, *RSC Adv.* **12** 15461 |
| 5 | `0.75 ≤ t ≤ 1.0` | first-hand | Muñoz et al. 2022, *Materials* **15** 3288 (`S5`) |
| 6 | `0.9 ≤ t ≤ 1.0` | first-hand | Manchón-Gordón et al. 2025, *Materials* **18** 3862; Zhang et al. 2023, *Materials* **16** 2214 |
| 7 | `0.89 < t < 1` | first-hand | Johnsson & Lemmens 2007 (`S6`), eq. (2) context, printed p. 3 of the arXiv version |
| 8 | `0.825 < t < 1.059` | first-hand | Bartel et al. 2019, *Sci. Adv.* **5** eaav0693 (`S7`) — a **decision-tree fit**, 74 % accuracy |
| 9 | `0.8 < t < 1.1` | first-hand | Jouybar et al. 2024, *Molecules* **29** 3355; *Micromachines* **15** 192 — a *stability* band, not a distortion assignment |
| 10 | `0.77 ≤ t ≤ 1.10` | first-hand | Reda, El-Dek & Arman 2022, *J. Mater. Sci.: Mater. Electron.* **33** 16753, Table 1 note (`S15`) |
| 11 | `0.76 – 1.13` | first-hand | Zhang et al. 2024, *iScience* **27** 110794 |
| 12 | `0.71 < t < 1.10` | first-hand | *RSC Adv.* **15** 12179 |
| 13 | `t = 1` → cubic; `0.9 < t < 1.0` → orthorhombic; `0.75 < t < 0.9` → rhombohedral; `1.00 < t < 1.13` → hexagonal | first-hand | Rout et al. 2025, *Small* **21** 2503138 (multi-band) |
| 14 | `1.00 < t < 1.13` hexagonal; `0.9 < t < 1.0` **cubic**; `0.75 < t < 0.9` orthorhombic; `t < 0.75` ilmenite | first-hand | Dey & Mehta 2022, *Science in One Health* **1** 100002 (multi-band; same three intervals as #13 but **cubic** where #13 says **orthorhombic**) |
| 15 | `t < 0.97` / `0.97 ≤ t < 1` / `1 ≤ t < 1.05` / `t ≥ 1.05` → monoclinic+orthorhombic / tetragonal / cubic / hexagonal | first-hand | Vu et al. 2023, *Inorg. Chem.* **62** 20020, Table 1 (`S4c`) — a printed four-band table |
| 16 | `0.97 < t < 1.0` tetragonal; `1.0 < t < 1.05` cubic; `t > 1.05` hexagonal; `t < 0.97` orthorhombic/monoclinic | first-hand | Rahmani et al. 2022, *RSC Adv.* **12** 34503; repeated by Hosen et al. 2023, *RSC Adv.* **13** 17545 |
| 17 | `0.9 < t < 1.10` cubic; `0.81 < t < 0.9` **tetragonal and orthorhombic** | first-hand | Rogalski et al. 2024, *Materials* **17** 4029 (`S4d`) — tetragonal placed **below** 1 |
| 18 | `0.89 < t < 1.0` cubic; `0.71 < t < 0.9` tetragonal or orthorhombic; `t > 1` hexagonal; overall `0.81 < t < 1.11` | first-hand | Lê et al. 2023, *Nano Convergence* **10** 47 (`S4e`) |
| 19 | `t = 1` ideal; `t < 1` tilting; `t > 1` → **hexagonal**; `0.857–1.032` for their 29 cubic oxides | first-hand | Kumar et al. 2008, *Open Appl. Phys. J.* **1** 11 (`S8`) — prints *several* conventions in five sentences |

### T1a — the two bands the dispatch named that are **NOT attested**

| band asked for | finding | evidence |
|---|---|---|
| `0.8 ≤ t ≤ 1.05` | **not found verbatim** anywhere in this round | nearest printed: `0.78 < t < 1.05` (*Chem. Sci.* **15** 11166), `0.75 < t < 1.05` (*Nat. Commun.* **16** 8587), `0.85 < t < 1.05` (*Chem. Rev.* **126** 9725) |
| `1.0 ≤ t ≤ 1.1` for tetragonal/ferroelectric | **not found as a band.** Only the *half-open* motif `t > 1` is printed, and the distortion it is attached to is **contested** | `t > 1 favors a tetragonal or hexagonal structure` (*Materials* **18** 1937); `a tetragonal phase may be formed if t > 1.0` (*Materials* **16** 2214); but `0.97 < t < 1.0` tetragonal (`RSC Adv.* **12** 34503) and `0.81 < t < 0.9` tetragonal (`Materials* **17** 4029) put tetragonal **below** 1 |

⇒ **Design consequence (impact on `theories/goldschmidt/plan.md` §1.1 and §4).** The plan's
`hiTetragonal = 11/10` constant and its prose "above which the structure distorts
(tetragonal/ferroelectric, `1.0 < t < 1.1`)" cite a band that no source in this round prints. The
constant may stay as a *declared model parameter* (it is exactly what the plan's parameterized-band
design is for), but the prose must stop presenting `[1, 11/10]` as the literature's tetragonal band.
What the literature prints is the half-open `t > 1`, with no agreement on the name of the distortion.
Both facts belong in the plan's honesty table (§12), not in the definition.

---

## T2 — Shannon radii used by the instance layer, one by one

Primary record: **R. D. Shannon, "Revised effective ionic radii and systematic studies of interatomic
distances in halides and chalcogenides", *Acta Crystallographica Section A* **32** (1976) 751–767,
DOI `10.1107/S0567739476001551`** — **Crossref-verified first-hand** (title, single author
`Shannon`, journal, volume 32, issue 5, pages 751–767, published 1976-09-01, ISSN 0567-7394). The
paper itself is **paywalled** (IUCr returns HTTP 403; not in PMC); **no value in this table was read
off the primary PDF.** Each row is therefore confirmed or left unconfirmed against the retrievable
sources named in the last column.

| ion | coordination / state | plan's value (Å) | printed confirmation | status |
|---|---|---|---|---|
| `Sr²⁺` | XII | `1.44` | **Johnsson & Lemmens 2007**: "`rA = 1.44 Å`" (SrTiO₃, with `rB = 0.605 Å`, `rO = 1.40 Å`); **Talebkeikhah et al. 2026**: "`Sr²⁺ (1.44 Å, coordination number 12)`" | **confirmed** (2 independent sources, both first-hand) |
| `Ti⁴⁺` | VI | `0.605` | **Johnsson & Lemmens 2007**: "`rB = 0.605 Å`"; **Talebkeikhah et al. 2026**: "`Ti⁴⁺ (0.605 Å, coordination number 6)`"; **Reda et al. 2022** `S15`: "the ionic radius of the `Ti4+` ion is `0.605 Å`" | **confirmed** (3 independent sources, first-hand) |
| `O²⁻` | (anion) | `1.40` | **Johnsson & Lemmens 2007**: "`rO = 1.40 Å`"; **Talebkeikhah et al. 2026**: "`O²⁻ (1.40 Å)`" | **confirmed** (2 sources, first-hand). ⚠️ **Convention is not universal**: Kumar et al. 2008 (`S8`) states "the ionic radius of `rA`, `rB` and `rX` (X = O⁻² **is 1.35 Å**)" and its whole Table 1 is computed with 1.35. `rO` moves `t` by ≈ 2 % per 0.05 Å, so **a source's `rO` must be recorded with its `t`** |
| `Ba²⁺` | XII | `1.61` | **Johnsson & Lemmens 2007**: "`rA = 1.61 Å`" (BaNiO₃); Kumar et al. 2008 Table 1 prints `rA = 1.61` for every Ba row | **confirmed** (2 sources, first-hand) |
| `La³⁺` | XII | `1.36` | Kumar et al. 2008 Table 1 prints `La³⁺ = 1.36` for LaTiO₃/LaVO₃/LaMnO₃/LaCoO₃ | **confirmed** (1 source, first-hand) |
| `Na⁺` | XII | `1.39` | Kumar et al. 2008 Table 1 prints `Na⁺ = 1.39` for NaNbO₃ and four other Na rows | **confirmed** (1 source, first-hand) |
| `Ni⁴⁺` | VI | `0.48` | **Johnsson & Lemmens 2007**: "`rB = 0.48 Å`" (BaNiO₃) | **confirmed** (1 source, first-hand) |
| `Ca²⁺` | XII | `1.34` | Kumar et al. 2008 Table 1 prints `Ca²⁺ = 1.34` for CaTiO₃/CaMnO₃/CaCoO₃ | **confirmed** (1 source, first-hand) |
| `Nb⁵⁺` | VI | `0.64` | Kumar et al. 2008 Table 1 prints `Nb⁵⁺ = 0.64` for NaNbO₃ and KNbO₃ | **confirmed** (1 source, first-hand) |
| `Mn³⁺` | VI, **high spin** | `0.645` | **not confirmed** against a retrieved first-hand source this round | **unverified** — the value is consistent with the rest of the set but I could not read it in any retrieved text |

**No mismatch found**: every radius this round could check agrees with the plan's value to the printed
precision. The two cautions are (i) `Mn³⁺(VI,HS) = 0.645` is unverified here, and (ii) a third
convention exists in which the printed `r(O²⁻)` is `1.35 Å` (`S8`), which shifts every derived `t` in
`T3` by ≈ 0.5–1 %.

---

## T3 — printed `t` values for the six instance compounds

`derived (this round)` = recomputed here from `T2`'s radii (`rO = 1.40`) as an **exact rational**;
it is a check on the transcription, not a literature value. "classic band" = `[4/5, 1]`,
"tetragonal band" = `[1, 11/10]` (a **declared model parameter** — see `T1a`).

| compound | printed `t` | source, as printed | radius convention of that source | structure assigned by that source | `derived` with `T2` radii | classic `[4/5,1]` | tetragonal `[1,11/10]` |
|---|---|---|---|---|---|---|---|
| **SrTiO₃** | ⭐ **`0,9x`** (OCR-ambiguous; below 1) | **Goldschmidt et al. 1926 (`S9`)**, his own printed table — ⚠️ **all cells of that table are `OCR-variant`** (image-only scan): usable as evidence that he used his own radii and placed `SrTiO₃` below 1, **not** as an exact number | **Goldschmidt's own radii** `R_A = 1.27`, `R_B = 0.64`, `R_X = 1.32` (as OCR'd) | cubic perovskite (the archetype of his discussion) | — | **holds** | fails |
| **SrTiO₃** | **`1.009`** | Kumar et al. 2008 (`S8`), Table 1 row 67 | `rO = 1.35`; `rA = 1.44`, `rB = 0.605` | `F` (has cubic perovskite structure) | `t² = 161312/160801`, `t = 1.00159…` | **fails** (`t > 1`) | holds |
| **SrTiO₃** | **`1.00`**, described as "the ideal cubic perovskite" | Johnsson & Lemmens 2007 (`S6`) | `rO = 1.40`; `rA = 1.44`, `rB = 0.605` (**identical to ours**) | cubic | `1.00159…` | **fails** | holds |
| **SrTiO₃** | "a Goldschmidt tolerance factor **close to unity**" | Talebkeikhah et al. 2026 (`S16`) | `rA = 1.44` (XII), `rB = 0.605` (VI), `rO = 1.40` | ideal cubic | `1.00159…` | **fails** | holds |
| CaTiO₃ | `0.973` | Kumar et al. 2008 (`S8`), row 92 | `rO = 1.35` | `NF` (no cubic perovskite) | `t² = 150152/160801`, `t = 0.96632…` | holds | **fails** |
| BaTiO₃ | `1.071` | Kumar et al. 2008 (`S8`), row 60 | `rO = 1.35` | `NF` | `t² = 181202/160801`, `t = 1.06154…` | **fails** | holds |
| BaTiO₃ | `1.071` | Reda et al. 2022 (`S15`), Table 1, `x = 0` | `rB(Ti⁴⁺) = 0.605` per that paper's own note | "tetragonal phase" | `1.06154…` | **fails** | holds |
| LaMnO₃ | `0.961` | Kumar et al. 2008 (`S8`), row 136 | `rO = 1.35`; `rA = 1.36`, `rB = 0.645` | `NF` | `t² = 152352/167281`, `t = 0.95433…` | holds | **fails** |
| NaNbO₃ | `0.974` | Kumar et al. 2008 (`S8`), row 21 | `rO = 1.35`; `rA = 1.39`, `rB = 0.64` | `NF` | `t² = 8649/9248`, `t = 0.96707…` | holds | **fails** |
| **BaNiO₃** | **`1.13`** | **Johnsson & Lemmens 2007** (`S6`), printed twice | `rA = 1.61`, `rB = 0.48`, `rO = 1.40` (**identical to ours**) | **hexagonal** variant; face-sharing `[NiO₆]` octahedra | `t² = 90601/70688`, `t = 1.13212…` | **fails** | **fails** |

### T3a — the two rows the dispatch singles out

**(1) SrTiO₃ — the printed discrepancy is real and is an `rO` artefact.**
With **our** radii (`1.44`, `0.605`, `1.40`) the unrounded value is `1.00159 > 1`. Two of the three
Shannon-era sources used the *same* triple and still printed `t = 1.00` (`S6`) or "close to unity"
(`S16`): they **rounded to two decimals**. The third (`S8`) printed `1.009`, because it computed with
`rO = 1.35`. I recomputed `S8`'s own convention: with `rO = 1.35`, `rA = 1.44`, `rB = 0.605` the value
is `1.0091`, i.e. `S8`'s printed `1.009` is **internally exact** and is **not** a misprint. And the
**primary text** `S9` prints `0,9x` (below 1) from **his** radii as OCR'd (`1.27 / 0.64 / 1.32`). So:

- the plan's row `inst_SrTiO3_tooLarge_classic` (`¬ inBandQ 4/5 1 1.44 0.605 1.40`) is **correct**;
- the plan's `inst_SrTiO3_conforms_symmetric` (`1 ± 1/50`) is **correct** (`1/50 = 0.02 > 0.00159`);
- the literature's `t ≈ 1.00` does **not** contradict the kernel: it is the same number at two
  decimals; the `1.009` variant is a different `rO` convention; and Goldschmidt's `0,9x` is a
  different **radius compilation** entirely. ⭐ **The same compound's band verdict flips with the
  radius source: `0,9x` (his radii, inside `[0.8, 1]`) versus `1.00159` (Shannon radii, outside).**
  **This is the honest reading and it should be written into the docstring of the SrTiO₃ rows.**

**(2) BaNiO₃ — the negative row, and our derived value agrees with the printed one.**
`S6` prints `t = 1.13` with `rA = 1.61`, `rB = 0.48` — exactly our radii — and assigns **hexagonal**
variants with face-sharing `[NiO₆]` octahedra. Our exact value is `t = 1.13212`, which rounds to
`1.13`. Therefore the plan's `inst_BaNiO3_not_tetragonal` is **confirmed against the literature's own
number**, and `BaNiO₃` is outside `[1, 11/10]` by `0.032` — a comfortable, not a marginal, negative.
The structure is independently confirmed as hexagonal: `S17` states "`BaNiO₃` is an ideal **2H
hexagonal perovskite** where what are formally `Ni⁴⁺O₆` octahedra share faces and form infinite 1D
chains along the hexagonal c-axis" (space group `P6₃/mmc`).

### T3b — printed values that differ from `derived` (declared, per the round brief)

| row | printed | derived | cause |
|---|---|---|---|
| SrTiO₃ (`S8`) | `1.009` | `1.00159` | different `rO` (`1.35` vs `1.40`) |
| CaTiO₃ (`S8`) | `0.973` | `0.96632` | different `rO` |
| BaTiO₃ (`S8`) | `1.071` | `1.06154` | different `rO` |
| LaMnO₃ (`S8`) | `0.961` | `0.95433` | different `rO` |
| NaNbO₃ (`S8`) | `0.974` | `0.96707` | different `rO` |
| BaTiO₃ (`S15`) | `1.071` | `1.06154` | different `rO`: `1.071` is exactly the `rO = 1.35` value for the `S8` radius set, while `S15`'s own text names only `r(Ti⁴⁺) = 0.605 Å` and `r(Zr⁴⁺) = 0.72 Å` |

`S15` also prints a **series** over `x = 0, 0.1, 0.2, 0.3`: `t = 1.071, 1.064, 1.058, 1.052`, with
`r(Zr⁴⁺) = 0.72 Å` and `r(Ti⁴⁺) = 0.605 Å` per its own text. Recomputation settles its convention: with
`rO = 1.35`, `rA = 1.61` and the linear mixture `rB = (1−x)·0.605 + x·0.72`, the model gives
`1.0706, 1.0643, 1.0582, 1.0520`, i.e. **all four printed values to the printed precision**
(`1.071, 1.064, 1.058, 1.052`). The successive drops `−0.0063, −0.0061, −0.0062` are constant to
three decimals — as the exact shift law requires — and the `−0.007` first step read off the printed
column is a rounding artefact of the two-decimal printing, not a counterexample. **This series is
therefore a usable external illustration of `tolFac_shift`, but only in the source's own convention
(`rO = 1.35`)**: the plan's rows must not mix it with the `rO = 1.40` set. It is an illustration, not
a kernel row — nothing about it may be *proved* from the citation.

⇒ **Convention rule this round recommends recording in `plan.md` §2:** every printed `t` is quoted
**with** the radius triple used by its source; two `t` values for the same compound from sources with
different `r_O` (or different `r_A`) are two different numbers and must not be compared, averaged, or
used to cross-validate each other.

---

## T4 — the coupled / charge-compensated substitution examples (printed)

Full discussion and the formalizable implications: record §S3.2 / §S3.2.1. This table is the numbers.

| # | pair as printed | increments as printed | host | source (record id) |
|---|---|---|---|---|
| **P0** | `NaAlSi₃O₈` / `CaAl₂Si₂O₈` (plagioclase) | ⭐ **Goldschmidt's own documented coupled example**: a `(+1,+4) ↔ (+2,+3)` swap (`Na⁺+Si⁴⁺ ↔ Ca²⁺+Al³⁺`). He prints the *condition* ("corresponding amounts of positive and corresponding amounts of negative building blocks"), **not** the increments | framework silicate | Goldschmidt et al. 1926, printed p. 81 (`S9`) |
| **P1** | `La³⁺` and `Na⁺` as **heterovalent** ions, "as represented by `A²⁺B⁴⁺O₃`" | `Δz = +1` (for `A²⁺` → `A³⁺`) paired with `Δz = −1` (for `A²⁺` → `A⁺`); **the source prints the host formula and the conclusion, not the two increments** | oxide perovskite, A site | Li, Zhao, Fan, Li, Tan, Wang et al., *Adv. Sci.* **13**, e16938 (2025), `10.1002/advs.202516938` (`PMC12766988`) |
| **P2** | `Sm³⁺` replacing `Bi³⁺` **and** `Na⁺`, with the printed arithmetic `0.5 − 0.0027 × 3/1 = 0.4919` | ⭐ **`3 Na⁺ per 1 Sm³⁺`** — the compensating-partner ratio printed as `3/1`; the isovalent half is `Sm³⁺ ↔ Bi³⁺` at `1:1` | oxide perovskite, `Bi₀.₅Na₀.₅TiO₃`-based | Tang, Hu, Koval, Zeng et al., *ACS Appl. Mater. Interfaces* **17**, 53780–53790 (2025), `10.1021/acsami.5c12016` (`PMC12464909`) |
| **P3** | `Pr³⁺ ↔ Cs⁺` paired with `Ni²⁺ ↔ Pb²⁺`; "self-compensating mechanism … maintains overall charge neutrality … total cationic charge remains `+4` per unit cell" | `Δz = +2` paired with `Δz = 0` | **halide** perovskite, `CsPbCl₃` | *RSC Adv.* **15** (2025), `10.1039/d5ra07356a` (`PMC12757862`) |
| — | `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` | — | — | ⚠️ **NOT DOCUMENTED** — no retrieved source, and not the primary memoir, prints this pair. The plan's `I6` row family should replace it (with `P1`/`P2`) or mark it as undocumented |

⭐ **The primary text's own words about the charge rule** (`S9`, printed p. 81, first-hand):
*"Wir dürfen uns aber nicht wundern, daß ein Unterschied der Valenz in unserem Isomorphiegesetz nicht
Ausdruck findet. Der Unterschied der Valenz ist nämlich bereits in unsern Größen der scheinbaren
Radien mit einkalkuliert."* — i.e. Goldschmidt **declines** to make valency a criterion because it is
already folded into his "apparent radii". **So `∑ dz = 0` is not his rule**; it is a later
systematization, and `plan.md` §12 must say so.

---

## T5 — the radius-ratio criterion, as printed

| criterion | as printed | status | source |
|---|---|---|---|
| ⭐ Pauling's radius-ratio table, **as Pauling's** | `Rcation/Ranion` → `1.0` = 12 (hexagonal or cubic closest packing); `1.0 - 0.732` = 8 Cubic; `0.732 – 0.414` = 6 Octahedral; `0.414 – 0.225` = 4 Tetrahedral; `0.225 – 0.155` = 3 Triangular; `< 0.155` = 2 Linear | **first-hand** | Jackson & Solomatova, CIDER 2016 slides (`S13`), "Pauling's First Rule — The Radius Ratio Rule" |
| octahedral factor `μ = r_B/r_O`, the **geometric** limit for 6-fold coordination | `rB/rX value of octahedron BX6 is ranging from 0.414 to 0.732` | **first-hand** | Kumar et al. 2008 (`S8`), §Results |
| the **same** interval read as the radius-ratio rule for 6-fold | `μ > 0.41` for the iodides; `μ > 0.425` for the oxides; boundary "corresponds exactly to the geometric limit for octahedral coordination of the B site of `μ = 0.41`" | **first-hand** | Travis et al. 2016 (`S3`) |
| octahedral factor as a *separate* axis of a `t`–`μ` structure map | "A plot of `t` against `μ` can then be constructed and used as a structure map" | **first-hand** | Travis et al. 2016 (`S3`) |

⭐ **`0.732` therefore appears in two different roles in the retrieved corpus, and they must not be
merged.**

1. `S13` prints it as **Pauling's** radius-ratio edge for **8-fold** coordination, on the ratio
   `r_cation/r_anion` — this is the criterion the dispatch names (`r_cation/r_anion ≥ 0.732` for
   8-fold/cubic).
2. `S8` prints the *same number* as the **upper end of the 6-fold octahedral-factor interval** for
   `rB/rX`. The interval `0.414–0.732` is printed by `S8` as a 6-fold statement, which is a
   **convention collision with Pauling's table** (`0.732–0.414` = 6-fold octahedral is the *same*
   interval read with Pauling's orientation). So the number is not in dispute; the **ratio it is
   attached to** and the **role (threshold vs interval end)** are.

Two consequences for the plan:

1. The plan has no `0.732` declaration and this round does **not** add one; the number is recorded
   above only because the dispatch asked for it, and because §S1.3 of the record needs it to keep the
   two criteria apart.
2. The radius-ratio rule and the tolerance factor are **different criteria on different ratios**
   (`r_B/r_O` or `r_cation/r_anion` vs `(r_A+r_O)/(√2(r_B+r_O))`). `S8` explicitly builds a
   **two-axis** structure map ("octahedron factor constructs another axe") and calls the octahedral
   factor "as important as the tolerance factor". So the plan's radius-window equivalence (plan §6)
   must never be read as a statement about `μ`; `μ` stays outside the theory (plan §1.4), recorded
   rather than silently omitted.

---

## T6 — internal consistency of the model's own two contact equations

`S6` prints the ideal-cubic relation `a = 2(r_A + r_O) = 2√2 (r_B + r_O)` — its eq. (1), where the
source's own typesetting renders the `√2` as a bare `2`; read as the standard form. This lets the
model's two quantities be checked against a printed number:

| quantity | printed | derived from `T2` radii (`rB = 0.605`, `rO = 1.40`) | verdict |
|---|---|---|---|
| `latticeOf rB rO = 2(r_B + r_O)` | `S16`: SrTiO₃ "crystallizes in an ideal cubic perovskite structure with a lattice constant of approximately **3.905 Å**" | `4.01 Å` | agrees to ≈ 2.6 %: the printed value is the **measured** lattice constant, the model's is the **ideal contact** value |
| `idealAO rB rO = √2(r_B + r_O)` | **not printed by any retrieved source** | `2.835 Å` | a purely internal derived quantity |
| `tolFac` with `T2` radii | `S6`: `t = 1.00`; `S16`: "close to unity" | `1.00159` | agrees at the printed precision (see `T3a`) |

This table exists so that `latticeOf` / `idealAO` are never read as literature-backed numbers: the
**only** literature-backed quantity in the instance layer is `t`, and even that only at two decimals.
The plan's `tolFac_eq_distRatio` is an internal identity given the declared geometry, **not** a
citation.

---

## T7 — sources whose bibliographic record is Crossref-verified (key for checkability)

| id | record as returned by `api.crossref.org/works/<DOI>` | DOI |
|---|---|---|
| `S1` | Goldschmidt, *Die Gesetze der Krystallochemie*, Die Naturwissenschaften **14** (21), 477–485, 1926-05 | `10.1007/BF01507527` |
| `S9` | ⭐ **primary text** — Goldschmidt, Barth, Lunde & Zachariasen, *Geochemische Verteilungsgesetze der Elemente VII: Die Gesetze der Krystallochemie*, Skrifter utgitt av Det Norske Videnskaps-Akademi i Oslo, I. Mat.-Naturv. Klasse **1926, No. 2**, 116 pp., Oslo: Jacob Dybwad (scan; **no DOI**) | OPUS `docId/19275`, URN `urn:nbn:de:hebis:30-1038510` |
| `S2` | Shannon, *Revised effective ionic radii …*, Acta Cryst. A **32** (5), 751–767, 1976-09-01 | `10.1107/S0567739476001551` |
| `S3` | Travis; Glover; Bronstein; Scanlon; Palgrave, *On the application of the tolerance factor to inorganic and hybrid halide perovskites: a revised system*, Chem. Sci. **7**, 4548–4556, 2016 | `10.1039/c5sc04845a` |
| `S6` | Johnsson; Lemmens, *Crystallography and Chemistry of Perovskites*, in *Handbook of Magnetism and Advanced Magnetic Materials* vol. 4, Wiley 2007 | `10.1002/9780470022184.hmm411` (text read via `arXiv:cond-mat/0506606`) |
| `S7` | Bartel; Sutton; Goldsmith; Ouyang; Musgrave; Ghiringhelli; Scheffler, *New tolerance factor to predict the stability of perovskite oxides and halides*, Sci. Adv. **5** (2), eaav0693, 2019-02 | `10.1126/sciadv.aav0693` |
| `S8` | A. Kumar; A. S. Verma; S. R. Bhardwaj, *Prediction of Formability in Perovskite-Type Oxides*, The Open Applied Physics Journal **1**, 11–19, 2008-12-16 (Crossref record verified) | `10.2174/1874183500801010011` ✔ |
| `S11` | Glazer, *The classification of tilted octahedra in perovskites*, Acta Cryst. B **28**, 3384–3392, 1972-11-15 | `10.1107/S0567740872007976` |
| `S12` | Parker; Fleischer, *Geochemistry of niobium and tantalum*, U.S. Geological Survey Professional Paper **612**, 1968, §"Isomorphous substitution", printed p. 13 | `10.3133/pp612` |
| `S13` | Jackson; Solomatova, *Mineral Physics 1: Earth Mineralogy and Phase Diagrams*, CIDER 2016 short-course slides (Goldschmidt-rules slides credited to A. Kavner, UCLA) — **no DOI** | `seismo.berkeley.edu/wiki_cider/images/e/eb/Jackson_CIDER_MinPhys.pdf` |
| `S14` | Ankara University lecture notes, *İyonik yer değiştirme (Substitution) — Goldschmidt kuralları* — **no DOI** | `acikders.ankara.edu.tr/pluginfile.php/16721/mod_resource/content/0/MKK-7.pdf` |
| `S15` | Reda, El-Dek & Arman, *J. Mater. Sci.: Mater. Electron.* **33**, 16753–16776, 2022 | `10.1007/s10854-022-08541-x` |
| `S16` | Talebkeikhah; Rad; Faghani; Zokaeian; Hernádi; Melchionna; Fornasiero; Nishioka, *Beyond SrTiO₃: Emerging Perovskite Photocatalysts for Solar Water Splitting*, Materials **19** (17), 3635 (2026-08-26) | `10.3390/ma19173635` |
| `S17` | *Hidden Hydroxides in KOH-Grown BaNiO₃ Crystals* (first-hand via `arXiv:2306.05488`) | `arXiv:2306.05488` |
| `S19` | coupled-substitution examples P1–P3 (§T4) | `10.1002/advs.202516938` · `10.1021/acsami.5c12016` · `10.1039/d5ra07356a` |

Every DOI in this table was resolved through `api.crossref.org/works/<DOI>` during this round, and
the volume / page / date columns are the values Crossref returned — **except** `S9`, `S13` and `S14`,
which have **no DOI** and were read either as a scan (`S9`, via delegate OCR; the OPUS host is behind
an Anubis bot wall for this session) or as lecture PDFs (`S13`, `S14`). `S3`, `S7`, `S16` are open
access and their full text was read first-hand.
