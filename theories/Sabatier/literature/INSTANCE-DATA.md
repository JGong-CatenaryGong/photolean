# theories/Sabatier/literature/INSTANCE-DATA.md — full transcriptions of the secondary instance tables

> Companion to `theories/Sabatier/LITERATURE.md` (the authority; it names every source as S<n>).
> This file exists only to keep the *long* tables out of the record's main text. Look-up keys, loci and
> statuses are the record's; nothing here is a new finding. Scratch/PDFs are **not** stored in the repo
> (`/tmp/sabatier/`), per the engine contract.
> `first-hand` = transcribed by the record's own read; `second-reader` = transcribed from a delegate's
> read of the retrieved text and **to be re-read before use**.

---

## T1 — Yang, Patil, McKone & Saidi, *Catal. Sci. Technol.* **11**, 6832 (2021), Table S2 (arXiv:`2109.04219` SI)

Calculated **DFT** `ΔG_H` (eV), four functionals. **status `first-hand`** (record's own read of the
arXiv PDF, which contains the SI). ⚠️ The `Mo / PBE+vdW` entry `3.620` is printed as such and is a
manifest outlier — do not build a Lean row on it without a second read of the SI.

| metal | PBE | RPBE | PBE+vdW | RPBE+vdW |
|---|---|---|---|---|
| Ag | 0.416 | 0.565 | 0.381 | 0.527 |
| Au | 0.418 | 0.574 | 0.388 | 0.532 |
| Bi | 1.040 | 1.127 | 1.004 | 1.099 |
| Cd | 1.051 | 1.038 | 1.058 | 1.031 |
| Co (Fm3̄m) | −0.355 | −0.202 | −0.411 | −0.252 |
| Co (P6₃/mmc) | −0.352 | −0.201 | −0.407 | −0.250 |
| Cu | 0.040 | 0.188 | −0.002 | 0.147 |
| In | 0.847 | 0.948 | 0.813 | 0.912 |
| Ir | −0.208 | −0.081 | −0.273 | −0.136 |
| Mo | −0.453 | −0.321 | 3.620 ⚠️ | −0.352 |
| Ni | −0.388 | −0.231 | −0.445 | −0.280 |
| Pd | −0.286 | −0.123 | −0.359 | −0.176 |
| Pt | −0.192 | −0.038 | −0.232 | −0.082 |
| Re | −0.293 | −0.154 | −0.333 | −0.195 |
| Rh | −0.270 | −0.116 | −0.318 | −0.159 |
| Ru | −0.330 | −0.180 | −0.375 | −0.220 |

Figure 1 of the same paper uses the **RPBE+vdW** column; the paper's own fitted descriptor–prefactor
relation is `ln(k₀) = 23.16|ΔG_H| + 3.17`, `r² = 0.82` (Fig. 3a caption).

## T2 — Nørskov et al., *J. Electrochem. Soc.* **152**, J23 (2005), Table II, printed p. J25

**DFT**, 0.25 ML, fcc(111); referenced to gas-phase H₂O (`n = 1` for OH, `n = 2` for O).
**status `first-hand`.** The last column is **the record's arithmetic** `ΔG_O − ΔG_OH`.
⚠️ This is a **metal** family; the OER volcano's apex (1.60 eV) belongs to **oxide** surfaces with their
own reference — keep them as separate Lean families.

| metal | ΔG_OH / eV | ΔG_O / eV | ΔG_O − ΔG_OH / eV [arith] |
|---|---|---|---|
| Pt | 1.40 | 1.62 | 0.22 |
| Rh | 0.69 | 0.49 | −0.20 |
| Ir | 0.98 | 1.05 | 0.07 |
| Pd | 1.27 | 1.58 | 0.31 |
| Ni | 0.48 | 0.39 | −0.09 |
| Cu | 0.72 | 1.25 | 0.53 |
| Ag | 1.07 | 2.17 | 1.10 |
| Au | 1.84 | 2.80 | 0.96 |
| Co | 0.27 | −0.17 | −0.44 |
| W | −0.45 | −2.01 | −1.56 |
| Mo | −0.26 | −1.57 | −1.31 |

The paper's own caveat (printed p. J25): Mo and W "should be covered by surface oxygen under the
conditions of interest here", so their measured currents are of the oxide, not the metal.

## T3 — Yang et al. 2021, Table 1 (arXiv `2109.04219`): collected **experimental** `j₀`

**status `first-hand`.** A cm⁻², with electrolyte, temperature and the source's own reference number.

| electrode | j₀ / A cm⁻² | electrolyte | T / K |
|---|---|---|---|
| Pt(111) | 4.5×10⁻⁴ | 0.05 M H₂SO₄ | 303 |
| Pt(100) | 6.0×10⁻⁴ | 0.05 M H₂SO₄ | 303 |
| Pt(110) | 9.8×10⁻⁴ | 0.05 M H₂SO₄ | 303 |
| Pt/C | 1.6×10⁻² | 0.2 M H₃PO₄ | 293 |
| Pt/C | 1.2×10⁻¹ | 0.1 M HClO₄ | 313 |
| Ir/C | 3.6×10⁻² | 0.1 M HClO₄ | 313 |
| Ir/C | 1.28×10⁻² | 0.2 M H₂SO₄ | 293 |
| Pd | 1.9×10⁻⁴ | 0.5 M H₂SO₄ | — |
| Pd/C | 3.0×10⁻³ | 0.1 M HClO₄ | 313 |
| Pd/C | 8.4×10⁻⁴ | 0.1 M HClO₄ | 293 |
| Rh/C | 5.2×10⁻³ | 0.1 M HClO₄ | 313 |
| Rh/C | 6.7×10⁻³ | 0.1 M HClO₄ | 293 |
| Ru | 4.5×10⁻³ | 1 M HCl + NaCl | 298 |
| Cu | 1.45×10⁻⁷ | 0.1 N HCl | — |
| Co | 3.6×10⁻⁶ | 1 M H₂SO₄ | 293 |
| Ni | 2.6×10⁻⁶ | 0.5 M H₂SO₄ | 295 |

## T4 — Zheng et al., *Sci. Adv.* **2**, e1501602 (2016), Table 1: experimental BEP coefficients

**status `first-hand`** (OA full text, `PMC4803484`). `β` and `A` fitted to
`i₀ = A exp(−βFE_peak/RT)`; `E_a` by RDE in 0.1 M KOH and by an H₂-pump at pH 0; `β_Ea` from
`ΔE_a = βFΔE_peak`. The paper prints `0 < β < 1` in its Eq. (1).

| catalyst | β | A | E_a (0.1 M KOH) / kJ mol⁻¹ | E_a (H₂ pump) / kJ mol⁻¹ | ΔE_peak / V | β_Ea |
|---|---|---|---|---|---|---|
| Pt/C | 0.5 | 59 | 29.6 ± 0.4 | 16 ± 2 | 0.17 | 0.8 |
| Ir/C | 0.8 | 68 | 32.8 ± 0.4 | 19 ± 3 | 0.20 | 0.7 |
| Pd/C | 0.6 | 37 | 38.9 ± 3.0 | 31 ± 2 | 0.14 | 0.6 |
| Rh/C | 0.6 | 36 | 26.6 ± 0.7 | 28 ± 1 | — | — |

## T5 — Martínez-Alonso, Guevara-Vela & LLorca, *Phys. Chem. Chem. Phys.* **24**, 4832 (2022)

Table 1, printed p. 13 (arXiv:`2202.01647`); `G_adsH` (eV, DFT, 300 K). **status `second-reader`.**
Its Eq. (4) is `G_adsH = E_adsH + 0.24 eV`. ⭐ The only source found that prints **Fe** (and Ru):

`Pt −0.25 · Au 0.33 · Cu −0.01 · Ag 0.41 · Pd −0.30 · Ni −0.28 · Ir −0.15 · Rh −0.29 · Cd 1.05 ·
Zn 0.91 · Co −0.27 · Nb −0.65 · Mo −0.50 · W −0.51 · Re −0.56 · Ru −0.40 · Fe −0.35 · Os −0.35 ·
Hf −0.84 · Ta −0.75 · V −0.66 · Cr −0.82 · Tc −0.48`
