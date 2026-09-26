# figures/ — figure sources and provenance

This directory holds the three manuscript figures, the one script that regenerates them, and this
provenance note. The manuscript includes the **vector PDFs**; the PNGs are 300-dpi previews for
screens and for a first visual check.

```bash
python3 figures/make_figures.py                  # writes figures/{fig1,fig2,fig3}_{...}.{pdf,png}
python3 figures/make_figures.py --outdir /tmp/x   # optional output directory
```

The script runs in a few seconds, needs only `matplotlib` and `numpy` (plus the standard library),
uses **no network**, and writes **only** into its output directory. It resolves the repository root
by walking up to the directory that holds `proofs/ENGINE.yml`, so it can be started from any working
directory. Matplotlib's config directory must be writable; in an environment where it is not, run
`export MPLCONFIGDIR=.lake/tmp/figs-scratch/mpl` first (the repository's scratch convention).

**Determinism.** The graph layout is a hand-placed coordinate table, there is no random number
generator anywhere, the PDF carries no `CreationDate` and `pdf.fonttype = 42` embeds TrueType
outlines. Reruns of the same tree therefore produce byte-identical files.

**Provenance.** The script prints, for each figure, every numeric value it drew and where that value
came from: a command it ran, a repository file it read, or a definition transcribed from a Lean
source. Before drawing, it re-checks that each transcribed formula is still present verbatim in its
Lean source (a "transcription guard": a moved or edited definition aborts the run instead of drawing
a stale formula). Values that could not be recomputed are printed with the label
`(manuscript constant, not recomputed)`.

Where a census tool is present, the script prefers it: if `tools/claims.json` exists, per-theory
authority counts, a total public-delivered count and the pair accounting (edges / registered
absences) are read from it (tolerant key search); every missing piece falls back to the per-theory
fidelity probes (and, for the pair accounting, to the release-doc constant).

---

## fig1_relation_graph — the relation graph

`fig1_relation_graph.pdf` / `.png` (vector + 300-dpi preview).

*What is plotted.* The seventeen theories as nodes on one graph plus the shared kernel drawn in
white. Node **area** is proportional to the theory's statement-authority count and the number inside
each node is that count; node **colour** encodes the family of the manuscript caption (F1 two-parabola
family, F1′ unequal-curvature generalization, F1″ photophysical kernel copies, F2 excited-state kinetic
bookkeeping, F3 geometry/radiation laws, F4 nonadiabatic dynamics at a CI). Edges are drawn in seven
classes: dotted grey = certificate pins (kernel copies; §1/§11/§12, plus the A1 tie-backs), red-brown
solid = the two-way equivalences E1–E7, dashed red = the one-way entailments O1–O3, dark blue =
composition edges carrying their premises (including the conditional Kasha→Marcus edge, premise
`hic`), light blue = the `QuantumYield` algebraic spine, grey dash-dot = registered shape look-alikes
(similarity recorded, no edge asserted), purple = the adjudicated Kasha–Kasha–Vavilov relation. The
three adjudications are marked by the coloured badges A1 (orange), A2 (purple), A3 (blue) and spelled
out in the strip below the graph.

*Data sources.*
`python3 theories/BEP/probes/bep-fidelity.py --theory <T>` for each of the seventeen theories (the
`skeleton declarations` line) supplies every node number and the total 1153; `PhotoLean/Kernel.lean`
is counted by the script for the kernel node (6 definitions + 2 theorems); `PhotoLean/Relations.lean`
is parsed for the section count and the number of registered declarations (78 in 17 sections);
`C(17,2) = 136` is computed with `math.comb`. The **edge inventory and its Lean rows** are a
hand-written table inside `make_figures.py`, one row per edge naming the declaration that carries it
(`transfer_eq_tsCoord_bridge`, `kashaWithin_one_marcus` with `hic`, `raci_qy_eq_yieldOf_two_channel`,
…); the families are transcribed from the caption and cross-checked against
`theories/GRAPH-REPORT.md` §1.1. The edge-graph arc curvatures are chosen by a deterministic scan over
a fixed candidate list (printed in the manifest) so that no edge runs through a node disk.

*Honest notes.* The caption's family list covers sixteen of the seventeen nodes; **Sabatier** carries
no family in it and is therefore drawn in its own colour (teal), labelled as a volcano over the BEP
barrier. Three of the six dash-dot entries (Goldschmidt↔Sabatier, Einstein↔StokesShift,
Förster↔Goldschmidt) are plan-level shape registrations with no Lean row; they are drawn dash-dot
precisely because no edge is asserted.

---

## fig2_adjudications — the three adjudications

`fig2_adjudications.pdf` / `.png`.

*Panel (a) — A1, the symmetry factor.* A colour map of
`x* = √k_p / (√k_r + √k_p)` over `(k_r,k_p) ∈ [0.01,4]²`, computed with numpy from the definition
transcribed out of `PhotoLean/SymmetryFactor/Basic.lean` (`tsCoordZero`), with the equal-curvature
diagonal `k_r = k_p` in black; the two witnesses `(1,4) ↦ 2/3` (blue) and `(4,1) ↦ 1/3` (red) are
marked and annotated, and the text states the verdict
`BetaHalfReading kr kp ↔ kr = kp (0 < kr, 0 < kp)` (`PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants`)
together with uniqueness on `[0,1]` without calculus
(`PhotoLean.SymmetryFactor.crossing_unique_in_unit_interval`).

*Panel (b) — A2, Kasha vs Kasha–Vavilov.* Two two-level schemes — left: the Kasha regime (fast
`S₂ → S₁` internal conversion, emission only from `S₁`); right: the anti-Kasha regime (observable
`S₂` emission). The rate labels (`rad 0`, `rad 1`, `ic 0`, `ic 1`, `upperYield`, `fluoYield`) are the
delivered names of `PhotoLean/Kasha/Basic.lean`; the four conjuncts of the verdict are those of
`PhotoLean.Relations.kv_d2_verdict` (re-export of `KashaVavilov.d2_verdict`), and the boundary row is
`PhotoLean.Relations.kv_antiKasha_boundary` (`0 < upperYield ↔ ¬ KashaRule` under `RateData`).

*Panels (c) — A3, Stern–Volmer.* The intensity panel plots the common linear curve for matched
parameters (`svRatioDyn 2 1 q = 1 + KSV·q` versus `svRatioStat (KSV 2 1) q`, which coincide pointwise
at every concentration — the non-injectivity of the intensity-only channel) and the upward-curving
coexistence curve `svRatioBoth 2 1 1 q`; the second-difference value drawn is recomputed in numpy and
equals the Lean row `SternVolmer.mixed_witness` (= 1). The lifetime panel plots the dynamic ratio
`τ₀/τ = 1 + KSV·[Q]` rising against the static `τ₀/τ ≡ 1` flat, annotated with
`LifetimeTracks m k₀ k_q K_a ↔ m = Mech.dyn` (`sv_identifiability_boundary`, weakest premise `0 < K_a`;
the three-part verdict `sv_d1_verdict` adds `k₀ ≠ 0`). All curves are evaluated from the definitions
transcribed out of `PhotoLean/SternVolmer/Basic.lean` (`dynDecay`, `svRatioDyn`, `tauRatioDyn`,
`svRatioStat`, `KSV`, `svRatioBoth`), at the parameters `(k₀,k_q,K_a) = (2,1,1)` of the delivered
instance.

---

## fig3_scale_and_gates — scale, composition, gates

`fig3_scale_and_gates.pdf` / `.png`.

*Panel (a) — scale.* Horizontal bars of the seventeen per-theory statement-authority counts (probe
output again), coloured by family, with the total 1153 and the module count 92 in the title. **All
recomputed:** the authority total (1153), the theory-module count (92, the script's own scan of
`PhotoLean/<T>/*.lean`), the source-level public declaration count (1214 public + 48 `private`
helpers, the script's scan with the fidelity probe's declaration regex — 1214 agrees with the probe
rule `word-for-word + delivered-not-in-authority` = 1153 + 61) and the delivered total (1214). The
manuscript's 1,214 public delivered declarations are therefore **independently recomputed, not
copied**; `tools/claims.json` did not exist when the figures were generated.

*Panel (b) — the composition of the 78 relation-module declarations.* The stacked bar shows the
**manuscript caption's** split — certificates 15 / equivalence-entailment-bridge 22 / composition 26 /
adjudication 8 / RACI 5 / other 2 — which is a hard-coded constant in the script and printed with the
label `manuscript caption constant, not recomputed`. Next to it the script prints its **own
section-derived split** parsed from `PhotoLean/Relations.lean`: certificates 15 (§1's 8 `rfl` rows +
§12's 7 definitional pins), equivalence/entailment/bridge 22 (§2–§6 = 20 plus the §11 tie-backs),
composition 30 (§7–§9, §15), adjudication 6 (§11 verdicts, §13, §14), RACI 5 (§17), other 0 — plus the
per-section table (§1 8, §2 6, §3 3, §4 4, §5 4, §6 3, §7 5, §8 6, §9 7, §10 0, §11 4, §12 7, §13 2,
§14 2, §15 12, §16 0, §17 5). The two splits disagree on four §11/§15 rows whose class the section
markers do not determine; the figure prints both rather than forcing a match.

*Panel (c) — verification gates.* A checklist, each item with its provenance:
the whole-tree gate (`verdict: PASS`, `build: OK`, `scan: clean`, 17/17 leaf planes) is **read** from
the recorded run in `theories/GRAPH-REPORT.md` — `make_figures.py` deliberately does not run
`lake build`, because that would write build artifacts outside its output directory; the leaf data
plane (17/17), the fidelity probes (17/17, 0 signature differences) and the delivered totals are
recomputed live by the script; the permitted axiom footprint `[propext, Classical.choice, Quot.sound]`
is read from `proofs/ENGINE.yml` (`ALLOWED_AXIOMS`); `C(17,2) = 136` is computed. The pair accounting
The pair accounting is **read from `tools/claims.json`** when the census has run
(`26 machine edges + 110 registered absences = 136`, 0 unaccounted; `tools/counts.py` recomputes it
with one citation per pair), and falls back to the release-doc constant otherwise — with the
provenance line saying which of the two was used.

---

## What is recomputed, and what is not

| value | status |
|---|---|
| per-theory authority counts, 1153 total, 61 probe-registered auxiliaries, 1214 delivered | **recomputed** — 17 live `bep-fidelity.py` runs when `tools/claims.json` is absent, otherwise read from the census (which itself runs the same 17 probes and marks the quoted totals MATCH); run `python3 tools/counts.py --md` after any delivery and before regenerating the figures |
| 92 theory modules, 1214 public declarations (+48 private) | **recomputed** — the script's source scan |
| 78 relation declarations, 17 sections, per-section counts, 15 certificate rows, 11 `rfl`-closing rows | **recomputed** — parse of `PhotoLean/Relations.lean` |
| kernel node (6 defs + 2 theorems), `C(17,2) = 136`, `x*(1,4) = 2/3`, `x*(4,1) = 1/3`, the Stern–Volmer curves and `mixed_witness`'s second difference `= 1` | **recomputed** from Lean-sourced formulas (transcription guard) |
| leaf planes 17/17, fidelity probes 17/17 with 0 differences, allowed axioms | **recomputed / read** from `theories/*/`, the probes, `proofs/ENGINE.yml` |
| gate verdict PASS / build OK / scan clean | **read** from the recorded run in `theories/GRAPH-REPORT.md` |
| relation-class split 15/22/26/8/5/2 | **manuscript constant**; `tools/counts.py` recomputes **15/22/30/6/5/0** and marks the caption's split `DIFF` (the four disputed §11/§15 rows are listed in `tools/README.md` "Classification decisions"); the figure prints both |
| pair accounting 26 machine edges + 110 absences (0 unaccounted) | **read from `tools/claims.json`** when present (recomputed by `tools/counts.py`, one citation per pair); release-doc fallback otherwise |
| the caption's family assignment (16 of the 17 nodes) | **transcribed** from the caption/`theories/GRAPH-REPORT.md` §1.1; Sabatier left unassigned there and drawn in its own colour |

## Files

| file | what it is |
|---|---|
| `make_figures.py` | the generator; prints the provenance manifest |
| `fig1_relation_graph.pdf` / `.png` | relation graph, vector + preview |
| `fig2_adjudications.pdf` / `.png` | A1/A2/A3 panels, vector + preview |
| `fig3_scale_and_gates.pdf` / `.png` | scale bars, relation-class composition, gate checklist |
| `README.md` | this file |
