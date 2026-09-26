# docs/CLAIMS.md — manuscript claim → deciding artifact

**Purpose.** Every quantitative or named claim in the manuscript
(*The Same and Not the Same: A Machine-Checked Genealogy of Photochemical Theory*) resolves to one of
three things in this repository: a **Lean declaration** (fully qualified, kernel-checked), a
**command** whose output is the claim, or a **registered convention** (documented, not proved). This
file is that mapping. A claim whose row says `command` and whose command does not reproduce at the
release commit is a defect in the manuscript, not in the code.

**Tree-state discipline.** Every row below is meaningful only together with the commit it was run at.
Record `git log -1 --oneline` and `git status --short` next to any result you quote.

Legend: `[D]` declaration · `[C]` command · `[V]` convention/registration.
All `#print axioms` of the named theorems are exactly
`[propext, Classical.choice, Quot.sound]`; check with
`proofs/scripts/axioms.sh <Module> <fully.qualified.name>`.

---

## 1. Corpus calibration (§2.1) and Table 1

| claim | artifact | how to check |
|---|---|---|
| seventeen theories | the 17 node names are fixed in `tools/counts.py` and in `theories/*/` | `[C]` `python3 tools/counts.py --md` |
| 92 theory modules; 95 `.lean` files | `[C]` | `find PhotoLean -name '*.lean' \| wc -l`; per-theory counts from `tools/counts.py` |
| statement authority 1,153 declarations | `[C]` per-theory probes | `python3 theories/BEP/probes/bep-fidelity.py --theory <T>` for the 17 theory names; sum the `delivered, word-for-word` column |
| 1,214 public delivered declarations | `[C]` probe rule: `word-for-word` + `delivered, not in authority`, summed over the 17 theories (excludes `private` helpers and the single `instance`; documented in `tools/README.md`) | `python3 tools/counts.py --md` |
| 17/17 probes passed, 0 signature discrepancies, 0 undelivered | `[C]` | the loop above; each probe must print `not delivered yet : 0` and `signature differences : 0` |
| each theory's task board carries an independent verifier PASS | `[V]` | `grep -il 'verifier' theories/*/TASKS.md` and read the record |
| whole-tree gate `verdict: PASS` | `[C]` | `proofs/scripts/check.sh --strict` (expect `build: OK`, scan `clean`, 17/17 leaf planes, `verdict: PASS`) |
| 15 `rfl` kernel certificates | `[D]` `PhotoLean.Relations.{kernel_barrier_eq_marcus, kernel_barrier_eq_hammond, kernel_barrier_eq_bep, kernel_reverseBarrier_eq_hammond, kernel_tsCoord_eq_hammond, kernel_transfer_eq_bep, kernel_reactantSurface_eq_hammond, kernel_productSurface_eq_hammond, eg_barrier_eq_kernel, eg_rate_eq_marcus, eg_invertedGap_iff_marcus, ss_s0Surface_eq_kernel, ss_s1Surface_eq_kernel, icvscic_barrier_eq_kernel, icvscic_icRate_eq_marcus}` | `grep -c ':= rfl$' PhotoLean/Relations.lean` (8) and the §12 certificate calls (7) |
| layered regression alarm: perturbing `Kernel.barrier` fails inside `Kernel`, perturbing `Kernel.reactantSurface` fails in the StokesShift copy | `[C]` perturbation experiment in a scratch copy | see `docs/REPRODUCE.md` §5 (recipe and measured messages) |

## 2. The relation graph (§2.3)

| claim | artifact | how to check |
|---|---|---|
| `Relations.lean` holds 78 declarations in 17 sections | `[C]` | `python3 tools/counts.py --md`; section markers `/-! ## ` |
| edge classes: certificates / equivalences / one-way entailments / compositions / look-alikes / no-edge / adjudications | `[D]` examples: `transfer_eq_tsCoord_bridge` (E1), `epBounds_of_reactionRegion` (O1), `kashaWithin_one_marcus` (K1, premise `hic`), `hammond_trend_exact_bep_law_inexact` (N1), `symmetryFactor_betaHalf_iff` (A1) | read `PhotoLean/Relations.lean` §1–§17; each class is documented in its section header |
| `hic` is a premise, not a theorem | `[V]` | `theories/kasha/plan.md` honesty table; the row carries the premise in its statement |
| all 136 node pairs carry an edge or a registered absence | `[C]` | `python3 tools/counts.py --md` (edges ∪ absences = 136, empty intersection) |
| the completion block registers the 26 pairs left out by the earlier batches, plus one in-module edge (SS-C9) | `[D]`/`[V]` | `PhotoLean/Relations.lean` §16, "Completion rows (added 2026-09-24 …)"; the in-module edge is `PhotoLean.StokesShift.emEnergy_pos_iff_inverted` in `PhotoLean/StokesShift/Criterion.lean` |

## 3. The three adjudications (§2.4)

### A1 — symmetry factor (adjudicated conflation)

| claim | artifact |
|---|---|
| thermoneutral crossing coordinate `√kp/(√kr+√kp)` satisfies the crossing equation | `[D]` `PhotoLean.SymmetryFactor.tsCoordZero_crosses` |
| unique in `[0,1]`, without calculus | `[D]` `PhotoLean.SymmetryFactor.crossing_unique_in_unit_interval`; the interval premise is load-bearing — `crossing_witness_outside_interval` exhibits the second real root at `(1,4)` |
| **the verdict**: `BetaHalfReading kr kp ↔ kr = kp` for `0 < kr, 0 < kp` | `[D]` `PhotoLean.SymmetryFactor.betaHalf_iff_equalForceConstants`; re-exported as `PhotoLean.Relations.symmetryFactor_betaHalf_iff` |
| refuting witness `(1,4) ↦ 2/3`; direction asymmetry `(4,1) ↦ 1/3` | `[D]` `PhotoLean.SymmetryFactor.tsCoordZero_one_four`, `…tsCoordZero_four_one`, `…betaHalf_falsified_by_unequal`, `…tsCoordZero_gt_half_iff_stiffProduct` |
| why it survives: on the diagonal it is a theorem, tied back to the kernel | `[D]` `…betaHalf_holds_in_kernel`, `…tsCoordZero_eq_kernel_thermoneutral`, `…betaHalf_eq_transfer_thermoneutral`; the packaged row `PhotoLean.Relations.symmetryFactor_conflation_falsified_and_holds_in_kernel` |
| the `ℚ` decision layer computes the real verdict at perfect-square curvatures | `[D]` `…betaHalfQ_cast`, `…betaHalfQ_iff`, `…tsCoordZeroQ_cast` |
| practice locus (Butler–Volmer "usually … 0.5") and warning locus (IUPAC: "can by no means be assumed") | `[V]` `theories/SymmetryFactor/LITERATURE.md` — status of each source is recorded there (practice locus vs authority) |

### A2 — Kasha vs Kasha–Vavilov (adjudicated independence)

| claim | artifact |
|---|---|
| four-part verdict: bidirectional witnesses, coincidence iff under closed quantification with loss, separation at the lossless corner | `[D]` `PhotoLean.KashaVavilov.d2_verdict` (re-exported as `PhotoLean.Relations.kv_d2_verdict`) |
| every Kasha violation is observable anti-Kasha emission | `[D]` `PhotoLean.KashaVavilov.antiKasha_observable_iff` (`0 < Kasha.upperYield ↔ ¬ Kasha.KashaRule`), re-exported as `PhotoLean.Relations.kv_antiKasha_boundary` |
| witnesses sit at positive excitation inside the lossy regime (`ic 0 = 1 > 0`); the loss premise is load-bearing | the `d2_verdict` statement itself; ladder definitions `kashaPureLadder*`, `antiVavilovLadder*`, `vavilovOnlyLadder*`, `losslessLadder*` |

### A3 — static vs dynamic Stern–Volmer (identifiability)

| claim | artifact |
|---|---|
| both plots linear; matched parameters give pointwise-identical intensity curves | `[D]` `PhotoLean.SternVolmer.d1_verdict`, `…intensity_curve_coincidence` |
| lifetime channel is the exact discriminator: `LifetimeTracks m k0 kq Ka ↔ m = Mech.dyn` | `[D]` `PhotoLean.SternVolmer.d1_verdict`, `…lifetimeTracks_iff_dyn` (weakest premise `0 < Ka` alone), re-exported as `PhotoLean.Relations.sv_d1_verdict`, `…sv_identifiability_boundary` |
| coexistence witness: second difference `= 1` | `[D]` `PhotoLean.SternVolmer.mixed_witness`, `…svRatioBoth_secondDifference`, `…curvature_witnesses_coexistence` |
| weakest premises `k0 ≠ 0`, `0 < Ka` | the `sv_d1_verdict` signature (audited 2026-09-23) |

## 4. Negative results (§2.5)

| claim | artifact |
|---|---|
| ten rows named as refutations/falsifications/model-mismatches | `[C]` pattern `^(theorem\|lemma) [A-Za-z_][A-Za-z0-9_.]*(refut\|falsif\|not_model_consistent)` over `PhotoLean/`; `tools/counts.py` prints the names |
| four literature families refuted as equal-curvature two-parabola models | `[D]` `PhotoLean.BEP.inst_I11_F1_not_model_consistent`, `…F2…`, `…F3…`, `…F5…`; affine slope misread: `…inst_I12_affine_conforms_model_refuted` |
| SS first form had its direction reversed (witness `lam = 1, e00 = 2`) | `[D]` `PhotoLean.StokesShift.invertedCorner_firstForm_refuted` + the corrected `…emEnergy_pos_iff_inverted` |
| FP monotonicity false at `kF = kIC = 0` | `[D]` `PhotoLean.FluorPhos.fpC5_firstForm_refuted` |
| β = 1/2 falsified at `(1,4)` | `[D]` `PhotoLean.SymmetryFactor.betaHalf_falsified_by_unequal`, `…inst_conflation_falsified` |
| premise audit: `kernel_surfaces_cross_at_tsCoord` needs `lam ≠ 0` (false at `lam = 0`); the EGL `x₁ ≠ x₂` spot is load-bearing | `[D]` `PhotoLean.Relations.kernel_surfaces_cross_at_tsCoord`; `[V]` `theories/EnergyGapLaw/plan.md` §3.1 and `proofs/API-NOTES.md` statement-change index |
| three existential over-generalization re-freezes and one `Rat.*` shadowing re-freeze | `[V]` per-theory `plan.md` §3.1 correction logs (batch), and `theories/SternVolmer/plan.md` for the cast rows |

## 5. Methods (§5)

| claim | artifact |
|---|---|
| statement authority = compile-only skeleton with every public declaration written verbatim, body replaced by a placeholder | `[V]` `theories/<T>/probes/<T>-statement-skeleton.lean`; compile with `proofs/scripts/lake env lean <file>` |
| the fidelity probe compares signatures up to the first `:=`; bodies are pinned by the certificates | `[V]` `theories/BEP/probes/bep-fidelity.py` docstring; measured blind spot documented in `review/REVIEW-PROMPT.md` §10.6 |
| weakest-premise criterion: a premise is decorative iff the statement without it still proves | `[V]` `theories/EnergyGapLaw/plan.md` §3.1 (origin), `PhotoLean.Relations` audited anchors |
| `Kernel.lean`: six definitions + two theorems, importing Mathlib only | `[C]` `grep -c '^def \|^theorem ' PhotoLean/Kernel.lean`; import line |
| `Relations.lean` is the only module importing across the batch | `[C]` `grep -h '^import' PhotoLean/*/*.lean \| sort -u` and read the dependency facts in §16 |
| the registry's dependency facts (measured import structure) | `[C]` same command; each registry bullet names the modules whose imports it asserts |
| 5 unused-variable warning lines in 3 files | `[C]` `proofs/scripts/check.sh --strict` output (`SternVolmer/Basic.lean:65`, `SternVolmer/RatModel.lean:61`, `FluorPhos/RatModel.lean:89`) |
| totalized conventions `x/0 = 0`, `Real.sqrt` of negatives `= 0` | `[V]` documented at every occurrence; no substantive row depends on it (see `theories/GRAPH-REPORT.md` §9) |
| no `sorry`, no custom axiom | `[C]` `proofs/scripts/check.sh --strict` scan + `proofs/scripts/axioms.sh` per named row + the exhaustive sweep in `review/REVIEW-PROMPT.md` §10.4 |
| verifier roles and AI assistance | `[V]` `theories/<T>/TASKS.md` records; `review/AUDIT-*.md`, `review/REAUDIT-*.md` for the adversarial audit rounds |

## 6. Figure 3 composition and other counts

| claim | artifact |
|---|---|
| Fig. 3 left: per-theory authority footprint, 1,153 over 92 modules; 1,214 delivered | `[C]` `python3 figures/make_figures.py` prints every value with provenance; `tools/counts.py` recomputes them |
| Fig. 3 right: 15 certificates / 22 equivalence-entailment-bridge / 26 composition / 8 adjudication / 5 RACI / 2 other = 78 | `[C]`/`[V]` the section→class mapping is explicit in `tools/counts.py`; the manuscript's split is cross-checked there and any disagreement is printed rather than forced |
| Figure 2 panels: closed form `x*`, the two witnesses, the four-conjunct verdict, the linear/non-injective/lifetime-discriminating statements | `[D]` as in §3 above; the figure script transcribes the formulas from the Lean sources and prints its sources |

---

## 7. Known manuscript-side items to resolve before submission

Produced by `python3 tools/counts.py --axioms` (the full reconciliation table is in `tools/README.md`;
27 checked claims: 24 MATCH, 3 DIFF, 2 NOTE). Nothing on this list is a defect in the repository — each
is a place where the *draft's* wording or figure caption is looser than the tree:

1. **Fig. 3 class composition (3 DIFFs)** — the caption's `26 composition / 8 adjudication / 2 other`
   is not reproducible from the module's section markers, which give `30 / 6 / 0`. It **is**
   reproducible by one consistent redistribution: count §9's seven rows as 3 composition + 2
   adjudication + 2 other, leaving everything else as the section mapping has it. Which four of §9's
   rows those are cannot be recovered from the repository (the caption's class list has no
   "non-relation" class, and §9's rows are labelled C1–C5 there). *Action:* either add the per-row
   class list to the caption/methods, or adopt the section-derived split `15 / 22 / 30 / 6 / 5 / 0`
   in the figure and text.
2. **"7 genuine equivalences (E1–E7) and 3 one-way implications (O1–O3)"** — `Relations.lean` §2–§3
   contains nine such rows (6 + 3); the tenth is not identifiable from the module alone (candidates:
   `kernel_marcusIC` §7, `symmetryFactor_tsCoordZero_eq_bepTransfer` §11, or
   `hammond_sharp_iff_marcus_sharp` §6). *Action:* name the tenth row in the text, or write
   "seven equivalences and three entailments, counted across §2, §3 and §6".
3. **"`#print axioms` reports exactly the three Mathlib axioms"** — the discipline claim holds as an
   upper bound (0 of 1,303 public declarations exceed the allowed set), but "exactly" overstates it:
   1,205 rows depend on all three, 78 on `propext` alone, 5 on `propext` + `Quot.sound`, 15 on none.
   *Action:* phrase it as "at most `[propext, Classical.choice, Quot.sound]`" where the sentence is
   about every row.

---

**How to use this file when the manuscript changes.** Add a row before the claim enters the text;
never let a number live only in the manuscript. When a row's command fails at a later commit, the
claim must be re-derived or withdrawn — an unbacked claim is exactly what this repository refuses.
