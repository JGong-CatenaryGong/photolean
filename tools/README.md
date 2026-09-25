# `tools/counts.py` — the repository's number source of record

Every count the manuscript quotes about PhotoLean is reproduced by one command. This folder is
the single place where those numbers are defined; a number that is not produced by this script is
not a number of this repository.

**No count may come from recollection.** If a value in the paper (or in a plan, a task board, or a
review note) is not reproduced here by a command, it is an open question, not a fact. The script
never consults a stored tally: it reads the tree, runs the probes, runs the gate, and reports.

## Commands

```bash
python3 tools/counts.py                        # human-readable census (source-level + gates)
python3 tools/counts.py --md                   # the same census as markdown
python3 tools/counts.py --json tools/claims.json   # machine-readable census (this is the file of record)
python3 tools/counts.py --axioms               # + the #print axioms sweep (~4 min)
python3 tools/counts.py --no-lean              # skip every Lean-toolchain step (CI without Lean)
```

* The checked-in `tools/claims.json` was produced by
  `python3 tools/counts.py --axioms --json tools/claims.json` (≈4 min, dominated by the
  `#print axioms` sweep); a source-level run reproduces every other field in seconds and is
  byte-identical to itself across runs.
* `--json [PATH]` writes the census (default `tools/claims.json`). The output has sorted keys and
  contains no run-dependent timestamp; `meta.tree_state` records the observed `HEAD` sha and the
  `git status --short` lines, so a diff of two runs shows what the tree movement was.
* `--no-lean` skips the `check.sh` gate run, the Lean-environment cross-check and the `--axioms`
  sweep, and still prints the source-level census (files, declaration counts, probe-derived
  authority/delivered totals, `Relations.lean` sections/classes, pair coverage, refutation rows).
  The gate/axiom claims are then reported as `NOTE` (`skipped (--no-lean)`), never as `MATCH`.
* The script is pure Python 3 (standard library only), needs no network, and **does not write
  inside the repository except** for its two scratch files under
  `.lake/tmp/counts-scratch/` (`env-census.lean`, `axioms-sweep.lean`) and the file named by
  `--json`. A run adds no path beyond `tools/counts.py`, `tools/claims.json` and
  `tools/README.md`: `git status --short` may still list other agents' in-flight edits, which the
  script neither creates nor touches (measured: the three census files are the only paths the
  tool's own runs ever change).

## Definitions — exactly what every number counts

### 1. Files

* **theory module** — a `.lean` file at depth ≥ 2 under `PhotoLean/`, i.e. `PhotoLean/<Theory>/x.lean`.
* **top-level module** — `PhotoLean/Kernel.lean`, `PhotoLean/Relations.lean`,
  `PhotoLean/Smoke.lean` (currently exactly these three).
* **theory directory** — a directory `PhotoLean/<Theory>/` that contains at least one `.lean` file.

### 2. Declarations — the source scan is the primary definition

The scan strips comments first — `--` line comments and nested `/- … -/` block comments, with
newlines preserved so line numbers stay meaningful — and then matches, at line start, an optional
same-line `@[…]` attribute, optional modifiers (`noncomputable`, `protected`, `private`, `unsafe`)
and one of the keywords

```
theorem | lemma | def | abbrev | structure | inductive | class | instance | example
```

with an optional declared name. Four classes are reported, over the whole tree and per theory:

* **(a) public declarations** — every matched row without the `private` modifier;
* **(b) public excluding `instance`** — (a) minus rows whose keyword is `instance`;
* **(c) public `theorem|lemma|def|abbrev`** — (a) restricted to those four keywords;
* **(d) private declarations** — matched rows carrying the `private` modifier.

Rows whose keyword appears in prose are not counted, because prose lives in comments and comments
are stripped first. Measured with the same keyword pattern, a comment-blind scan reports
`grep -rnE '^(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b'` = 1,184
lines while the comment-aware scan reports 1,169 rows at the same position — the 15-row difference
is prose inside block comments (e.g. lines beginning "instance …"). Keyword by keyword the effect is
larger: a raw `^instance` scan reports 10 lines against 1 real declaration, and a raw `^example`
scan reports 1 against 0 (both hits are inside doc comments).

**Environment cross-check (needs the Lean toolchain).** A generated `run_cmd` file folds over
`env.constants` (`ConstMap = SMap Name ConstantInfo`), keeps `n.getRoot == \`PhotoLean` and
`!isPrivateName n`, groups each constant by its *defining module* (`env.getModuleIdxFor?`) mapped
to that module's theory directory, classifies with `match ci with | .thmInfo _ | .defnInfo _ |
.inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ | .axiomInfo _ | .opaqueInfo _`, and flags
instances with `liftCoreM (Lean.Meta.isInstance n)` and structures with `Lean.isStructure env n`.
The environment count is **larger by construction**: it contains generated machinery (structure
projections, constructors, recursors, `noConfusion`-style theorems, `deriving` instances and
elaborator auxiliaries) that has no source line, and it **cannot see `private` declarations of
imported modules** (they are renamed `_private.…`, so both the root filter and the import boundary
exclude them; the source scan therefore counts 48 private rows that no importer can observe). The
source scan stays the primary definition; the environment figure is the independent check that
nothing in the scan is imaginary. Measured at the reported tree state: **2,393** non-private
`PhotoLean` constants (`thmInfo` 1,321, `defnInfo` 968, `inductInfo` 21, `ctorInfo` 61, `recInfo`
21, `axiomInfo` 1, `quotInfo`/`opaqueInfo` 0) against 1,303 source-scan public rows; the per-theory
side-by-side is `per_theory` in `claims.json`, and every name the source scan extracts is
namespace-aware and resolved by the `--axioms` sweep (1,303 requested, 1,303 resolved).

### 3. Statement authority (per theory)

`python3 theories/BEP/probes/bep-fidelity.py --theory <T>` is run for each of the seventeen
theories; the script parses the probe's five counters (`skeleton declarations`,
`delivered, word-for-word`, `delivered, not in authority`, `not delivered yet`,
`signature differences`). The **statement authority** of a theory is its
`skeleton declarations` counter; the authority of the repository is the sum.

### 4. Public delivered declarations (the rule behind the manuscript's "1,214")

Reproduced verbatim so the definition cannot drift:

> **delivered-total = Σ_over the seventeen theories (probe `delivered, word-for-word` +
> probe `delivered, not in authority`)**, i.e. the statement authority (1,153) plus the
> probe-registered auxiliaries (61) = **1,214**. This is the count of public declarations
> delivered, *including* authority-external auxiliaries and *excluding* private helpers and
> instance declarations.

The probe's `not in authority` counter excludes the single `instance` declaration of the tree
(`PhotoLean/QuantumYield/RatModel.lean:69 instance instDecidableQYData …`), because the probe's
declaration pattern covers `theorem|def|inductive|structure` only; the probe pattern likewise never
matches a `private` row. So instances are *not* added on top of 1,214 — QuantumYield legitimately
reports 29 authority / 0 auxiliaries even though its module directory contains 30 public rows.
Cross-check: the comment-aware source scan over `PhotoLean/<Theory>/*.lean` gives 1,215 public rows
(1,214 + the one `instance`; 1,302 public rows for the whole tree including the 88 top-level rows).

### 5. The relation module

`PhotoLean/Relations.lean` is parsed for its section markers (`/-! ## <n>. <title> … -/`), for the
declarations of each section, and for the class of each row.

**The class mapping is explicit and machine-readable** — `CLASS_OF_SECTION` for whole sections and
`CLASS_OF_ROW` for the rows of a mixed section (section → class, with the row names listed in the
script). The primary mapping is:

| section | rows | class |
|---|---|---|
| §1 Kernel certificates | 8 | `certificate` |
| §2 True equivalences | 6 | `equivalence/entailment/bridge` |
| §3 One-way entailments | 3 | `equivalence/entailment/bridge` |
| §4 Definitional reuse | 4 | `equivalence/entailment/bridge` |
| §5 Remaining ledger rows | 4 | `equivalence/entailment/bridge` |
| §6 Non-relations and shape differences | 3 | `equivalence/entailment/bridge` |
| §7 Conditional composition edge (Kasha → Marcus) | 5 | `composition` |
| §8 Composition edge (Sabatier → BEP) | 6 | `composition` |
| §9 Look-alike but different (Sabatier ↔ Marcus) | 7 | `composition` |
| §10 no-edge registry | 0 | — (documentation) |
| §11 Adjudicated conflation (A1) | 4 | mixed (see below) |
| §12 Kernel certificates of the photophysics batch | 7 | `certificate` |
| §13 The D2 adjudication | 2 | `adjudication` |
| §14 The D1 adjudication | 2 | `adjudication` |
| §15 Composition edges of the batch | 12 | `composition` |
| §16 extended no-edge registry | 0 | — (documentation) |
| §17 The seventeenth node (RACI) | 5 | `RACI` |

§11 is the only mixed section; the row-level rule is taken from the rows' own docstrings, which
label them *A1 certificate* vs *A1 verdict*:

* `symmetryFactor_tsCoordZero_eq_kernel`, `symmetryFactor_tsCoordZero_eq_bepTransfer`
  → `equivalence/entailment/bridge`;
* `symmetryFactor_betaHalf_iff`,
  `symmetryFactor_conflation_falsified_and_holds_in_kernel` → `adjudication`.

**`rfl` kernel certificates** are the definitional pin rows: §1 (8 rows whose proof term is a
literal `:= rfl`) plus §12 (7 rows re-exporting the in-module `cert_*` theorems, each closed by
`rfl`/`Iff.rfl`) = **15**. Three further rows of the module are also rfl-level but are proved with
`unfold` + `rfl` *inside* `Relations.lean` and are classified by the section rule above:
`kernel_marcusIC` (§7), `marcus_rate_eq_activity` (§9, row C1) and `icvscic_icRate_eq_eg_nrRate`
(§15). The two §11 tie-back rows are *not* rfl-level: they go through a delivered theory lemma.

### 6. Pair coverage

All C(17,2) = 136 unordered theory pairs are enumerated in the script and assigned to exactly one
of two sets, each pair carrying a citation string (section + row name):

* **edge set** — pairs carrying a delivered machine row, read from `PhotoLean/Relations.lean`
  (§2–§9, §11–§15, §17) and `PhotoLean/StokesShift/Criterion.lean`: **26 pairs**.
* **absence set** — pairs registered in the no-edge registries (§10, §16, §17): **110 pairs**.

The script asserts `edge ∪ absence = all 136` with empty intersection and prints any unaccounted or
double-counted pair; every edge citation is additionally checked to name at least one declaration
that exists in the tree (guards against stale row names). Two honesty notes come out of this:

* four pairs are listed twice by the registry itself — `FluorPhos–StokesShift`,
  `Forster–StokesShift`, `Forster–ICvsISC`, `Einstein–StokesShift` — which is harmless for
  coverage: the pair is simply assigned to the absence set once, with both bullets cited;
* `Marcus–RACI` carries a machine row but is counted as an **absence**: the manuscript's §5.7 and
  Fig. 1 caption both list "the classical surface crossing versus the codimension-2 conical
  intersection of RACI" among the shape look-alikes registered *without* an edge, and §17's row
  (`kernel_surfaces_cross_at_tsCoord`) pins only the classical side. The alternative reading (an
  edge, because §17's closing bullet groups Marcus with "the five machine rows") would give
  27 edges + 109 absences with the same 136/136 coverage — see the Classification decisions section.

### 7. Negative results

The pattern of §5.6 of the paper is applied to the comment-aware source:

```
^(theorem|lemma) [A-Za-z_][A-Za-z0-9_.]*(refut|falsif|not_model_consistent)[A-Za-z0-9_.]*
```

The script reports the matched rows (name, file, line) and, as a cross-check, the raw `grep` count
over the same tree (both are 10). `symmetryFactor_conflation_falsified_and_holds_in_kernel` is one
row packing the A1 falsification and the persistence theorem, and is counted once.

### 8. Gates

`proofs/scripts/check.sh --strict` is run and parsed: `build:` status, the scan verdict
(`clean`/`HITS`), the number of `theories/<T> (5/5)` leaf-plane lines, and the final `verdict:`.
Unused-variable warnings are counted from the gate output; because `lake build` replays a module's
cached message log only when it decides to (measured: a cached `check.sh` run can print nothing),
the script falls back on Lake's `.trace` files (`.lake/build/lib/**/*.trace`), which store the
messages of each module's last elaboration. Both numbers are reported; the fallback is used only
when the gate output yields none.

### 9. Axioms (`--axioms`)

A generated batch file imports every `PhotoLean` module and carries one `#print axioms <name>` line
per public declaration; names are namespace-aware (the scanner tracks `namespace`/`end` blocks and
`section`/`end`, and skips `private` rows). The file is run with
`proofs/scripts/lake env lean .lake/tmp/counts-scratch/axioms-sweep.lean`; the output is
whitespace-flattened before parsing `'<name>' depends on axioms: [<list>]` (the list wraps across
lines) or `'<name>' does not depend on any axioms`. The name class is bounded so a prime-suffixed
identifier (`…conicalSet'`) cannot make the match run across two declarations. The allowed set is
read from `ALLOWED_AXIOMS` in `proofs/ENGINE.yml`. A footprint outside that set, or an unknown
identifier, is reported with its name.

## Reconciliation table (quoted vs computed)

Produced by `python3 tools/counts.py --axioms --json tools/claims.json`; the verdicts below are
`claims[*].verdict` of that file.

| # | quoted (paper) | source | computed | verdict |
|---|---|---|---|---|
| 1 | seventeen theories | §2.1, §3.1 | 17 theory directories | MATCH |
| 2 | 92 theory modules | §2.1, Fig. 3 | 92 | MATCH |
| 3 | 95 `.lean` files (with `Kernel`, `Relations`, `Smoke`) | §2.1, Fig. 3 | 95 = 92 + 3 | MATCH |
| 4 | statement authority 1,153 | §2.1, §5.2 | 1,153 | MATCH |
| 5 | per-theory authority 51/102/191/151/132/139/35/29/46/29/30/26/36/20/32/33/71 | Fig. 3 | identical, in the same order | MATCH |
| 6 | 17/17 probes, 0 signature discrepancies, 0 undelivered | §2.1 | 17/17, 0, 0 | MATCH |
| 7 | "public declarations delivered in total: 1,214 …" | §2.1, §5.2 | 1,214 (rule in §4 above) | MATCH |
| 8 | 78 declarations in 17 sections (`Relations.lean`) | §2.3, Fig. 1 | 78 / 17 | MATCH |
| 9 | **15 rfl kernel certificates** | §2.1, §2.3, §5.3, Fig. 3 | 15 (§1 + §12) | MATCH |
| 10 | Fig. 3: 15 certificates | Fig. 3 | 15 | MATCH |
| 11 | Fig. 3: 22 equivalence/entailment/bridge | Fig. 3 | 22 | MATCH |
| 12 | Fig. 3: **26 composition** | Fig. 3 | **30** | **DIFF** |
| 13 | Fig. 3: **8 adjudication (A1–A3)** | Fig. 3 | **6** | **DIFF** |
| 14 | Fig. 3: 5 RACI | Fig. 3 | 5 | MATCH |
| 15 | Fig. 3: **2 other registrations** | Fig. 3 | **0** | **DIFF** |
| 16 | Fig. 3 total 78 | Fig. 3 | 78 | MATCH |
| 17 | all 136 node pairs covered | §3.1, §5.7 | 136 = 26 edges + 110 absences | MATCH |
| 18 | 26 pairs registered by the completion block | §3.1, §5.7 | 26 | MATCH |
| 19 | one edge of SS delivered within the theory module | §3.1, §5.7 | `PhotoLean/StokesShift/Criterion.lean` `emEnergy_pos_iff_inverted` | MATCH |
| 20 | ten refutation rows | §5.6 | 10 | MATCH |
| 21 | `Kernel.lean`: six definitions + two algebra theorems | §5.3 | 6 `def` + 2 `theorem` | MATCH |
| 22 | 17/17 leaf planes OK | §5.8 | 17/17 | MATCH |
| 23 | verdict PASS | §2.1, §5.8 | `build: OK`, scan `clean`, `verdict: PASS` | MATCH |
| 24 | five unused-variable warnings in three files | §5.9/§5.10 | 5 in `SternVolmer/Basic.lean`, `SternVolmer/RatModel.lean`, `FluorPhos/RatModel.lean` | MATCH |
| 25 | `#print axioms` never exceeds `[propext, Classical.choice, Quot.sound]` **[a]** | §5.8 | 1,288 printed + 15 axiom-free = 1,303; 0 footprints outside | MATCH |
| 26 | exactly one auxiliary axiom constant, no user-declared axiom | METHOD NOTE, §5.8 | 1 (`PhotoLean.RACI.nonModelNoCI._elambda_1`) | MATCH |
| 27 | "7 genuine equivalences (E1–E7) and 3 one-way implications (O1–O3)" | §2.3 bullet | §2 has 6 rows, §3 has 3 | NOTE |

**[a]** The claim id `axiom_footprints` also carries the paper's stronger wording "reports
**exactly** the three Mathlib axioms". The discipline half is exact (no footprint outside the
allowed set); the "exactly three" half is an upper bound that 83 rows do not meet — 1,205 rows
report all three axioms, 78 report `[propext]` alone, 5 report `[propext, Quot.sound]` and 15
report none. See the Discrepancies section.

Claim-id map (the `id` field of every entry of `claims.json`): 1 `theories`; 2 `theory_modules`;
3 `lean_files`; 4 `statement_authority_total`; 5 `statement_authority_per_theory`;
6 `fidelity_probes`; 7 `public_delivered_total`; 8 `relations_declarations_sections` and
`relations_module_rows`; 9 `rfl_kernel_certificates`; 10–16 `fig3_class_certificate`,
`fig3_class_equivalence_entailment_bridge`, `fig3_class_composition`, `fig3_class_adjudication`,
`fig3_class_RACI`, `fig3_class_other`, `fig3_class_total`; 17 `pair_coverage`;
18 `completion_block_pairs`; 19 `stokes_shift_in_module_edge`; 20 `refutation_rows`;
21 `kernel_contents`; 22 `leaf_planes`; 23 `gate_verdict`; 24 `unused_variable_warnings`;
25 `axiom_footprints`; 26 `auxiliary_axiom_constants`; 27 `equivalences_entailments`.

## Discrepancies, and the counting rule that would produce the quoted value

### The Fig. 3 class composition (items 12–15)

The recomputed split from `Relations.lean`'s own section markers is **15 / 22 / 30 / 6 / 5 / 0 = 78**
(certificate / equivalence-entailment-bridge / composition / adjudication / RACI / other); the
manuscript caption quotes **15 / 22 / 26 / 8 / 5 / 2 = 78**. The total agrees, and three of the six
classes agree (certificate 15, bridge 22, RACI 5) — the whole difference is a redistribution of four
rows out of `composition` into `adjudication` (+2) and `other` (+2).

Two assignments reproduce the caption exactly. Both are arithmetically forced *given* their extra
premise, and neither premise is licensed by the module text:

* **Reconstruction A — the §15 shape rows leave composition.** Keep the §11 split of the primary
  mapping (2 tie-back certificates → bridge, 2 verdict rows → adjudication), keep §9 wholly in
  composition, and count §15 as 8 composition / 2 adjudication / 2 other. The two "other" rows are
  then exactly the two rows §15's own prose calls *shape rows*:
  `fretEff6_inv_eq_one_plus` (the SV/FO `1 + control` look-alike) and `eg_boundary_eq_tsCoord_zero`
  (the EG/Hammond boundary row). Weakness: **no §15 row carries an A-label**, so the two rows that
  would have to move into `adjudication` have no textual support (the nearest candidates are the
  D-adjacent rows `sv_quench_dilutes_yield` and `kasha_radBranch_eq_yieldOf`).
* **Reconstruction B — the §9 look-alike rows leave composition.** Count §11 wholly as
  adjudication (all four rows are A1 rows: 4 + §13's 2 + §14's 2 = 8), keep §15 wholly in
  composition, and split §9's seven rows as 3 composition / 2 bridge / 2 other. Weakness: §9's own
  accounting labels its rows C1 (a definitional certificate), C2 (the shared predicate,
  instantiated) and C3a/C3b/C4/C5a/C5b (non-relations) — no 3/2/2 split follows, and the class list
  has no "non-relation" class.

The script therefore **reports the primary mapping, prints the full per-row assignment of every
row, and never applies a reconstruction**; `relations_module.reconciliation` in `claims.json`
carries both reconstructions and their weaknesses. A human adjudicating the figure needs the
manuscript's own row list for §9/§15 — that list is not in the draft text.

**Recommendation: update the Fig. 3 caption to the recomputed split 15 / 22 / 30 / 6 / 5 / 0.** The
section markers of `Relations.lean` do not support 15/22/26/8/5/2, and every way of reaching the
caption requires an assignment the module text does not license; the recomputed split is the one
that a reader can re-derive from the file alone.

### "7 genuine equivalences (E1–E7) and 3 one-way implications (O1–O3)"

The edge-vocabulary bullet of §2.3 names ten rows (7 + 3) "concentrated among the three readings of
the F1 core", but `Relations.lean` §2–§3 contains **nine** such rows (6 equivalences + 3 one-way).
The tenth row is not identifiable from the module alone: candidates are the §7 kernel certificate
`kernel_marcusIC`, the §11 tie-back `symmetryFactor_tsCoordZero_eq_bepTransfer` (whose docstring
says it "extend[s] the E1 chain") or `hammond_sharp_iff_marcus_sharp` (§6, a co-extensiveness
composition). The script therefore counts the class structurally (22 bridge rows) and flags the
E/O sub-tally as a NOTE rather than guessing the missing label.

### "`#print axioms` reports exactly the three Mathlib axioms"

The discipline claim holds: **no** footprint exceeds `ALLOWED_AXIOMS` (0 of 1,303 declarations), and
no declaration depends on an axiom outside it. But "exactly three" is an upper bound, not a
constant: of the 1,303 public declarations, 1,205 depend on all three, 78 on `propext` alone (mostly
`decide`/`norm_num`-style rows in the `RatModel`/`Instances` modules), 5 (`Goldschmidt/Rules.lean`,
`Goldschmidt/Instances.lean`) on `propext` + `Quot.sound`, and 15 on no axiom at all. A claim about
*every* row should read "at most `[propext, Classical.choice, Quot.sound]`".

## Classification decisions

Some numbers in this census are produced by judgment, not by pattern matching. Every such judgment
is listed here with its reason and its alternative reading, so a reader can overturn it knowingly.
The machine-readable copies live in `claims.json`
(`pair_coverage.classification_decisions`, `relations_module.reconciliation`,
`relations_module.class_of_section` / `class_of_row`).

**(a) `Marcus ↔ RACI` — registered absence, not an edge** (this single decision is the 26/110 vs
27/109 difference). The pair *does* carry a delivered machine row, §17's
`kernel_surfaces_cross_at_tsCoord`, but that row is labelled a *look-alike machine note*: it pins
the classical two-parabola side (a one-condition surface crossing) and asserts no edge to the RACI
two-state conical intersection. Both the manuscript's §5.7 ("the classical surface crossing versus
the codimension-2 conical intersection of RACI" among the shape look-alikes registered without an
edge) and the Fig. 1 caption ("RACI versus Marcus as 'real crossing vs. codimension-2 degeneracy'"
in the same list) classify it as a shape look-alike without an edge. The register therefore counts
**26 edges + 110 registered absences**, and any text that states 27 edges + 109 absences is off by
exactly this judgment. (§17's closing bullet does group Marcus with "the five machine rows", which
is what makes the pair ambiguous in the first place; the census records that reading as the
alternative.)

**(b) `Hammond ↔ SymmetryFactor` — edge, but transitively only.** No row of `Relations.lean` names
both theories. The edge rests on §10's registry line "SymmetryFactor ↔ Marcus, Hammond, BEP — §11
(yes, A1 + specialization)" together with §11's tie-backs to `Kernel.tsCoord` / `BEP.transfer` and
§1's kernel certificates `kernel_tsCoord_eq_hammond` (`Kernel.tsCoord = Hammond.tsCoord`) and
`kernel_transfer_eq_bep` (`Kernel.transfer = BEP.transfer`). It must **not** be mistaken for a
direct row: the direct machine rows for the SymmetryFactor node are the two §11 certificates against
the kernel and BEP only.

**(c) The four registry double-listings.** The registry lists `FluorPhos–StokesShift`,
`Forster–StokesShift`, `Forster–ICvsISC` and `Einstein–StokesShift` under two bullets each (§16's
per-theory bullets overlap: the FluorPhos bullet lists StokesShift, and the StokesShift bullet lists
FluorPhos; the Forster and ICvsISC bullets overlap the same way). Each pair is assigned **once**, to
the absence set, with both bullets cited. Harmless for coverage, reported so the registry can be
de-duplicated.

**(d) The §11 mixed section.** §11 is the only section that mixes classes, so its rows are
classified individually from their own docstrings: `symmetryFactor_tsCoordZero_eq_kernel` and
`symmetryFactor_tsCoordZero_eq_bepTransfer` ("A1 certificate") → `equivalence/entailment/bridge`;
`symmetryFactor_betaHalf_iff` ("A1 verdict") and
`symmetryFactor_conflation_falsified_and_holds_in_kernel` ("A1 falsification-and-persistence") →
`adjudication`. Alternative reading: all four rows adjudication (that is Reconstruction B above, and
it drops the bridge count to 20).

**(e) §6 ("Non-relations and shape differences") → `equivalence/entailment/bridge`.** Its three rows
are proved cross-theory content (an exactness/failure contrast between the Hammond trend and the BEP
line law, the co-extensiveness composition `hammond_sharp_iff_marcus_sharp`, and the
predicate-strength row `rate_predicate_satisfiable_without_positive_curvature`). Alternative: `other`
(shape registrations), which would give bridge 19 / other 3.

**(f) §9 ("Look-alike but different") → `composition`.** The section is an edge-section of the graph
(it carries the Sabatier ↔ Marcus pair and its C1–C5 analysis), so its rows are counted there.
Alternative: `other` (C3–C5 are explicitly non-relations). This choice is the crux of the Fig. 3 gap:
moving §9 out of composition is what any caption-faithful mapping must do.

**(g) Negation rows that are also edges.** `symmetryFactor_conflation_falsified_and_holds_in_kernel`
is one row packing the A1 falsification *and* the persistence theorem; it is counted once, as an
adjudication row, and appears once in the §5.6 refutation scan.

## What this tool does not determine

* **The manuscript's §9 row split** (see above) — the paper's per-row class assignment is not in
  the draft text, only its six totals.
* **The environment figures under `--no-lean`.** The Lean-environment cross-check and the axiom
  sweep need the toolchain; without it the JSON carries `environment`/`axioms` = absent and the
  corresponding claims are `NOTE`.
* **Stale build traces.** The unused-variable fallback reads `.lake/build/lib/**/*.trace`, so it
  reports the warnings of the last elaboration of each module. Only traces whose `.lean` source
  still exists are counted; in a fresh checkout without `.lake/build` the fallback finds nothing and
  the claim falls back to whatever `check.sh` printed.
* **Anything not in the tree.** The script never infers a count from a plan, a task board or a
  commit message; if two sources disagree, the tree wins and the disagreement is printed.
