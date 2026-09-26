# docs/REPRODUCE.md — reproducing every result in the manuscript

This guide reproduces, in order: the toolchain, the three acceptance gates, the per-theory fidelity
numbers, the whole-repository census (every count the manuscript quotes), the figures, and the two
perturbation experiments the manuscript cites. Every command is run **from the repository root**.

**Tree-state discipline.** A whole-tree result is meaningful only together with the tree state it was
taken in. Record it before quoting any number:

```bash
git log -1 --oneline && git status --short
```

---

## 0. Setup

**Two paths.** This repository was developed with a pinned toolchain unpacked at `.toolchain/`
(Lean `4.17.0`), invoked through the wrapper `proofs/scripts/lake`; that wrapper is what the internal
scripts use. For a fresh machine:

```bash
# Portable path (fresh clone, no .toolchain/ present)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh   # installs elan
lake --version                       # should print Lean 4.17.0 after elan reads lean-toolchain
lake exe cache get                   # downloads the prebuilt mathlib v4.17.0 oleans (~4.7 GB)
lake build                           # builds PhotoLean.Smoke and every defaultTarget
```

```bash
# Internal path (the author environment, wrapper + pinned toolchain in-tree)
proofs/scripts/lake build
```

Python tooling (census + figures): `python3 -m pip install -r requirements.txt` (matplotlib, numpy;
the census and the fidelity probes need only the standard library).

**Do not run `lake update`.** `lean-toolchain` and the mathlib `rev` in `lakefile.toml` are a pinned
pair; a mismatch triggers a multi-hour rebuild instead of using the cache.

**Scratch experiments.** Anything that mutates Lean sources must be done in a copy, never in the
delivered tree:

```bash
S=.lake/tmp/repro                  # gitignored
mkdir -p "$S/.lake"
rsync -a --exclude '.lake' ./ "$S/"
ln -s "$PWD/.lake/packages" "$S/.lake/packages"     # 4.7 GB of prebuilt mathlib: symlink, never copy
cd "$S" && proofs/scripts/check.sh --strict          # baseline: verdict PASS
```

---

## 1. The three acceptance gates

```bash
# (1) whole-tree gate: build + strict scan (placeholder / custom-axiom keywords) + leaf data planes
proofs/scripts/check.sh --strict
#     expected: build: OK · scan: clean · 17/17 leaf planes OK · verdict: PASS   (exit 0)
#     note: 5 `unused variable` warning lines in 3 files are pre-existing and registered

# (2) fidelity probes: authority statements delivered word for word
for T in Marcus Hammond BEP Kasha Sabatier Goldschmidt SymmetryFactor KashaVavilov SternVolmer \
         QuantumYield FluorPhos EnergyGapLaw StokesShift ICvsISC Forster Einstein RACI; do
  python3 theories/BEP/probes/bep-fidelity.py --theory "$T"
done
#     expected: every probe `not delivered yet: 0`, `signature differences: 0`;
#     authority total 1153, probe-registered auxiliaries 61, delivered total 1214

# (3) axiom audit for a named row (short names fail: use the fully qualified name)
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kv_d2_verdict
#     expected: verdict: PASS (only mathlib infrastructure axioms)
```

`lake build` returning 0 is **not** acceptance: placeholders and custom axioms compile with exit 0.
The three gates above are the acceptance definition (contract: `proofs/ENGINE.yml`).

**Exhaustive variant of (3)** (the project's records sweep row by row; this sweeps everything):
see `review/REVIEW-PROMPT.md` §10.4 for the generator + parser. Measured at the 2026-09-24 audit:
95 files, 1313 extracted names, 1278 rows printed, **0** footprints outside
`[propext, Classical.choice, Quot.sound]`.

---

## 2. The census — every number the manuscript quotes

```bash
python3 tools/counts.py --md                # human-readable table, quoted vs computed
python3 tools/counts.py --json tools/claims.json
python3 tools/counts.py --axioms            # adds the exhaustive #print axioms sweep (minutes)
```

`tools/README.md` defines each count exactly. The census covers: files and modules; per-theory and
total declaration counts; statement-authority and delivered totals; the `Relations.lean` section and
class composition; the 136-pair coverage (edges ∪ registered absences); the refutation-row scan; the
gate results; the linter-warning count.

---

## 3. Figures

```bash
python3 figures/make_figures.py        # vector PDF + 300-dpi PNG, with a provenance manifest
```

`figures/README.md` documents, per figure, which command or file each plotted number came from.
Values the script cannot recompute are labelled `(manuscript constant, not recomputed)` in its output.

---

## 4. Relation-graph coverage

```bash
python3 tools/counts.py --md | sed -n '/pairs/,/^$/p'
```

Expected: `26` machine edges + `110` registered absences = `136` pairs, `0` unaccounted. The edge set
and the absence set are encoded explicitly in `tools/counts.py`, each with the section or row that
carries it, so a disagreement is printed rather than averaged away.

---

## 5. Perturbation experiments (the "regression alarm" claim)

In a scratch copy (§0). The two definition bodies to perturb are, verbatim, from
`PhotoLean/Kernel.lean`:

```lean
noncomputable def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam)     -- line 46
noncomputable def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2            -- line 36
```

```bash
# (a) perturb the kernel barrier; expect the failure inside Kernel.lean itself
sed -i 's|def barrier (lam x : ℝ) : ℝ :=.*|def barrier (lam x : ℝ) : ℝ := (lam - x) ^ 2 / (4 * lam) + 1|' \
    PhotoLean/Kernel.lean
proofs/scripts/lake build PhotoLean.Kernel    # expect `unsolved goals` at reverseBarrier_eq_barrier_neg
git checkout -- .                              # restore the copy

# (b) perturb a kernel surface; expect the failure in the theory module that keeps the copy
sed -i 's|def reactantSurface (lam q : ℝ) : ℝ :=.*|def reactantSurface (lam q : ℝ) : ℝ := lam * q ^ 2 + 1|' \
    PhotoLean/Kernel.lean
proofs/scripts/lake build PhotoLean.StokesShift.Basic   # expect a type mismatch at `cert_s0Surface`
git checkout -- .
```

Measured 2026-09-24: (a) fails inside `Kernel.lean` (`unsolved goals` at the algebra theorem
`reverseBarrier_eq_barrier_neg`); (b) fails in `PhotoLean/StokesShift/Basic.lean` (`type mismatch` at
`cert_s0Surface`). In both cases the build stops before the relation module is reached — the alarm is
layered: kernel theorem → theory certificate → relation-module certificate.

**Gate-biting (does the gate catch what it claims?).** Measured: appending `sorry` or `axiom` to any
module makes `check.sh --strict` exit 1 with `verdict: FAIL (strict)`; changing a theorem's statement
fails the build. And the hole that must be re-checked after every delivery: a `.lean` file under
`PhotoLean/` that is **not** in `lakefile.toml`'s `defaultTargets` is not compiled by the bare gate —
verify `defaultTargets` equals the disk module set (`review/REVIEW-PROMPT.md` §10.3).

---

## 6. The statement authorities (compile-only skeletons)

```bash
proofs/scripts/lake env lean theories/RACI/probes/RACI-statement-skeleton.lean
# placeholders are intentional here (statement-first calibration); exit 0 with warnings
```

The skeletons live outside `SOURCE_DIRS`, so their placeholders do not trip the strict scan. If a
*delivered* file ever moves under such a path, the gate would miss it — check that nothing delivered
lives outside `PhotoLean/**` (the census asserts this).

---

## 7. Adversarial audit

```bash
# paste review/REVIEW-PROMPT.md §1–§11 into a fresh LLM session with shell + read access
```

Two completed rounds are recorded: `review/AUDIT-2026-09-24.md` (findings F1–F8) and
`review/REAUDIT-2026-09-24.md` (fixes + re-audit; lead-verified in commit
`240308c`).
