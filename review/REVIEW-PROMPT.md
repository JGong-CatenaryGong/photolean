# review/REVIEW-PROMPT.md — auditor instructions for the PhotoLean repository

> **使用说明（中文）**：把下面 **§1 起到 §12 止的全部英文内容**整段粘贴进一个全新 LLM session（需要 shell +
> 读文件能力；不需要网络）。§13 是中文速览，可一并粘贴，也可只留作人读。该 session 的产物是一份**审查报告**
> （格式见 §8），不是补丁：**禁止修改 `PhotoLean/**` 与 `theories/**` 的交付内容**；所有实验只在仓库内
> gitignore 的草稿目录 `.lake/tmp/`（或任何可写目录）中的**副本**里做。§11 的每条配方都在本仓库实测过，
> 括号内给出实测结果；实测方法见 `proofs/EXPERIENCE.md`。

---

## 1. Mission

You are an **independent adversarial auditor** of this repository. Your job is not to summarize it, and
not to praise it: it is to find the places where the repository is **wrong, unproved, unverified,
over-generalized, or over-claimed** — and to prove that each defect is real by running commands whose
raw output backs the finding.

Deliverable: one report (§8) containing

1. a verdict line,
2. a findings list with severity, file:line, claim, **raw evidence**, minimal reproduction, and why it
   is a defect,
3. a **claim ledger** for every headline claim you examined (MACHINE-BACKED / TEXT-ONLY / FALSE / STALE
   / UNDETERMINED, each with the command that decided it),
4. a **coverage ledger** (audit axis → EXECUTED / NOT EXECUTED with the reason), and
5. what you could not check.

The repository is a Lean 4 formalization project: everything it asserts *should* be reducible to
declarations a kernel has accepted. Your leverage is that most of its downstream claims — counts,
"word-for-word", "verified", "complete", "no edge", "the weakest premises", "the literature says" — are
**not** kernel-checked, and are therefore where the defects live.

---

## 2. What this repository claims (so that "overclaim" is defined correctly here)

Orientation, to be verified rather than trusted (all of it is checkable):

* It is a Lean 4.17.0 / mathlib v4.17.0 project (`lean-toolchain`, `lakefile.toml`, `proofs/scripts/lake`
  wrapper) that formalizes phenomenological photochemistry / photophysics: **17 theories**, organized as
  one directory per theory under `theories/` (leaves: `plan.md`, `TASKS.md`, `LITERATURE.md`,
  `RESULTS.md`, `probes/`) and one module directory per theory under `PhotoLean/`.
* The contract is `proofs/ENGINE.yml`; the acceptance commands are its `CHECK_CMD` / `AXIOMS_CMD`, plus
  `proofs/scripts/check.sh` (build + a text scan for unproved placeholders and custom axioms) and
  `proofs/scripts/axioms.sh` (prints `#print axioms` for one fully-qualified declaration).
* Its stated epistemic rules: **statement-first** (a statement must compile before its proof work
  starts); **no `sorry` and no custom `axiom` in delivered theorems**; `#print axioms` must be exactly
  `[propext, Classical.choice, Quot.sound]`; **build success is not acceptance** (placeholders compile
  with exit 0); physical approximations are explicit premises; **weakest premises** (only load-bearing
  hypotheses); negative results are first-class (a refuted draft is delivered as a
  counterexample-witness theorem, never silently weakened); the lead ticks a task only after an
  independent verifier PASS.
* Its cross-cutting claims: a shared kernel (`PhotoLean/Kernel.lean`), one machine-checked relation
  inventory (`PhotoLean/Relations.lean`), prose companions (`theories/RELATIONS.md` incremental,
  `theories/GRAPH-REPORT.md` consolidated), and per-theory statement authorities
  (`theories/<T>/probes/<T>-statement-skeleton.lean`) whose fidelity to the delivered modules is
  measured by a shared checker (`theories/BEP/probes/bep-fidelity.py`, with per-theory `--theory`).
* Language policy: repository markdown, Lean comments and commit messages in **English**;
  `RESULTS.md` is bilingual by design; `README.md` is the repository's registered Chinese authority
  (its pre-policy English mirror `README.en.md` is frozen); conversation with the human is Chinese.

**The audit question is therefore not "is the Lean true" — the kernel settles that — but: is every
non-kernel claim (counts, coverage, fidelity, independence, identifiability, completeness, literature
attribution, "verified") exactly as strong as the evidence behind it, and are the delivered statements
as strong as the prose says they are?**

---

## 3. Ground rules (non-negotiable)

1. **Read-only on delivered content.** Never edit `PhotoLean/**`, `theories/**` (except a scratch copy),
   `lakefile.toml`, `proofs/**`, `README.md`. Your output is a report, not a patch. Propose at most a
   minimal correction sketch.
2. **Experiments happen in a copy.** Use a gitignored scratch directory inside the repository,
   `.lake/tmp/<name>/` (create it; see §10.1). Never run mutating experiments against the delivered tree.
3. **Never run `lake update` / `lake exe cache`** and never touch `lean-toolchain` or the mathlib rev:
   the toolchain/rev pairing is hard-wired to a 4.7 GB prebuilt mathlib cache; a mismatch costs hours.
4. **Use the wrapper** `proofs/scripts/lake` (plain `lake` may not resolve the pinned toolchain).
5. **Do not trust any document, including this one.** Every number you repeat must come from a command
   you ran, in the tree state you report. State that state: `git log -1 --oneline` and `git status --short`.
6. **Distinguish the gate from the acceptance claim.** `check.sh --strict` green does **not** establish
   "no unproved axiom anywhere", "all modules built", "statements faithful", or "premises weakest".
7. **Report only what you can evidence.** If you suspect a defect but cannot decide it, write it under
   "could not check" with the reason — do not upgrade a suspicion into a finding.
8. **Do not report style as a defect.** The repository's own registered conventions (listed in §6.L) are
   not findings; *violations* of them are.

---

## 4. The trust model: mechanical vs discipline-only (this is your audit surface)

| claim class | how it is established today | can it silently be false? |
|---|---|---|
| a Lean declaration type-checks | kernel | no |
| a declaration's axiom footprint | `#print axioms` (run per row by hand) | **yes**, if the row was never swept |
| no placeholder/axiom text in `PhotoLean/**` | `check.sh --strict` text scan | no (but the scan is text-level; see §6.B) |
| every module on disk is built | `defaultTargets` in `lakefile.toml` | **yes** — a module missing from the list is never compiled by the bare gate |
| delivered statement = authority statement | signature-normalized text comparison by the fidelity probe | **yes** — only up to the first `:=` (bodies excluded), and only for rows present in the skeleton |
| premises are the weakest | human judgement + audit rounds | **yes** |
| a statement is non-vacuous (existentials have content; `∀`-rows are instantiable) | human judgement | **yes** |
| edges / no-edge registry / "every node is on the graph" | prose + import greps | **yes** |
| counts in README / leaves / reports | human counting | **yes** (this class has produced real defects repeatedly) |
| literature attribution ("the paper says X") | a research subagent's reading | **yes** |
| verifier PASS / "independently verified" | a recorded run | **yes**, if the run's scope is narrower than the claim |

Design your audit to spend most of its effort on the right-hand column.

---

## 5. Reading order (do this first, then verify by running)

1. `proofs/ENGINE.yml` — the contract: `SOURCE_DIRS`, `ALLOWED_AXIOMS`, `FORBID_SORRY`, `THEORIES`,
   leaf paths, `*_CMD` acceptance commands.
2. `proofs/ENGINE.md` — the engine's interface design and iteration loop (context for the roles).
3. `README.md` — the repository's own current-state claims (Chinese; the authoritative README).
4. `theories/GRAPH-REPORT.md` — the consolidated report of the relation graph: node inventory, edge
   inventory, adjudication classes, no-edge registry, verification record.
5. `theories/RELATIONS.md` — the incremental discussion draft (three batch layers); compare its claims
   against `PhotoLean/Relations.lean`.
6. `PhotoLean/Kernel.lean` and `PhotoLean/Relations.lean` — the machine-checked core of the graph.
7. `theories/<T>/{plan,TASKS,LITERATURE,RESULTS}.md` — per theory: plan (with its §3.1 correction log),
   board (status + verifier records), literature (sources + formalizable implications), bilingual results.
8. `proofs/EXPERIENCE.md`, `proofs/API-NOTES.md` — the project's own failure history (your best source
   of *what kinds of defects this codebase actually produces*, §9).

Before trusting any of it, run the four commands of §10.2 and record their raw output.

---

## 6. Audit plan

Each axis: **goal → what to run → what counts as a finding**. Report every axis as EXECUTED or NOT
EXECUTED (with reason).

### A. Tree state, environment, contract integrity

* Record `git log -1 --oneline`, `git status --short`, `find PhotoLean -name '*.lean' | wc -l`,
  directory listing of `theories/`.
* Read `proofs/ENGINE.yml`; check: every `THEORIES` entry has a directory with the five leaves; every
  declared leaf path exists; `SOURCE_DIRS` covers every delivered Lean file (nothing delivered lives
  under a path the scan skips, e.g. `theories/**/probes/`); `ALLOWED_AXIOMS` is the three mathlib
  infrastructure axioms; `CHECK_CMD`/`AXIOMS_CMD` are the scripts actually used.
* Check `lean-toolchain` vs the mathlib `rev` in `lakefile.toml` (they must pair; a mismatch triggers a
  full rebuild and is a real finding).
* Finding if: a declared leaf is missing, a theory directory is half-initialized, or a delivered file
  sits outside `SOURCE_DIRS`.

### B. Does the gate actually bite? (gate-biting tests, in the scratch copy)

Run each mutation in `.lake/tmp/<name>/` and record exit codes and the relevant output lines. Expected
results — measured in this repository on 2026-09-23 (re-verify; do not copy them):

| mutation | expected |
|---|---|
| append `theorem p : True := by sorry` to a module | `check.sh --strict` → exit 1, `!! found sorry/axiom occurrences`, `verdict: FAIL (strict)` |
| append `axiom p : True` | same (FAIL) |
| change a theorem's **statement** (e.g. add `∧ False` to the conclusion) | `lake build` fails: `error: ... type mismatch`, `build: FAILED`, `verdict: FAIL` |
| add a **brand-new file** `PhotoLean/NewFile.lean` with a type error | **gate PASSES** — the bare gate builds `defaultTargets` only; a file absent from that list is never compiled |
| remove an existing target from `defaultTargets` and break that module | **gate PASSES** for the same reason |

**Therefore: verify `defaultTargets` set-equality with the disk set** (`§10.3`). Any delivered `.lean`
file under `PhotoLean/` that is not a target *and* is not imported by a target is an unbuilt,
unverified file — an S1 finding if it contains delivered content. Report the diff, and report whether
the lakefile's own comment about this hazard matches measured behaviour.

### C. Exhaustive axiom sweep (the one test the project runs only per-row-by-hand)

Generate a `#print axioms` batch over **every** declaration of **every** module (recipe: §10.4;
measured: 39/39 declarations of one theory in ~6 s, 0 outside the allowed triple). Then:

* report the total number of declarations swept and the number whose footprint is not a subset of
  `{propext, Classical.choice, Quot.sound}`;
* any occurrence of `sorryAx`, `Lean.ofReduceBool` (introduced by `native_decide`), `Classical.choice`
  outside the allowed set, or an unknown axiom name is an **S1 finding**;
* report declarations for which `#print axioms` is impossible (private declarations, extraction errors)
  as coverage gaps, with counts, not as findings;
* cross-check the grep surface: `native_decide`, `decide!`, `unsafe`, `partial`, `opaque`,
  `@[implemented_by]`, `#eval`, `by decide` on ℚ, `set_option` (especially `maxHeartbeats 0`,
  `linter.* false`, `autoImplicit`, `debug.*`). For each site, decide whether it can hide a defect.
  (Measured state at the time of writing: `native_decide` occurs 3× **only inside doc comments that
  ban it**; `unsafe`/`partial`/`#eval`/`maxHeartbeats` absent; `set_option` present at many sites,
  mostly scoped `linter.unusedVariables false`; `autoImplicit false` in the Kasha theory; the RACI port
  deliberately keeps Lean's default `autoImplicit true` — verify that each is registered.)

### D. Statement-level fidelity, and its blind spots

* Run all 17 fidelity probes; record `delivered, word-for-word`, `delivered, not in authority`,
  `not delivered yet`, `signature differences` for each.
* **Audit the checker itself** (`theories/BEP/probes/bep-fidelity.py`): read its comment stripping,
  whitespace collapsing, name qualification, and the "unique bare name" fallback. Then adversarially
  test it **in the scratch, invoked as `python3 theories/BEP/probes/bep-fidelity.py` from the scratch
  root** (measured, with `--theory KashaVavilov`; the checker resolves the repo root from its own path,
  so calling the *original* script from a scratch audits the original tree and shows nothing):

  | mutation in the scratch | measured result |
  |---|---|
  | rename an authority declaration (`SpecSame` → `SpecSameX`) | 29 → `word-for-word 27`, `not delivered yet 1`, `signature differences 1`, row printed |
  | add a premise to an authority theorem | `word-for-word 28`, `signature differences 1`, row printed |
  | add a brand-new auxiliary declaration | `delivered, not in authority` 10 → 11 |
  | change a definition **body** only (`:= <body>` → `:= 0`) | **29/29, `signature differences 0`** — documented blind spot (the checker compares up to the first `:=`) |

* Findings if: any probe reports a difference; any theory's "not in authority" declarations are
  undocumented (are they in the leaf? are they auxiliary only, or do they carry content?); the
  skeleton is *weaker* than the delivered statement in a way the normalization hides (spot-check ≥20
  rows across theories by hand: `diff <(signature of delivered) <(signature of skeleton)`); or the
  bare-name fallback can key two different declarations to the same name (construct that case in the
  scratch and report).
* Report explicitly: the fragment of delivered content that **no gate covers** — definition bodies of
  rows not pinned by a `rfl` certificate or by a proved identity elsewhere. Estimate its size.

### E. Statement-level science audit (the heart of the review)

For each theory, take its headline claims (start from `theories/<T>/plan.md` §"statement" tables and
`RESULTS.md`), and test:

1. **Non-vacuity / instantiation.** For every `∃`-row: expand the witness and check it satisfies the
   stated predicate *and* carries the intended physical content (a witness inside an empty class is
   vacuous). For every `∀`-row: exhibit at least one instantiation of its hypotheses; if its hypotheses
   are jointly unsatisfiable for some intended parameter region, that is an S2 finding. (The project
   has already re-frozen three vacuous existentials — look for what it missed.)
2. **Premise load-bearing.** For a sample of ≥2 rows per theory: drop a premise and try to refute the
   weakened statement (numeric search in Python first, then a Lean counterexample in the scratch). A
   premise that can be dropped without falsifying the statement is either over-strong (S3) or the row
   is not the sharp statement its prose claims (S2). `unused variable` warnings are the cheap signal —
   check the 3 pre-registered residue sites and then look for premises that *are* used in the proof
   term but whose absence would not falsify the statement.
3. **Over-generalization.** Enumerate the parameter corners the statements admit (0, negative, equal
   quantities, degenerate curvature `lam = 0`, zero rates, coincident constants) and decide for a
   sample whether the statement is *meaningful* there. Totalized conventions (`x / 0 = 0`,
   `Real.sqrt` of a negative = 0) are declared, not defects — but any row whose **truth** depends on
   them, or whose prose silently reads the convention away, is a finding.
4. **Direction and boundary claims.** For every "iff" boundary (the three adjudications A1/A2/A3 and the
   sharp conditions per theory): check both directions are really present, that the boundary is not an
   artefact of the chosen parameter domain, and that the quoted witnesses satisfy the *general* row
   (recompute them independently in Python — e.g. β(1,4) = 2/3, β(4,1) = 1/3, the Stern–Volmer second
   difference = 1, the lossless-corner witness `ic 0 = 0`).
5. **Quantifier drift between prose and Lean.** For every "for all", "exactly", "if and only if",
   "unique", "sharp" in a leaf's prose, locate the declaration and compare quantifiers and premises.
   This is the most frequent overclaim seam in any formalization project.

### F. Numeric and decision layers

* For every closed-form / numeric row (`RatModel` and `Instances` modules, ℚ classifiers, sharp
  constants, κ²-type bounds, witness triples): recompute the value independently (Python `Fraction`)
  and compare to the Lean literal. The project has already had one episode where a *false* numeric goal
  made `norm_num` fail opaquely (`discr(1,2) = 4` — the true value was 1); treat every numeric row as
  suspect until recomputed.
* Check the ℚ decision layers actually *decide* (a stuck `decide` on ℚ with `/` or `^` is a documented
  toolchain boundary) and that no row claims a decision its proof does not perform.

### G. Relation graph: completeness and correctness

* Enumerate all unordered pairs of the 17 nodes (**136**). For each pair, determine from
  `PhotoLean/Relations.lean` (§2, §7–§9, §11–§15) and its registries (§10, §16, §17) whether it has an
  edge or a registered absence with a reason. Report **unregistered pairs** (that is the claim
  "every theory sits on the graph") and any registry row whose stated dependency fact is false (check
  the import structure mechanically: does `PhotoLean/<A>/*` really import only what the row says?).
* **Cause a certificate failure** in the scratch (perturb a `Kernel` definition body, e.g. `barrier`) and
  record which `rfl` certificates and which downstream proofs break. That set is the measured meaning of
  "regression alarm"; compare with the claim in `theories/RELATIONS.md` / `theories/GRAPH-REPORT.md`.
* Verify the accounting claims of each section ("this row adds no mathematics", "this is a re-export"): a
  misclassified row (a new theorem counted as a re-export, or vice versa) is an S2 finding.
* Check the derived count claims: `78` declarations in `Relations.lean`, section-by-section row counts,
  `15` `rfl` certificates (`8` in §1 + `7` in §12), `10` refutation/falsification rows — recount them (`§10.5`).

### H. Documentation claim audit (overclaim hunt)

Read `README.md`, `theories/GRAPH-REPORT.md`, `theories/RELATIONS.md`, and all 17
`theories/<T>/RESULTS.md` + `plan.md` + `TASKS.md`. Build the claim ledger (§8). Rules:

* every number must be recounted from the tree;
* every "verified"/"PASS"/"clean"/"0 differences"/"word-for-word"/"byte-identical" must be matched
  against the *scope* of the command that produced it (signature-level? comment-stripped? sampled?);
  an unscoped verification word is at least S3, and S2 if it implies more than was run;
* every "all"/"every"/"complete"/"only" must be checked by enumeration, not by reading;
* every stale count, wrong plural, or reference to a renamed declaration is a finding (this class has
  already produced at least five real defects in this repository).

### I. Literature and provenance

* For each theory, read `LITERATURE.md`: every source must be checkable (authors, venue, year, DOI) and
  every entry must carry a **formalizable implication** (which assumption became a Lean premise, what
  was declared not proved, what cannot be expressed) and an explicit statement of its epistemic status
  (authority vs practice locus vs preprint). Spot-check 2–3 sources per theory against the file's own
  metadata (no network is available — check internal consistency, DOI/volume/page plausibility, and
  whether the seed corrections the repository records, e.g. the AIE-discovery attribution and the RACI
  terminology pair, are actually applied in the text).
* Finding if: a source is used to justify a *theorem* (literature may only fix statements and premises),
  a formalizable implication is missing, the status is overstated, or a corrected attribution survives
  somewhere in the tree.

### J. Non-kernel "facts" stated as facts

* `TASKS.md` verifier records: do they name a scope, a date, a verdict, and does the tick follow the
  PASS? Any "independently verified" whose record is narrower than the claim is an S2 finding.
* Statement-authority hashes: if a leaf records a sha256 of a skeleton, recompute it
  (`sha256sum`); a mismatch means the authority changed silently. (The repository has had an off-by-one
  prefix defect here.)
* Commit discipline claims: check the actual `git log` against "one commit per theory / per lemma".
* Leaf/text synchronization: a theory whose `RESULTS.md`/`TASKS.md` status text contradicts the tree
  (or another leaf) is a finding.

### K. Policy compliance

* Language: count Chinese characters in delivered Lean sources and leaf markdown
  (`grep -c -P '[\x{4e00}-\x{9fff}]'`). Expected: Lean comments English (a full translation was done);
  `RESULTS.md` bilingual **by design**; `README.md` Chinese **by the repository's own registered
  decision**. Anything else is a finding. Report counts per file, and check whether the files that are
  *supposed* to be bilingual really are bilingual section-by-section (a missing Chinese rendering is a
  drift, not a translation mirror).
* No parallel translated copies (`.en.md` / `.zh.md` mirrors) except the explicitly frozen
  `README.en.md`; new mirrors are findings.

### L. Registered conventions (do not report these as defects — report violations of them)

* `theories/<T>/probes/*-statement-skeleton.lean` intentionally contain placeholders and are outside
  `SOURCE_DIRS` (their compile is a statement-first check, not a delivered proof); verify nonetheless
  that no *delivered* artifact lives under such an excluded path.
* `private` helper lemmas; `set_option linter.unusedVariables false` scoped per declaration; the
  totalized-division convention; three pre-existing `unused variable` warning sites; the RACI port's
  registered deviations (autoImplicit, flattened `Rates/` subdirectory, namespace wrapping).
* Negative results delivered as witness theorems.

---

## 7. Overclaim / over-generalization taxonomy (search patterns)

| id | pattern | how to falsify it |
|---|---|---|
| O1 | **over-generalization**: `∀`-row whose intended domain is a strict sub-case (e.g. positivity/positivity-of-curvature/zero-driving-force assumptions omitted) | instantiate at the un-intended corner in the scratch; if the row is still true but its prose implies the intended domain, quote both |
| O2 | **mechanism from shape**: "same predicate", "same functional form", "same statement shape" silently upgraded to "same mechanism / same object" | locate the declared difference rows; if none exist, the claim is unsupported |
| O3 | **accounting**: "adds no mathematics", "no new content", "re-export" attached to a row that does prove something (or the reverse) | read the row and its proof; reclassify |
| O4 | **verification scope**: "verified / PASS / clean / 0 differences / byte-identical" without the scope (sample? signature-level? comment-stripped? per-row?) | rerun the command; compare its scope to the claim |
| O5 | **population**: "all 17", "every pair", "complete", "only" | enumerate and count; diff against the claim |
| O6 | **literature**: a practice locus or preprint quoted as authority; attribution drift; DOI/venue errors | internal consistency + the repository's own seed-correction notes |
| O7 | **provenance**: "measured at HEAD X / commit Y", "reproducible with command Z" where X/Y/Z do not reproduce the stated result | run Z at HEAD; report divergence |

Severity: **S1** = a delivered statement is false or unproved (including a custom axiom, an unbuilt
delivered module, or a gate that does not bite); **S2** = a claim is stronger than its evidence
(including misclassified accounting, unfaithful statement, non-load-bearing premise presented as
weakest, unregistered pair presented as complete); **S3** = stale/cosmetic documentation defects.

---

## 8. Required report format

```markdown
# PhotoLean audit — <date> — HEAD <sha> (git status: <clean/dirty; list>)

## Verdict
<one paragraph: overall health, number of S1/S2/S3 findings, and the single most important defect>

## Findings
### F1 [S1|S2|S3] <short title>
- Claim / expectation: <quoted, with file:line>
- Evidence: <command> → <raw output excerpt, verbatim>
- Why it is a defect: <argument>
- Minimal reproduction: <exact steps, with scratch path>
- Smallest honest correction (proposal only): <one or two sentences>

## Claim ledger
| claim (file:line) | my verdict | command + raw result |
|---|---|---|
| e.g. "17/17 probes, 0 differences" (theories/GRAPH-REPORT.md:N) | MACHINE-BACKED | `python3 ... --theory RACI` → `signature differences: 0` |
| e.g. "every theory sits on the graph" | UNDETERMINED | pairs 3/136 unregistered (list) |

## Coverage ledger
| axis | status | notes / commands |
|---|---|---|
| A tree & contract | EXECUTED | ... |
| ... | NOT EXECUTED | reason |

## What I could not check (and why)
<list>

## Appendix: raw command log
<commands with exit codes and key output lines>
```

Use exactly these verdicts in the claim ledger: `MACHINE-BACKED` (a kernel-accepted declaration or a
command's output directly establishes it), `TEXT-ONLY` (true as written but nothing checks it),
`FALSE`, `STALE` (was true, no longer is), `UNDETERMINED` (you could not decide; say why).

---

## 9. Calibrated failure archaeology (the defects this codebase actually produces)

These are real, previously-found defect classes in this repository. Use them as search templates —
each one was found by the kind of check you are about to run, and each has a plausible sibling still
present.

1. **Vacuous bridge rows**: four `Rat.*_cast` rows read `↑x = ↑x` because a `Rat.`-prefixed
   declaration name made the right-hand side resolve inside `namespace Rat` (shadowing). *Template:
   `#print`-check every bridged/`Rat.*` row.*
2. **A "decorative" premise that was load-bearing**: a delivery note called `x₁ ≠ x₂` decorative; at
   `x₁ = x₂ = 2, lam = 1` the iff is false. *Template: strip each premise and test.*
3. **A load-bearing premise trimmed by a linter**: dropping `lam ≠ 0` from a crossing row made it false
   at `lam = 0, x = 1`. *Template: never trim on linter advice alone.*
4. **A reversed direction**: a Stokes-shift corner row was delivered with the implication the wrong way
   (witness `lam = 1, e00 = 2`). *Template: instantiate both sides.*
5. **A degenerate parameter corner**: a phosphorescence ratio row was false at `kF = kIC = 0`. *Template:
   test the zero/zero corner of every ratio row.*
6. **A numeric row whose expected constant was wrong**, making `norm_num` fail opaquely. *Template:
   recompute constants in Python first.*
7. **Prose counts drifting from the tree**: stale theory counts, "five probes" where seven were run, an
   off-by-one sha256 prefix, a lost auxiliary in an enumeration. *Template: recount every number.*
8. **A skeleton extractor that silently kept term-mode bodies** (44/46 placeholders while the note said
   46) — a flagged count discrepancy left as a note instead of a TODO. *Template: verify placeholder
   counts, not just "it compiles".*
9. **A checker with a keying bug** that keyed signatures by bare name, hiding 5 false differences, and
   later truncated dotted names. *Template: audit the checker as adversarially as the content.*
10. **Policy violations surviving a translation pass** (~149 Chinese comment lines in ported modules).
    *Template: grep by character class, not by eyeballing.*
11. **Process inversion**: board rows ticked before the audit that validated them. *Template: compare
    timestamps/order of records with the commit history.*
12. **A verification phrase narrower than the claim**: "all 30 declarations" checked for one early
    module pair, "46 rows" checked for a batch, while the repository-wide phrase is "no custom axioms".
    *Template: match every scope word to the command that produced it.*

---

## 10. Verified recipes

Every recipe below was executed on 2026-09-23 against this repository; the parenthesised values are the
measured results. **Re-run them yourself and report the values you get** — a divergence between your
numbers and these is itself evidence.

### 10.1 Scratch copy (never mutate the delivered tree)

```bash
cd <repo root>
S=.lake/tmp/audit               # gitignored; any writable dir works (note: /tmp and $HOME may be
mkdir -p "$S/.lake"             #  volatile/read-only on some machines — prefer this path)
rsync -a --exclude '.lake' ./ "$S/"
ln -s "$PWD/.lake/packages" "$S/.lake/packages"     # ~4.7 GB of prebuilt mathlib: symlink, never copy
cd "$S" && proofs/scripts/check.sh --strict          # (clear build ~43 s; ~1 s when .lake/build was copied)
```

`.toolchain` is itself a symlink and copies fine. Do not copy `.lake/packages`.

### 10.2 The repository's acceptance commands (run first, from the real tree)

```bash
git log -1 --oneline && git status --short
proofs/scripts/check.sh --strict                      # (exit 0; build: OK; scan: clean; 17/17 leaf planes; verdict: PASS)
for T in Marcus Hammond BEP Kasha Sabatier Goldschmidt SymmetryFactor KashaVavilov SternVolmer \
         QuantumYield FluorPhos EnergyGapLaw StokesShift ICvsISC Forster Einstein RACI; do
  python3 theories/BEP/probes/bep-fidelity.py --theory "$T"
done                                                  # (each: signature differences: 0, not delivered yet: 0)
proofs/scripts/axioms.sh PhotoLean.Relations PhotoLean.Relations.kv_d2_verdict   # (verdict: PASS block)
```

### 10.3 `defaultTargets` vs the disk set (the measured acceptance hole)

```bash
find PhotoLean -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | sort > .lake/tmp/disk-mods.txt
python3 - <<'EOF'
import re
s = open('lakefile.toml').read()
block = s.split('defaultTargets')[1].split(']')[0]
targets = set(re.findall(r'"(PhotoLean[^"]+)"', block))
disk = {l.strip() for l in open('.lake/tmp/disk-mods.txt') if l.strip()}
print('targets:', len(targets), 'disk:', len(disk))
print('on disk, not a target:', sorted(disk - targets))
print('target, not on disk   :', sorted(targets - disk))
EOF
```

Measured 2026-09-23: no diff (95 targets = 95 files). But the hole is real — see the table in §6.B:
a module removed from the list is not compiled by the bare gate, so this equality must be re-verified
after every delivery.

### 10.4 Exhaustive `#print axioms` sweep

```bash
python3 - <<'PY' > .lake/tmp/sweep.lean
import re, glob, os
# NOTE: `private` declarations are excluded on purpose — their names are mangled and are not
# addressable by `#print axioms`. They add no trust beyond their public consumers (which are swept).
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|protected\s+)?"
                  r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([A-Za-z_][\w'\!\?]*)")
NS, END = re.compile(r"^namespace\s+(\S+)"), re.compile(r"^end(\s+(\S+))?\s*$")
files = sorted(glob.glob('PhotoLean/**/*.lean', recursive=True))
names, stack = [], []
for f in files:
    for line in open(f, encoding='utf-8'):
        if (m := NS.match(line)): stack += m.group(1).split('.')
        elif (m := END.match(line)):
            if m.group(2):
                for _ in m.group(2).split('.'):
                    if stack: stack.pop()
            elif stack: stack.pop()
        elif (m := DECL.match(line)):
            names.append('.'.join(stack + [m.group(2)]) if stack else m.group(2))
print('\n'.join('import ' + os.path.splitext(f)[0].replace('/', '.') for f in files))
print('\n'.join(f'#print axioms {n}' for n in names))
print(f"-- files {len(files)} names {len(names)}", file=__import__('sys').stderr)
PY
proofs/scripts/lake env lean .lake/tmp/sweep.lean > .lake/tmp/sweep.out 2>&1
python3 - <<'PY'
import re
txt = re.sub(r"\s+", " ", open('.lake/tmp/sweep.out').read())
rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [(n, a) for n, a in rows if {x.strip() for x in a.split(',') if x.strip()} - allowed]
print('rows:', len(rows), '| outside allowed:', len(bad))
for n, a in bad[:20]: print(' ', n, '->', a)
print('unparsed mentions:', txt.count('depends on axioms') - len(rows), '| unknown consts:',
      txt.count('unknown constant'))
print('failing names (triage as extraction noise or a real defect):')
import re as _re
for m in _re.finditer(r"(?:unknown constant|unknown identifier) '([^']+)'", txt): print('  ?', m.group(1))
PY
```

Measured on 2026-09-23 (this exact script, from the repository root): 95 files, 1313 extracted names,
**1278 rows printed, 0 outside the allowed triple**, 18 unknown constants (extraction noise — mostly
dotted/namespace-aliased names), runtime ~2.5–5 min. The whitespace-flattening parse is what makes the
wrapped output parseable (a naive line-based parse silently loses ~95 % of the rows).

Two things to report from this sweep: (i) it sweeps *every* public declaration in the repository in one
run — the project's own records sweep per row by hand, so this is a strictly stronger check and any hit
is an S1 finding; (ii) the number of declarations printed will **not** equal the documented "delivered"
totals (the extractor also picks up `structure`/`inductive`/`instance` lines, and the documented totals
are per-theory public counts). Reconcile the difference or report it as unexplained.

### 10.5 Recounting the headline numbers (measured values in parentheses)

```bash
find PhotoLean -name '*.lean' | wc -l                        # (95 = 92 theory modules + Kernel + Relations + Smoke)
ls -d theories/*/ | wc -l                                    # (17 theories)
awk '/\/-! ## /{n++} END{print n}' PhotoLean/Relations.lean  # (17 sections)
grep -cE '^(theorem|lemma|def|noncomputable def) ' PhotoLean/Relations.lean   # (78 declarations)
grep -rhoE '^(theorem|lemma) [A-Za-z_][A-Za-z0-9_.]*(refut|falsif|not_model_consistent)[A-Za-z0-9_.]*' \
  PhotoLean/ | sort -u | wc -l                               # (10 names; one of them packs both halves)
grep -c ':= rfl$' PhotoLean/Relations.lean                     # (8 — the §1 kernel certificates)
grep -nE '^\s+(EnergyGapLaw|StokesShift|ICvsISC)\.cert_' PhotoLean/Relations.lean | wc -l   # (7 — the §12 certificates)
```

Note the third command: a *partial* pattern (omitting `not_model_consistent`) yields 6, and a
recollection-based count has already produced a wrong number in this repository's own report
(GRAPH-REPORT said "9 rows" until the recount above corrected it to 10) — this is exactly the O5
pattern, so treat every count in every document as a claim to be recounted, including the ones in this
file.

### 10.6 Fidelity-checker adversarial tests (in the scratch, invoked from the scratch)

```bash
cd .lake/tmp/audit
python3 theories/BEP/probes/bep-fidelity.py --theory KashaVavilov            # baseline: 29/29, 0 differences
# then, one at a time:
#  (a) rename an authority declaration       → word-for-word 27, not delivered yet 1, signature differences 1
#  (b) add a premise to an authority theorem → word-for-word 28, signature differences 1
#  (c) add a new auxiliary declaration       → delivered, not in authority 10 → 11
#  (d) change a definition body only         → 29/29, signature differences 0   (documented blind spot)
git checkout -- PhotoLean   # or re-rsync, to restore
```

**Trap (measured):** the checker resolves the repository root from its own file path. Invoking the
*original* script by absolute path while standing in the scratch compares the **original** tree and
shows "0 differences" no matter what you mutated. Always invoke the copy.

### 10.7 Causing a certificate failure (regression-alarm claim)

In the scratch, change one line of a `Kernel` definition body (e.g. add `+ 1` to `barrier`), then run
`proofs/scripts/check.sh --strict` and record exactly which certificates and which downstream theorems
fail. Report that set against the claim that a failing certificate is a "regression alarm".

### 10.8 Enumerating the relation graph's pairs

```bash
python3 - <<'PY'
import itertools
nodes = ['Marcus','Hammond','BEP','Kasha','Sabatier','Goldschmidt','SymmetryFactor','KashaVavilov',
         'SternVolmer','QuantumYield','FluorPhos','EnergyGapLaw','StokesShift','ICvsISC','Forster',
         'Einstein','RACI']
pairs = list(itertools.combinations(nodes, 2))
print(len(pairs), 'unordered pairs')          # (136)
PY
```

For each pair, cite the section of `PhotoLean/Relations.lean` (edge) or the registry paragraph
(`§10`, `§16`, `§17`) that covers it. Uncovered pairs are findings against §6.G.

---

## 11. Non-negotiables, restated for the report's appendix

* Your audit must not leave the delivered tree modified: run `git status --short` at the end and state
  it in the report. If the tree is dirty, say so and list the files.
* Every finding must carry the command and raw output that produced it; a finding you cannot reproduce
  goes to "could not check".
* Do not fix, do not commit, do not tick anything. The repository's own rule when a certificate fails is
  *stop and investigate*; the same applies to everything you find.
* If you find no defect in an axis, say so **with the evidence** ("axis B: gate bites — three mutations,
  three expected failures, raw output in appendix") — an unevidenced "looks fine" is not a result.

---

## 12. 中文速览

**任务**：作为独立对抗性审查者，全面找出本仓库的**错误、缺口、漏洞、过度归纳、过度声称**，每条结论必须附
原始命令输出。产物是**审查报告**，不是补丁。

**红线**：只读交付内容（`PhotoLean/**`、`theories/**` 等）；实验只在仓库内 gitignore 的 `.lake/tmp/<name>/`
副本里做；禁止 `lake update`；用 `proofs/scripts/lake` 包装器。

**必须写的三张表**：①**发现表**（严重级别 S1/S2/S3 + file:line + 断言原文 + 原始输出 + 最小复现 + 为何
是缺陷）；②**断言账**（每条招牌断言 → MACHINE-BACKED / TEXT-ONLY / FALSE / STALE / UNDETERMINED + 判定
命令）；③**覆盖账**（轴 A–L 逐条 EXECUTED / NOT EXECUTED 及原因）。外加"无法核查的清单"与末尾
`git status`。

**十条审查轴**：A 树状态与契约；B 门是否真的咬人（四个变异实验 + **defaultTargets 与磁盘集合相等性**——
实测：不在该列表里的模块根本不被编译，门照样 PASS）；C **全仓库** `#print axioms` 扫描（项目平时只抽查）；
D 保真度与探针自身的盲区（实测：改定义**体**探针看不见 29/29；改签名/改名/加声明都能看见）；E 语句级科学
审查（非空泛、前提承重、退化角落、iff 边界、散文与 Lean 的量词漂移）；F 数值/判定层独立重算；G 关系图
136 对配对的完整性与 `rfl` 证书报警的真实性；H 文档断言审计（每个数字重数、每个"已验证"对照其范围）；
I 文献与出处；J 非内核"事实"（verifier 记录、sha256、提交纪律）；K 语言政策；L 已登记约定（不要当作缺陷）。

**过度声称分类 O1–O7**：O1 过度归纳（∀ 覆盖了非预期域）；O2 由"形状相同"滑到"机制相同"；O3 记账错误
（"不含新数学"其实含）；O4 验证词的作用域大于实际（签名级/抽样/剥注释）；O5 全域词（"全部 17""每一对"）
未枚举；O6 文献越权（实践位点当权威）；O7 出处不可复现（HEAD/命令与数字不符）。

**已实测的陷阱**：`bep-fidelity.py` 用**自身路径**解析仓库根——在副本里必须跑副本里的脚本，否则你在审查
原树、任何变异都显示 0 差异；`.lake/packages` 是 4.7 GB 预构建 mathlib，只能软链不能拷；`#print axioms`
输出会折行，必须先压平空白再正则解析。

**校准过的历史缺陷类型（共 12 类，见 §9）**：空泛的桥接行、被误标"装饰性"的承重前提、被 linter 建议削掉
的承重前提、方向写反、零/零角落为假、数值行期望值算错、文档计数漂移（已发生 ≥5 次）、骨架占位计数
44/46、检查器自身键控 bug、语言政策违规、先打勾后审计、验证词范围窄于声称。**用它们当搜索模板**。
