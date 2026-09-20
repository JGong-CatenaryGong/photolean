# Experience Bank

> English translation of `proofs/EXPERIENCE.md`. The Chinese original at `proofs/EXPERIENCE.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.

> This file is the **engine's self-reflective memory**. `TASKS.md` records "what has been done"; this file records
> **"what was tried, why it failed, and what finally worked"** — the latter is what can be reused across rounds.

## Why it exists

The most expensive waste in a formalization iteration is **re-walking the same dead end**: one class of goals (for example "strict monotonicity
of the reals under composition with `1/x`") has to be re-discovered tactic by tactic for every new lemma. The engine's iteration loop
(`workflow` fan-out / `ralph` fresh rounds) carries no memory of its own — the shared workspace is the carrier of long-term
memory, and this file is that carrier.

This corresponds to the **Experience Bank** of Hyra-1.0: the Proposal Agent writes its "inspirations" back every round, and the
next round starts from historical experience instead of from zero. One simplification in the Lean setting is that
**the evaluator is the kernel** (`lake build` + `check.sh --strict`); there is no "the evaluator gets reward-hacked so it must
co-evolve" problem as in αEvolve/Hyra, so a single layer of experience accumulation suffices.

## How entries are written (mandatory format)

Each entry gets one `##` heading with four fixed parts: `Goal` / `Tried and failed` / `Worked` / `Reusable pattern`.
**Failed paths must be recorded** — an experience bank that records only successes has no value.

```markdown
## YYYY-MM-DD — <lemma or class of goals> — <role> — <result>
- Goal: <exact statement or goal shape>
- Tried and failed: <tactic/lemma + key error message> (one per item)
- Worked: <final proof skeleton + commit>
- Reusable pattern: <one sentence, a criterion that transfers to other lemmas>
```

---

## 2026-09-20 — Behavioral validation of the acceptance gate itself (scaffolding) — lead — DONE

- Goal: confirm that `check.sh --strict` + `axioms.sh` really stop the three kinds of cheating, instead of only being written down in the documentation.
- Tried and failed: none (this is a validation of the gate itself, not of the proofs the gate is supposed to stop).
- Worked (four samples, measured results):

  | Sample | `lake build` | `check.sh --strict` | `axioms.sh` |
  |---|---|---|---|
  | clean tree | EXIT 0 | **PASS** | PASS |
  | proof body contains `sorry` | **EXIT 0** ⚠️ | FAIL | FAIL (sorryAx) |
  | custom `axiom` declaration | **EXIT 0** ⚠️ | FAIL | FAIL |
  | theorem body hides `sorry` (statement is clean) | **EXIT 0** ⚠️ | FAIL | FAIL (sorryAx) |

- **Reusable pattern (the most important one)**: a successful `lake build` **cannot** prove that a theorem is true —
  `sorry` and a custom `axiom` both produce only a warning, and `build` returns 0 all the same.
  Hence "the build passes" never constitutes acceptance; it must be layered with (1) a source scan + (2) `#print axioms`.
  Any one of the three layers can be bypassed on its own: a custom `axiom` contains no `sorry` keyword (caught by scanning for `axiom` at the start of a line),
  and an in-line `sorry` may be let through by the comment rules (caught by the `sorryAx` reported by `#print axioms`).
  **The engine's acceptance gate must have all three layers, and it must be executed by a role that does not write the proofs.**

## 2026-09-20 — Marcus plan written to disk + statement skeleton (S0) — lead — DONE

- Goal: turn the three-part requirement of "the Marcus inverted region" (formalized description / proof and conditions of validity / instance decision)
  into exact Lean statements for M1–M5, and get the skeleton to compile (the statement-first gate).
- Tried and failed (three items, all hard facts of the toolchain):
  1. Using the Greek letter `λ` as a Lean identifier (`noncomputable def barrier (λ x : ℝ) ...`) →
     30+ errors across the whole skeleton: `unexpected token 'λ'; expected '_' or identifier`.
     **In Lean 4, `λ` is the lambda keyword, not a legal identifier character**.
  2. `by decide` on `zoneQ (1 : ℚ) (3/4) = Zone.normal` → fails:
     `its 'Decidable' instance ... did not reduce to 'isTrue' or 'isFalse'`;
     the reduction gets stuck on the gcd/division path of `Rat.instDecidableLt` → `Int.decNonneg`.
     **For ℚ, `decide` is only reliable on the integer reduction path** (`zoneQ 1 3`, `zoneQ 1 1` do go through).
  3. Writing the statement skeleton directly into `PhotoLean/` → it gets caught by the unfinished-proof scan of `check.sh --strict`
     (zero tolerance in the source tree), which makes "write the statements first, fill in the proofs later" unenforceable as a discipline.
- Worked:
  1. All Lean-side identifiers are ASCII: `lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` /
     `a1` / `a2` (physical notation is kept only in the documentation);
  2. rational decisions involving division switch to `norm_num [zoneQ]`; purely integer arguments keep `decide`;
  3. the skeleton lives in `proofs/probes/marcus-statement-skeleton.lean` (**not in `SOURCE_DIRS`**) →
     31 unfinished-proof warnings, **0 errors**; the four risk probes at the end (`decide`, `Real.exp_lt_exp.mpr`,
     `positivity`, `nlinarith` + `div_lt_div_of_pos_right`) **all genuinely pass**, i.e. the key goal shape of M2
     already has a usable kernel.
- Reusable patterns:
  - **a statement-first skeleton must live outside the scope of the source scan**, otherwise that gate is unenforceable as a discipline;
  - **symbol characters are forbidden in Lean identifiers** (`λ` / `∀` / `→` / `∑`): ASCII-izing the physical quantity names once up front
    saves a whole round of renaming;
  - the reliable domain of `decide` is **pure Nat/Int reduction**; as soon as a literal involves division or a modulus, switch to `norm_num`
    (it produces a proof term and does not rely on kernel reduction).

## 2026-09-20 — Planning-phase discovery: the positivity premise on the descriptor cannot be dropped (physics side, the core of this project) — lead — DONE

- Goal: pin down the **sharp conditions of validity** of the "inverted-region descriptor" (the second part of the human requirement).
- Tried and failed: writing the descriptor as
  `InvertedDescriptor A lam kB T := ∀ x₁ x₂, lam < x₁ → x₁ < x₂ → rate A lam kB T x₂ < rate A lam kB T x₁`
  and conjecturing `InvertedDescriptor ⟺ 0 < lam ∧ 0 < kB*T ∧ 0 < A` —— **this conjecture is wrong**.
- Counterexample (found by hand computation during planning, later pinned down by writing it as the M4a stretch theorem): take `A < 0 ∧ lam < 0 ∧ 0 < kB*T`:
  `lam < 0` makes `barrier lam ·` **decreasing** inside the inverted region, so `exp(-Φ/(kBT))` is increasing and,
  multiplied by the negative `A`, becomes **strictly decreasing** —— the descriptor holds, but the rate is **negative** (unphysical).
  (The other unphysical branch: for `lam = 0` the Lean division-by-zero convention gives `barrier 0 x = 0`, the rate is constantly `A`, and strictness fails.)
- Worked (the corrected statement written into `plan.md` §7.1): fold "the rate is positive everywhere" into the characterization:
  `((∀ x, 0 < rate A lam kB T x) ∧ InvertedDescriptor A lam kB T) ⟺ 0 < A ∧ 0 < lam`
  (under the physical premises `0 < kB`, `0 < T`); necessity splits into the two branches `lam = 0` and `lam < 0`,
  and both branches need only ready-made lemmas from M2.
- Reusable patterns:
  - **predicate propositions of the form "some descriptor holds" must be given a sharp characterization jointly with "the physical quantities have physical meaning" (positivity)**,
    otherwise a purely algebraic manipulation produces solutions that "hold formally but are physically absurd";
  - **keeping the unphysical branch as a theorem** (`inverted_descriptor_holds_of_neg`) is more valuable than deleting it ——
    it is precisely the checkable evidence that "the positivity premise cannot be dropped";
  - whenever a definition contains a division, first ask **"what does Lean take as the value when the denominator is zero"**: the `/0 = 0`
    convention quietly manufactures extra degenerate branches, and a sharpness proof must cover them explicitly.

## 2026-09-20 — M1 descriptor layer: correctness of the `zone` three-way classification (4 theorems) — prover_a — DONE

- Goal: `zone_eq_normal_iff` / `zone_eq_barrierless_iff` / `zone_eq_inverted_iff` / `zone_trichotomy` of
  `PhotoLean/Marcus/Basic.lean` (`zone lam x := if x < lam then .normal else if x = lam then .barrierless else .inverted`).
- Tried and failed (four items, all measured errors, archived in the probe `proofs/probes/marcus-prover_a-scratch.lean`):
  1. `iff_of_false (by decide) (ne_of_lt h).symm` →
     `application type mismatch: Ne.symm (ne_of_lt h) has type lam ≠ x but is expected to have type ¬x = lam`.
     **The direction of `ne_of_lt h : a ≠ b` is already the `¬(a = b)` the proof needs; wrapping an extra layer of `Ne.symm` around it flips the direction the wrong way.**
  2. Alternative A, `cases h : zone lam x <;> simp` → it goes through (all three branches close automatically), but it relies on `simp`'s
     reduction of `Or` and of constructor equalities; **`by_cases` + `if_pos` with explicit branches is more robust** (see below).
  3. Alternative B, a single layer of `by_cases h : x < lam` followed by `simp [zone, NormalRegion, h]` → the second branch gives
     `unsolved goals ⊢ ¬(if x = lam then Zone.barrierless else Zone.inverted) = Zone.normal`:
     `simp` first reduces `a ↔ False` to `¬a`, and at that point the inner `if` lacks a criterion for `x = lam`, so **a second layer, `by_cases h2`, must be added**.
  4. Alternative C, using `lt_trichotomy` for the three-way split and then pushing `h : lam < x` directly into `simp` →
     `unsolved goals ⊢ (if x < lam then Zone.normal else if x = lam then Zone.barrierless else Zone.inverted) = Zone.inverted`:
     **`simp` cannot use `h` to simplify `x < lam` in reverse** (`lam < x` is not a rewrite rule for `x < lam`),
     so the negated proposition must be supplied explicitly: `not_lt.mpr (le_of_lt h)` / `ne_of_gt h`.
- Worked (one commit per lemma: `3644a82` definitions / `f3d2055` / `ac80776` / `c98c85d` / `1376f8e`):
  ```lean
  unfold zone NormalRegion            -- or zone / zone InvertedRegion
  by_cases h : x < lam
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]
    by_cases h2 : x = lam
    · rw [if_pos h2]; exact iff_of_false (by decide) h
    · rw [if_neg h2]; exact iff_of_false (by decide) h
  ```
  `zone_trichotomy` uses the same branch tree to hand out the witnesses directly: `Or.inl rfl` / `Or.inr (Or.inl rfl)` / `Or.inr (Or.inr rfl)`.
- Names confirmed usable by measurement (the `#check` output is in the probe; archived for API-NOTES):
  `@if_pos : ∀ {c} {h : Decidable c}, c → ∀ {α} {t e}, (if c then t else e) = t` (with `if_neg` the dual of the same shape),
  `@iff_of_true : ∀ {a b : Prop}, a → b → (a ↔ b)`, `@iff_of_false : ∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)`,
  `@le_of_not_gt`, `@le_of_lt`, `@ne_of_lt`, `@lt_of_le_of_ne`, `@Ne.symm`, `@lt_irrefl`, `@not_lt`.
- Reusable patterns:
  - **for an ⟺ lemma about an `if`-based classifier, "two layers of `by_cases` + `if_pos`/`if_neg` + `iff_of_true`/`iff_of_false`"
    is the shortest path with zero reliance on `simp`**; the `simp` route needs **all** the criteria of both layers fed to it, otherwise the inner `if` does not move;
  - **constructor distinctness for `Zone` (deriving `DecidableEq`) can be closed directly by `by decide`** ——
    no need for names such as `noConfusion` / `reduceCtorEq` that would have to be guessed;
  - ⚠️ **the scan of `check.sh --strict` includes block comments**: writing the two scanned keyword literals inside a file header's `/- ... -/`
    causes a false-positive FAIL (measured: one occurrence in the header comment gives `verdict: FAIL`).
    When discussing the discipline inside a delivered file, **change the wording** (in that instance it was changed to "零占位证明、无自定义公理声明" [= "zero placeholder proofs, no custom axiomatic declarations"]).
    This is a pitfall that the prover side must know about (the script's own comments mention only "manually re-checked by the verifier"; in fact `--strict` gives FAIL directly).

## 2026-09-20 — M4b microscopic reorganization-energy positivity (`Marcus/Reorg.lean`, zero-dependency side branch) — prover_d — DONE

- Goal: the 2 definitions + 4 theorems of `PhotoLean/Marcus/Reorg.lean` (which only does `import Mathlib`);
  the signatures must be **verbatim identical** to the M4b section of `proofs/probes/marcus-statement-skeleton.lean`
  (verified by extracting the statements on both sides with a script and diffing them: 6/6 VERBATIM MATCH).
- Tried and failed (3 items, all transferable):
  1. **The proof hint in `plan.md` §7.2 is wrong at the API level**: copying the hint and writing `sq_pos_of_ne_zero dq hdq`
     → `application type mismatch: dq has type ℝ but is expected to have type ?m ≠ 0`.
     The signature measured on v4.17 is `∀ {R} [LinearOrderedSemiring R] [ExistsAddOfLE R] {a : R}, a ≠ 0 → 0 < a ^ 2`
     —— **`a` is an implicit argument**, and the correct form is `sq_pos_of_ne_zero hdq`.
     Conclusion: a proof hint in a planning document is an "intention", not an API fact.
  2. `set_option linter.unusedVariables false in` **cannot immediately follow a doc comment** `/-- ... -/`
     → `error: unexpected token 'set_option'; expected 'lemma'` (only declaration commands are accepted after a doc comment).
     Fix: write the explanation as an ordinary block comment `/- ... -/` → then `set_option ... in` → then the doc comment + theorem.
  3. A hand-computed geometric factor in a probe was wrong: for `R = 1/2, a1 = a2 = 1`,
     `1/(2a₁) + 1/(2a₂) − 1/R = −1 < 0` (the geometric factor can be positive only for `R > 1`)
     → `norm_num` reports unsolved goals; **let the machine backstop hand computation** (do not trust mental arithmetic when constructing non-empty witnesses).
- Worked (proof skeletons, passing on the first attempt):
  - `lamInner_nonneg`: `unfold lamInner; positivity` (`positivity` reads the hypothesis `0 ≤ kk` directly);
  - `lamInner_pos`: `have hsq : 0 < dq ^ 2 := sq_pos_of_ne_zero hdq` → `unfold lamInner; positivity`;
  - `lamOuter_pos`: `linarith` turns `hgeom` / `hPekar` into positivity of the two factors respectively →
    `positivity` yields `0 < dE ^ 2` → `mul_pos (mul_pos hdE2 hgeom') hPekar'`;
  - `lam_total_pos`: `linarith`.
  - Commits (one commit per lemma): `2d4e296` definitions / `723034d` / `acc5e8e` / `fcb7589` / `de63c09`.
  - Evidence: `check.sh --strict PhotoLean.Marcus.Reorg` verdict PASS; for all 4 theorems `axioms.sh` reports
    `depends on axioms: [propext, Classical.choice, Quot.sound]` → PASS.
- Reusable patterns:
  - **`linarith` is the best converter from "inequality premises" to "positivity of factors"**: when the goal has the shape `0 < A + B - C`,
    directly `have : 0 < A + B - C := by linarith`, then hand it to a `mul_pos` combination;
    this is more robust, and its error messages are more readable, than letting `positivity` chew on "a multi-factor product with parentheses" alone.
  - **`positivity` does read the positivity hypotheses from the context**, so `unfold <def>; positivity` is the default closer for
    goals of the kind "the definition equals an explicit product/quotient" —— but strictness premises (such as `dq ≠ 0`)
    must first be supplied as `have hsq : 0 < dq ^ 2` by yourself.
  - **when the signature carries a "physical domain premise" that the proof does not use, do not change the signature for that reason** (plan §7.2 explicitly requires
    these premises to be visible in the signature). The approach: use an ordinary block comment to state clearly "which premises are domain conditions and which ones the proof genuinely uses",
    then silence the warning with a **local** `set_option linter.unusedVariables false in` —— it affects only that theorem,
    the statement and the skeleton remain verbatim identical (and this is easier for the verifier to read than a row of warnings).
  - **run a "statement vs skeleton" script diff before delivery** (extract the `theorem/def ... :=` prefixes with a regex, then normalize whitespace);
    it is more reliable than a manual comparison and can serve as the machine evidence for statement-first.
  - `experience.md` is a hot spot for concurrent writes: when appending, use a **unique anchor** for the local replacement; if it reports
    "file changed since it was read", read it again and retry (in this instance a concurrent append by prover_a blocked it once).

## 2026-09-20 — ⚠️ the lead's concurrent-commit incident: `git add -A` swallowed the workers' intermediate artifacts — lead — FAIL→fixed

- Goal: commit the back-filled literature parameters of `plan.md` §8.3 together with the task-board status update.
- Tried and failed: the commit used `git add -A` (to save effort). Three workers were concurrently writing their own work files at that moment,
  and so:
  - `e53d562` (which was supposed to be "task board + lakefile") got mixed with a 453-line draft of `proofs/LITERATURE.md`,
    two probes from `api_researcher`, `prover_b`'s scratch probe, and the **deletion of `marcus-lemma-skeletons.lean`**;
  - `c000996` (which was supposed to be "plan document update") got mixed with **WIP on `PhotoLean/Marcus/Barrier.lean`** and two scratch probes.
  Consequence: **`barrier_nonneg` (the first theorem of M2) lost its own per-lemma commit** —— its content landed in a
  commit titled `docs(plan): ...`, and the audit trail was polluted.
- Worked (remediation):
  1. **the rule was written into the task board**: the lead uses only `git add <explicit path>` (`plan.md`/`proofs/TASKS.md`/`proofs/EXPERIENCE.md`/`lakefile.toml`),
     and **never `git add -A`/`git add .`**; the corresponding rule for workers is "add only your own owned files";
  2. the deviation is **recorded truthfully in the task board** on the `barrier_nonneg` row (no faking a "remediation commit" to back-fill the audit trail —— that would be worse than the deviation itself);
  3. the affected workers were notified: do not retry the already-absorbed commit, keep committing the remainder lemma by lemma.
- Reusable pattern: **when several writers share one git repository, `git add -A` is the number-one source of concurrency incidents**.
  The correct posture is "ownership is the commit boundary": whoever owns a file adds it, and the lead adds only the leaf documents.
  One more: **the incident itself must be written into the experience bank rather than erased** —— erasing it makes the next round's fresh agent repeat the same mistake,
  whereas recording it turns the "rule" into a checkable task-board item.
- Unaffected (important): the four delivered M1 theorems and the five M4b theorems each have correct per-lemma `feat(M1)`/`feat(M4b)` commits.

## 2026-09-20 — race-condition bug in the acceptance gate itself: a fixed probe path causes "ask A, answer B" — prover_b reports / lead fixes — FIXED

- Goal: make `axioms.sh` produce **trustworthy evidence** when several workers run acceptance concurrently.
- Tried and failed (**a problem with the gate itself, not with the proofs**): the original implementation wrote the probe to the fixed path
  `.lake/tmp/AxiomsProbe.lean`. prover_b measured the following while looping over three theorems serially:
  ```
  ask PhotoLean.Marcus.rate_pos          → prints 'PhotoLean.Marcus.Rat.zoneQ_eq_zone' depends ...
  ask PhotoLean.Marcus.rate_ratio        → prints 'PhotoLean.Marcus.barrier_at_lam' depends ...
  ```
  i.e. another prover running at the same instant had overwritten the probe file. **The harm is not a false PASS (the printed axiom set still comes from some real theorem),
  but mismatched false evidence**: the verifier would use A's axiom report to prove that B is clean —— the audit trail is polluted, which is more dangerous than a plain error.
- Worked: the probe path was made **unique per invocation** (`AxiomsProbe.$$.$RANDOM.lean`) + `trap 'rm -f' EXIT` cleanup;
  concurrency isolation measured: 4 different theorems run at the same time, each printing its own name, all of them
  `verdict: PASS (only mathlib infrastructure axioms)`. **The acceptance criterion did not change; only the race was eliminated.**
- Reusable patterns:
  1. **the acceptance gate itself must be validated too** (this project already validated once at Sprint 0 that "the gate stops cheating"),
     but that validation was **serial**; **concurrency** is a different failure mode (a race) and must be validated separately whenever several agents work in parallel;
  2. in any script that "writes a temporary file and reads it back", the temporary file name **must contain a PID or a random segment**; a fixed temporary name = a time bomb;
  3. the bug reporter (prover_b), besides reporting the bug, also supplied an **isolated re-check** (starting a probe on a unique path, re-running it, and keeping the output) ——
     this is "the correct response when evidence has been polluted": not giving up, but obtaining the evidence again through a path that cannot be polluted.

## 2026-09-20 — M2 barrier algebra (9 theorems, including the direction reversal of the two μ/λ branches) — prover_a — DONE

- Goal: the 9 theorems of `PhotoLean/Marcus/Barrier.lean` (which only does `import PhotoLean.Marcus.Basic` and **creates no new definitions**),
  whose signatures must be **verbatim identical** to the M2 section of `proofs/probes/marcus-statement-skeleton.lean`:
  `barrier_nonneg` / `barrier_at_lam` / `barrier_symm` / `barrier_min_at_lam` / `barrier_mono_of_pos` /
  `barrier_antitone_of_pos` / `barrier_antitone_of_neg` / `barrier_zero_lam` / `barrier_mono_cases`
  (the last three are the "direction reversal" and the degenerate branch: for `lam < 0` the barrier **decreases** inside the inverted region, and for `lam = 0` it is identically zero).
- Tried and failed (4 items, the first 3 transferable):
  1. **`nlinarith` cannot take a goal containing division directly.** On a shape such as `(lam-x₁)^2/(4*lam) < (lam-x₂)^2/(4*lam)`, a direct
     `nlinarith` cannot close it (it neither clears the denominator for you nor introduces the positivity of the denominator) → the **sign** of the denominator must first be built into an explicit `have`,
     reducing the goal to a denominator-independent pure square comparison:
     `have h4 : (0:ℝ) < 4*lam := by positivity`,
     `have hsq : (lam-x₁)^2 < (lam-x₂)^2 := by nlinarith`, then `div_lt_div_of_pos_right hsq h4`.
     **The negative-denominator branch is more dangerous**: for `lam < 0` you cannot use `div_lt_div_of_pos_right`; and
     `div_lt_div_of_neg_right` **does not exist** (`#check` reports unknown). What is available is
     `div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)` —— it is an **iff, and the RHS order is reversed**
     (the right-hand side is `b < a`), which is extremely easy to write the wrong way round the first time. Correct close:
     `have h4 : 4 * lam < 0 := by linarith` → `unfold barrier` → `exact (div_lt_div_right_of_neg h4).mpr hsq`,
     where `hsq : (lam - x₁)^2 < (lam - x₂)^2` (note that the left-right order is the opposite of the intuitive one).
  2. **Probe design pitfall: a probe must not reference theorems from "the delivery file it is about to validate".** In a probe that only does
     `import PhotoLean.Marcus.Basic`, I wrote `rw [barrier_at_lam]` →
     `error: unknown identifier 'barrier_at_lam'` (that theorem belongs to the M2 file still to be built; it is not in Basic).
     Correct approach: first declare a **local** lemma of the same name inside the probe (`theorem scratch_at_lam (lam : ℝ) : barrier lam lam = 0 := by simp [barrier]`)
     and then reuse it. **What a probe can validate is only a "tactic kernel", not "the existence of the theorems in the delivery file"** —— evidence for the latter can only come from
     `check.sh --strict` / `axioms.sh` on the real delivery file.
  3. **Process failure (concurrent git)**: `git add -A` sweeps concurrent writers' WIP into the commit (the lead's `c000996` incident:
     it swallowed `Barrier.lean`, which at that time contained only 1 theorem, into a `docs(plan): ...` commit) → `barrier_nonneg` lost its own
     per-lemma audit trail (following the lead's instruction, **no empty commit was added and that item was left untouched**; the deviation is recorded truthfully in the task board).
     The correct posture on the worker side is a **pathspec-limited commit**:
     `git commit -q -m "feat(M2): <lemma>" -- PhotoLean/Marcus/Barrier.lean`
     —— it takes only that path's working-tree content and **does not** fold in content that someone else has already `git add`ed into the index
     (it is more pollution-resistant than `git add <file>` + `git commit`: the latter commits together with whatever others have staged in the index).
     After committing, self-check with `git show --name-only <hash>` that "this commit touched only my owned file".
  4. The first version worried that linter warnings about "premises written but unused" would pollute the acceptance output (the `hlam : lam ≠ 0` of `barrier_symm`
     and the `h₁ : 0 ≤ x₁` of `barrier_antitone_of_pos` are **genuinely both unused** in the proofs); at one point I wanted to change the signatures to drop them, but the discipline vetoed it.
- Worked:
  - File structure: `import PhotoLean.Marcus.Basic` → top-level `set_option linter.unusedVariables false`
    (**no `in`, so it applies to the whole file**; the `... in` form applies only to the single declaration immediately following it) → `namespace PhotoLean.Marcus` → the 9 theorems.
  - Two skeletons (not covered by the lead's risk probes, so they were filled in here):
    ```lean
    theorem barrier_symm {lam : ℝ} (hlam : lam ≠ 0) (x : ℝ) :
        barrier lam x = barrier lam (2 * lam - x) := by
      unfold barrier; congr 1; ring     -- congr 1 reduces the goal to (lam-x)^2 = (lam-(2*lam-x))^2

    theorem barrier_mono_cases (lam : ℝ) : (…four-way conjunction…) :=
      ⟨fun h x₁ x₂ h₁ h₂ => barrier_mono_of_pos h h₁ h₂,
       fun h x₁ x₂ h₁ h₂ h₃ => barrier_antitone_of_pos h h₁ h₂ h₃,
       fun h x₁ x₂ h₁ h₂ => barrier_antitone_of_neg h h₁ h₂,
       fun h x => by subst h; exact barrier_zero_lam x⟩   -- lam=0 branch: after subst the goal is exactly barrier 0 x = 0
    ```
  - The remaining items share one kernel (key point: **`unfold barrier` is not needed** —— `exact` at the default transparency already decides that `barrier lam x`
    equals `(lam-x)^2/(4*lam)`):
    `have h4 : (0:ℝ) < 4*lam := by positivity` → `have hsq : … := by nlinarith` → `exact div_lt_div_of_pos_right hsq h4`;
    `barrier_nonneg` / `barrier_min_at_lam` use `unfold barrier; positivity` (the latter first does `rw [barrier_at_lam]`);
    `barrier_at_lam` / `barrier_zero_lam` are directly `simp [barrier]`.
  - Names confirmed by measurement (v4.17.0; the raw `#check` output is archived in the probe `proofs/probes/marcus-prover_a2-scratch.lean`):
    `@div_lt_div_of_pos_right : a < b → 0 < c → a / c < b / c`;
    `@div_lt_div_right_of_neg : c < 0 → (a / c < b / c ↔ b < a)`;
    `@div_lt_div_iff_of_pos_right : 0 < c → (a / c < b / c ↔ a < b)`;
    `@div_le_div_iff_of_pos_right : 0 < c → (a / c ≤ b / c ↔ a ≤ b)`; `@sq_nonneg`, `@mul_self_lt_mul_self`.
  - Two layers of machine evidence: a script extracts the signatures and compares them with the skeleton → **mismatches: 0** (9/9 verbatim identical);
    `check.sh --strict PhotoLean.Marcus.Barrier` → scan `clean` + `verdict: PASS`;
    `axioms.sh` one by one → `[propext, Classical.choice, Quot.sound]` + `verdict: PASS (only mathlib infrastructure axioms)` ×9.
  - One commit per lemma (pathspec-limited): `8d9c2ff` / `03c740f` / `169a0c7` / `3dc2fcc` / `4ab7259` /
    `4561931` / `ae1276e` / `f0d79ee`.
- Reusable patterns:
  1. **three steps for ordered comparisons involving division**: ① build a `have` for the sign of the denominator; ② reduce the goal to a denominator-independent comparison (where `nlinarith` excels);
     ③ recombine with a `div_lt_div_*`-style lemma. Mnemonic: **a positive denominator preserves the order (`div_lt_div_of_pos_right`);
     a negative denominator gives an iff with the RHS reversed (`div_lt_div_right_of_neg`); for a negative denominator there is no `_of_neg_right` version**.
  2. **the reliable domain of `nlinarith` is the subgoal "after the denominators have been cleared"**: put it inside `have hsq`, do not aim it at a goal containing `/`.
  3. **physical domain premises are kept even when mathematically redundant** (statement-first; the premises themselves are documentation):
     state in the file-header block comment "which one is the domain condition and which one the proof genuinely uses", and silence the noise with a **top-level**
     `set_option linter.unusedVariables false`. The two redundant premises here are `hlam : lam ≠ 0` and `h₁ : 0 ≤ x₁`;
     I additionally verified that **the statement of `barrier_symm` with `hlam` removed still compiles** (the division-by-zero convention makes both sides 0 when `lam = 0`) ——
     measured evidence about "premise redundancy" is worth more than a guess.
  4. **a probe proves tactics only, not the existence of theorems**: if a probe needs a lemma from a file yet to be built, write a local copy under the same name;
     evidence for a delivered theorem always comes from `check.sh --strict` + `axioms.sh` (three layers: building ≠ acceptance).
  5. **in a shared repository the commit boundary = file ownership**: `git commit -m "..." -- <your own file>` (pathspec-limited),
     then self-check with `git show --name-only`; any single `git add -A` can turn someone else's WIP into "your commit's content".

## 2026-09-20 — a "full-gate FAIL" during concurrent writes is a transient phenomenon, not a defect signal — lead — confirmed

- Goal: decide whether `proofs/scripts/check.sh --strict` (run bare, building every module of `defaultTargets`) is trustworthy while several agents write concurrently.
- Tried and failed: one bare full-gate run was observed with `verdict: FAIL` (`build: FAILED`). Reading that directly as "someone's delivery is broken"
  would be a misjudgement —— at that moment `Rate.lean` / `Sharp.lean` were **mid-write** by two workers (half-finished work still in the working tree).
- Worked: **re-checking module by module** the four modules already delivered and accepted (`Basic` / `Barrier` / `Reorg` / `RatModel`) → all OK;
  a few seconds later (once the writers finished the current edit) the full gate was run again → `verdict: PASS`. That is, on a **frozen commit** the gate's verdict is stable.
- Reusable patterns:
  1. **a gate verdict must be bound to a "frozen commit / file blob"**: `verdict: PASS` is only meaningful if "at the instant you ran the gate, nobody was writing the files under validation".
     Before writing a final conclusion, first confirm that `git status` is clean or record the blob hashes explicitly.
  2. **the first action on seeing a full-gate FAIL is "re-check module by module + look at `git status`"**, not an immediate bug report or rollback ——
     a concurrency window manufactures both transient FAILs and transient PASSes (the latter is more dangerous: a half-finished artifact happens to pass).
  3. this is also the **flip side of the `defaultTargets` hole**: running the gate module by module (`check.sh --strict <Module>`)
     is unaffected by other people's WIP and is the **stable acceptance channel** in a concurrent environment; a bare full-gate run is only good as a "final freeze check".

## 2026-09-20 — literature vs formalization: "conservation of information" in the sharp characterization — literature_researcher + lead — mutual correction

- Goal: write down a **necessary and sufficient** condition of validity for the "inverted-region descriptor" (the second part of the human requirement).
- Tried and failed (**all three parties independently walked into the same pit; worth recording**):
  - The planning phase (lead) conjectured `InvertedDescriptor ⟺ 0<lam ∧ 0<kB*T ∧ 0<A` —— wrong. Counterexample `A<0 ∧ lam<0 ∧ kB*T>0`:
    `lam<0` makes the barrier **decreasing** in the inverted region ⇒ the rate increasing ⇒ after multiplying by the negative `A` it is **strictly decreasing** ⇒ the descriptor holds but the rate is negative.
  - The literature branch independently derived `desc ⟺ 0<λ ∧ 0<τ ∧ 0<A` —— the same mistake (`desc` alone does not imply `A>0`).
  - The "corrected version" the lead handed to the literature branch, `(∀x,0<rate) ∧ desc ⟺ 0<A ∧ 0<λ ∧ 0<τ` —— **also not general**:
    counterexample `λ=-3/2, τ=-1, A=1` (`λτ>0, A>0` ⇒ the descriptor holds and the rate is positive everywhere, yet neither `0<λ` nor `0<τ` holds).
- Worked: the literature branch used an **exhaustive numerical re-check** (λ, τ, A each ranging over −2…2, all combinations, 0 counterexamples) to determine the true equivalence:
  `desc ⟺ 0 < A·λ/τ` (equivalently `0 < A·λ·τ`); `(∀x, 0<rate) ∧ desc ⟺ 0 < A ∧ 0 < λ·τ`.
  And `descriptor_sharp` of `plan.md` §7.1 **happens to dodge every trap**: it puts `0<kB`, `0<T` in the **premises**
  (⇒ `0<τ`), so the `⟺` degenerates to `0<A ∧ 0<lam` —— **the plan's formulation needs no modification**, and has been delivered by M4a and has passed the gate.
- Reusable pattern (summarized by the literature branch itself, worth generalizing):
  **"the right-hand side of a sharp characterization's `⟺` must correspond one-to-one with the conjuncts on the left."**
  The information content of `desc` is only `sign(A·λ/τ)` (**a single product**), and recovering the **individual signs** of three parameters from it is impossible;
  to recover them one must **fold the extra information, such as "the rate is positive", into the left-hand side**. **Count the information on the left first, then write the right.**
- By-product (honesty): using per-compound data, the literature computed that in the inverted region the classical formula **falls off too fast by about 3.6 orders of magnitude**
  (predicting 5.1 orders of magnitude vs 1.46 measured) ⇒ this has been written into `plan.md` §8.3, restricting the instance-layer prose
  to claim **only** that "the classical model satisfies the descriptor", and **not** that it predicts the measured rate.

## 2026-09-20 — M3 rate layer (6 theorems, two batches) + M5a decision layer — prover_b / prover_c — DONE

- Goal: push the monotonicity of the barrier up to the rate (M3), and make "instance decision" computable in the kernel (M5a).
- Tried and failed:
  - **`rate_ratio`**: trying to move the minus sign inside the exponent by hand with `rw [neg_div, neg_div, neg_sub_neg, sub_neg_eq_add, ← neg_sub]`
    → `tactic 'rewrite' failed, did not find instance of the pattern ?a - -?b`.
  - **`by decide` on ℚ**: `zoneQ (1:ℚ) (3/4) = Zone.normal` fails, reporting
    `'Decidable' instance did not reduce to 'isTrue' or 'isFalse'` —— the blockage is in the **gcd/division reduction** of `Rat.instDecidableLt` → `Int.decNonneg`
    (not the Eq chain). Likewise `(4:ℚ)/4 = 1` and `(0.75:ℚ) < 1` both get stuck.
  - **`rw [← Rat.zoneQ_eq_zone]` written the wrong way round**: the pattern of `←` is `zone ↑?lam ↑?x`, which does not match the hypothesis `h : Rat.zoneQ 1 3 = ...`.
  - **a cast literal ≠ an `OfNat` literal**: on the ℝ side, writing `InvertedRegion (1:ℝ) 3` against the lemma conclusion `↑1 < ↑3` gives a type mismatch.
  - **`rw` does not unfold a `def`**: `rw [← Rat.zoneQ_inverted_iff]` fails on `¬ InvertedRegion ↑1 ↑(3/4)` (syntactically there is no `<` pattern).
- Worked:
  - The shortest path for `rate_ratio`: `unfold rate` → `rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]` → `congr 1` →
    `field_simp` → `ring` (**let `field_simp` go first and let `ring` finish; do not move the minus sign by hand**).
  - The three M3 rate theorems = a two-line composite of "barrier monotonicity + `rate_gt_of_barrier_lt`"; note the direction convention of the core lemma
    (`Φx < Φy ⇒ rate y < rate x`): in the normal region take `y := x₁`, in the inverted region take `y := x₂`; `lam < x₁` must be weakened to `lam ≤ x₁` with `le_of_lt`.
  - ℚ decision convention: **integer / division-free literals use `decide`; anything containing division or a decimal always uses `norm_num [zoneQ]`**.
  - On the ℝ side always write the parameters as `((n : ℚ) : ℝ)` (aligned verbatim with the lemma's conclusion), and bridge decimal literals explicitly with `norm_num`;
    for negated shapes, `show` the unfolded form first and then `rw`; which of the two rewrite directions applies depends on whether `zoneQ` (forward) or `zone ↑↑` (backward) occurs in the expression.
- Reusable patterns:
  1. **the reliable domain of `decide` is the path "the kernel can reduce to the end"** (Nat/Int comparisons); once `Rat` gcd/division or decimal literals are involved,
     switch to `norm_num` (it produces a proof term and does not rely on kernel reduction).
  2. **the transfer lemma is the only bridge between the "computable decision layer" and the "non-computable theory layer"**; the two ends of the bridge have different literal types (`Rat.cast` vs `OfNat`),
     and they must be connected by explicit `norm_num` equations —— do not expect the coercion to unify them on its own.
  3. `rw` is **syntactic pattern matching** and does not go through defeq: before rewriting, ask "which symbol is in the expression now, and what is the LHS of the rule?";
     the direction is decided by the pattern, not by intuition.

## 2026-09-20 — M4c composite theorem + M4b geometric lemma (`hgeom` goes from hypothesis to derivation) — prover_d — DONE

- Goal: compose "microscopic positivity ⇒ the inverted-region descriptor holds" into a single theorem (M4c), and downgrade the **positivity of the geometric factor**
  of the outer reorganization energy from a "hypothesis" to "derived from the non-overlap of the two spheres" (`a1 + a2 ≤ R ⇒ 1/R < 1/(2a1) + 1/(2a2)`).
- Tried and failed:
  - applying `nlinarith` / `gcongr` directly to a three-denominator goal ✗ (before a common denominator is formed you cannot see the signs of the denominators); using `field_simp` on an **inequality** ✗
    (`simp made no progress` —— it is only reliable for **equalities**).
  - Lean 4 **mixing positional and named arguments** (`f a b (h := …) c`) **silently under-binds one argument**,
    reporting `type mismatch … but is expected to have type …` (in fact a partial application), which is extremely hard to spot at a glance.
  - `#check`-ing the composite theorem requires `import PhotoLean.Marcus.Compose`; importing only `Sharp`+`Reorg` reports
    `unknown identifier` (**the module where a definition lives ≠ the modules imported in the file**).
  - `git commit -- <path>` on a **brand-new untracked** file reports `pathspec … did not match any file(s) known to git`
    ⇒ a new file must first be `git add -- <path>` (a limited path; `-A` is still not allowed).
- Worked skeleton (`hgeom_of_nonoverlap`):
  `have hpos : 0 < a1 + a2 := by linarith` → `one_div_le_one_div_of_le hpos hRge` →
  `field_simp; ring` yields the **common-denominator equality** `1/(2a1)+1/(2a2) = (a1+a2)/(2a1a2)` →
  `div_lt_div_iff₀ hpos hden` cross-multiplies → `nlinarith`.
  Core equivalence: `2a1a2 < (a1+a2)² ⟺ 0 < a1² + a2²`.
  The composite theorem itself is a one-line combination: `inverted_descriptor_holds hA (lam_total_pos (lamInner_nonneg hkk dq) (lamOuter_pos …)) (mul_pos hkB hT)`.
- Reusable patterns:
  1. **"first form a common denominator (`field_simp` for equalities) → then cross-multiply (`div_lt_div_iff₀`) → finally `nlinarith`"**
     is the general three-step for inequalities with several denominators; using `field_simp` directly on an inequality always fails.
  2. **the way arguments are bound must be uniform** (all positional or all named) —— mixing silently produces partial applications, and the error message points nowhere.
  3. non-emptiness evidence must be produced **proactively**: `a1=a2=1, R=3, kk=0, nSq=1, epsS=2` makes the two composite theorems land on
     `InvertedDescriptor 1 (1/3) 1 1`, which proves that the premise set is satisfiable (`kk = 0` exactly demonstrates that one must go through `lamInner_nonneg` and not `_pos`).

## 2026-09-20 — M5b instance decision (31 theorems in two batches) — prover_c — DONE

- Goal: substitute the instances into the formalized theory and **decide** whether they match the inverted-region descriptor (the third part of the human requirement).
- Tried and failed:
  1. **A passage in the lead's dispatch note does not hold up (measured, and it failed)**: to prove "the rate is not positive" I wrote
     `intro h; have := h 0; norm_num [rate, barrier] at this` —— `norm_num` reduces the hypothesis to
     `h0 : Real.exp (1/4) < 0`, but **it does not know the positivity of `Real.exp`**, and so leaves the unsolved goal
     `unsolved goals … h0 : Real.exp (1/4) < 0 ⊢ False`.
     What worked: compute the barrier value first and then refute with `Real.exp_pos`:
     `have hb : barrier (-1) 0 = -(1/4) := by norm_num [barrier]; rw [rate, hb] at h0;
      norm_num at h0; linarith [Real.exp_pos (1/4)]`.
  2. When appending the second batch to `Instances.lean`, I forgot to **re-open the namespace** (batch 1 already ended with `end PhotoLean.Marcus`)
     ⇒ every occurrence of `InvertedDescriptor`/`rate` reported `unknown identifier`.
  3. Three pitfalls of the decision evidence chain (recorded in batch 1; reconfirmed here as to their **necessity**): the direction of `rw [← Rat.zoneQ_eq_zone]` depends on
     whether `zoneQ` or `zone ↑↑` occurs in the expression; an ℝ decimal literal and a cast ℚ fraction are **not equal at the definitional level**, and must be bridged with an explicit
     `norm_num`; `rw` does not unfold a `def` such as `InvertedRegion` (`show` first).
- Worked:
  - All 13 new theorems are obtained by **instantiating** upstream theorems that have already passed the gate ((⟸) of `descriptor_sharp` for the "admissible" decisions,
    `inverted_rate_decreases` for the rate comparisons, `descriptor_fails_of_nonpos_lam` for the counterexample decisions),
    and **no new real-analysis step was introduced** —— this is the structural evidence that "the instance layer is nothing but instantiation".
  - `kBT` is written as a **universally quantified variable** of the theorem (with the premise `0 < kBT`), which makes "the decision is independent of temperature" **part of the statement** rather than a claim in a comment.
- Reusable patterns:
  1. **`norm_num` is not omnipotent**: it can compute numbers, but **it does not know the properties of transcendental functions** (`Real.exp_pos` and the like).
     A refutation involving `exp`/`log` must supply the positivity lemma explicitly (`linarith [Real.exp_pos x]`).
  2. **every appended section of a file must establish its own namespace context** (`namespace … end`), which is very easy to miss under concurrent or section-by-section editing.
  3. **the correct posture for the instance layer is "instantiate", not "prove again"**: the proof body of a new theorem should call only upstream theorems that have passed the gate
     + `norm_num` for the bounds; if you find yourself rewriting a real-analysis argument inside an instance, the abstraction has not been factored out cleanly.

## 2026-09-20 — M4a sharp characterization (9 theorems, main theorem `descriptor_sharp`) — prover_a — DONE

- Goal: prove the **necessary and sufficient condition** for "the inverted-region descriptor holds": `(the rate is positive everywhere ∧ descriptor) ⟺ 0 < A ∧ 0 < lam` (under the premises `0<kB`, `0<T`).
- Tried and failed:
  1. `#check` / `#print` **cannot immediately follow a doc comment** `/-- … -/` → `unexpected token '#check'; expected 'lemma'`;
     separate them with a `--` line comment or a blank line (the same family of pitfalls as `set_option` recorded in API-NOTES).
  2. `git commit -- <path>` on a **brand-new untracked file** reports `pathspec … did not match any file(s) known to git`;
     a new file must first be `git add -- <path>` (explicit path; `-A` is still **not allowed**), then `commit -- <path>`.
  3. Not writing implicit arguments out explicitly triggers an `unused variable` warning: in `fun x₁ x₂ h₁ h₂ => rate_gt_of_barrier_lt hA hkT …`,
     `x₁`/`x₂` are used only by unification inference. After changing it to `rate_gt_of_barrier_lt (x := x₁) (y := x₂) …`, 0 warnings.
  4. The `{x y}` **direction of `rate_gt_of_barrier_lt` is opposite in the two branches**: its conclusion is `rate y < rate x`.
     The inverted region needs `rate x₂ < rate x₁` ⇒ take `x := x₁, y := x₂`; the normal region needs `rate x₁ < rate x₂` ⇒ take `x := x₂, y := x₁`. Writing it the wrong way round makes the kernel report a type mismatch at once.
- Worked (the "structural evidence" of branch coverage):
  - Necessity is split by **mechanism** into three kernels rather than one lemma covering two cases:
    the signature of `sharp_lam_pos_of_eq` **contains no positivity premise at all** (it relies only on the division-by-zero convention ⇒ the rate is constantly `A` ⇒ `A < A`),
    and therefore it is **structurally impossible** for it to be absorbed by the `lam < 0` branch; `sharp_lam_pos` assembles the three branches with `rcases lt_trichotomy lam 0`.
  - Printing the proof term with `#print` confirms that all three branches occur (nested `Or.casesOn`), which is stronger than reading the source.
- Reusable patterns:
  1. **the necessity direction of "sharpness" must be split by mechanism**, and each branch's signature must be able to **certify that it is not swallowed by another branch** (for instance, let one branch omit a premise that only the other branch needs).
  2. **the strongest way to verify branch coverage is to print the proof term** (`#print` + `pp.proofs`), not to read the tactic script.
  3. the direction arguments of composite lemmas (`{x y}` and the like) are often **opposite** between the "monotonically increasing / decreasing" branches —— re-check the direction at every call site.

## 2026-09-20 — M5a addendum: the ℚ→ℝ numeric bridge for `barrierQ` (patching the "unconstrained definition" found by the structural audit) — prover_c — DONE

- Goal: `barrierQ` (the ℚ-side barrier) originally had **no accompanying theorem at all** (found independently by the structural audit and by the M3+M5a verifier);
  add `barrierQ_cast : ((barrierQ lam x : ℚ) : ℝ) = barrier (lam:ℝ) (x:ℝ)` so that the ℚ-side numbers are entitled to serve as evidence at the ℝ layer.
- Tried and failed:
  1. `unfold barrierQ barrier; push_cast` **alone is not enough** → it leaves an `unsolved goals` of the form `X = X`, and `ring` must be added;
     whereas the explicit `rw [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]` **carries its own rfl finish**,
     so writing `ring` afterwards reports `no goals to be solved` —— **the two routes have opposite "tail rules"**.
  2. `apply Rat.cast_inj.mp` reports `typeclass instance problem is stuck … CharZero ?m`
     → one must write **`(Rat.cast_inj (α := ℝ))`** explicitly.
  3. `↑(0:ℚ)` and `(0:ℝ)` **are not defeq** (the cast-literal pitfall already recorded in API-NOTES recurs here).
- Worked: `unfold barrierQ barrier; push_cast; ring` (one line); at the degenerate point, `(Rat.cast_inj (α := ℝ)).mp` + `rw [barrierQ_cast]` + `simp [barrier]`.
- Reusable patterns:
  1. **"a definition not constrained by any theorem" is a structural bad smell** —— it means the definition could be changed arbitrarily without anyone noticing.
     A "definition → reference count" audit after delivery finds it directly (the only instance in this project was `barrierQ`).
  2. `push_cast` and an explicit `rw [Rat.cast_*]` are two routes with **opposite tail rules**: the former does not give rfl and needs `ring`, the latter carries rfl itself.
  3. if a shorter route would require **adding an import** to the file (breaking the "depends only on M1" convention), **write it a bit longer** rather than break the dependency boundary.

<!-- Entries continue to be appended from here on -->
