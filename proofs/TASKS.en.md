# PhotoLean Task Board (single source of truth for status)

> *English translation of `proofs/TASKS.md`. The Chinese original at `proofs/TASKS.md` is authoritative — the formalization engine's contract (`proofs/ENGINE.yml`) reads the Chinese paths.*

- Status vocabulary: `todo` (not started) → `stmt` (statement calibrated and compiling)
  → `proving` (proof under way) → `review` (handed to the verifier) → `done` (verifier PASS and committed).
- Line format: `- [ ] theorem — file — owner — status — note`.
- **Ticking a box (`[x]`) is allowed only after a verifier PASS**, and is performed by the lead; workers must not tick their own boxes.
- The owner column holds an engine role name (`prover_a` / `prover_b` / `prover_c` / `prover_d`);
  no file may have two concurrent owners.
- Contract and role definitions: `proofs/ENGINE.md`; plan and statements: `plan.md`;
  **authoritative statements = `proofs/probes/marcus-statement-skeleton.lean` (already compiling successfully)**.
- Theoretical direction: **the Marcus inverted region (classical Marcus model)**, confirmed by the human on 2026-09-20.

---

## Sprint 0 — Environment and statement calibration (wrapped up)

- [x] Lean toolchain and mathlib cache connected (`lake build` cold start ~10s, `PhotoLean.Smoke` passes)
- [x] Acceptance-gate scripts usable (`proofs/scripts/check.sh --strict` / `axioms.sh`)
- [x] **Acceptance-gate behavior verified**: a clean tree PASSes; all three classes of violation are
      blocked — the unfinished-proof keyword, a custom axiom, and a hidden unfinished-proof keyword
      (evidence: first entry of `proofs/EXPERIENCE.md` — key finding:
      `lake build` **returns 0 for all three classes**, so a passing build alone does not constitute acceptance)
- [x] Project contract on disk (`proofs/ENGINE.yml`, leaf data plane complete)
- [x] **Theoretical plan on disk**: `plan.md` = Marcus inverted region M1–M5
      (human-confirmed: the full five segments + dual-track instances + literature-checkable parameters)
- [x] **Statement skeleton compiles**: `proofs/probes/marcus-statement-skeleton.lean`
      (all M1–M5 statements; 31 unfinished-proof warnings, **0 errors**; the 4 risk probes at the end genuinely pass with no unfinished proof)
- [x] `proofs/probes/` directory created; `git init` + baseline commit
- [x] API calibration complete (`api_researcher`): `proofs/API-NOTES.md` rewritten (the three columns usable /
      drifted / unavailable, plus an identifier-legality matrix of 20 retained tokens),
      5 probes with 0 errors, plus `proofs/probes/marcus-proof-skeletons.lean` (36 proof bodies that **already go through**, covering M1–M5a)
- [x] Literature parameter table complete (`literature_researcher`): `proofs/LITERATURE.md`, 552 lines, with 6 groups of "checked"
      parameters, DOI corrections, the Pekar condition, 5 approximations that must be made explicit, and a ranked list of what cannot be expressed

---

## M1 — Description layer (`PhotoLean/Marcus/Basic.lean`; owner prover_a; Sprint 1)

- [x] Definitions of `barrier` / `rate` / `InvertedRegion` / `NormalRegion` / `InvertedDescriptor`
      / `NormalDescriptor` / `Zone` / `zone` — Marcus/Basic.lean — prover_a — done — plan §2.2; commit 3644a82
- [x] `zone_eq_normal_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2; commit f3d2055
- [x] `zone_eq_barrierless_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2; commit ac80776
- [x] `zone_eq_inverted_iff` — Marcus/Basic.lean — prover_a — done — plan §4.2; commit c98c85d
- [x] `zone_trichotomy` — Marcus/Basic.lean — prover_a — done — plan §4.2; commit 1376f8e

## M2 — Barrier algebra (`PhotoLean/Marcus/Barrier.lean`; owner prover_a; Sprint 2)

- [x] `barrier_nonneg` — Marcus/Barrier.lean — prover_a — done — plan §5; ⚠️ **commit deviation**: its content was
      absorbed into the lead's `c000996` (an accidental `git add -A` sweep), so this entry has no separate feat commit;
      the remaining 8 entries each still have their own commit
- [x] `barrier_at_lam` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 8d9c2ff
- [x] `barrier_symm` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 03c740f
- [x] `barrier_min_at_lam` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 169a0c7
- [x] `barrier_mono_of_pos` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 3dc2fcc
- [x] `barrier_antitone_of_pos` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 4ab7259
- [x] `barrier_antitone_of_neg` — Marcus/Barrier.lean — prover_a — done — plan §5; commit 4561931
- [x] `barrier_zero_lam` — Marcus/Barrier.lean — prover_a — done — plan §5; commit ae1276e
- [x] `barrier_mono_cases` — Marcus/Barrier.lean — prover_a — done — plan §5; commit f0d79ee

## M3 — Rate layer (`PhotoLean/Marcus/Rate.lean`; owner prover_b)

- [x] `rate_pos` — Marcus/Rate.lean — prover_b — done — plan §6 (Sprint 2; depends only on M1); commit 8840fdf
- [x] `rate_gt_of_barrier_lt` — Marcus/Rate.lean — prover_b — done — plan §6 (**core lemma**; Sprint 2); commit 464edbf
- [x] `normal_rate_increases` — Marcus/Rate.lean — prover_b — done — plan §6 (Sprint 3; depends on M2); commit 671bee1
- [x] `inverted_rate_decreases` — Marcus/Rate.lean — prover_b — done — plan §6 (Sprint 3; depends on M2); commit 8cfde00
- [x] `rate_peak_at_lam` — Marcus/Rate.lean — prover_b — done — plan §6 (Sprint 3; depends on M2); commit c4a70fd
- [x] `rate_ratio` (stretch goal, non-blocking) — Marcus/Rate.lean — prover_b — done — plan §6; commit 60fe95f

## M4a — Sharp characterization (`PhotoLean/Marcus/Sharp.lean`; owner prover_a; Sprint 4)

- [x] `inverted_descriptor_holds` — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit e15e9d5
- [x] `normal_descriptor_holds` — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit ccab8fe
- [x] `descriptor_fails_of_nonpos_lam` — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit a520b0a
- [x] `descriptor_sharp` (**critical path**; the verifier is to re-check the two branches of the necessity direction) — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit bfcbb6c
- [x] `inverted_descriptor_holds_of_neg` (stretch; proves that the "rate positivity" premise cannot be dropped) — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit 67c42f5
- [x] Necessity-direction internal kernel (4 lemmas, not in the skeleton) `sharp_A_pos` / `sharp_lam_pos_of_lt` / `sharp_lam_pos_of_eq` / `sharp_lam_pos` — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit f28288b / 692763d / da9aa17 / df5b9f3 (PASSed together with the M4a acceptance) — Marcus/Sharp.lean — prover_a — done — plan §7.1; commit 67c42f5

## M4b — Microscopic reorganization-energy positivity (`PhotoLean/Marcus/Reorg.lean`; owner prover_d; Sprint 1, **zero dependencies**)

- [x] `lamInner` / `lamOuter` definitions — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit 2d4e296
- [x] `lamInner_nonneg` — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit 723034d
- [x] `lamInner_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit acc5e8e
- [x] `lamOuter_pos` (positivity of the Pekar factor) — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit fcb7589
- [x] `lam_total_pos` — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit de63c09
- [x] **[stretch]** `hgeom_of_nonoverlap` (`a1+a2 ≤ R ⇒ geometric factor positive`, turning `hgeom` from an assumption into a derivation) — Marcus/Reorg.lean — prover_d — done — plan §7.2; commit 61759b3

## M4c — Composite theorems (`PhotoLean/Marcus/Compose.lean`; owner prover_d; Sprint 5)

- [x] `descriptor_holds_of_microscopic` (imports Sharp + Reorg) — Marcus/Compose.lean — prover_d — done — plan §7.2; commit c778d4e
- [x] `descriptor_holds_of_nonoverlap` (stretch: geometry replaces hgeom) — Marcus/Compose.lean — prover_d — done — plan §7.2; commit 6338f7f

## M5a — ℚ decision layer (`PhotoLean/Marcus/RatModel.lean`; owner prover_c; Sprint 2)

- [x] `zoneQ` / `barrierQ` — Marcus/RatModel.lean — prover_c — done — plan §8.1; commit 77e45c8
- [x] `zoneQ_eq_zone` (transfer lemma) — Marcus/RatModel.lean — prover_c — done — plan §8.1; commit d43f806
- [x] `zoneQ_inverted_iff` — Marcus/RatModel.lean — prover_c — done — plan §8.1; commit 166ab4e

## M5b — Instances and decisions (`PhotoLean/Marcus/Instances.lean`; owner prover_c)

> **The file is authoritative for the numbering** (it differs from the old numbering in plan §8.2; the deliverer wrote a "numbering note" inside the file):
> I1/I2 = pure numbers (inverted region / normal region); **I3 = the literature MCC barrierless point (1.20, 1.23)**;
> **I4 = the literature MCC inverted-region pair (1.20, 2.40 / 2.00)**; **I5 = the literature MCC normal region (1.20, 0.60)**;
> **I6 = the photosynthetic reaction center deep inverted region (0.25, 1.10)**; I7 = non-physical parameters; I8 = **description-operator instantiation + rate comparison** for the literature parameters.

> **⚠️ Wording boundary at the instance layer (quantitative warning from the literature)**: the classical model falls off **too fast** in the inverted region
> (at λ=1.2, going from x: 2.0→2.4 drops about 5 orders of magnitude,
> while experiment drops only about 2). Instance conclusions may only state "this system falls in the inverted region, and the **classical Marcus model** satisfies the description at this (lam,x,T,A)";
> they **must not** be written as assertions about experiment.

- [x] Transfer helper `normalRegion_of_zoneQ_normal` / `not_invertedRegion_of_zoneQ_normal` — Marcus/Instances.lean — prover_c — done — plan §8.2; commit f3f93f5
- [x] I1 inverted region (pure numbers `lam=1, x=3`) + I2 normal region (`3/4`) decision chains — Marcus/Instances.lean — prover_c — done — plan §8.2; commit 4e14952 / f3f93f5
- [x] I3 literature barrierless point (1.20, 1.23): `barrier 1.20 1.23 = 0.0001875` (agreeing with the literature `ΔG‡ ≈ 0.0002 eV`) + inverted-region decision — Marcus/Instances.lean — prover_c — done — plan §8.3; commit 6df4cf9
- [x] I4 literature MCC inverted-region pair (1.20, 2.40) and (1.20, 2.00) — Marcus/Instances.lean — prover_c — done — plan §8.3; commit 6df4cf9
- [x] I5 literature MCC normal region (1.20, 0.60) (including the negative decision "not in the inverted region") — Marcus/Instances.lean — prover_c — done — plan §8.3; commit 6df4cf9
- [x] I6 photosynthetic reaction center deep inverted region (0.25, 1.10) — Marcus/Instances.lean — prover_c — done — plan §8.3; commit 6df4cf9
- [x] I7 non-physical parameter decisions (`lam ≤ 0` ⇒ the description fails; `A<0 ∧ lam<0` ⇒ the description holds but the rate is non-positive ⇒ not admissible) — Marcus/Instances.lean — prover_c — done — plan §8.2; commit cb72b16
- [x] I8 **description-operator instantiation** for the literature parameters + **rate comparison** (`rate(x=2.40) < rate(x=1.23)` and the like, with `kBT` as an explicit premise) — Marcus/Instances.lean — prover_c — done — plan §8.2; commit a83bfe7 / 8f8f041

---

## M5b's lead pre-acceptance evidence (superseded by the verifier verdicts, retained for cross-checking)

> **2026-09-20 update**: M5b has been judged PASS by **two independent verifier runs** (see below), and the 8 rows are ticked.
> The table below is retained as a cross-check record of "lead fast-path evidence vs. independent verifier evidence".

## ⏳ M5b's lead pre-acceptance evidence (original record)

On 2026-09-20, before the verifier verdicts arrived, the lead independently ran the M5b acceptance checklist by the **fast path**, with the conclusions below
(the evidence can be re-run; but by discipline, **these 8 rows must not be ticked before the verifier PASSes**):

| check | command | result |
|---|---|---|
| gate | `check.sh --strict PhotoLean.Marcus.{Instances,RatModel}` | both `verdict: PASS` |
| bulk axioms | single-probe `#print axioms` × 35 (Instances 31 + RatModel 4) | **35/35, 0 errors**: 34 with the three axioms + 1 with `propext` only |
| script spot checks | `axioms.sh` × 3 (including `inst_I4_mcc_rate_drop`) | 3/3 printed name = requested name, no race |
| commit discipline | `git show --name-only` × 6 | 6 `feat(M5b)` commits, **exactly 1 file each** |
| definition-layer cross-validation | `proofs/probes/marcus-lead-crosscheck.lean` | **9 lemmas**: without calling any delivered instance theorem, re-derives the same batch of conclusions directly from the definitions (including `rate(2.40) < rate(1.23)` for all `kBT>0`) |
| numerical check | Python computed from the definitions | all four instance theorems confirmed one by one; `barrier 1.20 1.23 = 0.0001875` agrees with the literature `≈0.0002 eV` |
| evidence-chain reading | reading the proof bodies | `inst_I1_zoneQ` = `by decide`; `inst_I2_not_inverted` goes through the normal-region transfer lemma; `inst_I4_mcc_rate_drop` is an instantiation of `inverted_rate_decreases` (not a re-expansion of the exp argument) |

## Acceptance records (the verifier runs the gate independently; the lead ticks boxes accordingly)

| batch | scope | verdict | key evidence | note |
|---|---|---|---|---|
| M1 + M4b | `Basic.lean` (12 declarations) + `Reorg.lean` (6) | **PASS / PASS** | four-step gate + 8/8 `axioms.sh` all `[propext, Classical.choice, Quot.sound]`; 18/18 statements **verbatim identical** to the skeleton; each of the 8/8 commits contains **exactly one** theorem and exactly one file; hack-detection sweep 0 hits; adversarial probes verified at kernel level | 1 **comment-level** defect awaiting repair (`Reorg.lean` describes 5 domain premises as "implied" when they are in fact "unused" — the verifier supplied a kernel counterexample); also: `zone_trichotomy` is itself weak in information content (it holds for any function `ℝ→ℝ→Zone`); what really pins down the semantics are the three `zone_eq_*_iff` lemmas |

| M2 | `Barrier.lean` (9 lemmas) | **PASS** | four-step gate + 9/9 `axioms.sh` clean (independently re-collected with a unique-path isolated probe); 9/9 statements verbatim identical to the skeleton; each of the 8/8 commits contains exactly one theorem and only that file; the `c000996` deviation is **verified as real** (`barrier_nonneg`'s content is indeed in it; the line count closes as 35+4+6+4+9+8+11+5+13 = 95 = total file lines); all three adversarial kernel checks pass (`barrier_antitone_of_neg` direction / `mono_cases` four branches exhaustive and the `lam=0` branch not mixed in / `barrier_min_at_lam` a true global minimum with the premise necessary) | **Finding A**: 3 places in the file and API-NOTES call `h₁ : 0 ≤ x₁` "derivable from the other premises" — **wrong** (counterexample `lam=1,x₁=-5,x₂=-4`); the correct characterization is "**not used** (unused)"; **Finding D**: the `lam = 0` branch relies on the division-by-zero convention (a formal convention, not a physical fact) ⇒ added to plan §13 |

| M3 + M5a | `Rate.lean` (6) + `RatModel.lean` (2 theorems + 2 definitions) | **PASS / PASS** | four-step gate + 8/8 `axioms.sh` clean (independently re-collected a second time with a unique-path isolated probe, including 5 definitions); 10/10 statements verbatim identical to the skeleton (including definition bodies); each of the 9/9 commits contains exactly one theorem and only the owner's file; **three adversarial kernel checks**: numerical check of the normal-region/inverted-region **direction** (0.852<0.939 rising; 0.368<0.779 falling; peak = 1.0), `rate_ratio` holds under all 5 classes of boundary assignment and yields a counterexample showing `hA` is necessary (the equality is false at `A=0`), and `zoneQ_eq_zone` is in three-way agreement with the Python expectation on **16 groups** of points including `lam=0`/`lam<0` | **Finding (a)**: line 4 of `plan.md §13` says the Lean form is `0<kB ∧ 0<T`, whereas the actual delivery uses `0 < kB*T` (the product) ⇒ the plan was amended; **(b)** `barrierQ` has no companion theorem (the theory over ℝ is not constrained by it) ⇒ a supplementary transfer lemma has been dispatched; **(c)** the `0 ≤ x₁` in `normal_rate_increases` is mathematically redundant (the verifier proved the stronger version without that premise); **(d)** row I2 of the table in `plan.md §8.2` still wrote `by decide` (the code block had already been corrected) ⇒ fixed; **(e)** if the M5b instances use barrier values from the ℚ side, the transfer lemma must come first |

| M4a | `Sharp.lean` (9 lemmas, including the main theorem) | **PASS** | gate + 9/9 `axioms.sh` clean (printed names match requested names verbatim); **5/5 statements agree three ways** (plan §7.1 / skeleton / delivery, compared character by character and against the kernel `#check` refined types); grep 0 hits (a separate check of the "trickery surface" `set_option/macro/elab/run_cmd/#eval/private/@[` etc. was also 0); each of the 9/9 commits contains exactly one theorem and only `Sharp.lean`; **adversarial**: the `lam=0` branch is independently reproduced by 4 premise-free `example`s (`barrier 0 x = 0` ⇒ `rate ≡ A` ⇒ `A < A`), the `lam<0` branch is numerically checked (`barrier(-1,0)=-1/4`, `barrier(-1,1)=-1` ⇒ the rate increases, opposite to the description), and the assembly is confirmed with `#print` proof terms to have `lt_trichotomy`'s three branches **all** wired up; **and the kernel counterexample answers**: "if the left conjunct `(∀x, 0<rate)` is deleted, the theorem fails" (counterexample `A=lam=-1`) |

| M4c + M4b addendum | `Compose.lean` (2 lemmas) + `hgeom_of_nonoverlap` in `Reorg.lean` | **PASS / PASS** | gate + 10 `axioms.sh` runs (including regression) clean; `descriptor_holds_of_microscopic` is **verbatim identical** to the skeleton / plan; the mechanical difference between `descriptor_holds_of_nonoverlap` and the microscopic version is **only** the single replacement `(hR, hgeom)` → `hRge` (neither `hgeom` nor `0<R` is among its premises); the comment change in `e626884` was confirmed by a **position-aware parser** to consist of 16 changed lines all inside comments, with an identical token stream (292=292); **strongest evidence**: the source file was copied byte-for-byte to `/tmp` and rebuilt from scratch, and the olean md5 matches the project ⇒ stale olean ruled out; **adversarial**: `hgeom_of_nonoverlap` holds on the boundary plus 256 rational scans, and the premise cannot be dropped (counterexample `a1=a2=1,R=1`); `descriptor_holds_of_microscopic` has its 12 premises eliminated one by one with `norm_num` to obtain λ=1/3 and derives a **concrete rate inequality** (not vacuous; the proof term uses 12/12 premises); the nonoverlap version's proof term **really calls** `hgeom_of_nonoverlap` (11/11 premises used) | **accounting gap (fixed)**: the two stretch statements had not been backfilled into the skeleton ⇒ now added (skeleton 43→45 entries; the fidelity check now covers **45/45**); `one_div_le_one_div_of_le` was missing from API-NOTES ⇒ referred to the calibrator |

| M5b + M5a addendum | `Instances.lean` (31 lemmas) + 2 new lemmas in `RatModel.lean` | **PASS / PASS** (**two independent verifier runs** judged simultaneously) | gate 2/2 PASS (whole-tree scan clean); **bulk axioms 33/33** (32 with the three axioms + 1 with `propext` only, 0 errors) + 3/3 official-script spot checks (printed name = requested name); hack-detection grep 0 hits; each of the 6 `feat(M5b)` commits contains exactly 1 file; **decisional kernel re-check**: the `#print` proof terms confirm `inst_I1_zoneQ` = `of_decide_eq_true`, that `inst_I2_not_inverted` really goes through the normal-region transfer lemma, and that **`Real.exp` occurs 0 times** in the term of `inst_I4_mcc_rate_drop` (a genuine instantiation); `kBT` instantiated with both the values 1 and 10 passes ⇒ universality holds; the non-physical branch was recomputed independently (rate −1.284 → −2.718, strictly decreasing); **wording-boundary check**: none of the 31 asserts a measured rate or decay magnitude | **findings (non-blocking)**: ① **contract-discipline deviation**: M5b's 31 lemmas sit in 6 commits (2/4/12/4/4/5), which does not satisfy iron rule 7 "one commit per lemma" ("semantic batches" were allowed at dispatch time, but this conflicts with the iron rule ⇒ recorded as a known deviation); ② the header comment of `RatModel.lean` saying "2 definitions and 2 theorems" is stale (now 4 entries) → fixed; ③ one comment in `Instances.lean` was missing the "classical model" qualifier → fixed; ④ **M5b's statements never entered the authoritative skeleton** ⇒ the fidelity check (45/45) does **not cover** these 33 lemmas (a known coverage gap); ⑤ `one_div_le_one_div_of_le` and others have been added to API-NOTES |

**Closure of M2 Finding A****Closure of M2 Finding A**: all three places (the header comment and doc comment of `Barrier.lean`, and `API-NOTES.md`) have been corrected to
"**the proof does not use it (unused)**", keeping the kernel counterexample as a warning about a "typical misstatement" —
`Barrier.lean` in `8ca59d7` (comments only; mechanical evidence: the code is byte-for-byte identical once comments are stripped);
`API-NOTES.md` in `a0796fc` (a dedicated correction record for "unused ≠ derivable" was added).

**Honesty reminders raised by the verifier (adopted)**:
1. **`zone_trichotomy` is very weak** — it does not assert that the classifier corresponds to the three regions, nor that the three branches are mutually exclusive;
   the semantics are carried by the three `zone_eq_*_iff` lemmas (exhaustive and consistent). Documentation and the final report **must not** overstate its role.
2. **The geometric convention is not in the Lean statement**: mathematically, the premises of `lamOuter_pos` allow assignments with `a1 < 0, R < 0`
   (and the conclusion is still true). That is, "two spheres, `R ≥ a1 + a2`, continuum medium" is written only in the plan and the comments —
   **if the M5 instance layer uses `lamOuter`, it must explicitly assert the physical domain** (`0 < a1`, `0 < a2`, `a1 + a2 ≤ R`).
3. **Concurrency window**: the scan of `check.sh --strict` covers the whole of `PhotoLean/`, so someone else's WIP can flip the gate's verdict ⇒
   **ticking boxes and final conclusions must re-run the gate on a frozen commit** (which is how this table was produced).
   **Measured confirmation**: on 2026-09-20 a bare full-tree gate run was once observed to report `build: FAILED` — on re-inspection this was the **transient state**
   of `Rate.lean`/`Sharp.lean` being written; the four already-accepted modules were each re-checked and all OK, and after the writers stopped the full gate PASSed again.
   In a concurrent environment, the **stable acceptance channel is per-module gate runs** (`check.sh --strict <Module>`); a bare full-tree run serves only as the final freeze check.

## Notes and conflict records

- **🔧 Infrastructure BUG fixed (2026-09-20, reported by prover_b)**: `proofs/scripts/axioms.sh` used to use a **fixed probe path**
  `.lake/tmp/AxiomsProbe.lean`, so concurrent acceptance-gate runs would overwrite each other → producing **false evidence** of the "asked A, answered B" kind
  (measured by prover_b: it asked about `rate_pos` but printed the axioms of `Rat.zoneQ_eq_zone`). This has been changed to
  `AxiomsProbe.$$.$RANDOM.lean` + `trap ... EXIT` cleanup; **concurrent isolation has been measured**
  (4 different theorems run simultaneously, each printing its own name, all PASS). The acceptance criterion is unchanged; only the race was eliminated.
- **⚠️ lead process mistake and its correction (2026-09-20, must be remembered)**: while making the `docs(plan)`/`chore(board)` commits I used
  `git add -A`, which swept the then-**uncommitted intermediate artifacts** (the WIP of `Barrier.lean`, `RatModel.lean`, several probes,
  the first draft of `LITERATURE.md`) into my commits (`e53d562`, `c000996`). **Rule from this moment on**: the lead may only use
  `git add <explicit paths it owns>` (`plan.md` / `proofs/TASKS.md` / `proofs/EXPERIENCE.md` / `lakefile.toml`),
  and must never use `git add -A` / `git add .`; workers likewise add only their own owned files.
  Impact: the per-lemma commits of the delivered theorems (the four in M1, the five in M4b) are **unaffected**; only `barrier_nonneg` was absorbed (see above).
- **Block-comment scanning pitfall (measured by the M1 deliverer, 2026-09-20)**: the unfinished-proof /
  custom-axiom scan of `check.sh --strict`
  **includes block comments `/- ... -/`** (it skips only line comments that begin with `--`), so writing one of the scanned
  keyword literals inside a **file-header doc comment** causes a false FAIL. Whole-team convention: use wording such as "zero-placeholder proof" in the doc comments of delivered files.
- **Sprint 0 measured findings** (written into `plan.md` §2.4 and `proofs/EXPERIENCE.md`):
  1. In Lean 4, `λ` is a keyword and **cannot be used as an identifier** → everything on the Lean side is ASCII
     (`lam` / `lamIn` / `lamOut` / `nSq` / `epsS` / `dE` / `dq` / `a1` / `a2`);
  2. `by decide` computes for **integer** literals over ℚ, but for rational literals **containing division** it gets stuck on
     `Rat`'s gcd/division reduction → the decision evidence was switched to `norm_num [zoneQ]`;
  3. the statement skeleton must live outside `SOURCE_DIRS` (`proofs/probes/`), otherwise it triggers the unfinished-proof scan.
- **Acceptance-gate gap warning**: `defaultTargets` has been extended with `PhotoLean.Marcus.Basic` and `PhotoLean.Marcus.Reorg` as they were delivered;
  the lead will keep adding further modules in step as they are delivered,
  otherwise a bare `check.sh --strict` builds only Smoke (**the scan still covers the whole directory**). Running the gate per module with
  `check.sh --strict <Module>` is unaffected.
