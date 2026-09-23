/-
PhotoLean.KashaVavilov.Basic — KV1, the description layer of the Kasha–Vavilov theory.

This theory is the home of adjudication target **D2** of the photophysics batch: the logical
independence of **Kasha's rule** (emission only from the lowest excited state of a given
multiplicity) from **Vavilov's rule** (the fluorescence quantum yield is independent of the
excitation wavelength). The Kasha base is reused by import — `PhotoLean.Kasha.Basic` fixes the
finite excited-state ladder, its branching probabilities, the observables `fluoYield`,
`upperYield`, `specFrac` and the predicates `KashaRule`, `VavilovAt`, `VavilovUpTo`, and
`PhotoLean.Kasha.Criterion` proves the laws of that cascade; nothing under `PhotoLean/Kasha/*` is
modified here (plan §1.2, §11).

This module is the description layer of the theory (milestone KV1, plan §4 rows KV-B1–KV-B7). It
adds exactly one new object — the spectral predicate `SpecSame`, the normalized spectra of two
excitation levels agreeing on the levels the two ladders share — and proves the rules of the
delivered observables that the D2 core consumes: the premise-bundle restriction `rateData_mono`,
the pure index split of the total yield (KV-B2, the delivered sibling
`Kasha.fluoYield_eq_low_add_upper` re-proved **without** its decorative `RateData` premise, per
the plan's weakest-premise standard), the two spectral corollaries of the exact rule, the descent
of the exact rule to lower excitation levels, and the exact rule's implication of the spectral
form of Vavilov's rule.

Honesty note (plan §3.1 entry 0, literature note): the canonical Vavilov rule quantifies over the
quantum **yield** only (LITERATURE S3, Birks p. 392). `SpecSame` is **this theory's own**
spectral predicate and that reading must not be attributed to Vavilov; it is used here as the
spectral form of the same independence claim, and every row that consumes it says so.

What is NOT derived here: the ladder model, the branching reading of the rates and the
identification of the observables with spectroscopic data — modelling assumptions inherited from
`PhotoLean.Kasha.Basic` (plan §9). Every positivity is an explicit hypothesis: `Kasha.RateData`
on every physical row, and the row-specific premises `0 < fluoYield`, `1 ≤ i` that the totalized
division genuinely needs (plan §8 — dropping them would be a false statement, not a stronger one).

Statement authority: every definition body and every theorem signature below is taken word for
word from `theories/KashaVavilov/probes/KashaVavilov-statement-skeleton.lean` (the frozen Phase-1
authority, sha256
`5a51614d80d8340d76b605657802152f6574ad40c31aa6eb9e8d373d65dfdb15`, 29 declarations), which
transcribes `theories/KashaVavilov/plan.md` §4. The fidelity checker
`python3 theories/BEP/probes/bep-fidelity.py --theory KashaVavilov` compares the two word for
word. Note deliberately: the two keyword literals that `proofs/scripts/check.sh --strict` scans
for are not spelled out anywhere in this file — the scan covers `PhotoLean/**/*.lean` including
block comments, so writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/KashaVavilov/plan.md` §4 (KV-B rows), sprint KV1; board
`theories/KashaVavilov/TASKS.md`. Acceptance commands:

    proofs/scripts/lake build PhotoLean.KashaVavilov.Basic
    proofs/scripts/check.sh --strict PhotoLean.KashaVavilov.Basic
    proofs/scripts/axioms.sh PhotoLean.KashaVavilov.Basic PhotoLean.KashaVavilov.<theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic declaration;
`#print axioms` of every theorem below lists at most `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib
import PhotoLean.Kasha.Basic
import PhotoLean.Kasha.Criterion

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace KashaVavilov

/-! ## KV1 — description layer (plan §4, rows KV-B1–KV-B7) -/

/-- Plan section 4, row KV-B1 — the new predicate of this theory: the normalized spectra at two
excitation levels agree on the common levels (pairwise spectral agreement). This is the theory's
own spectral predicate, not Vavilov's rule (plan §3.1 entry 0). -/
def SpecSame (rad ic : ℕ → ℝ) (M N : ℕ) : Prop :=
  ∀ i, i ≤ M → i ≤ N → Kasha.specFrac rad ic i M = Kasha.specFrac rad ic i N

/-- Plan section 4, row KV-B2 — the total yield splits into the lowest level's emission and the
leak; pure `Finset.range`/`Icc` split, no premises (totalized). The delivered sibling
`Kasha.fluoYield_eq_low_add_upper` carries a `RateData` signature premise that this identity does
not consume, so the row is proved here in its weakest-premise form (plan §3.1/§8 standard); the
index identity itself is `range (N+1) = {0} ∪ Icc 1 N`. -/
theorem fluoYield_eq_emitYield_zero_add_upperYield (rad ic : ℕ → ℝ) (N : ℕ) :
    Kasha.fluoYield rad ic N = Kasha.emitYield rad ic 0 N + Kasha.upperYield rad ic N := by
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold Kasha.fluoYield Kasha.upperYield
  rw [hrange, Finset.sum_insert (by simp)]

/-- Plan section 4, row KV-B3 — premise-bundle restriction: the standing physical premises at
level `N` restrict to any lower level `M ≤ N`. -/
theorem rateData_mono {rad ic : ℕ → ℝ} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N) :
    Kasha.RateData rad ic M :=
  ⟨fun n hn => h.decay_pos n (le_trans hn hMN), h.rad_nonneg, h.ic_nonneg⟩

/-- Plan section 4, row KV-B4 — under the exact Kasha rule the lowest level carries the whole
normalized spectrum. The premise `0 < fluoYield` is load-bearing: `specFrac` is totalized division
(plan §8). Proof route: `Kasha.kashaRule_iff_rad_zero` + `radBranch = 0` + `div_self`. The
`RateData` bundle was dropped in the Phase-3 premise audit (plan §3.1 entry 2, 2026-09-23): it
was never consumed — the index split KV-B2 and the nonzero denominator suffice; the stripped form
was re-proved before the edit. -/
theorem specFrac_zero_of_kashaRule {rad ic : ℕ → ℝ} {N : ℕ}
    (hK : Kasha.KashaRule rad ic N) (hpos : 0 < Kasha.fluoYield rad ic N) :
    Kasha.specFrac rad ic 0 N = 1 := by
  have hsplit := fluoYield_eq_emitYield_zero_add_upperYield rad ic N
  have hu : Kasha.upperYield rad ic N = 0 := hK
  have hlow : Kasha.emitYield rad ic 0 N = Kasha.fluoYield rad ic N := by linarith
  have hF : Kasha.fluoYield rad ic N ≠ 0 := ne_of_gt hpos
  unfold Kasha.specFrac
  rw [hlow]
  exact div_self hF

/-- Plan section 4, row KV-B5 — under the exact Kasha rule every upper level carries none of the
normalized spectrum. The premise `1 ≤ i` is load-bearing: the exact rule says nothing about the
lowest level, which carries everything by KV-B4. Proof route: `Kasha.kashaRule_iff_rad_zero` +
`radBranch = 0` + `zero_div`. -/
theorem specFrac_succ_of_kashaRule {rad ic : ℕ → ℝ} {N i : ℕ} (h : Kasha.RateData rad ic N)
    (hK : Kasha.KashaRule rad ic N) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    Kasha.specFrac rad ic i N = 0 := by
  have hrad : rad i = 0 := (Kasha.kashaRule_iff_rad_zero h).mp hK i hi1 hiN
  have hemit : Kasha.emitYield rad ic i N = 0 := by
    unfold Kasha.emitYield Kasha.radBranch
    rw [hrad, zero_div, zero_mul]
  unfold Kasha.specFrac
  rw [hemit, zero_div]

/-- Plan section 4, row KV-B6 — the exact Kasha rule at level `N` descends to every lower level
`M ≤ N`: the levels above `M` are a subset of the levels above `0`. -/
theorem kashaRule_mono {rad ic : ℕ → ℝ} {M N : ℕ} (h : Kasha.RateData rad ic N) (hMN : M ≤ N)
    (hK : Kasha.KashaRule rad ic N) : Kasha.KashaRule rad ic M :=
  (Kasha.kashaRule_iff_rad_zero (rateData_mono h hMN)).mpr fun i hi1 hiM =>
    (Kasha.kashaRule_iff_rad_zero h).mp hK i hi1 (le_trans hiM hMN)

/-- Plan section 4, row KV-B7 — the exact rule gives the spectral Vavilov rule: under Kasha the
spectrum is the delta at level `0` (KV-B4/KV-B5, the latter descended to every `M ≤ N` by
KV-B6), hence excitation-independent. The premise `0 < fluoYield · M` is the load-bearing
denominator hypothesis of KV-B4 (plan §8). -/
theorem specSame_of_kashaRule {rad ic : ℕ → ℝ} {N : ℕ} (h : Kasha.RateData rad ic N)
    (hpos : ∀ M, M ≤ N → 0 < Kasha.fluoYield rad ic M) (hK : Kasha.KashaRule rad ic N) :
    ∀ M, M ≤ N → SpecSame rad ic M N := by
  intro M hM i hiM hiN
  have hM' : Kasha.RateData rad ic M := rateData_mono h hM
  have hKM : Kasha.KashaRule rad ic M := kashaRule_mono h hM hK
  by_cases hi0 : i = 0
  · subst hi0
    exact (specFrac_zero_of_kashaRule hKM (hpos M hM)).trans
      (specFrac_zero_of_kashaRule hK (hpos N le_rfl)).symm
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    exact (specFrac_succ_of_kashaRule hM' hKM hi1 hiM).trans
      (specFrac_succ_of_kashaRule h hK hi1 hiN).symm

end KashaVavilov

end PhotoLean
