/-
BEP milestone — API probe (topic E): the `EPZone` classifier and its nine characterizations.

Scope. The classifier is the nine-branch `if`-cascade of plan §4.1 — a *deliberately different*
splitting from `Hammond.hammondZone`'s seven branches: `lam = 0` and `lam < 0` are separate leading
guards, so `degenerate` is characterized with **no** hypothesis and the seven remaining
characterizations carry only `0 < lam` (in the Hammond classifier the `lam = 0` case had to be
absorbed by the guards, which left three of its characterization lemmas with a redundant premise).

Running:  proofs/scripts/lake env lean theories/BEP/probes/bep-api-zone.lean
Status:   0 errors / 0 warnings.

Kernel-checked rows: plan §4.2 #7–#15. The uniform recipe is `unfold epZone`, then
`split_ifs with h1 … h8` (nine goals; in branch `k` the names are the negated guards `1…k-1` plus
the guard of branch `k`), then one `iff_of_true rfl _` / `iff_of_false (by decide) _` per leaf with
`linarith` on the arithmetic side.
-/
import Mathlib

namespace PhotoLean.BEP.ProbeZone

/-- Regimes of the transfer coefficient (decidable classifier). -/
inductive EPZone where
  | degenerate
  | unphysical
  | thermoneutral
  | exergonic
  | endergonic
  | atForwardLimit
  | atReverseLimit
  | beyondForward
  | beyondReverse
  deriving DecidableEq, Repr

/-- Regime classifier, in the style of `Hammond.hammondZone` / `Marcus.zone`. -/
noncomputable def epZone (lam x : ℝ) : EPZone :=
  if lam = 0 then EPZone.degenerate
  else if lam < 0 then EPZone.unphysical
  else if x = 0 then EPZone.thermoneutral
  else if x = lam then EPZone.atForwardLimit
  else if x = -lam then EPZone.atReverseLimit
  else if lam < x then EPZone.beyondForward
  else if x < -lam then EPZone.beyondReverse
  else if 0 < x then EPZone.exergonic
  else EPZone.endergonic

/-- Plan §4.2 #7: the degenerate regime needs **no** hypothesis (the leading guard is the
statement). -/
theorem epZone_eq_degenerate_iff (lam x : ℝ) : epZone lam x = EPZone.degenerate ↔ lam = 0 := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

set_option linter.unusedVariables false in
/-- Plan §4.2 #8. The premise `hlam : lam ≠ 0` is **redundant here**: at `lam = 0` both sides are
false (`degenerate ≠ unphysical`, and `0 < 0` fails). It is kept for signature fidelity with the
plan and the linter is switched off locally. -/
theorem epZone_eq_unphysical_iff {lam x : ℝ} (hlam : lam ≠ 0) :
    epZone lam x = EPZone.unphysical ↔ lam < 0 := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1]; exact lt_irrefl 0)
  · exact iff_of_true rfl h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2

/-- Plan §4.2 #9. -/
theorem epZone_eq_thermoneutral_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.thermoneutral ↔ x = 0 := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_true rfl h3
  · exact iff_of_false (by decide) (by rw [h4]; linarith)
  · exact iff_of_false (by decide) (by rw [h5]; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_false (by decide) h3
  · exact iff_of_false (by decide) h3

/-- Plan §4.2 #10. -/
theorem epZone_eq_exergonic_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.exergonic ↔ 0 < x ∧ x < lam := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by rintro ⟨-, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; rw [h3] at hx; exact lt_irrefl 0 hx)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; rw [h4] at hlt; exact lt_irrefl lam hlt)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; rw [h5] at hx; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hx, -⟩; linarith)
  · exact iff_of_true rfl ⟨h8, lt_of_le_of_ne (not_lt.mp h6) h4⟩
  · exact iff_of_false (by decide) (fun h => h8 h.1)

/-- Plan §4.2 #11. -/
theorem epZone_eq_endergonic_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.endergonic ↔ -lam < x ∧ x < 0 := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by rintro ⟨-, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; rw [h3] at hlt; exact lt_irrefl 0 hlt)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; rw [h4] at hlt; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hlt, -⟩; rw [h5] at hlt; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨hlt, -⟩; linarith)
  · exact iff_of_false (by decide) (by rintro ⟨-, hlt⟩; linarith)
  · exact iff_of_true rfl ⟨lt_of_le_of_ne (not_lt.mp h7) (Ne.symm h5),
      lt_of_le_of_ne (le_of_not_gt h8) h3⟩

/-- Plan §4.2 #12. -/
theorem epZone_eq_atForwardLimit_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.atForwardLimit ↔ x = lam := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_false (by decide) (by rintro rfl; linarith)
  · exact iff_of_true rfl h4
  · exact iff_of_false (by decide) (by rintro h; rw [h5] at h; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h] at h6; exact absurd h6 (lt_irrefl lam))
  · exact iff_of_false (by decide) (by rintro h; rw [h] at h7; linarith)
  · exact iff_of_false (by decide) h4
  · exact iff_of_false (by decide) h4

/-- Plan §4.2 #13. -/
theorem epZone_eq_atReverseLimit_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.atReverseLimit ↔ x = -lam := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h3] at h; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h4] at h; linarith)
  · exact iff_of_true rfl h5
  · exact iff_of_false (by decide) (by rintro h; rw [h] at h6; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h] at h7; exact lt_irrefl (-lam) h7)
  · exact iff_of_false (by decide) h5
  · exact iff_of_false (by decide) h5

/-- Plan §4.2 #14. -/
theorem epZone_eq_beyondForward_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.beyondForward ↔ lam < x := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h3] at h; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h4] at h; exact lt_irrefl lam h)
  · exact iff_of_false (by decide) (by rintro h; rw [h5] at h; linarith)
  · exact iff_of_true rfl h6
  · exact iff_of_false (by decide) (by rintro h; linarith)
  · exact iff_of_false (by decide) h6
  · exact iff_of_false (by decide) h6

/-- Plan §4.2 #15. -/
theorem epZone_eq_beyondReverse_iff {lam x : ℝ} (hlam : 0 < lam) :
    epZone lam x = EPZone.beyondReverse ↔ x < -lam := by
  unfold epZone
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact iff_of_false (by decide) (by rw [h1] at hlam; exact absurd hlam (lt_irrefl 0))
  · exact iff_of_false (by decide) (by linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h3] at h; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h4] at h; linarith)
  · exact iff_of_false (by decide) (by rintro h; rw [h5] at h; exact lt_irrefl (-lam) h)
  · exact iff_of_false (by decide) (by rintro h; linarith)
  · exact iff_of_true rfl h7
  · exact iff_of_false (by decide) h7
  · exact iff_of_false (by decide) h7

/-! ## Controls (mandatory in this repository) -/

/-- Exhaustiveness of the nine constructors (direct from the cascade's structure). -/
example (lam x : ℝ) :
    epZone lam x = EPZone.degenerate ∨ epZone lam x = EPZone.unphysical ∨
      epZone lam x = EPZone.thermoneutral ∨ epZone lam x = EPZone.exergonic ∨
      epZone lam x = EPZone.endergonic ∨ epZone lam x = EPZone.atForwardLimit ∨
      epZone lam x = EPZone.atReverseLimit ∨ epZone lam x = EPZone.beyondForward ∨
      epZone lam x = EPZone.beyondReverse := by
  unfold epZone
  split_ifs <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

/-- Non-vacuity of every constructor (plan §5 #20–26; explicit witnesses, no case bash). -/
example : ∃ lam x : ℝ, epZone lam x = EPZone.degenerate := ⟨0, 1, by unfold epZone; rw [if_pos rfl]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.unphysical :=
  ⟨-1, 1, by unfold epZone; rw [if_neg (by norm_num : ¬((-1 : ℝ) = 0)), if_pos (by norm_num)]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.thermoneutral :=
  ⟨1, 0, by unfold epZone; rw [if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) < 0)), if_pos rfl]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.exergonic :=
  ⟨2, 1, by unfold epZone; rw [if_neg (by norm_num : ¬((2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) < 0)), if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) = 2)), if_neg (by norm_num : ¬((1 : ℝ) = -2)),
    if_neg (by norm_num : ¬((2 : ℝ) < 1)), if_neg (by norm_num : ¬((1 : ℝ) < -2)),
    if_pos (by norm_num : (0 : ℝ) < 1)]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.endergonic :=
  ⟨2, -1, by unfold epZone; rw [if_neg (by norm_num : ¬((2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) < 0)), if_neg (by norm_num : ¬((-1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((-1 : ℝ) = 2)), if_neg (by norm_num : ¬((-1 : ℝ) = -2)),
    if_neg (by norm_num : ¬((2 : ℝ) < -1)), if_neg (by norm_num : ¬((-1 : ℝ) < -2)),
    if_neg (by norm_num : ¬((0 : ℝ) < -1))]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.atForwardLimit :=
  ⟨1, 1, by unfold epZone; rw [if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) < 0)), if_neg (by norm_num : ¬((1 : ℝ) = 0)), if_pos rfl]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.atReverseLimit :=
  ⟨1, -1, by unfold epZone; rw [if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) < 0)), if_neg (by norm_num : ¬((-1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((-1 : ℝ) = 1)), if_pos (by norm_num : (-1 : ℝ) = -1)]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.beyondForward :=
  ⟨1, 2, by unfold epZone; rw [if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) < 0)), if_neg (by norm_num : ¬((2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) = 1)), if_neg (by norm_num : ¬((2 : ℝ) = -1)),
    if_pos (by norm_num : (1 : ℝ) < 2)]⟩
example : ∃ lam x : ℝ, epZone lam x = EPZone.beyondReverse :=
  ⟨1, -2, by unfold epZone; rw [if_neg (by norm_num : ¬((1 : ℝ) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) < 0)), if_neg (by norm_num : ¬((-2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((-2 : ℝ) = 1)), if_neg (by norm_num : ¬((-2 : ℝ) = -1)),
    if_neg (by norm_num : ¬((1 : ℝ) < -2)), if_pos (by norm_num : (-2 : ℝ) < -1)]⟩

/-- Negative controls: each characterization is refuted at a concrete counterexample, so none of
them is a tautology of the cascade. -/
example : ¬ (epZone 1 1 = EPZone.thermoneutral) := by
  rw [epZone_eq_thermoneutral_iff (by norm_num : (0 : ℝ) < 1)]
  norm_num
example : ¬ (epZone 1 2 = EPZone.exergonic) := by
  rw [epZone_eq_exergonic_iff (by norm_num : (0 : ℝ) < 1)]
  norm_num
example : ¬ (epZone (-1) 0 = EPZone.thermoneutral) := by
  have h : epZone (-1) (0 : ℝ) = EPZone.unphysical :=
    (epZone_eq_unphysical_iff (by norm_num : ¬((-1 : ℝ) = 0))).mpr (by norm_num)
  rw [h]
  decide
example : ¬ (epZone 0 5 = EPZone.thermoneutral) := by
  have h : epZone 0 (5 : ℝ) = EPZone.degenerate :=
    (epZone_eq_degenerate_iff 0 5).mpr rfl
  rw [h]
  decide

end PhotoLean.BEP.ProbeZone
