/-
PhotoLean.Kasha.Basic — K1, the description layer of Kasha's rule.

Kasha's rule ("luminescence is emitted only from the lowest excited state of a given
multiplicity, whatever the excitation") is formalized here in the finite excited-state cascade
model of `theories/kasha/plan.md` §1.2: a ladder of excited levels `0, 1, …, N`, truncated at the
excitation level `N`; level `0` is the lowest excited state of the multiplicity under
consideration (`S₁` for fluorescence), level `n ≥ 1` is the n-th state above it. Each level
carries a radiative rate `rad n` and a nonradiative rate `ic n` (internal conversion `n → n-1`
for `n ≥ 1`, loss to the ground state for `n = 0`). Under the standing premise bundle `RateData`
(positive total decay up to the excitation level, nonnegative rates — an explicit hypothesis of
every physical theorem here, never hidden in a definition) the branching probabilities are
`radBranch = rad / decay` and `icBranch = ic / decay`, the probability of arriving at level `i`
from level `N` without emitting is the product `cascade i N`, and the observables are the
level-resolved yield `emitYield i N`, the total fluorescence yield `fluoYield N`, the leak
`upperYield N` (emission from levels above the lowest one), the normalized spectrum `specFrac`,
the funnel margin `kashaMargin` and the two funnel ratios (`funnelRatio`, `ladderRatio`). On top
of those sit the predicates `KashaRule` (exact rule), `KashaWithin` (its tolerance form),
`VavilovAt` / `VavilovUpTo` (excitation-independence of the total yield) and `KashaDescriptor`
(non-vacuity), plus the decidable regime classifier `kashaZone` with its three branch
characterizations.

This module is the description layer only. The laws of the cascade — the Markov recursion, the
conservation identity, the exact criterion `KashaRule ↔ rad = 0` above the lowest level, the
Kasha–Vavilov equivalence, the sharp funnel-ratio threshold, the effective two-level reduction
and the Marcus bridge — are milestones K2–K4 in `PhotoLean/Kasha/{Criterion,Sharp,Compose}.lean`.

What is NOT derived here (plan §1.2, §12, §13): the ladder model itself, the identification of
the branching probabilities with the outcome of competing exponential clocks, the reading of the
time-integrated yields as the observables of Kasha/Vavilov spectroscopy, and the interpretation
of `ic 0` as the lowest state's loss channel. They are modelling assumptions, registered as such
in the plan's honesty table and scope limits; no theorem below depends on one of them silently.

Statement authority: every definition body and every theorem signature below is taken word for
word from `theories/kasha/probes/kasha-statement-skeleton.lean` (its §K1 block; sha256
`e3ddc2d01317ec6bc46957cae7763034a23df691bffc480a08c9a23d9fe6412b`), which in turn transcribes
`theories/kasha/plan.md` §4.1 and §4.2. The design rule of the engine applies throughout: a
physical approximation is an explicit hypothesis (that is what `RateData` is for), never a
definition. Note deliberately: the two keyword literals that `proofs/scripts/check.sh --strict`
scans for are not spelled out anywhere in this file — that scan covers `PhotoLean/**/*.lean`
including block comments, so writing them (even in prose) would be a false-positive FAIL.

Plan locus: `theories/kasha/plan.md` §4 (K1); board `theories/kasha/TASKS.md` §K1. This module
imports `Mathlib` only — no `PhotoLean.Marcus`, no other `PhotoLean` module: the description
layer is self-contained. Docstrings §4.2 #n refer to the plan's theorem table.

Acceptance commands (run on a clean tree):

    proofs/scripts/lake build PhotoLean.Kasha.Basic
    proofs/scripts/check.sh --strict PhotoLean.Kasha.Basic
    proofs/scripts/axioms.sh PhotoLean.Kasha.Basic PhotoLean.Kasha.<fully.qualified.theorem>

The delivered file contains no unfinished-proof placeholder and no custom axiomatic
declaration; the `#print axioms` gate of every theorem below lists at most `propext`,
`Classical.choice`, `Quot.sound`.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace PhotoLean

namespace Kasha
/-! ## Definitions (plan §4.1) -/

/-- Total decay rate of level `n`: the sum of its radiative and its nonradiative channel. -/
noncomputable def decay (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n + ic n

/-- Probability that level `n` decays radiatively (emits a photon). -/
noncomputable def radBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := rad n / decay rad ic n

/-- Probability that level `n` decays nonradiatively: internal conversion `n → n-1` for `n ≥ 1`,
loss to the ground state for `n = 0`. -/
noncomputable def icBranch (rad ic : ℕ → ℝ) (n : ℕ) : ℝ := ic n / decay rad ic n

/-- Probability that, starting at level `N`, the molecule reaches level `i` without having emitted
(plan §1.2). -/
noncomputable def cascade (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (i + 1) N, icBranch rad ic j

/-- Time-integrated emission yield of level `i` under excitation at level `N`. -/
noncomputable def emitYield (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := radBranch rad ic i * cascade rad ic i N

/-- Total fluorescence quantum yield under excitation at level `N` (plan §1.2). -/
noncomputable def fluoYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), emitYield rad ic i N

/-- Emission from levels **above** the lowest one — the leak past the funnel of Kasha's rule. -/
noncomputable def upperYield (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, emitYield rad ic i N

/-- The normalized emission spectrum: the fraction of the emitted photons that comes from level
`i` (plan §1.2). -/
noncomputable def specFrac (rad ic : ℕ → ℝ) (i N : ℕ) : ℝ := emitYield rad ic i N / fluoYield rad ic N

/-- Funnel margin of the N-level ladder: how much emission from the lowest level accompanies one
unit of leak (plan §2, §6.1 #5). -/
noncomputable def kashaMargin (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  emitYield rad ic 0 N / upperYield rad ic N

/-- The two-level funnel ratio: the `k_IC / k_rad`-shaped quantity whose threshold is the sharp
criterion (plan §1.3, §6.1 #2). -/
noncomputable def funnelRatio (rad ic : ℕ → ℝ) : ℝ := rad 0 * ic 1 / (rad 1 * decay rad ic 0)

/-- The N-level funnel ratio: the quantity the general threshold tests (plan §6.1 #5, §7.2 #9). -/
noncomputable def ladderRatio (rad ic : ℕ → ℝ) (N : ℕ) : ℝ :=
  rad 0 * cascade rad ic 0 N / (upperYield rad ic N * decay rad ic 0)
end Kasha

end PhotoLean
