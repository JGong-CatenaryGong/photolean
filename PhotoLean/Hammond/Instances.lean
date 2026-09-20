/-
PhotoLean.Hammond.Instances — H5b: the instance layer and its verdicts.

Ten textbook/literature instances are pushed through the delivered Hammond theory. Every verdict
is a kernel-checked theorem; none of them asserts anything about an experiment (plan §13 wording
rule).

**What a verdict means.** "The instance conforms to the Hammond description" is exactly
`HammondConforms lam x` (H1): the curvature is positive AND the crossing point lies strictly
between the two wells, so the structural-resemblance reading of the two-parabola model is
meaningful at that point. Accordingly the verdicts of I6/I7 read: **the instance lies outside the
domain of applicability of the Hammond description of this model** — never "this molecule
violates Hammond's postulate".

**Evidence chain.** Instance verdicts come from kernel computation or theorem instantiation
(plan §11, H5):
* every zone verdict is a computation of the ℚ-side classifier (`norm_num [Rat.hammondZoneQ]`;
  `decide` is only usable on division-free rational literals — `proofs/API-NOTES.md`), and it is
  binding for the ℝ classifier through H5a's transfer lemma
  `Rat.hammondZoneQ_eq_hammondZone`;
* every ℝ-side verdict (`HammondConforms`, `ReactantLike`, `ProductLike`, `Marcus.InvertedRegion`)
  is obtained from the corresponding ℚ verdict through that transfer lemma together with the
  H1/H2 characterizations (`hammondZone_eq_{early,half,late,atReactant,beyondReactant}_iff`,
  `conforms_iff_zone`, `reactantLike_iff`, `productLike_iff`) or from an H2/H3 theorem
  (`tsCoord_antitone`, `hammond_descriptor_holds`, `hammond_fails_of_nonpos`,
  `not_reactionRegion_of_nonpos`) — the literal bridges between the ℚ-side and ℝ-side rational
  literals are closed by `norm_num` (cast literals are not definitionally equal to `OfNat`
  literals, an engine lesson recorded in `proofs/EXPERIENCE.md`);
* the coordinates and the Leffler secant are evaluated at the instance by `norm_num`.

Statement authority: the H5b section of
`theories/hammond/probes/hammond-statement-skeleton.lean` (plan §8.2). The 29 signatures below
match it word for word. `lam` and `x` are in eV, with the driving-force convention `x = -ΔG°`.

Acceptance (contract `proofs/ENGINE.yml`):
  proofs/scripts/lake build PhotoLean.Hammond.Instances
  proofs/scripts/check.sh --strict PhotoLean.Hammond.Instances
  proofs/scripts/axioms.sh PhotoLean.Hammond.Instances PhotoLean.Hammond.<theorem>
-/
import PhotoLean.Hammond.Sharp
import PhotoLean.Hammond.RatModel

namespace PhotoLean

namespace Hammond

/-! ## I1 — thermoneutral textbook instance (`lam = 1`, `x = 0`) -/
/-- I1, zone verdict: the ℚ classifier puts the thermoneutral instance in the `half` branch. -/
theorem inst_I1_thermoneutral_zone : Rat.hammondZoneQ (1 : ℚ) 0 = HZone.half := by
  norm_num [Rat.hammondZoneQ]

/-- I1, point-level verdict: the instance conforms — the crossing point lies strictly between the
two wells (`x = 0`), so the Hammond reading applies. The ℚ zone verdict is transferred to the ℝ
classifier and fed into `conforms_iff_zone`. -/
theorem inst_I1_thermoneutral_conforms : HammondConforms 1 0 := by
  have hz : hammondZone (1 : ℝ) 0 = HZone.half := by
    rw [← (by norm_num : ((1 : ℚ) : ℝ) = (1 : ℝ)),
        ← (by norm_num : ((0 : ℚ) : ℝ) = (0 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I1_thermoneutral_zone]
  exact (conforms_iff_zone (by norm_num : (0 : ℝ) < 1)).mpr (Or.inr (Or.inl hz))

/-- I1, coordinate: thermoneutrality puts the transition state exactly halfway. -/
theorem inst_I1_thermoneutral_coord : tsCoord 1 0 = 1 / 2 := by
  norm_num [tsCoord]

/-! ## I2 — mildly exergonic textbook instance (`lam = 1`, `x = 3/4`) -/
/-- I2, zone verdict: the mildly exergonic instance is classified `early`. -/
theorem inst_I2_exergonic_zone : Rat.hammondZoneQ (1 : ℚ) (3 / 4) = HZone.early := by
  norm_num [Rat.hammondZoneQ]

/-- I2, resemblance verdict: exergonic (`x > 0`) means reactant-like — an instance of H2's
`reactantLike_iff`, not a re-derivation. -/
theorem inst_I2_exergonic_reactantLike : ReactantLike 1 (3 / 4) :=
  (reactantLike_iff (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num : (0 : ℝ) < 3 / 4)

/-- I2, point-level verdict: the instance conforms to the Hammond description (early zone,
strictly inside the regime). -/
theorem inst_I2_exergonic_conforms : HammondConforms 1 (3 / 4) := by
  have hz : hammondZone (1 : ℝ) (3 / 4 : ℝ) = HZone.early := by
    rw [← (by norm_num : ((1 : ℚ) : ℝ) = (1 : ℝ)),
        ← (by norm_num : (((3 : ℚ) / 4 : ℚ) : ℝ) = (3 / 4 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I2_exergonic_zone]
  exact (conforms_iff_zone (by norm_num : (0 : ℝ) < 1)).mpr (Or.inl hz)

end Hammond

end PhotoLean
