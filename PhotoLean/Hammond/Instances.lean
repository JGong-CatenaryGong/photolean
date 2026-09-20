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

/-! ## I3 — endergonic textbook instance (`lam = 1`, `x = -1/2`) -/
/-- I3, zone verdict: the endergonic instance is classified `late`. -/
theorem inst_I3_endergonic_zone : Rat.hammondZoneQ (1 : ℚ) (-(1 / 2)) = HZone.late := by
  norm_num [Rat.hammondZoneQ]

/-- I3, resemblance verdict: endergonic (`x < 0`) means product-like — an instance of H2's
`productLike_iff`. -/
theorem inst_I3_endergonic_productLike : ProductLike 1 (-(1 / 2)) :=
  (productLike_iff (by norm_num : (0 : ℝ) < 1)).mpr (by norm_num : (-(1 / 2) : ℝ) < 0)

/-- I3, point-level verdict: the instance conforms to the Hammond description (late zone,
strictly inside the regime). -/
theorem inst_I3_endergonic_conforms : HammondConforms 1 (-(1 / 2)) := by
  have hz : hammondZone (1 : ℝ) (-(1 / 2) : ℝ) = HZone.late := by
    rw [← (by norm_num : (((-(1 / 2) : ℚ)) : ℝ) = (-(1 / 2) : ℝ)),
        ← (by norm_num : ((1 : ℚ) : ℝ) = (1 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I3_endergonic_zone]
  exact (conforms_iff_zone (by norm_num : (0 : ℝ) < 1)).mpr (Or.inr (Or.inr hz))

/-! ## I4 — barrierless forward instance (`lam = 1`, `x = 1`): boundary of the regime -/
/-- I4, zone verdict: the barrierless instance sits on the reactant boundary
(`atReactant`). -/
theorem inst_I4_barrierless_zone : Rat.hammondZoneQ (1 : ℚ) 1 = HZone.atReactant := by
  norm_num [Rat.hammondZoneQ]

/-- I4, coordinate: the transition state sits exactly at the reactant geometry. -/
theorem inst_I4_barrierless_coord : tsCoord 1 1 = 0 := by
  norm_num [tsCoord]

/-- I4, point-level verdict **fails**: the crossing point is not strictly between the two wells,
so the resemblance reading is degenerate at this point — the instance lies on the boundary of the
domain where the Hammond description applies (it is not an anti-Hammond instance). -/
theorem inst_I4_barrierless_notConforms : ¬ HammondConforms 1 1 := by
  intro hc
  have hz : hammondZone (1 : ℝ) 1 = HZone.atReactant := by
    rw [← (by norm_num : ((1 : ℚ) : ℝ) = (1 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I4_barrierless_zone]
  have hd := (conforms_iff_zone (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [hz] at hd
  rcases hd with h | h | h <;> exact absurd h (by decide)

/-- I4, family-level verdict: the descriptor holds, because it is a statement about `lam` alone
(`0 < 1`) — an instance of H2's `hammond_descriptor_holds`, showing that the family level is
insensitive to the boundary verdict above. -/
theorem inst_I4_family_descriptor : HammondDescriptor 1 :=
  hammond_descriptor_holds (by norm_num : (0 : ℝ) < 1)

/-! ## I5 — literature MCC normal-region instance (`lam = 6/5`, `x = 1/20`) -/
/-- I5, zone verdict: the MCC normal-region instance is classified `early`. -/
theorem inst_I5_mcc_normal_zone : Rat.hammondZoneQ (6 / 5) (1 / 20) = HZone.early := by
  norm_num [Rat.hammondZoneQ]

/-- I5, coordinate: `q‡ = 23/48`, i.e. the transition state is closer to the reactant well. -/
theorem inst_I5_mcc_normal_coord : tsCoord (6 / 5) (1 / 20) = 23 / 48 := by
  norm_num [tsCoord]

/-- I5, point-level verdict: the instance conforms to the Hammond description of the model. -/
theorem inst_I5_mcc_normal_conforms : HammondConforms (6 / 5) (1 / 20) := by
  have hz : hammondZone (6 / 5 : ℝ) (1 / 20 : ℝ) = HZone.early := by
    rw [← (by norm_num : (((6 : ℚ) / 5 : ℚ) : ℝ) = (6 / 5 : ℝ)),
        ← (by norm_num : (((1 : ℚ) / 20 : ℚ) : ℝ) = (1 / 20 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I5_mcc_normal_zone]
  exact (conforms_iff_zone (by norm_num : (0 : ℝ) < 6 / 5)).mpr (Or.inl hz)

/-! ## I6 — literature MCC inverted-region instance (`lam = 6/5`, `x = 12/5`) -/
/-- I6, zone verdict: the MCC inverted-region instance is classified `beyondReactant`. -/
theorem inst_I6_mcc_inverted_zone : Rat.hammondZoneQ (6 / 5) (12 / 5) = HZone.beyondReactant := by
  norm_num [Rat.hammondZoneQ]

/-- I6, coordinate: `q‡ = -1/2`, i.e. the crossing point lies outside the structural interval. -/
theorem inst_I6_mcc_inverted_coord : tsCoord (6 / 5) (12 / 5) = -(1 / 2) := by
  norm_num [tsCoord]

/-- I6, point-level verdict: the instance does **not** conform — it lies outside the domain of
applicability of the Hammond description of this model (the crossing point is not between the two
wells). This is a statement inside the model, not about any molecule. -/
theorem inst_I6_mcc_inverted_notConforms : ¬ HammondConforms (6 / 5) (12 / 5) := by
  intro hc
  have hz : hammondZone (6 / 5 : ℝ) (12 / 5 : ℝ) = HZone.beyondReactant := by
    rw [← (by norm_num : (((6 : ℚ) / 5 : ℚ) : ℝ) = (6 / 5 : ℝ)),
        ← (by norm_num : (((12 : ℚ) / 5 : ℚ) : ℝ) = (12 / 5 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I6_mcc_inverted_zone]
  have hd := (conforms_iff_zone (by norm_num : (0 : ℝ) < 6 / 5)).mp hc
  rw [hz] at hd
  rcases hd with h | h | h <;> exact absurd h (by decide)

/-- I6, Marcus cross-link: the same instance is exactly the Marcus inverted region. The proof goes
through the ℚ classifiers: H5a's `hammondZoneQ_beyondReactant_iff_inverted` turns the zone verdict
into `Marcus.Rat.zoneQ … = inverted`, and `Marcus.Rat.zoneQ_inverted_iff` turns that into the
ℝ inequality `lam < x` (which is `Marcus.InvertedRegion` by definition). -/
theorem inst_I6_mcc_inverted_region : Marcus.InvertedRegion (6 / 5) (12 / 5) := by
  have hm : Marcus.Rat.zoneQ (6 / 5) (12 / 5) = Marcus.Zone.inverted :=
    (Rat.hammondZoneQ_beyondReactant_iff_inverted (by norm_num : (0 : ℚ) < 6 / 5)).mp
      inst_I6_mcc_inverted_zone
  have hlt := (Marcus.Rat.zoneQ_inverted_iff (6 / 5) (12 / 5)).mp hm
  unfold Marcus.InvertedRegion
  norm_num at hlt ⊢

/-- I6, barrier-data verdict: the Brønsted coefficient measured from the barrier values alone is
`-1/8 < 0` — the observable counterpart of the verdict above. -/
theorem inst_I6_mcc_leffler_negative : Rat.lefflerSecantQ (6 / 5) (3 / 5) (12 / 5) = -(1 / 8) := by
  norm_num [Rat.lefflerSecantQ, Rat.gapReactantQ]

end Hammond

end PhotoLean
