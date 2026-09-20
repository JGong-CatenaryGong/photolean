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

/-- I6, barrier-data verdict: the Brønsted coefficient computed from the model's barrier values alone
is `-1/8 < 0` — the barrier-data counterpart, inside the model, of the verdict above. (It is not a
statement about an experimentally measured slope; for the pair `3/5 -> 12/5` the secant's midpoint is
`x = 3/2`, where the model's own coordinate is `-1/8`.) -/
theorem inst_I6_mcc_leffler_negative : Rat.lefflerSecantQ (6 / 5) (3 / 5) (12 / 5) = -(1 / 8) := by
  norm_num [Rat.lefflerSecantQ, Rat.gapReactantQ]

/-! ## I7 — literature reaction-centre deep-inverted instance (`lam = 1/4`, `x = 11/10`) -/
/-- I7, zone verdict: the reaction-centre instance is classified `beyondReactant`. -/
theorem inst_I7_rc_inverted_zone : Rat.hammondZoneQ (1 / 4) (11 / 10) = HZone.beyondReactant := by
  norm_num [Rat.hammondZoneQ]

/-- I7, coordinate: `q‡ = -17/10`, far outside the structural interval. -/
theorem inst_I7_rc_inverted_coord : tsCoord (1 / 4) (11 / 10) = -(17 / 10) := by
  norm_num [tsCoord]

/-- I7, point-level verdict: the instance does **not** conform — outside the domain of
applicability of the Hammond description of this model. -/
theorem inst_I7_rc_inverted_notConforms : ¬ HammondConforms (1 / 4) (11 / 10) := by
  intro hc
  have hz : hammondZone (1 / 4 : ℝ) (11 / 10 : ℝ) = HZone.beyondReactant := by
    rw [← (by norm_num : (((1 : ℚ) / 4 : ℚ) : ℝ) = (1 / 4 : ℝ)),
        ← (by norm_num : (((11 : ℚ) / 10 : ℚ) : ℝ) = (11 / 10 : ℝ)),
        ← Rat.hammondZoneQ_eq_hammondZone, inst_I7_rc_inverted_zone]
  have hd := (conforms_iff_zone (by norm_num : (0 : ℝ) < 1 / 4)).mp hc
  rw [hz] at hd
  rcases hd with h | h | h <;> exact absurd h (by decide)

/-! ## I8 — non-physical curvature instances (rejected by the sharp characterization) -/
/-- I8 (negative curvature): the descriptor fails — H3's `hammond_fails_of_nonpos` at
`lam = -1/2`. -/
theorem inst_I8_nonphysical_fails_neg : ¬ HammondDescriptor (-(1 / 2)) :=
  hammond_fails_of_nonpos (by norm_num : (-(1 / 2) : ℝ) ≤ 0)

/-- I8 (zero curvature): the descriptor fails as well — the degenerate branch exists only through
the division convention `x / 0 = 0` (plan §13, assumption 5). -/
theorem inst_I8_nonphysical_fails_zero : ¬ HammondDescriptor 0 :=
  hammond_fails_of_nonpos (by norm_num : (0 : ℝ) ≤ 0)

/-- I8, point-level: with negative curvature no driving force satisfies the regime — an instance
of H1's `not_reactionRegion_of_nonpos`. -/
theorem inst_I8_nonphysical_no_region : ¬ ReactionRegion (-(1 / 2)) 1 :=
  not_reactionRegion_of_nonpos (by norm_num : (-(1 / 2) : ℝ) ≤ 0)

/-! ## I9 — the Hammond direction on the literature MCC pair -/
/-- I9: going from `x = 3/5` to `x = 12/5` lowers the transition-state coordinate — the Hammond
direction, instantiated from H2's `tsCoord_antitone` (no new arithmetic). -/
theorem inst_I9_mcc_structural_monotone : tsCoord (6 / 5) (12 / 5) < tsCoord (6 / 5) (3 / 5) :=
  tsCoord_antitone (by norm_num : (0 : ℝ) < 6 / 5) (by norm_num : (3 / 5 : ℝ) < 12 / 5)

/-! ## I10 — non-vacuity of the instance layer on literature parameters -/
/-- I10: on the literature parameters both resemblance verdicts are inhabited — reactant-like at the
recorded pair `x = 1/20`, and product-like at its sign-mirror `x = -1/20` (the mirror is a
model-constructed companion of the recorded pair, not a second recorded value; cf. the literature
record section 6.2 item 7) — via H2's `reactantLike_iff` / `productLike_iff`. -/
theorem inst_I10_nonvacuous : ReactantLike (6 / 5) (1 / 20) ∧ ProductLike (6 / 5) (-(1 / 20)) :=
  ⟨(reactantLike_iff (by norm_num : (0 : ℝ) < 6 / 5)).mpr (by norm_num : (0 : ℝ) < 1 / 20),
   (productLike_iff (by norm_num : (0 : ℝ) < 6 / 5)).mpr (by norm_num : (-(1 / 20) : ℝ) < 0)⟩

end Hammond

end PhotoLean
