# Relation-Audit R3 Migration Fragment Integration Report

Status: **fragments validated** — this is not a production registry and not an
audit verdict. It covers exactly the 41 R2 certificate-required declarations.

## Counts

| item | value |
|---|---|
| fragments | 3 |
| queue declarations | 41 |
| covered declarations | 41 |
| certified | 27 |
| reclassified | 14 |
| conditionalComposition certificates | 0 |

## Certified by kind

| kind | declarations |
|---|---|
| `definitionalIdentity` | 18 |
| `implication` | 1 |
| `equivalence` | 6 |
| `observationalEquivalence` | 2 |

## Reclassification targets

| target category | declarations |
|---|---|
| `model-level-composition` | 4 |
| `scoped-relation-documentation` | 2 |
| `support-lemma` | 8 |

## Fragments

| fragment | module | declarations | certified | reclassified |
|---|---|---|---|---|
| `sections01_05` | `PhotoLean.RelationAudit.Full.Sections01_05` | 16 | 16 | 0 |
| `sections06_10` | `PhotoLean.RelationAudit.Full.Sections06_10` | 6 | 2 | 4 |
| `sections11_17` | `PhotoLean.RelationAudit.Full.Sections11_17` | 19 | 9 | 10 |

## Certified rows

| declaration | kind | premises | certificate |
|---|---|---|---|
| `D-S01-kernel_barrier_eq_hammond` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelBarrierHammondPin` |
| `D-S01-kernel_barrier_eq_bep` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelBarrierBepPin` |
| `D-S01-kernel_reverseBarrier_eq_hammond` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelReverseBarrierHammondPin` |
| `D-S01-kernel_tsCoord_eq_hammond` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelTsCoordHammondPin` |
| `D-S01-kernel_transfer_eq_bep` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelTransferBepPin` |
| `D-S01-kernel_reactantSurface_eq_hammond` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelReactantSurfaceHammondPin` |
| `D-S01-kernel_productSurface_eq_hammond` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.kernelProductSurfaceHammondPin` |
| `D-S02-transfer_eq_tsCoord_bridge` | `observationalEquivalence` | `bep.lamNeZero` | `PhotoLean.RelationAudit.Full.Sections01_05.transferTsCoordBridge` |
| `D-S02-secSlope_eq_lefflerSecant` | `observationalEquivalence` | — | `PhotoLean.RelationAudit.Full.Sections01_05.secSlopeLefflerSecantBridge` |
| `D-S02-tsCoord_lt_zero_iff_inverted` | `equivalence` | `marcus.curvaturePositive` | `PhotoLean.RelationAudit.Full.Sections01_05.tsCoordLtZeroInvertedEquivalence` |
| `D-S02-lefflerSecant_neg_iff_inverted` | `equivalence` | `marcus.curvaturePositive`, `hammond.distinctDrivingForces` | `PhotoLean.RelationAudit.Full.Sections01_05.lefflerSecantNegInvertedEquivalence` |
| `D-S02-hammondZoneQ_beyondReactant_iff_inverted` | `equivalence` | `marcus.curvaturePositive` | `PhotoLean.RelationAudit.Full.Sections01_05.hammondZoneQInvertedEquivalence` |
| `D-S03-hammondDescriptor_of_epConformsOnWindow` | `implication` | — | `PhotoLean.RelationAudit.Full.Sections01_05.windowConformanceDescriptorImplication` |
| `D-S05-bep_eact_eq_marcus_barrier` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.bepEactMarcusBarrierPin` |
| `D-S05-bep_rate_eq_exp_neg_eact` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.bepRateExpNegEactPin` |
| `D-S05-hammond_barrier_eq_gapReactant` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections01_05.hammondBarrierGapReactantPin` |
| `D-S06-hammond_sharp_iff_marcus_sharp` | `equivalence` | `hammondMarcusSharp.preExponentialPositive`, `hammondMarcusSharp.boltzmannPositive`, `hammondMarcusSharp.temperaturePositive` | `PhotoLean.RelationAudit.Full.Sections06_10.hammondMarcusSharpCertificate` |
| `D-S07-kernel_marcusIC` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections06_10.kernelMarcusICPin` |
| `D-S12-eg_barrier_eq_kernel` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.egBarrierEqKernelCertificate` |
| `D-S12-eg_rate_eq_marcus` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.egRateEqMarcusCertificate` |
| `D-S12-eg_invertedGap_iff_marcus` | `equivalence` | — | `PhotoLean.RelationAudit.Full.Sections11_17.egInvertedGapEquivalenceCertificate` |
| `D-S12-ss_s0Surface_eq_kernel` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.ssS0SurfaceEqKernelCertificate` |
| `D-S12-ss_s1Surface_eq_kernel` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.ssS1SurfaceEqKernelCertificate` |
| `D-S12-icvscic_barrier_eq_kernel` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.icvscicBarrierEqKernelCertificate` |
| `D-S12-icvscic_icRate_eq_marcus` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.icvscicIcRateEqMarcusCertificate` |
| `D-S15-egBarrier_zero_iff_emEnergy_zero` | `equivalence` | `energyGapLaw.lamNonzero` | `PhotoLean.RelationAudit.Full.Sections11_17.egBarrierZeroIffEmEnergyZeroCertificate` |
| `D-S15-icvscic_icRate_eq_eg_nrRate` | `definitionalIdentity` | — | `PhotoLean.RelationAudit.Full.Sections11_17.icvscicIcRateEqEnergyGapLawCertificate` |

## Reclassified rows

Every row below is evidence-only and is **not** a certified relation.

| declaration | target | blockers | evidence |
|---|---|---|---|
| `D-S08-linearVolcano_eq_bepTangent` | `model-level-composition` | `propositional-term-identity`, `not-definitional`, `not-typed-parent-composition`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections06_10.section08_linearVolcano_eq_bepTangent` |
| `D-S08-linearVolcano_le_parabolic` | `model-level-composition` | `pointwise-order-inequality`, `not-definitional`, `not-typed-parent-composition`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections06_10.section08_linearVolcano_le_parabolic` |
| `D-S08-parabolic_descriptor` | `model-level-composition` | `single-model-property`, `not-definitional`, `not-typed-parent-composition`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections06_10.section08_parabolic_descriptor` |
| `D-S08-linearVolcano_apex_exact` | `model-level-composition` | `pointwise-value-identity`, `not-definitional`, `not-typed-parent-composition`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections06_10.section08_linearVolcano_apex_exact` |
| `D-S11-symmetryFactor_tsCoordZero_eq_kernel` | `scoped-relation-documentation` | `numeric-tie-back`, `not-definitional`, `not-statement-level-implication-or-equivalence`, `transitive-only-pair` | `PhotoLean.RelationAudit.Full.Sections11_17.symmetryFactorTsCoordZeroEqKernel_evidence` |
| `D-S11-symmetryFactor_tsCoordZero_eq_bepTransfer` | `scoped-relation-documentation` | `numeric-tie-back`, `not-definitional`, `not-statement-level-implication-or-equivalence`, `transitive-only-pair` | `PhotoLean.RelationAudit.Full.Sections11_17.symmetryFactorTsCoordZeroEqBepTransfer_evidence` |
| `D-S15-kasha_radBranch_eq_yieldOf` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.kashaRadBranchEqYieldOf_evidence` |
| `D-S15-sv_quench_dilutes_yield` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.svQuenchDilutesYield_evidence` |
| `D-S15-phiF_eq_yieldOf` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.phiFEqYieldOf_evidence` |
| `D-S15-phiP_eq_yieldOf_cascade` | `support-lemma` | `product-of-yields`, `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.phiPEqYieldOfCascade_evidence` |
| `D-S15-einstein_yield_via_qy` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.einsteinYieldViaQY_evidence` |
| `D-S15-fretEff6_eq_one_sub_yieldOf` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.fretEff6EqOneSubYieldOf_evidence` |
| `D-S15-fpRatio_invariant_under_quench` | `support-lemma` | `model-level-identity`, `stern-volmer-side-is-added-rate`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.fpRatioInvariantUnderQuench_evidence` |
| `D-S17-raci_qy_eq_yieldOf_two_channel` | `support-lemma` | `propositional-term-identity`, `not-definitional`, `no-typed-parent`, `no-seven-kind-constructor` | `PhotoLean.RelationAudit.Full.Sections11_17.raciQyEqYieldOfTwoChannel_evidence` |

## Generated checks

- source: `relation_audit/reports/migration-lean-checks.lean` (`9de0d85d48cc…`), 222 commands, imports `PhotoLean.RelationAudit.Full`

## Non-claims

- This report is not a production full registry and does not claim 136/136 or resolved coverage.
- The queue covers exactly the 41 R2 certificate-required declarations, not all 78 scanned declarations and not the 136-pair universe.
- Reclassified rows are not certified relations; their Lean names are evidence re-exports only and deliberately are not Certificate values.
- No conditionalComposition certificate is created in R3; the generator supports its canonical projections but emits none for these fragments.
- A definitionalIdentity certificate is a fresh DefEq/rfl check, not propositional equality and not a physical-identity claim.
- An observationalEquivalence certificate records agreement on the declared channels and is not a propositional equivalence.
- A generated #print axioms footprint check covers only the named declarations; it is not a whole-repository proof or audit verdict.
- The R1 pilot, R2 inventory, original theory modules, dispositions, schema and manuscript are unchanged by this integration round.
