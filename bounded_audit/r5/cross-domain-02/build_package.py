#!/usr/bin/env python3
"""Deterministic builder for the R5 XD2 screening package.

Usage (repository root, after the evidence scans have been re-run):
    python3 bounded_audit/r5/cross-domain-02/build_package.py

The builder reads the frozen R1 inventory and pair queue, pulls every endpoint field from the
inventory (so no hash or line number is transcribed by hand), and writes the three artifacts in
dependency order:

    search-log.json        (no forward reference)
    screening.json         (pins the search-log SHA-256)
    coverage-fragment.json (pins the screening SHA-256)

The package is an English repository artifact. It writes no Lean file: the package claims no
`certified` and no `refuted` outcome, so it introduces no certificate and no probe. Its nine
pairs are statement-level `outOfScope` registrations, each carried by a scoped search log, a
machine-recomputable signature scan and an import-closure fact.
"""

import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
REL = os.path.relpath(HERE, ROOT)

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
SNAPSHOT = 'snap-bounded-audit-2026-11-04'
WP_ID = 'WP-cross-domain-screening-02'
ROUND = 'R5'

PAIR_ORDER = [
    'P-Goldschmidt-KashaVavilov',
    'P-Goldschmidt-SternVolmer',
    'P-Goldschmidt-QuantumYield',
    'P-Goldschmidt-FluorPhos',
    'P-Goldschmidt-EnergyGapLaw',
    'P-Goldschmidt-StokesShift',
    'P-Goldschmidt-ICvsISC',
    'P-Goldschmidt-Forster',
    'P-Goldschmidt-Einstein',
]

GOLDSCHMIDT_TOKENS = [
    'tolFac', 'latticeOf', 'idealAO', 'idealA', 'rAMin', 'rAMax', 'InBand',
    'GoldschmidtConforms', 'goldschmidtZone', 'GoldschmidtZone', 'gapA', 'classicLo',
    'classicHi', 'tetragonalHi', 'tauGoldschmidt', 'RadiusMatch', 'chiTol',
    'Substitutable', 'ChargeBalanced', 'isovalent',
]

PARTNER_TOKENS = {
    'KashaVavilov': ['SpecSame', 'fluoYield', 'emitYield', 'upperYield', 'rateData',
                     'specFrac', 'kashaRule', 'vavilovAt', 'VavilovAt', 'VavilovUpTo',
                     'lossless', 'KashaRule', 'radBranch', 'icBranch', 'cascade'],
    'SternVolmer': ['dynDecay', 'svRatioDyn', 'tauRatioDyn', 'svRatioStat', 'tauRatioStat',
                    'KSV', 'svRatioBoth', 'svRatioOf', 'tauRatioOf', 'LifetimeTracks',
                    'svZoneQ', 'SVZone', 'Mech'],
    'QuantumYield': ['totalRate', 'yieldOf', 'tauOf', 'QYData', 'sum_yieldOf_eq_one'],
    'FluorPhos': ['s1Decay', 'phiF', 'iscBranch', 't1BranchP', 'phiP', 'FPZone', 'fpZoneQ',
                  'FPData', 'crossover_isc'],
    'EnergyGapLaw': ['nrBarrier', 'nrRate', 'InvertedGap', 'lnRate', 'eglTangent', 'egZoneQ',
                     'EGZone', 'aromaticSeries', 'secant_slope'],
    'StokesShift': ['s0Surface', 's1Surface', 'absEnergy', 'emEnergy', 'stokesShift',
                    'SSZone', 'ssZoneQ', 'mirror_midpoint', 'emission_window'],
    'ICvsISC': ['fcBarrier', 'icRate', 'iscRate', 'rate_ratio_eq', 'log_rate_ratio',
                'isc_dominates_iff', 'spin_discount', 'FCData', 'hso_zero_isc_absent',
                'barrier_diff'],
    'Forster': ['kappaSq', 'fretRate', 'fretEff6', 'fretEff', 'r0six', 'kappaConvention',
                'fret_blind_spot'],
    'Einstein': ['radFactor', 'aOfB', 'b12OfB21', 'fOfA', 'aOfInt', 'tauR',
                 'detailed_balance', 'degeneracy_roundtrip', 'af_roundtrip'],
}

PAIR_INFO = {
    'P-Goldschmidt-KashaVavilov': dict(
        partner='KashaVavilov', tag='KV', ctx='GdKvCandidateCtx',
        map_text='a ladder of per-level rates (rad, ic) at level n',
        rel_line=942),
    'P-Goldschmidt-SternVolmer': dict(
        partner='SternVolmer', tag='SV', ctx='GdSvCandidateCtx',
        map_text='a measured intensity/lifetime slope pair (slopeI, slopeTau)',
        rel_line=945),
    'P-Goldschmidt-QuantumYield': dict(
        partner='QuantumYield', tag='QY', ctx='GdQyCandidateCtx',
        map_text='a channel vector k and a channel index i',
        rel_line=948),
    'P-Goldschmidt-FluorPhos': dict(
        partner='FluorPhos', tag='FP', ctx='GdFpCandidateCtx',
        map_text='the five S1/T1 channel rates (kF, kISC, kIC, kP, kNR)',
        rel_line=952),
    'P-Goldschmidt-EnergyGapLaw': dict(
        partner='EnergyGapLaw', tag='EG', ctx='GdEgCandidateCtx',
        map_text='a reorganization energy and gap coordinate (lam, x)',
        rel_line=991),
    'P-Goldschmidt-StokesShift': dict(
        partner='StokesShift', tag='SS', ctx='GdSsCandidateCtx',
        map_text='a reorganization energy and 0-0 energy (lam, e00)',
        rel_line=998),
    'P-Goldschmidt-ICvsISC': dict(
        partner='ICvsISC', tag='IC', ctx='GdIcCandidateCtx',
        map_text='an IC/ISC barrier pair and a spin-orbit coupling (lamI, xI, HSO)',
        rel_line=1002),
    'P-Goldschmidt-Forster': dict(
        partner='Forster', tag='FR', ctx='GdFrCandidateCtx',
        map_text='a donor-acceptor separation and a Forster radius (R, R0)',
        rel_line=1021),
    'P-Goldschmidt-Einstein': dict(
        partner='Einstein', tag='EI', ctx='GdEiCandidateCtx',
        map_text='an Einstein A coefficient',
        rel_line=969),
}

CONTEXTS = {
    'GdKvCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'n : ℕ'],
        physicalReading=(
            'Candidate shared context: the perovskite A/B/O radii of the tolerance factor plus a '
            'Kasha-Vavilov ladder of per-level radiative rates rad n and internal-conversion rates '
            'ic n. It is the smallest context that would contain both statements. No delivered '
            'statement relates its radius part to its ladder part, so it is a candidate context, '
            'not a shared context: the Goldschmidt authority has no ladder term and the '
            'KashaVavilov authority has no radius term.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdKvCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdSvCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lo : ℝ', 'hi : ℝ',
                'slopeI : ℚ', 'slopeTau : ℚ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii with the band edges (lo, hi) and the '
            'Stern-Volmer measured slope pair (slopeI, slopeTau) of the intensity and lifetime '
            'responses. A verdict equivalence would have to live here. The radius triple fixes a '
            'lattice contact ratio; the slope pair is a concentration-response datum with no '
            'ionic-radius component, and no delivered statement maps one part onto the other.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdSvCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdQyCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lo : ℝ', 'hi : ℝ', 'k : Fin n → ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii with band edges plus a finite vector '
            'of channel rates k. The Goldschmidt side decides a band membership on a length '
            'ratio; the QuantumYield side decides the share of one channel in the total rate. A '
            'shared context would need a delivered statement identifying a radius ratio with a '
            'rate share, and none exists.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdQyCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdFpCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lo : ℝ', 'hi : ℝ',
                'kF : ℚ', 'kISC : ℚ', 'kIC : ℚ', 'kP : ℚ', 'kNR : ℚ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii with band edges plus the five '
            'FluorPhos channel rates. Both endpoints are three-way classifiers, so the candidate '
            'context is the only place a verdict equivalence could live; but the decision '
            'functions read a single real radius ratio on one side and two rational products on '
            'the other, and no delivered statement maps the two input families.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdFpCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdEgCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lam : ℝ', 'x : ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii plus the energy-gap-law '
            'reorganization energy and gap coordinate (lam, x). The Goldschmidt statements read '
            'lengths only; lam and x are energies, and the only delivered occurrence of a Marcus '
            'barrier in the corpus is the Kernel copy that EnergyGapLaw pins. No delivered '
            'statement sends a radius to an energy.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdEgCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdSsCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lam : ℝ', 'e00 : ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii plus the StokesShift surfaces '
            '(lam, e00). The Stokes statements are differences of electronic energies on two '
            'harmonic surfaces; the Goldschmidt statements are ratios of ionic contact lengths. '
            'The context is a union of two vocabularies, not a shared observable.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdSsCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdIcCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'lamI : ℝ', 'xI : ℝ', 'HSO : ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii plus an IC barrier coordinate '
            '(lamI, xI) and a spin-orbit coupling HSO. The ICvsISC statement orders two '
            'Franck-Condon barriers; the Goldschmidt statement orders a radius ratio against a '
            'band. No delivered statement carries a spin-orbit coupling into the lattice '
            'vocabulary or a radius into the rate vocabulary.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdIcCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdFrCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'R0 : ℝ', 'R : ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii plus a Forster radius and a '
            'donor-acceptor separation (R0, R). Both endpoints are geometric threshold criteria, '
            'which is why the legacy register calls the pair a look-alike. The lengths are '
            'nevertheless different objects: R is an intermolecular separation in solution, R0 is '
            'a spectroscopic length built from the overlap integral and the orientation factor, '
            'and rA/rB/rO are ionic contact radii in a crystal. No delivered statement maps one '
            'family onto the other.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdFrCandidateCtx '
                   '(candidate context; no Lean structure)'),
    'GdEiCandidateCtx': dict(
        fields=['rA : ℝ', 'rB : ℝ', 'rO : ℝ', 'A : ℝ'],
        physicalReading=(
            'Candidate shared context: the perovskite radii plus an Einstein A coefficient. The '
            'shared symbol tau is the only link the names offer: on the Goldschmidt side '
            'tauGoldschmidt is the dimensionless 3/20 of the radius rule, on the Einstein side '
            'tauR is the radiative lifetime 1/A. A lifetime is not a radius tolerance, and no '
            'delivered statement maps a radius to a rate.'),
        provenance='bounded_audit/r5/cross-domain-02/screening.json#GdEiCandidateCtx '
                   '(candidate context; no Lean structure)'),
}

SCOPES = {
    'scope-XD2-KV-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x KashaVavilov '
                    'pair: a lattice length ratio against a ladder of per-level rates.',
        domain='the Goldschmidt tolerance-factor/band statements and the KashaVavilov ladder '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-SV-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x SternVolmer '
                    'pair: a radius-ratio classifier against a slope-pair classifier.',
        domain='the Goldschmidt zone-classifier statements and the SternVolmer zone/slope '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-QY-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x QuantumYield '
                    'pair: a band membership on a length ratio against a channel share of a rate '
                    'total.',
        domain='the Goldschmidt band statements and the QuantumYield rate/yield algebra of the '
               'frozen snapshot; no claim outside the named jurisdiction reason.'),
    'scope-XD2-FP-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x FluorPhos '
                    'pair: a radius-ratio classifier against a five-rate competition classifier.',
        domain='the Goldschmidt zone-classifier statements and the FluorPhos competition-zone '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-EG-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x '
                    'EnergyGapLaw pair: a geometric rattling length against a Marcus crossing '
                    'energy.',
        domain='the Goldschmidt gap/band statements and the EnergyGapLaw barrier/rate/zone '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-SS-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x StokesShift '
                    'pair: a dimensionless packing ratio against an emission energy.',
        domain='the Goldschmidt tolerance-factor statements and the StokesShift surface/energy '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-IC-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x ICvsISC '
                    'pair: a band verdict against a barrier-ordering theorem with a spin-orbit '
                    'premise.',
        domain='the Goldschmidt band statements and the ICvsISC barrier/rate statements of the '
               'frozen snapshot; no claim outside the named jurisdiction reason.'),
    'scope-XD2-FR-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x Forster '
                    'pair: two geometric threshold criteria over unrelated lengths '
                    '(legacy look-alike).',
        domain='the Goldschmidt contact/tolerance statements and the Forster geometry/threshold '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
    'scope-XD2-EI-jurisdiction': dict(
        description='Statement-level jurisdiction registration for the Goldschmidt x Einstein '
                    'pair: a dimensionless radius-rule constant against a radiative lifetime.',
        domain='the Goldschmidt radius-rule statements and the Einstein coefficient/lifetime '
               'statements of the frozen snapshot; no claim outside the named jurisdiction '
               'reason.'),
}

QUERIES = [
    dict(
        qid='Q-XD2-KV-01', pair='P-Goldschmidt-KashaVavilov',
        title='Is the tolerance-factor band verdict a property of the Kasha-Vavilov ladder?',
        question=(
            'Does the Goldschmidt band verdict `GoldschmidtConforms lo hi rA rB rO` - a statement '
            'about the A-O contact distance in a cubic ABO3 perovskite - constrain the lossless '
            'Kasha/Vavilov separation `lossless_separates_kasha_vavilov`, whose witness is a '
            'ladder of radiative and internal-conversion rates?'),
        rationale=(
            'Goldschmidt measures a ratio of ionic contact lengths, '
            't = (rA + rO) / (sqrt 2 * (rB + rO)), and the band verdict tests that ratio against '
            'edges (lo, hi). The Kasha-Vavilov statement is a separation theorem about a ladder of '
            'per-level radiative rates rad n and internal-conversion rates ic n; its witness is '
            'rad = 1 with ic 0 = 0, where Kasha holds and Vavilov fails. A relation would need a '
            'shared quantity: an excited-state branching fraction on one side and a lattice length '
            'ratio on the other. Neither statement measures the other\'s quantity. The only '
            'similarity is that both decide a two-way split (in-band/out-of-band versus '
            'Kasha/Vavilov), which is a statement shape, not a shared observable.'),
        src='goldschmidt.conformance',
        tgt='stmt-KashaVavilov-PhotoLean-KashaVavilov-lossless_separates_kasha_vavilov',
        kind='implication',
        kindRationale=(
            'Even the weakest admissible link is a one-way implication from a band verdict to a '
            'ladder property. That already requires a shared scalar; the two endpoints measure '
            'a length ratio and a family of per-level rates, so no implication of the declared '
            'form can be stated without inventing a translation.'),
        falsification=(
            'The counterexample shape is `exists d, Pi d and P d and not Q d`: a perovskite triple '
            '(rA, rB, rO) inside the band whose lossless ladder witness fails the separation. A '
            'delivered statement mapping an ionic radius to a ladder rate would also remove the '
            'jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The Goldschmidt endpoint decides '
            'a band membership on a radius ratio and the KashaVavilov endpoint decides a '
            'separation of two ladder predicates; the two statement authorities share no '
            'identifier, no observable and no import path. This is a statement-level jurisdiction '
            'registration, not a claim that no relation could ever be written; the legacy census '
            'registers the same absence (Relations.lean section 16 line 942).'),
        statementLevel=(
            'Statement-level jurisdiction reason: the Goldschmidt side is `GoldschmidtConforms lo '
            'hi rA rB rO` (a band predicate on the radius ratio computed by `tolFac`), and the '
            'KashaVavilov side is `lossless_separates_kasha_vavilov` (an existential witness over '
            'rate ladders `rad`, `ic` with `ic 0 = 0`, `Kasha.VavilovUpTo` and not '
            '`Kasha.KashaRule`). No Goldschmidt statement contains a rate, a level index or a '
            'branching fraction; no KashaVavilov statement contains an ionic radius or a '
            'tolerance factor. The signature scan over all 139 Goldschmidt and all 29 '
            'KashaVavilov declaration signatures finds zero shared identifiers.'),
        searchId='SL-XD2-KV-01',
        searched=[
            'goldschmidt.conformance',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-lossless_separates_kasha_vavilov',
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-d2_verdict'],
        kinds=['implication', 'equivalence', 'observationalEquivalence'],
        contexts=['GdKvCandidateCtx (rA, rB, rO, rad, ic, n): a union of a lattice context and a '
                  'ladder context, with no delivered statement linking the two parts'],
        candidate=dict(
            kind='band-verdict-to-ladder-loss',
            statement='An in-band perovskite triple would force the lossless ladder corner '
                      '(`rad = 1`, `ic 0 = 0`) or its negation.',
            status='not admitted: the two predicates read disjoint vocabularies, and no delivered '
                   'statement maps (rA, rB, rO) to (rad, ic); asserting the link would be a '
                   'forced relation.'),
        gap=('No shared context, no declared translation, and no shared observable between the '
             'tolerance-factor band statements and the Kasha-Vavilov ladder statements; the '
             'boundary is a jurisdiction boundary, not a logical absence.'),
        searchRationale=(
            'Recorded as outOfScope with a statement-level reason: the endpoints are named, their '
            'vocabularies are disjoint in the signature scan, and the import closures do not '
            'intersect. The legacy pair-level notEstablished anchor is coverage history, not a '
            'named chemical query.'),
        greps=[
            ('grep -nE \'SpecSame|fluoYield|emitYield|upperYield|rateData|specFrac|kashaRule|'
             'vavilovAt|VavilovAt|VavilovUpTo|lossless|KashaRule|radBranch|icBranch|cascade\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered ladder identifier.',
             'Three matches of the plain word `cascade`, all in docstrings '
             '(Goldschmidt/Instances.lean:136, :151; Goldschmidt/RatModel.lean:181). No '
             'declaration signature carries a ladder identifier (signature scan: 0).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; KashaVavilov '
                    'imports `Mathlib`, `PhotoLean.Kasha.Basic`, `PhotoLean.Kasha.Criterion` and '
                    'its own modules. The non-own import sets do not intersect and neither side '
                    'imports the other.'),
    ),
    dict(
        qid='Q-XD2-SV-01', pair='P-Goldschmidt-SternVolmer',
        title='Do the Goldschmidt zone classifier and the Stern-Volmer zone classifier decide '
              'the same classification?',
        question=(
            'Does the three-way Goldschmidt classifier `goldschmidtZone lo hi t`, which compares '
            'one real tolerance factor against a band, coincide with the four-way Stern-Volmer '
            'classifier `svZoneQ slopeI slopeTau`, which reads a pair of rational slopes?'),
        rationale=(
            'Both endpoints are data classifiers of a measured scalar against a band, so a verdict '
            'equivalence is the natural query. Goldschmidt classifies the radius ratio t into '
            'tooSmall/ideal/tooLarge by testing t < lo and then t <= hi. Stern-Volmer classifies a '
            'measured slope pair into dynLike/statLike/mixedLike/inconsistent by comparing slopeI '
            'and slopeTau; it has four verdicts, not three, and its input is a pair of rational '
            'concentration-response slopes, not one real length ratio. A verdict equivalence would '
            'need a total translation from (slopeI, slopeTau) to (lo, hi, t) that preserves the '
            'decision boundaries. No delivered statement provides one, and the translation would '
            'have to identify a photophysical response slope with a lattice length ratio.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
        tgt='stmt-SternVolmer-PhotoLean-SternVolmer-svZoneQ',
        kind='equivalence',
        kindRationale=(
            'The question is a verdict equivalence: the two classifiers agree on every input under '
            'the declared translation. It is the strongest form the shared classifier shape could '
            'support, and it fails at the input and arity level before any proof is attempted.'),
        falsification=(
            'The refutation shape is one input with `P d` and `not Q d` (or the converse): a slope '
            'pair whose Stern-Volmer verdict differs from the Goldschmidt verdict of its '
            'translated triple. A delivered statement that maps a slope pair to a radius triple '
            'would also remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The shared classifier shape is '
            'not a shared context: the inputs are a radius ratio and a slope pair, the verdict '
            'types are `GoldschmidtZone` (three constructors) and `SVZone` (four constructors), '
            'and no delivered translation exists between them. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `goldschmidtZone lo hi t : GoldschmidtZone` '
            'tests a real t against (lo, hi); `svZoneQ slopeI slopeTau : SVZone` tests rational '
            'slopes against each other and returns a four-constructor verdict. The arities, the '
            'input types (`Real` versus `Rat`) and the verdict types already differ, and no '
            'delivered statement in either authority mentions the other\'s input. The signature '
            'scan over all 139 Goldschmidt and all 46 SternVolmer declaration signatures finds '
            'zero shared identifiers.'),
        searchId='SL-XD2-SV-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-GoldschmidtZone',
            'stmt-SternVolmer-PhotoLean-SternVolmer-svZoneQ',
            'stmt-SternVolmer-PhotoLean-SternVolmer-svZoneQ_dynLike',
            'sternvolmer.intensityDyn'],
        kinds=['equivalence', 'definitionalIdentity', 'distinguishability'],
        contexts=['GdSvCandidateCtx (rA, rB, rO, lo, hi, slopeI, slopeTau): the union context a '
                  'verdict equivalence would need'],
        candidate=dict(
            kind='classifier-verdict-equivalence',
            statement='The two classifiers return corresponding verdicts on every input.',
            status='not admitted: the two verdict types have different cardinalities (3 versus 4) '
                   'and the inputs are a real triple versus a rational pair; a correspondence '
                   'would have to be invented, which is a forced relation.'),
        gap=('No shared context, no declared translation and no shared input family between the '
             'Goldschmidt radius-ratio classifier and the Stern-Volmer slope-pair classifier; '
             'jurisdiction boundary, not logical absence.'),
        searchRationale=(
            'Recorded as outOfScope with a statement-level reason naming both classifier '
            'declarations, their input types and their verdict arities. The legacy pair anchor is '
            'coverage history only.'),
        greps=[
            ('grep -nE \'dynDecay|svRatioDyn|tauRatioDyn|svRatioStat|tauRatioStat|KSV|svRatioBoth|'
             'svRatioOf|tauRatioOf|LifetimeTracks|svZoneQ|SVZone|Mech\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered Stern-Volmer identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; SternVolmer '
                    'imports `Mathlib` plus its own four modules. The non-own import sets are '
                    'empty on both sides and neither side imports the other.'),
    ),
    dict(
        qid='Q-XD2-QY-01', pair='P-Goldschmidt-QuantumYield',
        title='Is the in-band predicate on the tolerance factor a quantum-yield statement?',
        question=(
            'Is the band membership `InBand lo hi t` on the tolerance factor the same kind of '
            'statement as the channel yield `yieldOf k i`, the share of channel i in the total '
            'rate?'),
        rationale=(
            'Both endpoints are ratios with a "part of a whole" reading: `InBand` tests a length '
            'ratio against two edges, and `yieldOf k i = k i / totalRate k` is the share of one '
            'decay channel in the total decay. The similarity is arithmetic, not physical. A '
            'quantum yield is an excited-state branching probability that sums to one over the '
            'channels; a band membership is a geometric packing verdict with no normalisation. '
            'Goldschmidt has no rate parameter and QuantumYield has no radius or length; the '
            'candidate bridge would have to read a radius ratio as a rate share.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-InBand',
        tgt='stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
        kind='implication',
        kindRationale=(
            'The weakest admissible link is a one-way implication from band membership to a '
            'channel share. A part-of-whole shape does not supply the shared scalar such an '
            'implication needs.'),
        falsification=(
            'The counterexample shape is `exists d, Pi d and P d and not Q d`: a band triple whose '
            'yield-side predicate fails. A delivered statement that reads a radius as a rate '
            'share would also remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The unnormalised band membership '
            'on a length ratio and the normalised channel share of a rate total are different '
            'observables; the part-over-whole resemblance is a statement shape, not a shared '
            'context, and no translation is delivered.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `InBand lo hi t := lo <= t and t <= hi` is a '
            'predicate on one real ratio with no rate; `yieldOf k i = k i / totalRate k` divides a '
            'channel rate by a sum of rates. No Goldschmidt statement in the 139-row authority '
            'contains a rate or a channel; no QuantumYield statement in the 29-row authority '
            'contains a radius, a band or a tolerance factor. The signature scan finds zero shared '
            'identifiers.'),
        searchId='SL-XD2-QY-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-InBand',
            'goldschmidt.conformance',
            'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
            'stmt-QuantumYield-PhotoLean-QuantumYield-totalRate'],
        kinds=['implication', 'definitionalIdentity', 'equivalence'],
        contexts=['GdQyCandidateCtx (rA, rB, rO, lo, hi, k): the union context a part-over-whole '
                  'identification would need'],
        candidate=dict(
            kind='part-over-whole shape',
            statement='A band membership and a channel share are the same normalised quantity.',
            status='not admitted: `InBand` is unnormalised and reads a length ratio; `yieldOf` is '
                   'normalised over a rate vector. Sharing the "part of a whole" shape is not a '
                   'shared context.'),
        gap=('No shared context, no declared translation and no shared observable between the '
             'Goldschmidt band statements and the QuantumYield rate algebra; jurisdiction '
             'boundary, not logical absence.'),
        searchRationale=(
            'Recorded as outOfScope: the endpoints are named, the ratio shapes are explicitly '
            'rejected as a rationale, and the machine scans show disjoint vocabularies and '
            'imports.'),
        greps=[
            ('grep -nE \'totalRate|yieldOf|tauOf|QYData|sum_yieldOf_eq_one\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered yield identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; QuantumYield '
                    'imports `Mathlib` plus its own four modules. Neither side imports the other '
                    'and the non-own import sets are empty.'),
    ),
    dict(
        qid='Q-XD2-FP-01', pair='P-Goldschmidt-FluorPhos',
        title='Does the Goldschmidt zone verdict coincide with the FluorPhos competition verdict?',
        question=(
            'Does the Goldschmidt band classifier `goldschmidtZone lo hi t` coincide with the '
            'FluorPhos competition classifier `fpZoneQ kF kISC kIC kP kNR`, which decides between '
            'fluorescence-dominant, balanced and phosphorescence-dominant decay?'),
        rationale=(
            'Both endpoints are three-way classifiers, so a verdict correspondence is the natural '
            'query. The decision functions differ: Goldschmidt tests one real t against (lo, hi), '
            'while FluorPhos compares kISC * kP with kF * (kP + kNR) over the rationals. The '
            'FluorPhos classifier takes five channel rates as arguments, and its own docstring and '
            'the build linter record that kIC is not consumed by the decision body, so even the '
            'partner classifier does not decide an internal-conversion rate. A verdict '
            'correspondence would need a translation from the five rates to (lo, hi, t); none is '
            'delivered, and it would have to read a competition between radiative and '
            'intersystem-crossing channels as a lattice contact ratio.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
        tgt='stmt-FluorPhos-PhotoLean-FluorPhos-fpZoneQ',
        kind='equivalence',
        kindRationale=(
            'The query asks for a verdict equivalence of the two three-way classifiers. The '
            'three-verdict shape is the strongest thing the pair offers; the input families and '
            'the decision functions are unrelated.'),
        falsification=(
            'The refutation shape is one input whose two verdicts differ under the declared '
            'translation. A delivered statement mapping the five channel rates to a radius triple '
            'would also remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. A shared three-verdict shape is '
            'not a shared context: the inputs are five rational rate parameters versus one real '
            'radius ratio, and no translation is delivered in either direction.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `goldschmidtZone lo hi t` compares a real t with '
            'two band edges, while `fpZoneQ kF kISC kIC kP kNR` compares the rational products '
            '`kISC * kP` and `kF * (kP + kNR)`. The FluorPhos signature carries five rates and the '
            'Goldschmidt signature carries radii; the two authorities share no identifier in the '
            'signature scan (139 Goldschmidt rows versus 30 FluorPhos rows, zero intersections).'),
        searchId='SL-XD2-FP-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
            'goldschmidt.conformance',
            'stmt-FluorPhos-PhotoLean-FluorPhos-fpZoneQ',
            'stmt-FluorPhos-PhotoLean-FluorPhos-fpZoneQ_phosphorDominant_iff',
            'stmt-FluorPhos-PhotoLean-FluorPhos-phiP'],
        kinds=['equivalence', 'implication', 'observationalEquivalence'],
        contexts=['GdFpCandidateCtx (rA, rB, rO, lo, hi, kF, kISC, kIC, kP, kNR): the union '
                  'context a verdict correspondence would need'],
        candidate=dict(
            kind='three-verdict classifier shape',
            statement='The two three-way classifiers order corresponding verdicts.',
            status='not admitted: the decision functions read disjoint parameter families '
                   '(radius ratio versus rate products), and the FluorPhos decision body does not '
                   'even consume kIC (build linter, FluorPhos/RatModel.lean:89).'),
        gap=('No shared context, no declared translation and no shared parameter family between '
             'the Goldschmidt band classifier and the FluorPhos competition classifier; '
             'jurisdiction boundary, not logical absence.'),
        searchRationale=(
            'Recorded as outOfScope with a statement-level reason that names both classifiers and '
            'their decision functions, and with the machine scans recorded.'),
        greps=[
            ('grep -nE \'s1Decay|phiF|iscBranch|t1BranchP|phiP|FPZone|fpZoneQ|FPData|crossover_isc\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered FluorPhos identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; FluorPhos '
                    'imports `Mathlib` plus its own four modules. Neither side imports the other '
                    'and the non-own import sets are empty.'),
    ),
    dict(
        qid='Q-XD2-EG-01', pair='P-Goldschmidt-EnergyGapLaw',
        title='Is the A-O rattling gap the nonradiative barrier?',
        question=(
            'Is the Goldschmidt A-O rattling gap `gapA rA rB rO`, a signed length, the same object '
            'as the energy-gap-law nonradiative barrier `nrBarrier lam x`, an energy?'),
        rationale=(
            'The names invite the identification: one is a "gap" and the other a "barrier". The '
            'objects do not match. `gapA rA rB rO = idealAO rB rO - (rA + rO)` is a length in '
            'angstrom, linear in the radii and antisymmetric under exchanging the actual and ideal '
            'A-O contact. `nrBarrier lam x = (lam - x)^2 / (4 lam)` is an energy, quadratic in '
            '(lam - x) and singular at lam = 0. Their dimensions, their dependence on their '
            'arguments and their physical readings all differ; the only overlap is the English '
            'word "gap". No delivered statement maps a radius triple to (lam, x).'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-gapA',
        tgt='stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
        kind='definitionalIdentity',
        kindRationale=(
            'The query tests the strongest possible identification, a kernel `rfl` after a '
            'translation, because a naming resemblance is the only evidence for identity. The '
            'strongest test is the honest one here: if the two were the same object, `rfl` would '
            'settle it.'),
        falsification=(
            'The definitional identity fails if no translation makes the two terms definitionally '
            'equal; the falsification condition is a delivered translation whose kernel `rfl` '
            'check fails, or, semantically, any radius triple with `gapA` positive while the '
            'translated `nrBarrier` is negative or undefined.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. `gapA` is a length and '
            '`nrBarrier` is an energy; a definitional identity between them would need a translation '
            'that is not merely undelivered but dimensionally ill-typed. Registering the naming '
            'collision is the honest move: it is a name, not an object.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `gapA (rA rB rO : Real) : Real` returns a signed '
            'contact-length excess; `nrBarrier (lam x : Real) : Real` returns the Marcus crossing '
            'energy `(lam - x)^2 / (4 * lam)`. The Goldschmidt authority has no energy statement '
            'and the EnergyGapLaw authority has no length statement; the signature scan over 139 '
            'Goldschmidt and 26 EnergyGapLaw signatures finds zero shared identifiers.'),
        searchId='SL-XD2-EG-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-gapA',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealAO',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-cert_nrBarrier',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate'],
        kinds=['definitionalIdentity', 'implication', 'equivalence'],
        contexts=['GdEgCandidateCtx (rA, rB, rO, lam, x): radii plus the energy-gap coordinate'],
        candidate=dict(
            kind='naming collision (gap / barrier)',
            statement='`gapA` and `nrBarrier` denote the same quantity.',
            status='not admitted: a length is not an energy. The identification would need a '
                   'translation from angstrom to joules and a map from radii to (lam, x); neither '
                   'is delivered or physically meaningful.'),
        gap=('No shared context and no declared translation between the geometric rattling length '
             'and the Marcus crossing energy; the boundary is dimensional, not merely '
             'undelivered.'),
        searchRationale=(
            'Recorded as outOfScope on statement-level dimensional grounds: the two declarations '
            'are named explicitly and their bodies are compared in the reason. The legacy absence '
            'registration agrees but is not the argument.'),
        greps=[
            ('grep -nE \'nrBarrier|nrRate|InvertedGap|lnRate|eglTangent|egZoneQ|EGZone|aromaticSeries|'
             'secant_slope\' PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered energy-gap-law identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; EnergyGapLaw '
                    'imports `Mathlib`, `PhotoLean.Kernel`, `PhotoLean.Marcus.Basic` and its own '
                    'modules. The non-own import sets do not intersect and neither side imports '
                    'the other.'),
    ),
    dict(
        qid='Q-XD2-EG-02', pair='P-Goldschmidt-EnergyGapLaw',
        title='Do the Goldschmidt band verdict and the energy-gap zone verdict agree?',
        question=(
            'Does the Goldschmidt band verdict `goldschmidtZone lo hi t` agree with the '
            'energy-gap-law verdict `egZoneQ lam x`, which classifies a reorganization energy and '
            'a gap coordinate against the Marcus normal/inverted boundary?'),
        rationale=(
            'Both endpoints are three-way classifiers, so the verdict correspondence is the '
            'natural query and it is the reason the pair is in the cross-domain batch at all. The '
            'decision functions differ: Goldschmidt tests a real t against two parameter edges; '
            'EnergyGapLaw compares a rational gap coordinate x with the reorganization energy lam. '
            'The inputs are a radius ratio versus an energy pair. A verdict correspondence would '
            'need a total translation (lam, x) -> (lo, hi, t) preserving the decision boundaries; '
            'none is delivered, and it would identify an energy gap with a lattice contact ratio.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
        tgt='stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-egZoneQ',
        kind='equivalence',
        kindRationale=(
            'The query asks for a verdict equivalence of two three-way classifiers. The classifier '
            'shape is the only formal contact, and the equivalence is the strongest claim that '
            'shape could support.'),
        falsification=(
            'The refutation shape is one input whose two verdicts differ under the declared '
            'translation. A delivered statement mapping (lam, x) to a radius triple would also '
            'remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The two classifiers decide over '
            'different input families (an energy pair versus a radius ratio) and no translation is '
            'delivered; the shared verdict arity is a shape, not a shared scalar.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `goldschmidtZone lo hi t` reads one real t '
            'against band edges; `egZoneQ lam x` reads two rational energies against the '
            'normal/inverted boundary. No Goldschmidt statement in the 139-row authority carries '
            'an energy or a reorganization energy, and no EnergyGapLaw statement in the 26-row '
            'authority carries a radius or a tolerance factor; the signature scan finds zero '
            'shared identifiers.'),
        searchId='SL-XD2-EG-02',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-goldschmidtZone',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-GoldschmidtZone',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-egZoneQ',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-egZoneQ_eq_inverted_iff',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-InvertedGap'],
        kinds=['equivalence', 'implication', 'observationalEquivalence'],
        contexts=['GdEgCandidateCtx (rA, rB, rO, lam, x): radii plus the energy-gap coordinate'],
        candidate=dict(
            kind='three-way classifier shape',
            statement='The two three-way classifiers order corresponding verdicts.',
            status='not admitted: the decision functions read a radius ratio versus an energy '
                   'pair, and no delivered map identifies them.'),
        gap=('No shared context, no declared translation and no shared input family between the '
             'Goldschmidt band classifier and the energy-gap zone classifier; jurisdiction '
             'boundary, not logical absence.'),
        searchRationale=(
            'Recorded as outOfScope. The classifier shape is named and explicitly rejected as a '
            'rationale, and the machine scans are recorded.'),
        greps=[
            ('grep -nE \'nrBarrier|nrRate|InvertedGap|lnRate|eglTangent|egZoneQ|EGZone|aromaticSeries|'
             'secant_slope\' PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered energy-gap-law identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; EnergyGapLaw '
                    'imports `Mathlib`, `PhotoLean.Kernel`, `PhotoLean.Marcus.Basic` and its own '
                    'modules. The non-own import sets do not intersect and neither side imports '
                    'the other.'),
    ),
    dict(
        qid='Q-XD2-SS-01', pair='P-Goldschmidt-StokesShift',
        title='Is the tolerance factor a Stokes-shifted emission energy?',
        question=(
            'Does the dimensionless tolerance factor `tolFac rA rB rO` carry the same physical '
            'content as the vertical emission energy `emEnergy lam e00` of the Stokes-shift '
            'surfaces?'),
        rationale=(
            '`tolFac rA rB rO = (rA + rO) / (sqrt 2 * (rB + rO))` is a dimensionless ratio of '
            'two ionic contact lengths; `emEnergy lam e00 = s1Surface lam e00 1 - s0Surface lam 1` '
            'is an energy, the vertical emission gap of two harmonic surfaces. A Stokes shift is a '
            'difference of electronic energies whose size is set by the reorganization energy; '
            'the tolerance factor is a packing ratio whose size is set by the ionic radii. Both '
            'are scalars in the real numbers, but no delivered statement maps (rA, rB, rO) to '
            '(lam, e00), and the physical readings (crystal contact geometry versus excited-state '
            'relaxation) are disjoint.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
        tgt='stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
        kind='implication',
        kindRationale=(
            'The weakest admissible link is a one-way implication from a geometric ratio to a '
            'spectral energy. A shared scalar type (the reals) does not supply a shared '
            'observable, so no implication of the declared form can be stated.'),
        falsification=(
            'The counterexample shape is `exists d, Pi d and P d and not Q d`: a radius triple '
            'whose translated emission energy fails the claimed spectral property. A delivered '
            'statement mapping radii to (lam, e00) would also remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. A dimensionless packing ratio '
            'and a vertical emission energy are different observables; no translation is '
            'delivered and the legacy register records the absence as a band-position versus '
            'geometry boundary.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `tolFac` is dimensionless and reads radii; '
            '`emEnergy` is an energy and reads the reorganization energy and the 0-0 energy. The '
            'Goldschmidt authority has no spectral statement and the StokesShift authority has no '
            'radius or lattice statement; the signature scan over 139 Goldschmidt and 36 '
            'StokesShift signatures finds zero shared identifiers.'),
        searchId='SL-XD2-SS-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'goldschmidt.conformance',
            'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
            'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
            'stmt-StokesShift-PhotoLean-StokesShift-absEnergy'],
        kinds=['implication', 'definitionalIdentity', 'equivalence'],
        contexts=['GdSsCandidateCtx (rA, rB, rO, lam, e00): radii plus the two-surface '
                  'parameters'],
        candidate=dict(
            kind='dimensionless-scalar shape',
            statement='The tolerance factor measures the same spectral relaxation as the emission '
                      'energy.',
            status='not admitted: one is dimensionless and geometric, the other is an energy; a '
                   'reading of the packing ratio as a spectral shift has no delivered support.'),
        gap=('No shared context, no declared translation and no shared observable between the '
             'tolerance factor and the emission energy; jurisdiction boundary, not logical '
             'absence.'),
        searchRationale=(
            'Recorded as outOfScope with the two declarations named and their dimensions compared. '
            'The legacy absence registration agrees but is not the argument.'),
        greps=[
            ('grep -nE \'s0Surface|s1Surface|absEnergy|emEnergy|stokesShift|SSZone|ssZoneQ|'
             'mirror_midpoint|emission_window\' PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered Stokes-shift identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; StokesShift '
                    'imports `Mathlib`, `PhotoLean.Kernel`, `PhotoLean.Marcus.Basic` and its own '
                    'modules. The non-own import sets do not intersect and neither side imports '
                    'the other.'),
    ),
    dict(
        qid='Q-XD2-IC-01', pair='P-Goldschmidt-ICvsISC',
        title='Does the tolerance-factor band verdict constrain the spin-discount IC/ISC '
              'competition?',
        question=(
            'Does the Goldschmidt band verdict `GoldschmidtConforms lo hi rA rB rO` constrain the '
            'ICvsISC spin-discount theorem `spin_discount`, which orders two Franck-Condon '
            'barriers under a spin-orbit premise and an ISC rate win?'),
        rationale=(
            '`spin_discount` concludes `fcBarrier lamS xS < fcBarrier lamI xI` from an ISC rate '
            'win, equal prefactors and a sub-unit spin-orbit coupling; every object it mentions is '
            'an energy or a coupling. `GoldschmidtConforms` asserts that a radius ratio lies in a '
            'band; every object it mentions is a length. A relation would need a shared energy or '
            'rate quantity, and Goldschmidt has none at all. The spin-orbit coupling is the '
            'clearest separator: no Goldschmidt statement carries an electronic coupling, and no '
            'ICvsISC statement carries an ionic radius.'),
        src='goldschmidt.conformance',
        tgt='stmt-ICvsISC-PhotoLean-ICvsISC-spin_discount',
        kind='implication',
        kindRationale=(
            'The weakest admissible link is a one-way implication from the band verdict to the '
            'barrier ordering. That requires a shared energy scale, which the Goldschmidt authority '
            'does not have.'),
        falsification=(
            'The counterexample shape is `exists d, Pi d and P d and not Q d`: a band triple whose '
            'translated barrier ordering fails. A delivered statement carrying a radius into the '
            'barrier vocabulary or a barrier into the Goldschmidt vocabulary would also remove the '
            'jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The ICvsISC theorem orders two '
            'energies under a spin-orbit premise; the Goldschmidt predicate orders a radius ratio '
            'against a band. The two authorities share no observable and no import path.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `GoldschmidtConforms lo hi rA rB rO` is a band '
            'predicate on radii; `spin_discount` carries the premises `FCData`, `0 < HSO`, '
            '`HSO < 1`, `AI = AS` and a strict `icRate`/`iscRate` inequality, and concludes a '
            'strict `fcBarrier` ordering. No Goldschmidt statement contains a rate, a barrier or a '
            'coupling; no ICvsISC statement contains a radius or a tolerance factor. The signature '
            'scan over 139 Goldschmidt and 20 ICvsISC signatures finds zero shared identifiers.'),
        searchId='SL-XD2-IC-01',
        searched=[
            'goldschmidt.conformance',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'stmt-ICvsISC-PhotoLean-ICvsISC-spin_discount',
            'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
            'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate'],
        kinds=['implication', 'equivalence', 'conditionalComposition'],
        contexts=['GdIcCandidateCtx (rA, rB, rO, lamI, xI, HSO): radii plus the two barrier '
                  'coordinates and a spin-orbit coupling'],
        candidate=dict(
            kind='band-verdict-to-barrier-ordering',
            statement='An in-band perovskite triple would force a specific IC/ISC barrier order.',
            status='not admitted: the conclusion needs barrier and coupling energies and the '
                   'premise supplies radii; no delivered statement relates the two vocabularies.'),
        gap=('No shared context, no declared translation and no shared energy scale between the '
             'band verdict and the spin-discount barrier ordering; jurisdiction boundary, not '
             'logical absence.'),
        searchRationale=(
            'Recorded as outOfScope with both declarations and the full premise list named, so the '
            'reason is statement-level rather than a theory-name contrast.'),
        greps=[
            ('grep -nE \'fcBarrier|icRate|iscRate|rate_ratio_eq|log_rate_ratio|isc_dominates_iff|'
             'spin_discount|FCData|hso_zero_isc_absent|barrier_diff\' PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered IC/ISC identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; ICvsISC '
                    'imports `Mathlib`, `PhotoLean.Kernel`, `PhotoLean.Marcus.Basic` and its own '
                    'modules. The non-own import sets do not intersect and neither side imports '
                    'the other.'),
    ),
    dict(
        qid='Q-XD2-FR-01', pair='P-Goldschmidt-Forster',
        title='Do the Goldschmidt contact threshold and the Forster half-efficiency threshold '
              'identify?',
        question=(
            'Do the two geometric thresholds - Goldschmidt\'s `t = 1` if and only if the A-O '
            'contact holds, and Forster\'s efficiency `1/2` at `R = R0` - identify under one '
            'shared length translation?'),
        rationale=(
            '`contact_iff_tolFac_one` states that the A-O contact equation `rA + rO = idealAO rB '
            'rO` is equivalent to `tolFac rA rB rO = 1`; `fretEff_self` states that the transfer '
            'efficiency at separation `R = R0` is `1/2`. The legacy register calls this pair a '
            'look-alike for exactly this reason: two purely geometric threshold criteria. The '
            'thresholds are 1 and 1/2, over a radius ratio and a distance ratio respectively, and '
            'the lengths are different objects - an ionic contact distance inside a crystal versus '
            'an intermolecular donor-acceptor separation in solution. An equivalence of the two '
            'threshold criteria would need a total translation (rA, rB, rO) -> (R0, R) that no '
            'delivered statement provides.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-contact_iff_tolFac_one',
        tgt='stmt-Forster-PhotoLean-Forster-fretEff_self',
        kind='equivalence',
        kindRationale=(
            'The query asks for an equivalence of the two threshold criteria under one translation, '
            'which is the strongest statement the look-alike shape could support.'),
        falsification=(
            'The refutation shape is one input where one threshold holds and the other fails under '
            'the declared translation. A delivered statement identifying the A-O contact distance '
            'with the donor-acceptor separation would also remove the jurisdiction reason.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. Two threshold criteria over '
            'unrelated lengths share a statement shape, not a length: `t = 1` certifies an ionic '
            'contact inside a perovskite, and `R = R0` certifies half transfer between two '
            'chromophores. No translation is delivered in either direction.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `contact_iff_tolFac_one` is about the A-O '
            'contact equation over ionic radii with the explicit premise `0 < rB + rO`; '
            '`fretEff_self` is about `fretEff R0 R0 = 1/2` over a Forster radius and a separation. '
            'The two authorities share no identifier in the signature scan (139 Goldschmidt rows '
            'versus 32 Forster rows, zero intersections), and the twelve occurrences of the plain '
            'word `transfer` in Goldschmidt docstrings never appear in a declaration signature.'),
        searchId='SL-XD2-FR-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-contact_iff_tolFac_one',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealAO',
            'stmt-Forster-PhotoLean-Forster-fretEff_self',
            'stmt-Forster-PhotoLean-Forster-fretEff',
            'stmt-Forster-PhotoLean-Forster-r0six'],
        kinds=['equivalence', 'definitionalIdentity', 'observationalEquivalence'],
        contexts=['GdFrCandidateCtx (rA, rB, rO, R0, R): ionic radii plus a Forster radius and a '
                  'donor-acceptor separation'],
        candidate=dict(
            kind='geometric threshold look-alike',
            statement='The contact threshold and the half-efficiency threshold are the same '
                      'criterion after translation.',
            status='not admitted: the thresholds and the underlying lengths differ, and the legacy '
                   'register itself classifies the coincidence as a look-alike with no machine '
                   'row. A shape-only identification would be a forced relation.'),
        gap=('No shared context and no declared translation between the ionic contact length and '
             'the donor-acceptor separation; the shared threshold shape is not a shared quantity.'),
        searchRationale=(
            'Recorded as outOfScope. The look-alike is stated explicitly, its two thresholds are '
            'compared, and the reason for rejecting the shape as a rationale is given at the '
            'statement level.'),
        greps=[
            ('grep -nE \'kappaSq|fretRate|fretEff6|fretEff|r0six|kappaConvention|fret_blind_spot\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered Forster identifier.',
             'No matches (grep exit 1). The plain word `transfer` occurs 12 times in Goldschmidt '
             'docstrings (grep -rnw transfer | wc -l = 12) and never in a declaration signature.'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; Forster '
                    'imports `Mathlib` plus its own four modules. Neither side imports the other '
                    'and the non-own import sets are empty.'),
    ),
    dict(
        qid='Q-XD2-FR-02', pair='P-Goldschmidt-Forster',
        title='Is the Goldschmidt lattice parameter the Forster radius?',
        question=(
            'Is the Goldschmidt cubic lattice parameter `latticeOf rB rO`, a length fixed by the '
            'B-O contact, the same quantity as the Forster radius sixth power `r0six C kappasq J n`, '
            'a spectroscopic length scale?'),
        rationale=(
            '`latticeOf rB rO = 2 * (rB + rO)` is a lattice length in angstrom fixed by the B-O '
            'contact; `r0six C kappasq Phi J n = C * kappasq * Phi * J / n^4` is the sixth power of '
            'the Forster radius in angstrom^6, built from the orientation factor, the donor '
            'quantum yield, the spectral overlap integral and the refractive index. The dimensions '
            'differ (length versus length to the sixth), the dependence differs (a linear ionic '
            'radius sum versus a product of spectroscopic factors), and no delivered statement '
            'maps an ionic radius to the overlap integral or the orientation factor. A '
            'definitional identity is therefore not merely unproved; it is not well-typed without '
            'inventing a map.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-latticeOf',
        tgt='stmt-Forster-PhotoLean-Forster-r0six',
        kind='definitionalIdentity',
        kindRationale=(
            'The query tests whether the two length scales are the same object, which is the '
            'strongest available identification (a kernel `rfl` after translation). The dimensional '
            'mismatch (angstrom versus angstrom^6) is decisive.'),
        falsification=(
            'The identity fails unless a delivered translation makes the two terms definitionally '
            'equal; the falsification condition is a translation whose kernel `rfl` check fails, or '
            'any radius pair whose translated Forster sixth power is not the sixth power of the '
            'lattice parameter.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. The lattice parameter is a '
            'geometric contact length and the Forster radius is a spectroscopic length assembled '
            'from the overlap integral; they are not the same object and no translation is '
            'delivered.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `latticeOf (rB rO : Real) : Real` is a linear '
            'ionic radius sum; `r0six (C kappasq Phi J n : Real) : Real` is a sixth power built '
            'from `kappasq`, `Phi`, `J` and `n`. The signatures share no argument and no '
            'identifier; the Goldschmidt authority has no overlap integral or orientation factor, '
            'and the Forster authority has no ionic radius.'),
        searchId='SL-XD2-FR-02',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-latticeOf',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealAO',
            'stmt-Forster-PhotoLean-Forster-r0six',
            'stmt-Forster-PhotoLean-Forster-kappaSq',
            'stmt-Forster-PhotoLean-Forster-fretRate'],
        kinds=['definitionalIdentity', 'implication', 'equivalence'],
        contexts=['GdFrCandidateCtx (rA, rB, rO, R0, R): ionic radii plus a Forster radius and a '
                  'donor-acceptor separation'],
        candidate=dict(
            kind='characteristic length scale',
            statement='The lattice parameter and the Forster radius are one length scale.',
            status='not admitted: a length and a length to the sixth power cannot be identified by '
                   'a translation, and the Forster scale is built from spectroscopic factors that '
                   'the lattice statement does not contain.'),
        gap=('No shared context and no declared translation between the geometric lattice length '
             'and the spectroscopic Forster length scale; the boundary is dimensional and '
             'structural.'),
        searchRationale=(
            'Recorded as outOfScope with the two declarations and their argument lists named. This '
            'is the second, independent query on the pair: the threshold look-alike and the length '
            'identification are chemically distinct questions.'),
        greps=[
            ('grep -nE \'kappaSq|fretRate|fretEff6|fretEff|r0six|kappaConvention|fret_blind_spot\' '
             'PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered Forster identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; Forster '
                    'imports `Mathlib` plus its own four modules. Neither side imports the other '
                    'and the non-own import sets are empty.'),
    ),
    dict(
        qid='Q-XD2-EI-01', pair='P-Goldschmidt-Einstein',
        title='Is Goldschmidt tau the Einstein radiative lifetime?',
        question=(
            'Is the Goldschmidt constant `tauGoldschmidt`, the printed 15 percent of the '
            'radius-substitution rule, the Einstein radiative lifetime `tauR A`?'),
        rationale=(
            'The shared symbol tau is the only link the names offer. `tauGoldschmidt : Real := '
            '3 / 20` is a dimensionless fraction: the printed 15 percent tolerance of '
            'Goldschmidt\'s radius rule, consumed by the radius-match rows. `tauR A = 1 / A` is a '
            'radiative lifetime whose inverse is the Einstein A coefficient. One is a tolerance on '
            'an ionic radius, the other a time. A definitional identity would require `3 / 20 = '
            '1 / A`, an arithmetic coincidence at `A = 20 / 3` that no delivered statement asserts '
            'and that would not be a statement-level relation even if it held. The naming '
            'similarity is exactly the kind of evidence the boundary contract forbids.'),
        src='stmt-Goldschmidt-PhotoLean-Goldschmidt-tauGoldschmidt',
        tgt='stmt-Einstein-PhotoLean-Einstein-tauR',
        kind='definitionalIdentity',
        kindRationale=(
            'The query tests the strongest possible identification of the two tau-named constants, '
            'a kernel `rfl` after a translation. A dimensionless tolerance cannot be '
            'definitionally equal to a lifetime.'),
        falsification=(
            'The identity fails unless a delivered translation makes the two terms definitionally '
            'equal; the falsification condition is a translation whose kernel `rfl` check fails, '
            'or any A where the translated tau values differ.'),
        outcomeRationale=(
            'The pair is outside the declared audit jurisdiction. A dimensionless radius-rule '
            'constant and a radiative lifetime are different objects with different dimensions; '
            'the shared symbol is notation, not a shared quantity, and no translation is '
            'delivered.'),
        statementLevel=(
            'Statement-level jurisdiction reason: `tauGoldschmidt : Real` is the constant `3 / 20` '
            'of the radius rule; `tauR (A : Real) : Real` is `1 / A`, the radiative lifetime. The '
            'Goldschmidt authority has no rate or lifetime statement and the Einstein authority '
            'has no radius or tolerance statement; the signature scan over 139 Goldschmidt and 33 '
            'Einstein signatures finds zero shared identifiers.'),
        searchId='SL-XD2-EI-01',
        searched=[
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tauGoldschmidt',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-RadiusMatch',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-aOfB'],
        kinds=['definitionalIdentity', 'implication', 'equivalence'],
        contexts=['GdEiCandidateCtx (rA, rB, rO, A): radii plus an Einstein A coefficient'],
        candidate=dict(
            kind='shared-symbol (tau) collision',
            statement='`tauGoldschmidt` and `tauR` denote the same constant.',
            status='not admitted: a dimensionless tolerance fraction and a lifetime `1 / A` differ '
                   'in dimension; the shared symbol is notation. A coincidence value `A = 20 / 3` '
                   'is not a statement-level relation.'),
        gap=('No shared context and no declared translation between the dimensionless radius-rule '
             'constant and the radiative lifetime; the boundary is dimensional, not merely '
             'undelivered.'),
        searchRationale=(
            'Recorded as outOfScope with both constants named and their dimensions compared. The '
            'legacy absence registration agrees but is not the argument.'),
        greps=[
            ('grep -nE \'radFactor|aOfB|b12OfB21|fOfA|aOfInt|tauR|detailed_balance|'
             'degeneracy_roundtrip|af_roundtrip\' PhotoLean/Goldschmidt/*.lean',
             'Search the Goldschmidt modules for a delivered Einstein identifier.',
             'No matches (grep exit 1).'),
        ],
        importFact=('Goldschmidt imports `Mathlib` plus its own five modules only; Einstein '
                    'imports `Mathlib` plus its own four modules. Neither side imports the other '
                    'and the non-own import sets are empty.'),
    ),
]

DEPENDENCIES = {
    'P-Goldschmidt-KashaVavilov': [
        ('PhotoLean/Relations.lean',
         '§16 line 942 "KashaVavilov <-> Sabatier / Goldschmidt / SymmetryFactor - no edge. No '
         'shared scalar: the D2 predicates speak about yields and ladders; the volcano, the ionic '
         'radii and the curvature pairs share none of them."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/KashaVavilov/Basic.lean',
         'SpecSame (line 72), specFrac rows (lines 101, 116), kashaRule_mono (line 128)',
         'Every KashaVavilov statement is a ladder or spectral-fraction statement; no radius.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-KashaVavilov',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-SternVolmer': [
        ('PhotoLean/Relations.lean',
         '§16 line 945 "SternVolmer <-> ... Goldschmidt ... - no edge. The SV model has no energy '
         'surface, no descriptor axis, no geometry: it is a rate-parameter model over a '
         'concentration variable."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/SternVolmer/RatModel.lean',
         'SVZone (line 112), svZoneQ (line 119), svZoneQ_dynLike (line 128)',
         'The SV classifier reads rational slope pairs and returns a four-constructor verdict.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-SternVolmer',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-QuantumYield': [
        ('PhotoLean/Relations.lean',
         '§16 line 948 "QuantumYield <-> ... Goldschmidt ... - no edge. The parallel-channel '
         'calculus is purely algebraic."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/QuantumYield/Basic.lean',
         'totalRate (line 40), yieldOf (line 44), tauOf (line 48)',
         'Every QuantumYield statement is a rate share or a rate total; no radius.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-QuantumYield',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-FluorPhos': [
        ('PhotoLean/Relations.lean',
         '§16 line 952 "FluorPhos <-> ... Goldschmidt ... - no edge except through QuantumYield. '
         'The competition layer\'s objects are branch probabilities."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/FluorPhos/RatModel.lean',
         'FPZone (line 84), fpZoneQ (line 89), fpZoneQ_phosphorDominant_iff (line 97)',
         'The FluorPhos classifier compares rational rate products and returns a three-way '
         'verdict; the build log records `kIC` as an unused variable at line 89.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-FluorPhos',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-EnergyGapLaw': [
        ('PhotoLean/Relations.lean',
         '§16 line 991 "EnergyGapLaw <-> Sabatier / Goldschmidt / SymmetryFactor / KashaVavilov / '
         'SternVolmer / QuantumYield / Einstein - no edge. ... none of the partner scalars (a '
         'descriptor axis, ionic radii, a curvature pair, a ladder, a concentration axis, a yield '
         'algebra, radiative conversions) occurs in nrBarrier/nrRate/lnRate/egZoneQ."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/EnergyGapLaw/Basic.lean',
         'nrBarrier (line 62), cert_nrBarrier (line 67), nrRate (line 74)',
         'The energy-gap quantities are energies pinned to the Kernel and Marcus barrier.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-EnergyGapLaw',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-StokesShift': [
        ('PhotoLean/Relations.lean',
         '§16 line 998 "StokesShift <-> Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor - '
         'no edge. ... the content is band positions (absEnergy, emEnergy, the emission window); '
         'no rate, line law, descriptor, curvature pair or radius occurs in a StokesShift row."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/StokesShift/Basic.lean',
         's0Surface (line 55), s1Surface (line 66), emEnergy (line 80)',
         'The Stokes statements are differences of electronic energies on two surfaces.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-StokesShift',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-ICvsISC': [
        ('PhotoLean/Relations.lean',
         '§16 line 1002 "ICvsISC <-> Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor - no '
         'edge. ... its FC-barrier/spin-discount content names none of the partner scalars."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/ICvsISC/Criterion.lean',
         'rate_ratio_eq (line 80), isc_dominates_iff (line 124), spin_discount (line 164)',
         'Every ICvsISC statement orders rates or Franck-Condon barriers under a spin-orbit '
         'premise; no radius.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-ICvsISC',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-Forster': [
        ('PhotoLean/Relations.lean',
         '§16 line 1021 "Forster <-> Goldschmidt - no edge (look-alike, no machine row). Two '
         'purely geometric threshold criteria - transfer geometry versus ionic radii - sharing no '
         'scalar; the Forster plan §10 registers the shape."',
         'The legacy register records the look-alike and explicitly declines a machine row.'),
        ('PhotoLean/Forster/Basic.lean',
         'kappaSq (line 50), fretEff (line 61), r0six (line 65)',
         'The Forster statements are transfer geometry and spectroscopic length scales.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-Forster',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
    'P-Goldschmidt-Einstein': [
        ('PhotoLean/Relations.lean',
         '§16 line 969 "Einstein <-> ... Goldschmidt ... - no edge. The radiative conversions\' '
         'only machine contact is the QuantumYield anchor."',
         'The legacy register records a registered absence with a statement-level reason.'),
        ('PhotoLean/Einstein/Basic.lean',
         'radFactor (line 45), aOfB (line 49), tauR (line 65)',
         'Every Einstein statement converts between the A coefficient, the B coefficients and the '
         'radiative lifetime; no radius.'),
        ('relation_audit/registry.json',
         'rec-notestablished-P-Goldschmidt-Einstein',
         'The legacy record is a pair-level notEstablished anchor with no kind and no certificate.'),
    ],
}


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


def dump(name, payload):
    path = os.path.join(HERE, name)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(payload, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    return sha_file(path)


def endpoint(inv_by_id, statement_id, form):
    row = inv_by_id[statement_id]
    return {
        'statementId': row['id'],
        'theory': row['theory'],
        'declaration': row['declaration'],
        'declarationKind': row['declarationKind'],
        'sourceArtifact': row['sourceArtifact'],
        'sourceLine': row['sourceLine'],
        'version': row['version'],
        'signatureSha256': row['signatureSha256'],
        'sourceArtifactSha256': row['sourceArtifactSha256'],
        'endpointForm': form,
    }


def short(decl):
    return decl.rsplit('.', 1)[-1]


def main():
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    inv_by_id = {row['id']: row for row in inv['statements']}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}

    # ---------------------------------------------------------------- search log
    entries = []
    for q in QUERIES:
        info = PAIR_INFO[q['pair']]
        deps = [{'artifact': a, 'locator': loc, 'finding': find}
                for a, loc, find in DEPENDENCIES[q['pair']]]
        deps.append({
            'artifact': 'audit_boundary/statement-inventory.json',
            'locator': 'sourceSignature column, theories Goldschmidt and %s'
                       % info['partner'],
            'finding': 'Signature scan: 139 Goldschmidt rows and %d %s rows; zero shared '
                       'identifiers in both directions.'
                       % (sum(1 for r in inv['statements'] if r['theory'] == info['partner']),
                          info['partner']),
        })
        greps = list(q['greps'])
        greps.append((
            'grep -rnE \'tolFac|latticeOf|idealAO|idealA|rAMin|rAMax|InBand|GoldschmidtConforms|'
            'goldschmidtZone|GoldschmidtZone|gapA|classicLo|classicHi|tetragonalHi|'
            'tauGoldschmidt|RadiusMatch|chiTol|Substitutable|ChargeBalanced|isovalent\' '
            'PhotoLean/%s/*.lean' % info['partner'],
            'Search the %s modules for a delivered Goldschmidt identifier.' % info['partner'],
            'No matches (grep exit 1).'))
        greps.append((
            'grep -rn \'^import\' PhotoLean/Goldschmidt/ PhotoLean/%s/' % info['partner'],
            'Recompute both import closures and check for a cross-import or a shared non-Mathlib '
            'module.',
            q['importFact']))
        greps.append((
            'python3 bounded_audit/r5/cross-domain-02/evidence/signature_scan.py %s'
            % info['partner'],
            'Re-run the machine signature scan over the frozen inventory.',
            'Goldschmidt rows 139, %s rows %d; Goldschmidt identifiers in %s signatures: 0; %s '
            'identifiers in Goldschmidt signatures: 0; RESULT: PASS.'
            % (info['partner'],
               sum(1 for r in inv['statements'] if r['theory'] == info['partner']),
               info['partner'], info['partner'])))
        greps.append((
            'python3 tools/relation_audit_registry.py --explain-pair %s' % q['pair'],
            'Recompute the accepted legacy disposition for the pair.',
            "pair: %s\ntheories: ['Goldschmidt', '%s']\nlegacy: label='absence' subtype='%s'\n"
            "candidate: False\nambiguous: False\nregistry records:\n  "
            "rec-notestablished-%s: status='notEstablished' kind=None certificate=None"
            % (q['pair'], info['partner'],
               'look-alike' if info['partner'] == 'Forster' else 'registered-absence',
               q['pair'])))
        entries.append({
            'searchId': q['searchId'],
            'queryId': q['qid'],
            'pairId': q['pair'],
            'status': 'outOfScope',
            'scope': 'scope-XD2-%s-jurisdiction' % info['tag'],
            'snapshot': SNAPSHOT,
            'searchedStatements': q['searched'],
            'searchedKinds': q['kinds'],
            'contextsConsidered': q['contexts'],
            'dependenciesConsulted': deps,
            'commands': [{'command': c, 'purpose': p, 'result': r} for c, p, r in greps],
            'strategiesAttempted': [
                {'strategy': 'Search for a delivered statement that carries an observable of the '
                             'other theory across the pair.',
                 'outcome': 'None. The signature scan finds zero shared identifiers in both '
                            'directions over the full statement authorities.'},
                {'strategy': 'Test the strongest admissible relation the pair offers (%s).'
                             % q['kind'],
                 'outcome': 'Not statable as a %s: %s'
                            % (q['kind'],
                               q['kindRationale'][0].lower() + q['kindRationale'][1:])},
                {'strategy': 'Check the dependency closures for a shared module or a cross-import.',
                 'outcome': q['importFact']},
                {'strategy': 'Check the legacy register for a named query or a certificate.',
                 'outcome': 'Only a pair-level notEstablished anchor with no kind and no '
                            'certificate; the census label is a registered absence, not an audit '
                            'verdict.'},
            ],
            'candidateEvidence': [q['candidate']],
            'remainingGap': q['gap'],
            'recomputeCommands': [
                'python3 bounded_audit/r5/cross-domain-02/evidence/signature_scan.py %s'
                % info['partner'],
                'grep -rn \'^import\' PhotoLean/Goldschmidt/ PhotoLean/%s/' % info['partner'],
                'python3 tools/relation_audit_registry.py --explain-pair %s' % q['pair'],
                'python3 bounded_audit/r5/cross-domain-02/validate.py',
            ],
            'rationale': q['searchRationale'],
        })

    status_counts = {'outOfScope': len(entries)}
    search_log = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': WP_ID,
        'snapshot': SNAPSHOT,
        'entries': entries,
        'counts': {'entries': len(entries), 'byStatus': status_counts},
        'nonClaims': [
            'Every entry is a scoped search record over the frozen R1 statement inventory, the '
            'delivered Lean sources and the accepted legacy registry; it is not an existence '
            'proof and not a completeness claim.',
            'A statement-level absence of a shared identifier is not a claim that no relation '
            'could be written outside the frozen inventory.',
            'The legacy census label is coverage history, not an audit verdict, and it is not used '
            'as evidence for any outcome in this package.',
        ],
    }
    search_sha = dump('search-log.json', search_log)

    # ---------------------------------------------------------------- screening
    pairs = []
    for pid in PAIR_ORDER:
        info = PAIR_INFO[pid]
        qrow = queue_by_id[pid]
        qs = [q for q in QUERIES if q['pair'] == pid]
        rows = []
        for q in qs:
            src_form = 'definition' if inv_by_id[q['src']]['declarationKind'] == 'def' \
                else 'theorem'
            tgt_form = 'definition' if inv_by_id[q['tgt']]['declarationKind'] == 'def' \
                else 'theorem'
            rows.append({
                'queryId': q['qid'],
                'pairId': pid,
                'title': q['title'],
                'chemicalQuestion': q['question'],
                'chemicalRationale': q['rationale'],
                'endpoints': {
                    'source': endpoint(inv_by_id, q['src'], src_form),
                    'target': endpoint(inv_by_id, q['tgt'], tgt_form),
                },
                'sharedContext': {
                    'id': info['ctx'],
                    'fields': CONTEXTS[info['ctx']]['fields'],
                    'physicalReading': CONTEXTS[info['ctx']]['physicalReading'],
                    'provenance': CONTEXTS[info['ctx']]['provenance'],
                },
                'translations': {
                    'left': {
                        'id': 'none-declared',
                        'term': '',
                        'requirement': 'none-declared',
                        'reason': (
                            'No total translation out of the candidate context into the '
                            'Goldschmidt statement context is declared: the Goldschmidt authority '
                            'has no term for %s, so the inclusion of that part of the candidate '
                            'context has no image.' % info['map_text']),
                    },
                    'right': {
                        'id': 'none-declared',
                        'term': '',
                        'requirement': 'none-declared',
                        'reason': (
                            'No total translation out of the candidate context into the %s '
                            'statement context is declared: the %s authority has no term for an '
                            'ionic radius, a lattice length or a tolerance band, so the '
                            'Goldschmidt part of the candidate context has no image.'
                            % (info['partner'], info['partner'])),
                    },
                },
                'premises': {
                    'predicate': 'fun _ : %s => True' % info['ctx'],
                    'premiseIds': [],
                    'definitions': [],
                },
                'observationChannels': [],
                'scope': {
                    'id': 'scope-XD2-%s-jurisdiction' % info['tag'],
                    'description': SCOPES['scope-XD2-%s-jurisdiction' % info['tag']]
                                   ['description'],
                    'domain': SCOPES['scope-XD2-%s-jurisdiction' % info['tag']]['domain'],
                    'snapshot': SNAPSHOT,
                },
                'expectedKind': q['kind'],
                'expectedKindRationale': q['kindRationale'],
                'falsificationCondition': q['falsification'],
                'outcome': {
                    'status': 'outOfScope',
                    'rationale': q['outcomeRationale'],
                    'evidence': {
                        'type': 'jurisdiction',
                        'searchLogRef': q['searchId'],
                        'jurisdictionRationale': q['outcomeRationale'],
                        'statementLevelReason': q['statementLevel'],
                    },
                },
                'provenance': {
                    'kind': 'scoped-search',
                    'sourceArtifact': REL + '/search-log.json',
                    'locator': q['searchId'],
                    'legacyDisposition': (
                        'rec-notestablished-%s (pair-level anchor, status notEstablished, no kind, '
                        'no certificate); PhotoLean/Relations.lean §16 line %d registers the '
                        'absence.' % (pid, info['rel_line'])),
                },
            })
        pairs.append({
            'pairId': pid,
            'theories': qrow['theories'],
            'primaryCluster': qrow['screeningCluster'],
            'queryIds': [q['qid'] for q in qs],
            'queries': rows,
        })

    kind_counts = {}
    for q in QUERIES:
        kind_counts[q['kind']] = kind_counts.get(q['kind'], 0) + 1

    screening = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WP_ID,
            'title': 'Cross-domain screening of the nine remaining Goldschmidt pairs',
            'source': 'loop/计划.md R5, Package XD2',
            'pairIds': list(PAIR_ORDER),
            'pairCount': len(PAIR_ORDER),
            'note': 'Exactly the nine R1 WP-cross-domain-screening-02 pairs, which are also the '
                    'nine remaining Goldschmidt-partner pairs. No accepted R2/R3/R4 pair is '
                    'rescreened, no pair outside the nine is touched, and P-Kasha-Sabatier is '
                    'not duplicated.',
        },
        'statusVocabulary': ['certified', 'refuted', 'unresolved', 'notEstablished',
                             'outOfScope'],
        'kindVocabulary': ['definitionalIdentity', 'implication', 'equivalence',
                           'conditionalComposition', 'observationalEquivalence',
                           'distinguishability', 'refutation'],
        'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'snapshot': {
            'id': SNAPSHOT,
            'date': '2026-11-04',
            'round': ROUND,
            'inventory': INV_REL,
            'inventorySha256': sha_file(os.path.join(ROOT, INV_REL)),
            'pairQueue': QUEUE_REL,
            'pairQueueSha256': sha_file(os.path.join(ROOT, QUEUE_REL)),
            'clusterPlan': CLUSTER_REL,
            'clusterPlanSha256': sha_file(os.path.join(ROOT, CLUSTER_REL)),
            'boundary': 'audit_boundary/BOUNDARY.md',
            'boundarySha256': sha_file(os.path.join(ROOT, 'audit_boundary/BOUNDARY.md')),
            'legacyRegistry': 'relation_audit/registry.json',
            'legacyRegistrySha256':
                sha_file(os.path.join(ROOT, 'relation_audit/registry.json')),
            'leanToolchain': 'leanprover/lean4:v4.17.0',
            'deliveredLeanFileCount': 102,
        },
        'inventoryReference': {
            'path': INV_REL,
            'sha256': sha_file(os.path.join(ROOT, INV_REL)),
            'statementRows': len(inv['statements']),
            'screeningEligibleRows': sum(1 for s in inv['statements'] if s['screeningEligible']),
        },
        'legacyRegistryReference': {
            'path': 'relation_audit/registry.json',
            'sha256': sha_file(os.path.join(ROOT, 'relation_audit/registry.json')),
            'certificateCount': len(load_rel('relation_audit/registry.json')['certificates']),
        },
        'coverageReference': {
            'path': 'bounded_audit/r5/cross-domain-02/coverage-fragment.json',
            'acceptedScreenedPairCount': 67,
            'pin': 'not-pinned',
            'note': 'The prior-coverage count is derived by the validator from the five accepted '
                    'screening packages (wp-surface-01, r3, r4/excited-01, r4/excited-02, '
                    'r4/conical-01). This package never reads and never pins the mutable R5 '
                    'cumulative ledger bounded_audit/coverage.json.',
        },
        'searchLogReference': {
            'path': REL + '/search-log.json',
            'sha256': search_sha,
            'entryCount': len(entries),
        },
        'certificateReference': {
            'path': None,
            'declarationCount': 0,
            'note': 'This package claims no certified and no refuted outcome, so it introduces no '
                    'Lean certificate and no probe. No `sorry`, no custom axiom and no untested '
                    'proof is involved: the package makes no positive claim and therefore no '
                    'falsification target. The delivered Lean tree is unchanged (102 files, '
                    'checked by the validator and by the strict build/scan gate).',
        },
        'aliasResolutions': [
            {
                'statementId': 'goldschmidt.conformance',
                'declaration': 'PhotoLean.Goldschmidt.GoldschmidtConforms',
                'note': 'The inventory id for GoldschmidtConforms is the legacy-friendly '
                        '`goldschmidt.conformance`; it resolves to a delivered declaration at '
                        'PhotoLean/Goldschmidt/Basic.lean:64 and is not a dangling legacy alias.',
            },
        ],
        'contextLibrary': dict(CONTEXTS),
        'scopeLibrary': {
            sid: {'id': sid, **body, 'snapshot': SNAPSHOT}
            for sid, body in SCOPES.items()
        },
        'jurisdictionEvidence': {
            'method': 'For each pair the validator re-derives three statement-level facts from the '
                      'frozen artifacts: (1) a signature scan over every declaration signature of '
                      'both authorities, which must find zero shared identifiers; (2) the two '
                      'import closures, which must not intersect outside Mathlib; (3) the legacy '
                      'registry disposition, which must be a pair-level notEstablished anchor with '
                      'no kind and no certificate. The token sets below are the scan vocabulary.',
            'goldschmidtTokens': GOLDSCHMIDT_TOKENS,
            'partnerTokens': PARTNER_TOKENS,
            'pairs': [
                {
                    'pairId': pid,
                    'partnerTheory': PAIR_INFO[pid]['partner'],
                    'goldschmidtStatementRows': sum(1 for r in inv['statements']
                                                    if r['theory'] == 'Goldschmidt'),
                    'partnerStatementRows': sum(
                        1 for r in inv['statements']
                        if r['theory'] == PAIR_INFO[pid]['partner']),
                    'goldschmidtTokensInPartnerSignatures': [],
                    'partnerTokensInGoldschmidtSignatures': [],
                    'importClosureIntersection': [],
                    'legacyRecordId': 'rec-notestablished-%s' % pid,
                    'legacyStatus': 'notEstablished',
                    'legacyKind': None,
                    'legacyCertificate': None,
                } for pid in PAIR_ORDER
            ],
        },
        'pairs': pairs,
        'counts': {
            'pairs': len(pairs),
            'queries': len(QUERIES),
            'byStatus': status_counts,
            'byExpectedKind': kind_counts,
            'certified': 0,
            'refuted': 0,
            'unresolved': 0,
            'notEstablished': 0,
            'outOfScope': len(QUERIES),
            'pairsWithAtLeastOneQuery': len(pairs),
            'pairsWithoutNamedQuery': 0,
        },
        'nonClaims': [
            'This package screens nine pairs; it is not a completeness theorem for the corpus and '
            'not a claim that no Goldschmidt-partner relation could be written outside the frozen '
            'inventory.',
            'Every outOfScope record is a scoped jurisdiction registration with a statement-level '
            'reason; it is not a claim of logical non-existence and not a negative verdict on the '
            'chemistry of perovskites or of photophysics.',
            'No relation is certified, refuted or forced in this package; the zero counts for '
            'certified/refuted are a property of the frozen statement authorities, not an '
            'achievement target.',
            'The legacy census label (registered absence, or look-alike for Forster) is coverage '
            'history and is not used as evidence for any outcome.',
            'The mutable R5 cumulative ledger is outside this package; prior coverage is derived '
            'from the five accepted screening packages.',
        ],
    }
    screening_sha = dump('screening.json', screening)

    # ---------------------------------------------------------------- fragment
    def by_status(qs):
        out = {}
        for q in qs:
            out[q['outcome']['status']] = out.get(q['outcome']['status'], 0) + 1
        return out

    fragment = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WP_ID,
            'path': REL + '/screening.json',
            'pairCount': len(PAIR_ORDER),
            'sha256': screening_sha,
        },
        'packageState': 'submitted-R5-pending-review',
        'universe': {
            'pairCount': len(queue['pairs']),
            'source': QUEUE_REL,
            'sourceSha256': sha_file(os.path.join(ROOT, QUEUE_REL)),
        },
        'pairs': [
            {
                'pairId': p['pairId'],
                'theories': p['theories'],
                'primaryCluster': p['primaryCluster'],
                'queryCount': len(p['queries']),
                'byStatus': by_status(p['queries']),
            } for p in pairs
        ],
        'counts': {
            'pairs': len(pairs),
            'queries': len(QUERIES),
            'byStatus': status_counts,
            'screenedDelta': len(PAIR_ORDER),
        },
        'overlapWithAccepted': {
            'acceptedScreenedPairCount': 67,
            'acceptedPackages': [
                'bounded_audit/wp-surface-01/screening.json',
                'bounded_audit/r3/screening.json',
                'bounded_audit/r4/excited-01/screening.json',
                'bounded_audit/r4/excited-02/screening.json',
                'bounded_audit/r4/conical-01/screening.json',
            ],
            'derivation': 'The prior pair set is the union of the pair rows of the five accepted '
                          'packages, not a hash-pinned ledger. The mutable R5 ledger is neither '
                          'read nor pinned.',
            'intersection': [],
        },
        'nonClaims': [
            'The fragment is a submission snapshot of this package only; it does not update, and '
            'must not be read as updating, the cumulative coverage ledger.',
            'The acceptedScreenedPairCount is derived from the accepted packages by the validator '
            'and carries no ledger hash.',
        ],
    }
    dump('coverage-fragment.json', fragment)

    print('wrote search-log.json        sha256=%s (%d entries)'
          % (search_sha, len(entries)))
    print('wrote screening.json         sha256=%s (%d pairs, %d queries)'
          % (screening_sha, len(pairs), len(QUERIES)))
    print('wrote coverage-fragment.json sha256=%s'
          % sha_file(os.path.join(HERE, 'coverage-fragment.json')))
    print('counts: pairs=%d queries=%d outOfScope=%d certified=0 refuted=0'
          % (len(pairs), len(QUERIES), len(QUERIES)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
