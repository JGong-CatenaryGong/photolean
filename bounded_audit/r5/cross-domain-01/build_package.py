#!/usr/bin/env python3
"""Build the R5 cross-domain-01 package artifacts from frozen R1 data and live search commands.

Run from the PhotoLean repository root:

    python3 bounded_audit/r5/cross-domain-01/build_package.py

The builder reads the frozen R1 inventory and pair queue, runs the package search commands
in this checkout, and writes:

    screening.json
    search-log.json
    coverage-fragment.json

It never reads or writes the mutable R5 cumulative ledger.  The command outputs embedded in
search-log.json are the actual stdout/stderr of the serialized commands recorded here.
"""

import hashlib
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
REL = os.path.relpath(HERE, ROOT)

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
PROBE_REL = REL + '/probes/XD1-probe.lean'
PROBE_LOG_REL = REL + '/probes/compile.log'
PROBE = 'bounded_audit/r5/cross-domain-01/probes/XD1-probe.lean'
PROBE_LOG = 'bounded_audit/r5/cross-domain-01/probes/compile.log'
BUILD = 'proofs/scripts/lake env lean ' + PROBE
SNAP = 'snap-bounded-audit-2026-11-04'

STATUS_VOCABULARY = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KIND_VOCABULARY = ['definitionalIdentity', 'implication', 'equivalence',
                   'conditionalComposition', 'observationalEquivalence',
                   'distinguishability', 'refutation']
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']

EXPECTED_PAIRS = [
    'P-Marcus-Goldschmidt',
    'P-Hammond-Goldschmidt',
    'P-BEP-Goldschmidt',
    'P-Kasha-Goldschmidt',
    'P-Sabatier-Goldschmidt',
    'P-Sabatier-KashaVavilov',
    'P-Sabatier-SternVolmer',
    'P-Sabatier-QuantumYield',
    'P-Sabatier-FluorPhos',
    'P-Sabatier-EnergyGapLaw',
    'P-Sabatier-StokesShift',
    'P-Sabatier-ICvsISC',
    'P-Sabatier-Forster',
    'P-Sabatier-Einstein',
    'P-Goldschmidt-SymmetryFactor',
]

R1_WP_ID = 'WP-cross-domain-screening-01'
R1_WP_PAIRS = [
    'P-Marcus-Goldschmidt',
    'P-Hammond-Goldschmidt',
    'P-BEP-Goldschmidt',
    'P-Kasha-Sabatier',
    'P-Kasha-Goldschmidt',
    'P-Sabatier-Goldschmidt',
    'P-Sabatier-KashaVavilov',
    'P-Sabatier-SternVolmer',
    'P-Sabatier-QuantumYield',
    'P-Sabatier-FluorPhos',
    'P-Sabatier-EnergyGapLaw',
    'P-Sabatier-StokesShift',
    'P-Sabatier-ICvsISC',
    'P-Sabatier-Forster',
    'P-Sabatier-Einstein',
    'P-Goldschmidt-SymmetryFactor',
]

CONTEXTS = {
    'GoldschmidtLatticeCtx': {
        'fields': ['rA : ℝ', 'rB : ℝ', 'rO : ℝ'],
        'physicalReading': (
            'The Goldschmidt ionic-radius context: three lengths rA, rB, rO fixing the '
            'tolerance factor t = (rA + rO) / (sqrt 2 * (rB + rO)), the ideal A-site radius '
            'idealA rB rO, and the band/substitution predicates. There is no energy, rate, '
            'yield, ladder, concentration, curvature or radiative observable in this context.'),
        'provenance': REL + '/screening.json#GoldschmidtLatticeCtx (jurisdiction record; no Lean structure)',
    },
    'SabatierDescriptorCtx': {
        'fields': ['alphaA : ℝ', 'betaA : ℝ', 'alphaB : ℝ', 'betaB : ℝ', 'dE : ℝ'],
        'physicalReading': (
            'The Sabatier catalytic context: a two-step cycle on one binding-energy descriptor '
            'dE, with affine Brønsted-Evans-Polanyi branches branchUp and branchDown and the '
            'effective barrier max(branchUp, branchDown). There is no ladder index, quencher '
            'concentration, finite channel set, donor-acceptor separation or radiative lifetime '
            'in this context.'),
        'provenance': REL + '/screening.json#SabatierDescriptorCtx (jurisdiction record; no Lean structure)',
    },
    'SabatierEglCandidateCtx': {
        'fields': ['lam1 : ℝ', 'lam2 : ℝ', 'dE : ℝ'],
        'physicalReading': (
            'Candidate shared two-parabola context: two reorganization energies lam1, lam2 and '
            'one reaction energy dE. The Sabatier two-parabola volcano reads dE as a catalytic '
            'descriptor; the energy-gap law reads the same real coordinate as an optical gap x. '
            'The joint reading is a candidate, not a delivered identification.'),
        'provenance': REL + '/screening.json#SabatierEglCandidateCtx (candidate context; no Lean structure)',
    },
    'SabatierStokesCandidateCtx': {
        'fields': ['lam : ℝ', 'e00 : ℝ'],
        'physicalReading': (
            'Candidate shared displaced-harmonic context: one reorganization energy lam and one '
            '0-0 energy e00. The Sabatier symmetric cycle and the StokesShift two-surface model '
            'both use a reorganization energy, but the optical lam and the catalytic lam are not '
            'identified by any delivered statement.'),
        'provenance': REL + '/screening.json#SabatierStokesCandidateCtx (candidate context; no Lean structure)',
    },
    'SabatierIcCandidateCtx': {
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'Candidate shared barrier-controlled rate context: prefactor A, reorganization energy '
            'lam, thermal energy kB*T and coordinate x. The Sabatier activity and the ICvsISC '
            'internal-conversion rate both have the Arrhenius form; no delivered statement '
            'identifies the catalytic step with the IC channel.'),
        'provenance': REL + '/screening.json#SabatierIcCandidateCtx (candidate context; no Lean structure)',
    },
}

SCOPES = {
    'scope-XD1-goldschmidt-jurisdiction': {
        'description': (
            'Statement-level jurisdiction over the six Goldschmidt pairs: the Goldschmidt '
            'authority is a geometric tolerance-factor and ionic-substitution calculus over '
            'three ionic radii, while the partner authorities are energy, rate, ladder, yield '
            'or curvature calculi.'),
        'domain': ('The six Goldschmidt pairs and the named endpoint statements; no claim '
                   'outside those statements and their source artifacts.'),
    },
    'scope-XD1-sabatier-jurisdiction': {
        'description': (
            'Statement-level jurisdiction over the six Sabatier pairs whose partner authority '
            'has no declared catalytic descriptor: ladder, quencher-concentration, finite '
            'channel-set, donor-acceptor distance or radiative-lifetime calculi.'),
        'domain': ('The six Sabatier outOfScope pairs and the named endpoint statements; no '
                   'claim outside those statements and their source artifacts.'),
    },
    'scope-XD1-sabatier-egl-candidate': {
        'description': (
            'Bounded search for a bridge between the Sabatier two-parabola effective barrier '
            'and the energy-gap-law nonradiative barrier.'),
        'domain': ('The Sabatier/EnergyGapLaw endpoint statements, the shared kernel barrier and '
                   'the candidate probe declaration; no claim outside that bounded comparison.'),
    },
    'scope-XD1-sabatier-stokes-candidate': {
        'description': (
            'Bounded search for a reorganization-energy bridge between the Sabatier symmetric '
            'apex barrier and the optical Stokes shift.'),
        'domain': ('The Sabatier/StokesShift endpoint statements, the displaced-harmonic '
                   'surfaces and the candidate probe declaration; no claim outside that bounded '
                   'comparison.'),
    },
    'scope-XD1-sabatier-ic-candidate': {
        'description': (
            'Bounded search for a rate-law bridge between the Sabatier activity functional and '
            'the ICvsISC internal-conversion rate at the Franck-Condon barrier.'),
        'domain': ('The Sabatier/ICvsISC endpoint statements, the kernel barrier and the '
                   'candidate probe declaration; no claim outside that bounded comparison.'),
    },
}


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


def ep(inv, stmt_id):
    row = inv[stmt_id]
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
        'endpointForm': 'definition',
    }


def short_name(decl):
    return decl.rsplit('.', 1)[-1]


PAIR_SPECS = [
    {
        'pairId': 'P-Marcus-Goldschmidt',
        'qid': 'Q-XD1-MG-01',
        'sid': 'SL-XD1-MG-01',
        'source': 'stmt-Marcus-PhotoLean-Marcus-InvertedRegion',
        'target': 'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
        'title': 'Is the Marcus inverted-region boundary the Goldschmidt tolerance-factor boundary?',
        'question': (
            'Marcus divides the driving-force axis at x = lam: the normal region is x < lam and '
            'the inverted region is x > lam. Goldschmidt divides the tolerance factor at t = 1: '
            'the ideal cubic packing is t = 1, and the classic cubic band is [0.8, 1]. Is the '
            'Marcus boundary lam the Goldschmidt tolerance boundary 1, i.e. does the tolerance '
            'factor measure a Marcus driving force?'),
        'rationale': (
            'Marcus boundary lam = x is an equality between an energy (the reorganization '
            'energy) and a driving force; Goldschmidt t is a dimensionless ratio of ionic radii. '
            'A relation would need a total map from (rA, rB, rO) to (lam, x) and a statement that '
            'the boundary values coincide for all perovskites. No delivered statement provides '
            'such a map; the only shared word is "boundary".'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Marcus statement context is declared: the candidate '
            'context carries only the ionic radii (rA, rB, rO), while Marcus.InvertedRegion '
            'consumes a reorganization energy lam and a driving force x. No delivered statement '
            'maps radii to the energy pair.'),
        'rightTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: no '
            'delivered statement maps the Goldschmidt radius triple to the Marcus energy pair; '
            'the tolerance factor is a dimensionless length ratio.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: Marcus.InvertedRegion lam x : Prop := lam < x consumes '
            'two energies; Goldschmidt.tolFac rA rB rO : ℝ := (rA + rO) / (sqrt 2 * (rB + rO)) '
            'consumes three lengths and is dimensionless. No declaration in either authority '
            'mentions the other variable set, and the delivered imports are disjoint (Marcus '
            'imports Mathlib plus Marcus; Goldschmidt imports Mathlib plus Goldschmidt). A radius '
            'ratio cannot be compared with an energy equality without a dimensioned conversion, '
            'which no statement supplies.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context, no declared translation and no shared observable. The '
            'legacy census agrees (energies vs ionic radii: no object in common). The registration '
            'is a jurisdiction record, not a claim of logical absence.'),
        'falsification': (
            'A Marcus statement exposing an ionic-radius or lattice observable, or a Goldschmidt '
            'statement exposing a reorganization energy or a driving force, would remove the '
            'jurisdiction reason.'),
        'legacyDisposition': (
            'rec-goldschmidt-marcus-noedge (pair-level notEstablished anchor, not a named query); '
            'PhotoLean/Relations.lean §10 line 568 registers "Goldschmidt <-> all six - no edge".'),
        'relationsLocator': '§10 line 568 "Goldschmidt <-> all six - no edge"',
        'relationsFinding': (
            'The legacy register states that Goldschmidt formalizes a geometric tolerance-factor '
            'and ionic-substitution criterion with no energy model, so there is no object for an '
            'edge to the energy-side theories.'),
        'searchedStatements': [
            'stmt-Marcus-PhotoLean-Marcus-InvertedRegion', 'marcus.barrier',
            'stmt-Marcus-PhotoLean-Marcus-rate', 'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'goldschmidt.conformance', 'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealA'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no reorganization energy or driving force',
            'Marcus energy context (lam, x): no ionic radius or lattice length'],
        'candidates': [
            {'kind': 'dimensionless-boundary analogy',
             'statement': 't = 1 (ideal packing) versus x = lam (Marcus normal/inverted boundary)',
             'status': 'rejected: one is a length ratio, the other an energy equality; no shared dimension or map'}],
        'strategies': [
            {'strategy': 'Search the Goldschmidt sources for a Marcus declaration, and the Marcus sources for a Goldschmidt declaration.',
             'outcome': 'No matches in either direction; the delivered imports are disjoint.'},
            {'strategy': 'Try to read the tolerance factor as a normalized Marcus coordinate.',
             'outcome': 'tolFac is a ratio of lengths and has no reorganization-energy or driving-force argument; the reading has no total translation.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'The registry has one pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A dimensioned context and a delivered map from (rA, rB, rO) to (lam, x), plus a '
            'statement that the Goldschmidt band edge is the Marcus boundary, are missing.'),
        'searchRationale': (
            'The legacy register records no edge; the only shared word is "boundary" and the two '
            'boundary objects have different dimensions. The honest status is outOfScope, not '
            'unresolved or refuted.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Hammond-Goldschmidt',
        'qid': 'Q-XD1-HG-01',
        'sid': 'SL-XD1-HG-01',
        'source': 'stmt-Hammond-PhotoLean-Hammond-tsCoord',
        'target': 'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
        'title': 'Is the Hammond transition-state coordinate the Goldschmidt tolerance factor?',
        'question': (
            'Both Hammond.tsCoord lam x = (lam - x) / (2 * lam) and Goldschmidt.tolFac rA rB rO are '
            'dimensionless numbers used as structural coordinates. Is the Hammond reactant/product-'
            'side coordinate the Goldschmidt tolerance factor? At thermoneutrality tsCoord = 1/2 '
            'and the ideal perovskite has t = 1; is there a delivered map between these two '
            'structural fractions?'),
        'rationale': (
            'Both are dimensionless fractions, but one is the normalized position of a crossing on '
            'a reaction coordinate built from two energies, and the other is the ratio of an A-O '
            'contact length to the ideal cuboctahedral distance. A relation would need a total map '
            'from (rA, rB, rO) to (lam, x) preserving the fractional reading. No delivered statement '
            'supplies it.'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Hammond statement context is declared: the candidate '
            'context carries only the ionic radii, while Hammond.tsCoord consumes a reorganization '
            'energy and a driving force. No delivered statement maps radii to the energy pair.'),
        'rightTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: no delivered '
            'statement maps the Hammond energy pair to the Goldschmidt radius triple; the two '
            'dimensionless fractions are built from different quantities.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: Hammond.tsCoord is a function of two energies (lam, x); '
            'Goldschmidt.tolFac is a function of three lengths. No declaration in Hammond mentions '
            'a radius or a lattice, and no Goldschmidt declaration mentions a driving force or a '
            'reorganization energy. The dimensionless coincidence 1/2 versus 1 is a numerical '
            'analogy, not a shared context.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The legacy census agrees (a reaction-'
            'coordinate fraction vs a lattice-length ratio). The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Hammond statement exposing an ionic-radius or lattice observable, or a Goldschmidt '
            'statement exposing a driving force or a reorganization energy, would remove the '
            'jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Hammond-Goldschmidt (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §10 line 568 registers "Goldschmidt <-> all six - no edge".'),
        'relationsLocator': '§10 line 568 "Goldschmidt <-> all six - no edge"',
        'relationsFinding': (
            'The legacy register states that Goldschmidt has no energy model, so there is no object '
            'for an edge to the Hammond structural coordinate.'),
        'searchedStatements': [
            'stmt-Hammond-PhotoLean-Hammond-tsCoord',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'stmt-Hammond-PhotoLean-Hammond-gapReactant',
            'goldschmidt.conformance',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealA'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no reaction coordinate or energy surface',
            'Hammond two-parabola context (lam, x): no radius or lattice length'],
        'candidates': [
            {'kind': 'dimensionless-fraction analogy',
             'statement': 'tsCoord in [0, 1] versus tolFac = 1 at ideal packing',
             'status': 'rejected: both are dimensionless but their arguments are different types of quantity; no total map'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other coordinate.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Identify tsCoord with a normalized tolerance factor.',
             'outcome': 'The normalized tolerance factor would need a map from radii to (lam, x); no delivered statement supplies one.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A total map from (rA, rB, rO) to (lam, x) and a statement preserving the fractional '
            'coordinate reading are missing.'),
        'searchRationale': (
            'The dimensionless coincidence is tempting but the quantities have different arguments '
            'and dimensions; the legacy register records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-BEP-Goldschmidt',
        'qid': 'Q-XD1-BG-01',
        'sid': 'SL-XD1-BG-01',
        'source': 'stmt-BEP-PhotoLean-BEP-bepRadius',
        'target': 'goldschmidt.conformance',
        'title': 'Is the BEP tolerance radius the Goldschmidt tolerance band?',
        'question': (
            'BEP defines bepRadius lam tol = 2 * sqrt(lam * tol), the half-width of the driving-'
            'force window on which the linear BEP law holds within tol. Goldschmidt defines a '
            'tolerance band on the dimensionless factor t. Is the BEP window radius the '
            'Goldschmidt tolerance band, i.e. does the BEP tolerance parameter measure the same '
            'acceptance interval as Goldschmidt\'s band?'),
        'rationale': (
            'Both are called tolerance and both define an acceptance interval, but bepRadius has '
            'the dimension of a driving force (energy) and GoldschmidtConforms acts on a '
            'dimensionless length ratio. A relation would need a dimensioned conversion and a map '
            'from (lam, tol) to (lo, hi, rA, rB, rO). No delivered statement supplies either.'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the BEP statement context is declared: the candidate context '
            'carries only ionic radii, while BEP.bepRadius consumes a reorganization energy and a '
            'tolerance in driving-force units. No delivered statement maps radii to that pair.'),
        'rightTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: no delivered '
            'statement maps a driving-force window half-width to a dimensionless tolerance band on '
            'ionic radii.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: BEP.bepRadius lam tol has driving-force units and is a '
            'window half-width; goldschmidt.conformance (GoldschmidtConforms lo hi rA rB rO) is a '
            'dimensionless band predicate on a radius ratio. No BEP declaration mentions a lattice '
            'or an ionic radius; no Goldschmidt declaration mentions a driving force or a line-law '
            'window. The shared word "tolerance" is not a shared quantity.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A BEP statement exposing an ionic radius or lattice observable, or a Goldschmidt '
            'statement exposing a driving-force window or a line-law defect, would remove the '
            'jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-BEP-Goldschmidt (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §10 line 568 registers "Goldschmidt <-> all six - no edge".'),
        'relationsLocator': '§10 line 568 "Goldschmidt <-> all six - no edge"',
        'relationsFinding': (
            'The legacy register states that Goldschmidt has no energy model; the only BEP string '
            'in the Goldschmidt sources is the fidelity-script path in comments, not a declaration.'),
        'searchedStatements': [
            'stmt-BEP-PhotoLean-BEP-bepRadius', 'goldschmidt.conformance',
            'stmt-BEP-PhotoLean-BEP-bepDefect', 'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'stmt-BEP-PhotoLean-BEP-EPConformsOnWindow'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no driving-force window',
            'BEP window context (lam, tol): no ionic radius or lattice length'],
        'candidates': [
            {'kind': 'tolerance-interval analogy',
             'statement': 'bepRadius lam tol defines an energy window; GoldschmidtConforms defines a dimensionless radius band',
             'status': 'rejected: different dimensions and argument types; no dimensioned conversion'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other tolerance object.',
             'outcome': 'The Goldschmidt hits for "BEP" are only the fidelity-script path in comments; no declaration or import.'},
            {'strategy': 'Read bepRadius as a Goldschmidt band width.',
             'outcome': 'bepRadius has driving-force units and a sqrt(lam * tol) form; GoldschmidtConforms has a dimensionless radius ratio. No map.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A dimensioned conversion between the BEP driving-force window and the Goldschmidt '
            'dimensionless band, and a material map from (lam, tol) to (rA, rB, rO), are missing.'),
        'searchRationale': (
            'The shared word "tolerance" does not make a shared quantity; the legacy register '
            'records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Kasha-Goldschmidt',
        'qid': 'Q-XD1-KG-01',
        'sid': 'SL-XD1-KG-01',
        'source': 'kasha.kashaRule',
        'target': 'goldschmidt.conformance',
        'title': 'Is Kasha\'s rule a Goldschmidt tolerance-band condition?',
        'question': (
            'Kasha\'s rule says the emission comes from the lowest excited state of a ladder; '
            'Goldschmidt\'s band says the tolerance factor lies in an interval. Is the Kasha rule '
            'the Goldschmidt band condition on the same scalar?'),
        'rationale': (
            'Kasha\'s rule is a statement about a rate ladder indexed by the natural numbers (rad, '
            'ic sequences); Goldschmidt\'s band is a statement about a triple of ionic radii. A '
            'relation would need a map from the ladder to the radius triple. No delivered statement '
            'supplies it.'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Kasha statement context is declared: the candidate '
            'context carries only ionic radii, while KashaRule consumes two rate sequences indexed '
            'by a ladder level. No delivered statement maps radii to a ladder.'),
        'rightTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: no delivered '
            'statement maps a Kasha rate ladder to a dimensionless radius band.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: Kasha.KashaRule rad ic N quantifies over two functions '
            'ℕ -> ℝ and a ladder bound N; goldschmidt.conformance (GoldschmidtConforms lo hi rA rB '
            'rO) quantifies over three real radii and two band edges. The types and variable sets '
            'do not meet, and no declaration in either authority mentions the other object.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Kasha statement exposing an ionic radius or lattice observable, or a Goldschmidt '
            'statement exposing a ladder rate sequence, would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Kasha-Goldschmidt (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §10 line 568 registers "Goldschmidt <-> all six - no edge".'),
        'relationsLocator': '§10 line 568 "Goldschmidt <-> all six - no edge"',
        'relationsFinding': (
            'The legacy register states that Goldschmidt has no energy or ladder model, so there is '
            'no object for an edge to the Kasha cascade.'),
        'searchedStatements': [
            'kasha.kashaRule', 'goldschmidt.conformance',
            'stmt-Kasha-PhotoLean-Kasha-radBranch',
            'stmt-Kasha-PhotoLean-Kasha-decay',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no rate ladder or emission yield',
            'Kasha ladder context (rad, ic : ℕ -> ℝ): no ionic radius or lattice length'],
        'candidates': [
            {'kind': 'band-vs-ladder analogy',
             'statement': 'Goldschmidt band membership versus Kasha rule on a ladder of levels',
             'status': 'rejected: different variable types (three radii vs two sequences); no map'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Read the Kasha rule as a band condition on an energy gap.',
             'outcome': 'Even if a gap were introduced, Goldschmidt has no gap variable or energy model; the translation is not total.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A total map from the Kasha ladder to the Goldschmidt radius triple and a statement '
            'identifying the band condition with the rule are missing.'),
        'searchRationale': (
            'The two statements have different variable types and no delivered contact; the legacy '
            'register records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-Goldschmidt',
        'qid': 'Q-XD1-SG-01',
        'sid': 'SL-XD1-SG-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-NearOptimal',
        'target': 'goldschmidt.conformance',
        'title': 'Is the Sabatier near-optimal band the Goldschmidt tolerance band?',
        'question': (
            'Sabatier\'s NearOptimal tol apexD dE := |dE - apexD| <= tol and Goldschmidt\'s '
            'GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO are both symmetric acceptance '
            'bands around an ideal value. Is the Sabatier within-tolerance optimum the Goldschmidt '
            'tolerance band, i.e. is the catalytic descriptor dE the perovskite tolerance factor t?'),
        'rationale': (
            'The band shapes coincide: a symmetric interval about an ideal value is an absolute-'
            'deviation bound. But the scalars are a binding energy (dE) and a dimensionless radius '
            'ratio (t). The legacy §10 row registers exactly this as a look-alike of shape with no '
            'edge; Goldschmidt\'s window equivalence is exact for every band, while Sabatier\'s '
            'sharp condition carries the product condition 0 < alphaA * alphaB. A relation would '
            'need a total map between the two scalars, which no statement supplies.'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only ionic radii, while NearOptimal consumes a binding-energy '
            'descriptor, an apex and a tolerance. No delivered statement maps radii to that '
            'descriptor axis.'),
        'rightTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: no delivered '
            'statement maps the catalytic descriptor dE to the perovskite tolerance factor t.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: NearOptimal consumes a dimensionless tolerance and an '
            'energy descriptor; GoldschmidtConforms consumes a dimensionless band and three '
            'lengths. No Sabatier declaration mentions a radius or a lattice; no Goldschmidt '
            'declaration mentions a binding energy or a catalytic branch. The interval identity '
            'NearOptimal tol apex dE <-> Goldschmidt.InBand (apex - tol) (apex + tol) dE is a shape '
            'identity on a real scalar, not a shared physical context.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The legacy §10 row already registers '
            'the band shape coincidence as a look-alike with no edge. Registering the coincidence '
            'is honest; treating it as an edge would be a shape-only identity.'),
        'falsification': (
            'A Sabatier statement exposing an ionic radius or a Goldschmidt statement exposing a '
            'binding energy or catalytic descriptor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-Goldschmidt (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §10 line 583 registers "Goldschmidt <-> '
            'Sabatier - a look-alike of shape, with no edge".'),
        'relationsLocator': '§10 line 583 "Goldschmidt <-> Sabatier - a look-alike of shape, with no edge"',
        'relationsFinding': (
            'The legacy register records the symmetric-band and three-way-classifier shape '
            'coincidences and states that no theorem transfers: the scalars are a radius ratio '
            'versus a binding energy with no delivered map.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-NearOptimal', 'goldschmidt.conformance',
            'stmt-Sabatier-PhotoLean-Sabatier-apex',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-InBand',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealA',
            'stmt-Sabatier-PhotoLean-Sabatier-sabatierZone'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no binding-energy descriptor',
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no radius or lattice'],
        'candidates': [
            {'kind': 'symmetric-band shape identity',
             'statement': 'NearOptimal tol apex dE <-> Goldschmidt.InBand (apex - tol) (apex + tol) dE',
             'status': 'rejected as a shape-only identity: it relates a band predicate on a binding energy to a band predicate on a radius ratio, with no map between the scalars'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other scalar.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Try to transfer the Goldschmidt window equivalence to the Sabatier band.',
             'outcome': 'The algebraic window identity is available, but it is a shape identity on an unrelated scalar; the legacy §10 row rejects the transfer for exactly this reason.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A total map from (rA, rB, rO) to dE and a statement preserving the band reading are '
            'missing; without them the interval identity is only a shape.'),
        'searchRationale': (
            'This is the sharpest shape coincidence in the package, and the legacy register names '
            'it explicitly. The honest status is outOfScope, not certified; certifying the band '
            'identity would manufacture a relation for coverage.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-KashaVavilov',
        'qid': 'Q-XD1-SKV-01',
        'sid': 'SL-XD1-SKV-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
        'title': 'Does the Sabatier activity profile predict the Kasha-Vavilov spectral ladder?',
        'question': (
            'Sabatier\'s activity is the Arrhenius turnover proxy exp(-Ea(dE)/(kB*T)) along a '
            'catalytic descriptor. Kasha-Vavilov\'s SpecSame rad ic M N says two ladder levels have '
            'the same spectral fraction. Is the Sabatier activity the Kasha-Vavilov spectral-same '
            'predicate on the same energy axis?'),
        'rationale': (
            'Kasha-Vavilov speaks about sequences rad, ic : ℕ -> ℝ indexed by a ladder level; '
            'Sabatier speaks about a real descriptor dE and a barrier profile. A relation would '
            'need a map from the ladder index to dE and a statement that the activity controls the '
            'spectral fractions. No delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while the Kasha-Vavilov '
            'spectral predicate consumes two ladder rate sequences. No delivered statement maps '
            'the ladder to dE.'),
        'rightTranslationReason': (
            'No total translation into the Kasha-Vavilov statement context is declared: no '
            'delivered statement maps the catalytic descriptor axis to a ladder index or a '
            'spectral fraction.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: Sabatier.activity is a real function of a real '
            'descriptor; KashaVavilov.SpecSame is a predicate on two ℕ-indexed rate sequences. '
            'The types do not meet, and no declaration in either authority mentions the other '
            'object. The shared Arrhenius exponential in Kasha.marcusIC is a different statement '
            'and is not an endpoint of this pair.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a ladder index or spectral fraction, or a Kasha-Vavilov '
            'statement exposing a catalytic descriptor, would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-KashaVavilov (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §16 line 942 registers "KashaVavilov <-> '
            'Sabatier / Goldschmidt / SymmetryFactor - no edge".'),
        'relationsLocator': '§16 line 942 "KashaVavilov <-> Sabatier / Goldschmidt / SymmetryFactor - no edge"',
        'relationsFinding': (
            'The legacy register states that the D2 predicates speak about yields and ladders; the '
            'volcano shares none of them.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
            'stmt-Kasha-PhotoLean-Kasha-marcusIC',
            'stmt-Kasha-PhotoLean-Kasha-radBranch',
            'stmt-Sabatier-PhotoLean-Sabatier-branchUp'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no ladder index',
            'Kasha-Vavilov ladder context (rad, ic : ℕ -> ℝ): no catalytic descriptor'],
        'candidates': [
            {'kind': 'Arrhenius-template analogy',
             'statement': 'Sabatier.activity and Kasha.marcusIC both use exp(-barrier/(kB*T)), but Kasha.marcusIC is not an endpoint of the KashaVavilov pair',
             'status': 'rejected: the shared exponential is in a third theory and does not relate the two endpoint statements'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Route the comparison through Kasha.marcusIC.',
             'outcome': 'Kasha.marcusIC is a Kasha/Marcus rate, not a KashaVavilov ladder statement; routing through it would change the endpoint pair.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A delivered map from the ladder index/spectral fraction to the catalytic descriptor, '
            'and a statement relating the activity to the spectral-same predicate, are missing.'),
        'searchRationale': (
            'The two theories have different index types and no delivered contact; the legacy '
            'register records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-SternVolmer',
        'qid': 'Q-XD1-SSV-01',
        'sid': 'SL-XD1-SSV-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'sternvolmer.intensityDyn',
        'title': 'Is the Sabatier activity the Stern-Volmer intensity ratio?',
        'question': (
            'Stern-Volmer\'s dynamic ratio is svRatioDyn k0 kq q = (k0 + kq * q) / k0, linear in '
            'quencher concentration q. Sabatier\'s activity is an Arrhenius function of a catalytic '
            'descriptor dE. Is the Sabatier activity the Stern-Volmer ratio, i.e. is the descriptor '
            'the quencher concentration?'),
        'rationale': (
            'One function is linear in a concentration; the other is exponential in a binding '
            'energy. A relation would need a map q <-> dE and an identification of the '
            'Stern-Volmer slope kq/k0 with the volcano slope. No delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while the Stern-Volmer '
            'ratio consumes a quencher concentration and two rate constants.'),
        'rightTranslationReason': (
            'No total translation into the Stern-Volmer statement context is declared: no '
            'delivered statement maps the catalytic descriptor axis to a quencher concentration or '
            'to the Stern-Volmer rate parameters.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: svRatioDyn consumes a concentration q and rate '
            'constants k0, kq; activity consumes a barrier profile and kB, T. No SternVolmer '
            'declaration mentions a catalytic descriptor; no Sabatier declaration mentions a '
            'quencher concentration. The linear-in-q and exponential-in-dE forms are different '
            'laws, not two readings of one quantity.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a quencher concentration or a Stern-Volmer statement '
            'exposing a catalytic descriptor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-SternVolmer (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §16 line 945 registers "SternVolmer <-> '
            'Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor - no edge".'),
        'relationsLocator': '§16 line 945 "SternVolmer <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the SV model has no energy surface, no descriptor '
            'axis and no geometry: it is a rate-parameter model over a concentration variable.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity', 'sternvolmer.intensityDyn',
            'stmt-SternVolmer-PhotoLean-SternVolmer-KSV',
            'stmt-Sabatier-PhotoLean-Sabatier-branchUp',
            'stmt-Sabatier-PhotoLean-Sabatier-apex'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no quencher concentration',
            'Stern-Volmer concentration context (k0, kq, q): no catalytic descriptor'],
        'candidates': [
            {'kind': 'real-function analogy',
             'statement': 'svRatioDyn k0 kq q and activity f kB T dE are both real-valued, but one is linear in q and the other exponential in dE',
             'status': 'rejected: different domains and functional forms; no delivered map'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other variable.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Read the quencher concentration as the catalytic descriptor.',
             'outcome': 'The SV ratio is linear in q and the activity is exponential in dE; the reading is an assumption, not a delivered statement.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A delivered map from the quencher concentration to the catalytic descriptor and a '
            'statement identifying the SV slope with the volcano slope are missing.'),
        'searchRationale': (
            'The SV model is a concentration-axis rate-parameter model; the volcano is a '
            'descriptor-axis barrier model. The legacy register records no edge, so outOfScope is '
            'the honest status.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-QuantumYield',
        'qid': 'Q-XD1-SQY-01',
        'sid': 'SL-XD1-SQY-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
        'title': 'Is the Sabatier activity the quantum yield of a decay channel?',
        'question': (
            'QuantumYield\'s yield is a branching ratio k i / sum(k) over a finite channel set. '
            'Sabatier\'s activity is an Arrhenius rate along a descriptor. Is the Sabatier activity '
            'the quantum yield of the catalytic channel?'),
        'rationale': (
            'A yield is a normalized branching ratio over a channel set; an activity is an '
            'unnormalized rate. A relation would need a declared channel set and a statement that '
            'the activity is the numerator of the yield. No delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while yieldOf consumes a '
            'finite channel vector.'),
        'rightTranslationReason': (
            'No total translation into the QuantumYield statement context is declared: no '
            'delivered statement maps the catalytic descriptor axis to a finite channel index.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: yieldOf is a ratio over Fin n channels; activity is a '
            'real function of a descriptor with no channel index or normalization. No QuantumYield '
            'declaration mentions a catalytic descriptor; no Sabatier declaration mentions a finite '
            'channel set. A branching ratio and an unnormalized rate are different observables.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a finite channel set or a QuantumYield statement '
            'exposing a catalytic descriptor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-QuantumYield (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §16 line 948 registers "QuantumYield <-> '
            'Marcus / Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor - no edge".'),
        'relationsLocator': '§16 line 948 "QuantumYield <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the parallel-channel calculus is purely algebraic; '
            'the energy-side theories enter only through specific channel rates.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
            'stmt-QuantumYield-PhotoLean-QuantumYield-totalRate',
            'stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor',
            'stmt-Sabatier-PhotoLean-Sabatier-apex'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no channel index',
            'QuantumYield channel context (k : Fin n -> ℝ, i : Fin n): no catalytic descriptor'],
        'candidates': [
            {'kind': 'rate-vs-yield analogy',
             'statement': 'activity is an unnormalized rate; yieldOf is a normalized branch probability',
             'status': 'rejected: different observables; no declared channel set containing the catalytic step'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Embed the activity as one channel of a two-channel yield.',
             'outcome': 'That would require a declared competing channel and a normalization statement; neither is delivered, and the construction would be forced.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A declared channel set containing the catalytic step and a statement identifying the '
            'activity with the numerator of the yield are missing.'),
        'searchRationale': (
            'A yield and an activity are different observables; the legacy register records no '
            'edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-FluorPhos',
        'qid': 'Q-XD1-SFP-01',
        'sid': 'SL-XD1-SFP-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
        'title': 'Is the Sabatier activity the fluorescence quantum yield?',
        'question': (
            'FluorPhos\'s phiF kF kISC kIC = kF / (kF + kISC + kIC) is a three-channel '
            'fluorescence yield. Sabatier\'s activity is an Arrhenius rate along a catalytic '
            'descriptor. Is the Sabatier activity the fluorescence yield, i.e. is the catalytic '
            'rate the radiative channel?'),
        'rationale': (
            'The fluorescence yield is a normalized branch probability; the activity is an '
            'unnormalized rate. A relation would need a declared channel set containing the '
            'catalytic step and a statement that the activity is the radiative numerator. No '
            'delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while phiF consumes three '
            'photophysical rate constants.'),
        'rightTranslationReason': (
            'No total translation into the FluorPhos statement context is declared: no delivered '
            'statement maps the catalytic descriptor axis to a radiative/ISC/IC channel set.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: phiF is a ratio of three rate constants; activity is a '
            'real function of a barrier profile. No FluorPhos declaration mentions a catalytic '
            'descriptor; no Sabatier declaration mentions a radiative, ISC or IC channel. The '
            'branch probability and the turnover rate are different observables.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a photophysical channel set or a FluorPhos statement '
            'exposing a catalytic descriptor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-FluorPhos (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §16 line 952 registers "FluorPhos <-> ... - no edge '
            'except through QuantumYield".'),
        'relationsLocator': '§16 line 952 "FluorPhos <-> ... - no edge except through QuantumYield"',
        'relationsFinding': (
            'The legacy register states that the competition layer\'s objects are branch '
            'probabilities and its contacts run through the QuantumYield spine.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
            'stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay',
            'stmt-FluorPhos-PhotoLean-FluorPhos-iscBranch',
            'stmt-Sabatier-PhotoLean-Sabatier-apex'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no channel set',
            'FluorPhos channel context (kF, kISC, kIC): no catalytic descriptor'],
        'candidates': [
            {'kind': 'branch-probability analogy',
             'statement': 'phiF is a normalized three-channel branch; activity is an unnormalized rate',
             'status': 'rejected: different observables; no delivered channel identification'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Set the activity as the radiative channel of the FluorPhos yield.',
             'outcome': 'That would require declaring the catalytic step as a photophysical channel and a competing ISC/IC set; neither is delivered.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A delivered statement identifying the catalytic step with a photophysical channel '
            'and a corresponding channel set is missing.'),
        'searchRationale': (
            'The two statements are a branch probability and a turnover rate; the legacy register '
            'records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-EnergyGapLaw',
        'qid': 'Q-XD1-SEG-01',
        'sid': 'SL-XD1-SEG-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
        'target': 'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
        'title': 'Is the Sabatier two-parabola volcano barrier the energy-gap-law nonradiative barrier?',
        'question': (
            'Sabatier\'s microscopic volcano is parabolicBarrier lam1 lam2 dE = max(BEP.eact lam1 '
            '(-dE), BEP.eact lam2 dE). The energy-gap law\'s nonradiative barrier is nrBarrier lam x '
            '= (lam - x)^2 / (4 * lam). On the strong-binding side the descending Sabatier branch '
            'is BEP.eact lam2 dE, which is the same kernel barrier as nrBarrier lam2 dE. Is the '
            'volcano\'s effective barrier therefore the energy-gap-law barrier?'),
        'rationale': (
            'The two theories share the kernel two-parabola barrier: the descending branch of the '
            'volcano is the reverse-step barrier (lam2 - dE)^2 / (4 * lam2), and the energy-gap law '
            'is the same barrier at gap x. The candidate branch identity is a kernel rfl, but the '
            'full query is about the effective barrier (a maximum of two branches) and about '
            'identifying the catalytic descriptor dE with the optical gap x. The legacy §16 row '
            'registers EnergyGapLaw <-> Sabatier as a shape edge with no theorem transfer; the only '
            'shared object is the kernel barrier, not the two processes.'),
        'status': 'unresolved',
        'context': 'SabatierEglCandidateCtx',
        'scope': 'scope-XD1-sabatier-egl-candidate',
        'leftTranslationReason': (
            'Candidate translation only: the context (lam1, lam2, dE) maps to the Sabatier '
            'two-parabola barrier, but the map is not total on the optical side because no '
            'delivered statement identifies dE with the energy gap x.'),
        'rightTranslationReason': (
            'Candidate translation only: (lam2, dE) maps to the energy-gap barrier nrBarrier lam2 '
            'dE, but the map is not total on the catalytic side because no delivered statement '
            'identifies the catalytic descriptor with the optical gap.'),
        'candidateSummary': (
            'Branch-level kernel identity: parabolaDown lam2 dE = nrBarrier lam2 dE '
            '(probe declaration sabatierStrongBranch_eq_eglBarrier). Missing: the branch-dominance '
            'side condition for the full parabolicBarrier and a delivered statement identifying '
            'the catalytic descriptor with the optical gap.'),
        'outcomeRationale': (
            'No delivered statement identifies the catalytic descriptor dE with the energy-gap x, '
            'and the legacy §16 row registers EnergyGapLaw <-> Sabatier as a shape edge with no '
            'theorem transfer. The kernel branch identity is checked in the candidate probe, but '
            'it is a formula identity of one branch, not a statement-level identification of the '
            'two processes. The full effective-barrier query remains open; it is not certified and '
            'not refuted.'),
        'falsification': (
            'A context with lam1, lam2 > 0 and dE <= apexPar lam1 lam2 at which parabolicBarrier '
            'lam1 lam2 dE != nrBarrier lam2 dE would refute the full implication; the branch '
            'identity alone does not establish it because the branch-dominance side condition and '
            'the identification of dE with the optical gap are not delivered.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-EnergyGapLaw (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §16 line 991 registers "EnergyGapLaw <-> '
            'Sabatier / ... - no edge" and records the shared kernel barrier as a shape edge.'),
        'relationsLocator': '§16 line 991 "EnergyGapLaw <-> Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the delivered EnergyGapLaw links are the kernel and '
            'Marcus pins, the Kasha ordering row, the Hammond boundary row, and the StokesShift '
            'and ICvsISC rows; none of the partner scalars occurs in the EnergyGapLaw statements.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
            'stmt-Sabatier-PhotoLean-Sabatier-parabolaDown',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
            'stmt-Sabatier-PhotoLean-Sabatier-apexPar'],
        'searchedKinds': ['implication', 'definitionalIdentity', 'observationalEquivalence'],
        'contextsConsidered': [
            'SabatierEglCandidateCtx (lam1, lam2, dE): a candidate two-parabola context',
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no optical gap',
            'EnergyGapLaw gap context (lam, x): no catalytic descriptor'],
        'candidates': [
            {'kind': 'kernel branch identity',
             'statement': 'parabolaDown lam2 dE = nrBarrier lam2 dE (checked in probes/XD1-probe.lean)',
             'status': 'checked formula identity; not admitted as a chemical relation because it is one branch and does not identify the two processes'},
            {'kind': 'Arrhenius rate-law substitution',
             'statement': 'activity (fun y => nrBarrier lam y) kB T x = nrRate 1 lam kB T x',
             'status': 'rejected as a shape-only identity: an Arrhenius shape alone does not identify a reaction barrier with an optical parameter'}],
        'strategies': [
            {'strategy': 'Search both authorities for a delivered statement mentioning the other barrier.',
             'outcome': 'No matches; the delivered imports are disjoint (Sabatier imports BEP; EnergyGapLaw imports Kernel and Marcus).'},
            {'strategy': 'Prove the descending-branch identity and try to lift it to the effective barrier.',
             'outcome': 'The branch identity is a kernel rfl (probe), but the effective barrier is a maximum of two branches; lifting it needs the branch-dominance side condition and the dE = x identification, neither delivered.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; the legacy §16 row calls the shared barrier a shape edge with no theorem transfer.'}],
        'remainingGap': (
            'A delivered statement that the strong-binding branch is rate-limiting and that the '
            'catalytic descriptor is the optical gap x; the kernel branch identity alone is a shape '
            'edge, not a chemical relation.'),
        'searchRationale': (
            'The branch identity is genuine and checked, which is why the pair is unresolved rather '
            'than outOfScope; the chemical identification is missing, which is why it is not '
            'certified.'),
        'extraCommands': [
            {'command': "grep -rn 'nrBarrier\\|eact' PhotoLean/Sabatier --include='*.lean'",
             'purpose': 'Search the Sabatier modules for the energy-gap barrier or the BEP barrier.'},
            {'command': "grep -rn 'parabola\\|parabolicBarrier\\|Sabatier' PhotoLean/EnergyGapLaw --include='*.lean'",
             'purpose': 'Search the EnergyGapLaw modules for a Sabatier or parabolic-barrier statement.'}],
        'probeDecl': 'sabatierStrongBranch_eq_eglBarrier',
    },
    {
        'pairId': 'P-Sabatier-StokesShift',
        'qid': 'Q-XD1-SSS-01',
        'sid': 'SL-XD1-SSS-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
        'target': 'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
        'title': 'Does the optical Stokes shift fix the Sabatier apex barrier through the shared reorganization energy?',
        'question': (
            'StokesShift defines stokesShift lam e00 = 2 * lam for the displaced harmonic surfaces. '
            'Sabatier\'s symmetric two-parabola volcano at thermoneutrality has parabolicBarrier lam '
            'lam 0 = lam / 4. Is the Sabatier apex barrier therefore one eighth of the Stokes shift, '
            'i.e. does the optical reorganization energy fix the catalytic barrier?'),
        'rationale': (
            'Both theories use a reorganization energy lam and a two-surface crossing. The '
            'candidate identity parabolicBarrier lam lam 0 = stokesShift lam e00 / 8 is a kernel '
            'calculation, but it requires identifying the optical reorganization energy with the '
            'catalytic reorganization energy and the thermoneutral descriptor with the optical '
            'crossing. The legacy §16 row registers StokesShift <-> Sabatier as no edge because no '
            'rate, descriptor or curvature pair occurs in a StokesShift row; the shared lam is a '
            'symbol, not a delivered identification.'),
        'status': 'unresolved',
        'context': 'SabatierStokesCandidateCtx',
        'scope': 'scope-XD1-sabatier-stokes-candidate',
        'leftTranslationReason': (
            'Candidate translation only: (lam, e00) maps to the symmetric Sabatier apex barrier '
            'parabolicBarrier lam lam 0, but the map is not total on the catalytic side because '
            'the optical lam and the catalytic lam are not identified by any delivered statement.'),
        'rightTranslationReason': (
            'Candidate translation only: (lam, e00) maps to the Stokes shift 2 * lam, but the map '
            'is not total on the optical side because no delivered statement identifies the '
            'catalytic reorganization energy with the optical one.'),
        'candidateSummary': (
            'Symmetric-apex identity: parabolicBarrier lam lam 0 = stokesShift lam e00 / 8 (probe '
            'declaration sabatierSymmetricApex_eq_stokesEighth). Missing: a delivered '
            'identification of the optical lam with the catalytic lam and of the thermoneutral '
            'descriptor with the optical crossing.'),
        'outcomeRationale': (
            'The one-eighth identity is checked in the candidate probe, but it is a formula '
            'identity under a symmetric specialization. No delivered statement identifies the '
            'optical reorganization energy with the catalytic one; the legacy §16 row registers '
            'StokesShift <-> Sabatier as no edge. The chemical query remains open; it is not '
            'certified and not refuted.'),
        'falsification': (
            'A context in which the optical lam is identified with the catalytic lam and the '
            'symmetric apex barrier is not one eighth of the Stokes shift would refute the '
            'candidate; the probe checks the formula, the identification is undelivered.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-StokesShift (pair-level notEstablished anchor, not a '
            'named query); PhotoLean/Relations.lean §16 line 996 registers "StokesShift <-> '
            'Hammond / BEP / Sabatier / Goldschmidt / SymmetryFactor - no edge".'),
        'relationsLocator': '§16 line 996 "StokesShift <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the StokesShift surfaces are kernel copies and the '
            'content is band positions; no rate, line law, descriptor, curvature pair or radius '
            'occurs in a StokesShift row.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
            'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
            'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
            'stmt-Sabatier-PhotoLean-Sabatier-apexBarrier',
            'stmt-StokesShift-PhotoLean-StokesShift-s1Surface'],
        'searchedKinds': ['implication', 'definitionalIdentity', 'observationalEquivalence'],
        'contextsConsidered': [
            'SabatierStokesCandidateCtx (lam, e00): a candidate displaced-harmonic context',
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no optical e00',
            'StokesShift surface context (lam, e00, q): no catalytic branch'],
        'candidates': [
            {'kind': 'symmetric-apex identity',
             'statement': 'parabolicBarrier lam lam 0 = stokesShift lam e00 / 8 (checked in probes/XD1-probe.lean)',
             'status': 'checked formula identity; not admitted as a chemical relation because the two reorganization energies are not identified'},
            {'kind': 'shared reorganization-energy analogy',
             'statement': 'both theories use a symbol named lam for a reorganization energy',
             'status': 'rejected: shared notation is not a shared statement or a delivered identification'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches; the delivered imports are disjoint (Sabatier imports BEP; StokesShift imports Kernel and Marcus).'},
            {'strategy': 'Prove the symmetric-apex one-eighth identity and try to read it as a bridge.',
             'outcome': 'The identity is a kernel calculation, but it assumes the optical and catalytic reorganization energies are the same; no delivered statement makes that identification.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; the legacy §16 row registers no edge.'}],
        'remainingGap': (
            'A statement-level identification of the optical reorganization energy with the '
            'catalytic reorganization energy; without it the one-eighth identity is a formula '
            'coincidence, not a chemical relation.'),
        'searchRationale': (
            'The identity is genuine and checked, which is why the pair is unresolved rather than '
            'outOfScope; the reorganization-energy identification is missing, which is why it is '
            'not certified.'),
        'extraCommands': [
            {'command': "grep -rn 'stokesShift\\|emEnergy\\|StokesShift' PhotoLean/Sabatier --include='*.lean'",
             'purpose': 'Search the Sabatier modules for a Stokes-shift or emission-energy statement.'},
            {'command': "grep -rn 'Sabatier\\|parabolicBarrier\\|apexBarrier' PhotoLean/StokesShift --include='*.lean'",
             'purpose': 'Search the StokesShift modules for a Sabatier or volcano-barrier statement.'}],
        'probeDecl': 'sabatierSymmetricApex_eq_stokesEighth',
    },
    {
        'pairId': 'P-Sabatier-ICvsISC',
        'qid': 'Q-XD1-SIC-01',
        'sid': 'SL-XD1-SIC-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
        'title': 'Is the Sabatier activity the internal-conversion rate at the Franck-Condon barrier?',
        'question': (
            'ICvsISC\'s internal-conversion rate is icRate AI lamI kB T xI = AI * '
            'exp(-fcBarrier(lamI, xI)/(kB*T)), an Arrhenius rate over the FC barrier. Sabatier\'s '
            'activity is exp(-Ea(dE)/(kB*T)). At Ea = fcBarrier(lamI, xI) and with the prefactor '
            'AI, is the Sabatier activity the IC rate?'),
        'rationale': (
            'The two rate laws share the Arrhenius template and the kernel barrier: icRate AI lamI '
            'kB T xI = AI * Sabatier.activity (fun y => fcBarrier lamI y) kB T xI. The candidate '
            'identity is checked in the probe, but it is a rate-law substitution: it does not '
            'identify the IC channel with the catalytic step or the FC barrier with the volcano '
            'barrier. The legacy §16 row registers ICvsISC <-> Sabatier as no edge because the '
            'FC-barrier/spin-discount content names no catalytic scalar.'),
        'status': 'unresolved',
        'context': 'SabatierIcCandidateCtx',
        'scope': 'scope-XD1-sabatier-ic-candidate',
        'leftTranslationReason': (
            'Candidate translation only: (A, lam, kB, T, x) maps to the Sabatier activity '
            'functional at the FC barrier, but the map is not total on the chemical side because '
            'no delivered statement identifies the catalytic step with the IC channel.'),
        'rightTranslationReason': (
            'Candidate translation only: (A, lam, kB, T, x) maps to the ICvsISC rate, but the map '
            'is not total on the chemical side because no delivered statement identifies the IC '
            'channel with the catalytic step.'),
        'candidateSummary': (
            'Rate-law identity: icRate A lam kB T x = A * Sabatier.activity (fun y => fcBarrier '
            'lam y) kB T x (probe declaration sabatierActivity_eq_icRate). Missing: a delivered '
            'statement identifying the IC channel with the catalytic step; the Arrhenius shape '
            'alone is not a chemical relation.'),
        'outcomeRationale': (
            'The rate-law identity is checked in the candidate probe, but it is a substitution of '
            'the FC barrier into the activity functional. It does not identify the IC channel with '
            'the catalytic step, and an Arrhenius shape alone does not identify a reaction barrier '
            'with an optical/IC parameter. The legacy §16 row registers ICvsISC <-> Sabatier as no '
            'edge. The chemical query remains open; it is not certified and not refuted.'),
        'falsification': (
            'A context in which the IC channel is identified with the catalytic step and the '
            'activity is not the IC rate would refute the candidate; the identity itself is '
            'checked, the process identification is not delivered.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-ICvsISC (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §16 line 1001 registers "ICvsISC <-> Hammond / BEP / '
            'Sabatier / Goldschmidt / SymmetryFactor - no edge".'),
        'relationsLocator': '§16 line 1001 "ICvsISC <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the FC-barrier/spin-discount content names none of '
            'the partner scalars; its contacts are the kernel/Marcus pins, the EnergyGapLaw rate '
            'identity and the RACI row.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
            'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
            'stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor',
            'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate'],
        'searchedKinds': ['implication', 'definitionalIdentity', 'observationalEquivalence'],
        'contextsConsidered': [
            'SabatierIcCandidateCtx (A, lam, kB, T, x): a candidate rate-law context',
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no FC barrier',
            'ICvsISC channel context (AI, AS, lamI, lamS, kB, T): no catalytic descriptor'],
        'candidates': [
            {'kind': 'rate-law identity',
             'statement': 'icRate A lam kB T x = A * activity (fun y => fcBarrier lam y) kB T x (checked in probes/XD1-probe.lean)',
             'status': 'checked formula identity; not admitted as a chemical relation because it is only an Arrhenius substitution and does not identify the two processes'},
            {'kind': 'spin-discount analogy',
             'statement': 'the IC channel is one branch of a two-channel decay, like the volcano has two branches',
             'status': 'rejected: branch-count similarity is not a shared scalar or a delivered statement'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches; the delivered imports are disjoint (Sabatier imports BEP; ICvsISC imports Kernel and Marcus).'},
            {'strategy': 'Prove the rate-law identity and try to read it as a chemical bridge.',
             'outcome': 'The identity is a substitution of fcBarrier into activity; it does not identify the IC channel with the catalytic step, so it is a shape-level relation.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; the legacy §16 row registers no edge.'}],
        'remainingGap': (
            'A statement-level identification of the IC channel and FC barrier with the catalytic '
            'step and volcano barrier; the rate-law identity alone is shape-level.'),
        'searchRationale': (
            'The rate-law identity is genuine and checked, which is why the pair is unresolved '
            'rather than outOfScope; the process identification is missing, which is why it is not '
            'certified.'),
        'extraCommands': [
            {'command': "grep -rn 'icRate\\|fcBarrier\\|ICvsISC' PhotoLean/Sabatier --include='*.lean'",
             'purpose': 'Search the Sabatier modules for an IC rate or FC barrier statement.'},
            {'command': "grep -rn 'Sabatier\\|activity\\|VolcanoDescriptor' PhotoLean/ICvsISC --include='*.lean'",
             'purpose': 'Search the ICvsISC modules for a Sabatier activity statement.'}],
        'probeDecl': 'sabatierActivity_eq_icRate',
    },
    {
        'pairId': 'P-Sabatier-Forster',
        'qid': 'Q-XD1-SF-01',
        'sid': 'SL-XD1-SF-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-Forster-PhotoLean-Forster-fretRate',
        'title': 'Is the Sabatier activity the Forster transfer rate?',
        'question': (
            'Forster\'s transfer rate is fretRate tauD r6 R = (1/tauD) * (r6 / R^6), a distance-'
            'dependent transfer law. Sabatier\'s activity is an Arrhenius function of a binding '
            'energy. Is the Sabatier activity the Forster rate, i.e. is the catalytic descriptor a '
            'donor-acceptor separation?'),
        'rationale': (
            'One law is inverse-sixth-power in a distance; the other is exponential in an energy. A '
            'relation would need a map from R to dE and a statement that the transfer rate is the '
            'catalytic turnover. No delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while fretRate consumes a '
            'lifetime, an R0^6 and a separation.'),
        'rightTranslationReason': (
            'No total translation into the Forster statement context is declared: no delivered '
            'statement maps the catalytic descriptor axis to a donor-acceptor separation.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: fretRate consumes a lifetime, an R0^6 and a separation '
            'R; activity consumes a barrier profile and kB, T. No Forster declaration mentions a '
            'catalytic descriptor; no Sabatier declaration mentions a separation or a transfer '
            'efficiency. The inverse-sixth-power law and the Arrhenius law are different '
            'observables, not two readings of one quantity.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a donor-acceptor separation or a Forster statement '
            'exposing a catalytic descriptor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-Forster (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §16 line 964 registers "Forster <-> Marcus / ... / '
            'Sabatier / ... - no edge".'),
        'relationsLocator': '§16 line 964 "Forster <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the transfer geometry shares no scalar with the '
            'energy-surface family; the SV and Goldschmidt look-alikes are shape registrations, '
            'not edges.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-Forster-PhotoLean-Forster-fretRate',
            'stmt-Forster-PhotoLean-Forster-fretEff6',
            'stmt-Forster-PhotoLean-Forster-r0six',
            'stmt-Sabatier-PhotoLean-Sabatier-apex'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no separation',
            'Forster transfer context (tauD, r6, R): no catalytic descriptor'],
        'candidates': [
            {'kind': 'real-valued-rate analogy',
             'statement': 'fretRate and activity are both rates, but one is R^-6 and the other is exp(-barrier/kBT)',
             'status': 'rejected: different functional forms and domains; no delivered map'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Read the donor-acceptor separation as the catalytic descriptor.',
             'outcome': 'The transfer rate is inverse-sixth-power in R and the activity is exponential in dE; the reading is an assumption, not a delivered statement.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A delivered map from the donor-acceptor separation to the catalytic descriptor and a '
            'statement identifying the transfer rate with the turnover are missing.'),
        'searchRationale': (
            'The transfer geometry and the volcano descriptor axis share no scalar; the legacy '
            'register records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Sabatier-Einstein',
        'qid': 'Q-XD1-SE-01',
        'sid': 'SL-XD1-SE-01',
        'source': 'stmt-Sabatier-PhotoLean-Sabatier-activity',
        'target': 'stmt-Einstein-PhotoLean-Einstein-tauR',
        'title': 'Is the Sabatier activity the Einstein radiative lifetime?',
        'question': (
            'Einstein\'s tauR A = 1 / A is a radiative lifetime. Sabatier\'s activity is an '
            'Arrhenius turnover proxy. Is the Sabatier activity the Einstein radiative lifetime, '
            'i.e. is the catalytic rate the Einstein A coefficient?'),
        'rationale': (
            'A lifetime is the reciprocal of a radiative rate; an activity is an exponential of a '
            'barrier. A relation would need a map from A to the volcano barrier and a statement '
            'that the catalytic turnover is the radiative rate. No delivered statement supplies it.'),
        'status': 'outOfScope',
        'context': 'SabatierDescriptorCtx',
        'scope': 'scope-XD1-sabatier-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Sabatier statement context is declared: the candidate '
            'context carries only the catalytic descriptor parameters, while tauR consumes the '
            'Einstein A coefficient.'),
        'rightTranslationReason': (
            'No total translation into the Einstein statement context is declared: no delivered '
            'statement maps the catalytic descriptor axis to a radiative coefficient or a '
            'lifetime.'),
        'statementLevelReason': (
            'Statement-level jurisdiction: tauR consumes the Einstein A coefficient; activity '
            'consumes a barrier profile. No Einstein declaration mentions a catalytic descriptor '
            'or a barrier profile; no Sabatier declaration mentions a radiative coefficient or a '
            'lifetime. A reciprocal radiative rate and an Arrhenius turnover are different '
            'observables.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Sabatier statement exposing a radiative coefficient or lifetime, or an Einstein '
            'statement exposing a catalytic descriptor or barrier profile, would remove the '
            'jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Sabatier-Einstein (pair-level notEstablished anchor, not a named '
            'query); PhotoLean/Relations.lean §16 line 969 registers "Einstein <-> Marcus / ... / '
            'Sabatier / ... - no edge".'),
        'relationsLocator': '§16 line 969 "Einstein <-> ... / Sabatier / ... - no edge"',
        'relationsFinding': (
            'The legacy register states that the radiative conversions\' only machine contact is '
            'the QuantumYield anchor; the J-integral link to Forster is a modelling premise.'),
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
            'stmt-Einstein-PhotoLean-Einstein-aOfB',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Sabatier-PhotoLean-Sabatier-apex'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'Sabatier descriptor context (alphaA, betaA, alphaB, betaB, dE): no radiative lifetime',
            'Einstein radiative context (A, K, B21): no catalytic descriptor'],
        'candidates': [
            {'kind': 'rate-vs-lifetime analogy',
             'statement': 'activity is an Arrhenius rate and tauR is the reciprocal of a radiative rate',
             'status': 'rejected: different observables and arguments; no delivered map'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'No matches in either direction; the imports are disjoint.'},
            {'strategy': 'Set the catalytic rate to the Einstein A coefficient.',
             'outcome': 'That would require a statement identifying the catalytic step with the radiative transition; neither authority supplies it.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A delivered statement identifying the catalytic rate with the radiative A coefficient '
            'and the volcano barrier with the transition energy is missing.'),
        'searchRationale': (
            'The radiative lifetime and the catalytic turnover are different observables; the '
            'legacy register records no edge. The honest status is outOfScope.'),
        'extraCommands': [],
    },
    {
        'pairId': 'P-Goldschmidt-SymmetryFactor',
        'qid': 'Q-XD1-GSF-01',
        'sid': 'SL-XD1-GSF-01',
        'source': 'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
        'target': 'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
        'title': 'Is the Goldschmidt tolerance factor the unequal-curvature transition-state coordinate?',
        'question': (
            'Goldschmidt\'s tolFac = (rA + rO) / (sqrt 2 * (rB + rO)) and SymmetryFactor\'s '
            'tsCoordZero = sqrt kp / (sqrt kr + sqrt kp) are both geometric ratios built from '
            'square roots. Is the Goldschmidt tolerance factor the unequal-curvature crossing '
            'coordinate, i.e. do the ionic radii play the role of the curvature pair (kr, kp)?'),
        'rationale': (
            'Both are dimensionless ratios with a square-root structure, but one is built from '
            'three ionic radii and the other from two potential curvatures. A relation would need '
            'a total map from (rA, rB, rO) to (kr, kp) preserving the crossing-coordinate reading. '
            'No delivered statement supplies it; the only textual contact is a comment in '
            'SymmetryFactor/RatModel.lean noting the shared rational-square pattern.'),
        'status': 'outOfScope',
        'context': 'GoldschmidtLatticeCtx',
        'scope': 'scope-XD1-goldschmidt-jurisdiction',
        'leftTranslationReason': (
            'No total translation into the Goldschmidt statement context is declared: the '
            'candidate context carries only ionic radii, while tsCoordZero consumes two curvature '
            'parameters. No delivered statement maps curvatures to radii.'),
        'rightTranslationReason': (
            'No total translation into the SymmetryFactor statement context is declared: no '
            'delivered statement maps the Goldschmidt radius triple to the curvature pair '
            '(kr, kp).'),
        'statementLevelReason': (
            'Statement-level jurisdiction: tolFac consumes three lengths; tsCoordZero consumes two '
            'curvature parameters. No Goldschmidt declaration mentions a potential curvature; no '
            'SymmetryFactor declaration mentions an ionic radius or a tolerance factor. The '
            'square-root shape is an algebraic analogy, not a shared context.'),
        'outcomeRationale': (
            'This pair is outside the declared audit jurisdiction: the two statement authorities '
            'have no shared context or declared translation. The registration is a jurisdiction '
            'record, not a claim of logical absence.'),
        'falsification': (
            'A Goldschmidt statement exposing a potential curvature or a SymmetryFactor statement '
            'exposing an ionic radius or tolerance factor would remove the jurisdiction reason.'),
        'legacyDisposition': (
            'rec-notestablished-P-Goldschmidt-SymmetryFactor (pair-level notEstablished anchor, not '
            'a named query); PhotoLean/Relations.lean §10 line 603 registers "SymmetryFactor <-> '
            'Kasha, Sabatier, Goldschmidt - no edge".'),
        'relationsLocator': '§10 line 603 "SymmetryFactor <-> Kasha, Sabatier, Goldschmidt - no edge"',
        'relationsFinding': (
            'The legacy register states that the curvature-pair scalar (kr, kp) shares no object '
            'with the ladder, the volcano descriptor axis or the ionic radii.'),
        'searchedStatements': [
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-tolFac',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-Goldschmidt-PhotoLean-Goldschmidt-idealA',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-CrossesAtThermoneutral',
            'symmetry.betaHalfReading'],
        'searchedKinds': ['implication', 'equivalence', 'definitionalIdentity',
                          'observationalEquivalence'],
        'contextsConsidered': [
            'GoldschmidtLatticeCtx (rA, rB, rO): no curvature pair',
            'SymmetryFactor curvature context (kr, kp): no ionic radius or lattice length'],
        'candidates': [
            {'kind': 'square-root-ratio analogy',
             'statement': 'tolFac has a sqrt 2 denominator; tsCoordZero has sqrt kr and sqrt kp',
             'status': 'rejected: both are square-root ratios but of different quantities; the only contact is a comment about a rational-square proof pattern'}],
        'strategies': [
            {'strategy': 'Search both authorities for a statement mentioning the other object.',
             'outcome': 'The only Goldschmidt string in SymmetryFactor is a RatModel comment about the rational-square pattern; no declaration or import.'},
            {'strategy': 'Read the curvature pair as ionic radii.',
             'outcome': 'kr and kp are potential curvatures; rA, rB, rO are lengths. The reading has no total map or delivered statement.'},
            {'strategy': 'Recompute the legacy disposition.',
             'outcome': 'One pair-level notEstablished anchor; no named query or certificate.'}],
        'remainingGap': (
            'A total map from (rA, rB, rO) to (kr, kp) and a statement preserving the crossing-'
            'coordinate reading are missing.'),
        'searchRationale': (
            'The square-root shape is an algebraic analogy; the legacy register records no edge. '
            'The honest status is outOfScope.'),
        'extraCommands': [],
    },
]


def run_commands(spec):
    left, right = spec['left'], spec['right']
    cmds = []
    if right == 'Goldschmidt':
        cmds.append((f"grep -rn '{left}' PhotoLean/Goldschmidt --include='*.lean'",
                     f'Search the Goldschmidt modules for a delivered {left} statement.'))
        cmds.append((f"grep -rn 'Goldschmidt\\|tolFac\\|GoldschmidtConforms' PhotoLean/{left} --include='*.lean'",
                     f'Search the {left} modules for a delivered Goldschmidt statement.'))
    elif left == 'Goldschmidt':
        cmds.append((f"grep -rn '{right}' PhotoLean/Goldschmidt --include='*.lean'",
                     f'Search the Goldschmidt modules for a delivered {right} statement.'))
        cmds.append((f"grep -rn 'Goldschmidt\\|tolFac\\|GoldschmidtConforms' PhotoLean/{right} --include='*.lean'",
                     f'Search the {right} modules for a delivered Goldschmidt statement.'))
    else:
        cmds.append((f"grep -rn '{right}' PhotoLean/Sabatier --include='*.lean'",
                     f'Search the Sabatier modules for a delivered {right} statement.'))
        cmds.append((f"grep -rn 'Sabatier\\|VolcanoDescriptor\\|activity' PhotoLean/{right} --include='*.lean'",
                     f'Search the {right} modules for a delivered Sabatier statement.'))
    cmds.append((f"grep -h '^import ' PhotoLean/{left}/*.lean | sort -u",
                 f'Measure the {left} module dependencies.'))
    cmds.append((f"grep -h '^import ' PhotoLean/{right}/*.lean | sort -u",
                 f'Measure the {right} module dependencies.'))
    cmds.append((f'python3 tools/relation_audit_registry.py --explain-pair {spec["pairId"]}',
                 'Recompute the accepted legacy disposition.'))
    for extra in spec.get('extraCommands', []):
        cmds.append((extra['command'], extra['purpose']))
    return cmds


def result_text(p):
    out = p.stdout.strip()
    err = p.stderr.strip()
    if p.returncode == 0:
        return out if out else '(no output; exit 0)'
    if p.returncode == 1 and not out:
        return 'No matches (grep exit 1; no stdout).'
    msg = out
    if err:
        msg = (msg + '\n' if msg else '') + err
    return msg if msg else f'(command exited {p.returncode})'


def main():
    inv_json = load(INV_REL)
    inv = {row['id']: row for row in inv_json['statements']}
    queue = load(QUEUE_REL)
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    registry = load(REGISTRY_REL)
    probe_sha = sha_file(os.path.join(ROOT, PROBE))
    queue_sha = sha_file(os.path.join(ROOT, QUEUE_REL))
    inv_sha = sha_file(os.path.join(ROOT, INV_REL))

    # ------------------------------------------------------------------ search log
    entries = []
    for spec in PAIR_SPECS:
        spec['left'], spec['right'] = queue_by_id[spec['pairId']]['theories']
        cmds = run_commands(spec)
        command_rows = []
        for command, purpose in cmds:
            p = subprocess.run(command, shell=True, capture_output=True, text=True, cwd=ROOT)
            command_rows.append({
                'command': command,
                'purpose': purpose,
                'result': result_text(p),
            })
        spec['command_rows'] = command_rows

        deps = [
            {
                'artifact': 'PhotoLean/Relations.lean',
                'locator': spec['relationsLocator'],
                'finding': spec['relationsFinding'],
            },
            {
                'artifact': 'relation_audit/registry.json',
                'locator': spec['legacyDisposition'].split(' ')[0],
                'finding': ('The legacy record is a pair-level notEstablished anchor, not a '
                            'named chemical query; it is coverage history, not an audit verdict.'),
            },
            {
                'artifact': inv[spec['source']]['sourceArtifact'],
                'locator': '%s#%s (line %d)' % (
                    inv[spec['source']]['sourceArtifact'],
                    short_name(inv[spec['source']]['declaration']),
                    inv[spec['source']]['sourceLine']),
                'finding': 'The source endpoint declaration consumed by the query.',
            },
            {
                'artifact': inv[spec['target']]['sourceArtifact'],
                'locator': '%s#%s (line %d)' % (
                    inv[spec['target']]['sourceArtifact'],
                    short_name(inv[spec['target']]['declaration']),
                    inv[spec['target']]['sourceLine']),
                'finding': 'The target endpoint declaration consumed by the query.',
            },
        ]
        if spec.get('probeDecl'):
            deps.append({
                'artifact': PROBE,
                'locator': 'PhotoLean.RelationAudit.BoundedAudit.XD1.' + spec['probeDecl'],
                'finding': ('Candidate identity checked in the local probe; it carries only '
                            'propext, Classical.choice and Quot.sound, but it is not used as a '
                            'certified outcome because the chemical identification is missing.'),
            })

        entries.append({
            'searchId': spec['sid'],
            'queryId': spec['qid'],
            'pairId': spec['pairId'],
            'status': spec['status'],
            'scope': spec['scope'],
            'snapshot': SNAP,
            'searchedStatements': spec['searchedStatements'],
            'searchedKinds': spec['searchedKinds'],
            'contextsConsidered': spec['contextsConsidered'],
            'dependenciesConsulted': deps,
            'commands': command_rows,
            'strategiesAttempted': spec['strategies'],
            'candidateEvidence': spec['candidates'],
            'remainingGap': spec['remainingGap'],
            'recomputeCommands': [row['command'] for row in command_rows[:5]],
            'rationale': spec['searchRationale'],
        })

    status_counts = {}
    for spec in PAIR_SPECS:
        status_counts[spec['status']] = status_counts.get(spec['status'], 0) + 1

    search_log = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': 'XD1-CROSS-DOMAIN-01',
        'snapshot': SNAP,
        'entries': entries,
        'counts': {
            'entries': len(entries),
            'byStatus': status_counts,
        },
        'nonClaims': [
            'A search-log entry records a bounded search, not a completeness claim over the corpus.',
            'A notEstablished or outOfScope legacy label is census metadata, not an audit verdict.',
            'Candidate identities checked in the local probe are not certified outcomes.',
        ],
    }
    search_path = os.path.join(HERE, 'search-log.json')
    with open(search_path, 'w', encoding='utf-8') as fh:
        json.dump(search_log, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    search_sha = sha_file(search_path)

    # ------------------------------------------------------------------ screening
    pairs = []
    for spec in PAIR_SPECS:
        ctx_id = spec['context']
        ctx = CONTEXTS[ctx_id]
        q = {
            'queryId': spec['qid'],
            'pairId': spec['pairId'],
            'title': spec['title'],
            'chemicalQuestion': spec['question'],
            'chemicalRationale': spec['rationale'],
            'endpoints': {
                'source': ep(inv, spec['source']),
                'target': ep(inv, spec['target']),
            },
            'sharedContext': {
                'id': ctx_id,
                'fields': ctx['fields'],
                'physicalReading': ctx['physicalReading'],
                'provenance': ctx['provenance'],
            },
            'translations': {
                'left': {
                    'id': 'none-declared' if spec['status'] == 'outOfScope' else 'candidate-not-total',
                    'term': '',
                    'requirement': ('No total translation into the source statement context is '
                                    'declared.' if spec['status'] == 'outOfScope' else
                                    'Candidate translation only; not total on the declared domain.'),
                    'reason': spec['leftTranslationReason'],
                },
                'right': {
                    'id': 'none-declared' if spec['status'] == 'outOfScope' else 'candidate-not-total',
                    'term': '',
                    'requirement': ('No total translation into the target statement context is '
                                    'declared.' if spec['status'] == 'outOfScope' else
                                    'Candidate translation only; not total on the declared domain.'),
                    'reason': spec['rightTranslationReason'],
                },
            },
            'premises': {
                'predicate': f'fun _ : {ctx_id} => True',
                'premiseIds': [],
                'definitions': [],
            },
            'observationChannels': [],
            'scope': {
                'id': spec['scope'],
                'description': SCOPES[spec['scope']]['description'],
                'domain': SCOPES[spec['scope']]['domain'],
                'snapshot': SNAP,
            },
            'expectedKind': 'implication',
            'expectedKindRationale': (
                'The weakest composable link would be a one-way implication from the source '
                'statement context to the target statement context; the expected kind records '
                'what a relation would have to be, not a claim that one exists.'),
            'falsificationCondition': spec['falsification'],
            'outcome': {
                'status': spec['status'],
                'rationale': spec['outcomeRationale'],
                'evidence': {
                    'type': 'jurisdiction' if spec['status'] == 'outOfScope' else 'scoped-search',
                    'searchLogRef': spec['sid'],
                },
            },
            'provenance': {
                'kind': 'scoped-search',
                'sourceArtifact': REL + '/search-log.json',
                'locator': spec['sid'],
                'legacyDisposition': spec['legacyDisposition'],
            },
        }
        if spec['status'] == 'outOfScope':
            q['outcome']['evidence'].update({
                'jurisdictionRationale': spec['statementLevelReason'],
                'statementLevelReason': spec['statementLevelReason'],
            })
        else:
            q['outcome']['evidence'].update({
                'candidateSummary': spec['candidateSummary'],
                'candidateProbe': {
                    'path': PROBE,
                    'sha256': probe_sha,
                    'declaration': 'PhotoLean.RelationAudit.BoundedAudit.XD1.' + spec['probeDecl'],
                    'axiomFootprint': ALLOWED_AXIOMS,
                    'allowedAxioms': ALLOWED_AXIOMS,
                    'buildCommand': BUILD,
                    'log': PROBE_LOG,
                },
            })
        pairs.append({
            'pairId': spec['pairId'],
            'theories': queue_by_id[spec['pairId']]['theories'],
            'primaryCluster': 'cross-domain-screening',
            'queryIds': [spec['qid']],
            'queries': [q],
        })

    kind_counts = {'implication': len(PAIR_SPECS)}
    full_status_counts = {s: status_counts.get(s, 0) for s in STATUS_VOCABULARY}

    screening = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': 'XD1-CROSS-DOMAIN-01',
            'title': 'Cross-domain screening: R1 WP-cross-domain-screening-01 minus the accepted P-Kasha-Sabatier pair',
            'source': 'loop/计划.md R5, Package XD1',
            'pairIds': EXPECTED_PAIRS,
            'pairCount': len(EXPECTED_PAIRS),
            'r1WorkPackage': {
                'id': R1_WP_ID,
                'pairIds': R1_WP_PAIRS,
                'pairCount': len(R1_WP_PAIRS),
                'excludedAcceptedPair': 'P-Kasha-Sabatier',
                'difference': {
                    'removed': ['P-Kasha-Sabatier'],
                    'reason': ('P-Kasha-Sabatier was screened and accepted in R2 '
                               '(query Q-WPS01-KS-01); R5 does not rescreen an accepted pair.'),
                },
            },
        },
        'statusVocabulary': STATUS_VOCABULARY,
        'kindVocabulary': KIND_VOCABULARY,
        'allowedAxioms': ALLOWED_AXIOMS,
        'snapshot': {
            'id': SNAP,
            'date': '2026-11-04',
            'round': 'R5',
            'inventory': INV_REL,
            'inventorySha256': inv_sha,
            'pairQueue': QUEUE_REL,
            'pairQueueSha256': queue_sha,
            'clusterPlan': CLUSTER_REL,
            'clusterPlanSha256': sha_file(os.path.join(ROOT, CLUSTER_REL)),
            'boundary': BOUNDARY_REL,
            'boundarySha256': sha_file(os.path.join(ROOT, BOUNDARY_REL)),
            'legacyRegistry': REGISTRY_REL,
            'legacyRegistrySha256': sha_file(os.path.join(ROOT, REGISTRY_REL)),
            'deliveredLeanFileCount': 102,
            'priorPackages': [
                {'round': 'R2', 'path': 'bounded_audit/wp-surface-01/screening.json',
                 'pairCount': 10, 'sha256': sha_file(os.path.join(ROOT, 'bounded_audit/wp-surface-01/screening.json'))},
                {'round': 'R3', 'path': 'bounded_audit/r3/screening.json',
                 'pairCount': 11, 'sha256': sha_file(os.path.join(ROOT, 'bounded_audit/r3/screening.json'))},
                {'round': 'R4', 'path': 'bounded_audit/r4/excited-01/screening.json',
                 'pairCount': 16, 'sha256': sha_file(os.path.join(ROOT, 'bounded_audit/r4/excited-01/screening.json'))},
                {'round': 'R4', 'path': 'bounded_audit/r4/excited-02/screening.json',
                 'pairCount': 14, 'sha256': sha_file(os.path.join(ROOT, 'bounded_audit/r4/excited-02/screening.json'))},
                {'round': 'R4', 'path': 'bounded_audit/r4/conical-01/screening.json',
                 'pairCount': 16, 'sha256': sha_file(os.path.join(ROOT, 'bounded_audit/r4/conical-01/screening.json'))},
            ],
            'priorAcceptedPairCount': 67,
            'priorCoverageSource': ('The accepted R2/R3/R4 screening packages listed above; the '
                                    'mutable R5 cumulative ledger is neither read nor pinned.'),
        },
        'inventoryReference': {
            'sha256': inv_sha,
            'statementRows': len(inv_json['statements']),
            'screeningEligibleRows': sum(1 for s in inv_json['statements'] if s['screeningEligible']),
        },
        'legacyRegistryReference': {
            'sha256': sha_file(os.path.join(ROOT, REGISTRY_REL)),
            'certificateCount': len(registry['certificates']),
        },
        'searchLogReference': {
            'path': REL + '/search-log.json',
            'sha256': search_sha,
            'entryCount': len(entries),
        },
        'probeReference': {
            'path': PROBE,
            'sha256': probe_sha,
            'log': PROBE_LOG,
            'declarationCount': 3,
            'role': 'candidate-evidence',
            'buildCommand': BUILD,
            'declarations': [
                'PhotoLean.RelationAudit.BoundedAudit.XD1.' + spec['probeDecl']
                for spec in PAIR_SPECS if spec.get('probeDecl')
            ],
        },
        'contextLibrary': CONTEXTS,
        'scopeLibrary': SCOPES,
        'pairs': pairs,
        'counts': {
            'pairs': len(PAIR_SPECS),
            'queries': len(PAIR_SPECS),
            'byStatus': status_counts,
            'byExpectedKind': kind_counts,
            'certified': full_status_counts['certified'],
            'refuted': full_status_counts['refuted'],
            'unresolved': full_status_counts['unresolved'],
            'notEstablished': full_status_counts['notEstablished'],
            'outOfScope': full_status_counts['outOfScope'],
        },
        'nonClaims': [
            'This package screens exactly the fifteen assigned pairs; it is not a completeness claim over the corpus.',
            'A certified record is a checked relation under its declared context; no pair is forced to improve coverage.',
            'The mutable R5 cumulative ledger is not read or pinned; prior coverage is derived from accepted packages.',
            'The local probe carries candidate identities, not certified outcomes; the three unresolved pairs remain open.',
        ],
    }
    screening_path = os.path.join(HERE, 'screening.json')
    with open(screening_path, 'w', encoding='utf-8') as fh:
        json.dump(screening, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    screening_sha = sha_file(screening_path)

    # ------------------------------------------------------------------ fragment
    fragment = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': 'XD1-CROSS-DOMAIN-01',
            'path': REL + '/screening.json',
            'pairCount': len(PAIR_SPECS),
            'sha256': screening_sha,
            'r1WorkPackage': R1_WP_ID,
            'excludedAcceptedPair': 'P-Kasha-Sabatier',
        },
        'packageState': 'submitted-R5-pending-review',
        'universe': {
            'pairCount': 136,
            'source': QUEUE_REL,
            'sourceSha256': queue_sha,
        },
        'pairs': [
            {
                'pairId': spec['pairId'],
                'theories': queue_by_id[spec['pairId']]['theories'],
                'primaryCluster': 'cross-domain-screening',
                'queryCount': 1,
                'byStatus': {spec['status']: 1},
            }
            for spec in PAIR_SPECS
        ],
        'counts': {
            'pairs': len(PAIR_SPECS),
            'queries': len(PAIR_SPECS),
            'byStatus': status_counts,
            'screenedDelta': len(PAIR_SPECS),
        },
        'overlapWithAccepted': {
            'acceptedScreenedPairCount': 67,
            'intersection': [],
            'note': ('The fragment is disjoint from the accepted 67 pairs, including the R2 '
                     'P-Kasha-Sabatier pair; the accepted count is derived from the accepted '
                     'R2/R3/R4 screening packages, not from the mutable R5 ledger.'),
        },
        'accumulationNote': (
            'This fragment is not the cumulative ledger. The integration agent composes it with the '
            'accepted 67 pairs into the R5 ledger. This package does not write the ledger.'),
        'nonClaims': [
            'A coverage fragment counts screened pairs; it is not a completeness claim.',
            'The fragment does not assign acceptance; the package stays submitted-R5-pending-review until independent K3 review.',
        ],
    }
    with open(os.path.join(HERE, 'coverage-fragment.json'), 'w', encoding='utf-8') as fh:
        json.dump(fragment, fh, indent=1, ensure_ascii=False)
        fh.write('\n')

    print('wrote screening.json       %s' % screening_sha)
    print('wrote search-log.json      %s' % search_sha)
    print('wrote coverage-fragment.json')
    print('probe                      %s' % probe_sha)
    print('pairs %d queries %d byStatus %s' % (len(PAIR_SPECS), len(PAIR_SPECS), status_counts))


if __name__ == '__main__':
    main()
