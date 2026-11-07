#!/usr/bin/env python3
"""Deterministic builder for the R5 Package RAD1 screening artifacts.

The builder reads the frozen R1 inventory / pair queue / cluster plan, the accepted legacy
registry and the accepted R2/R3/R4 packages (for the prior-coverage statement only), then writes

    bounded_audit/r5/radiative-01/search-log.json
    bounded_audit/r5/radiative-01/screening.json
    bounded_audit/r5/radiative-01/coverage-fragment.json

in that order, because each artifact pins the SHA-256 of the ones before it. It deliberately does
NOT read or pin ``bounded_audit/coverage.json``: the R5 cumulative ledger is owned by the
integration step and is mutable while packages are written. Prior coverage (67 pairs) is derived
from the five accepted ``screening.json`` packages directly.

Run from the repository root:

    python3 bounded_audit/r5/radiative-01/build_screening.py
"""

import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
R2_REL = 'bounded_audit/wp-surface-01/screening.json'
R3_REL = 'bounded_audit/r3/screening.json'
R4_E1_REL = 'bounded_audit/r4/excited-01/screening.json'
R4_E2_REL = 'bounded_audit/r4/excited-02/screening.json'
R4_CI_REL = 'bounded_audit/r4/conical-01/screening.json'
SCREENING_REL = 'bounded_audit/r5/radiative-01/screening.json'
SEARCH_REL = 'bounded_audit/r5/radiative-01/search-log.json'
FRAGMENT_REL = 'bounded_audit/r5/radiative-01/coverage-fragment.json'
PROBE_REL = 'bounded_audit/r5/radiative-01/probes/RAD1-probe.lean'
PROBE_LOG_REL = 'bounded_audit/r5/radiative-01/probes/compile.log'

WORK_PACKAGE = 'WP-radiative-energy-transfer-01'
PRIMARY_CLUSTER = 'radiative-energy-transfer'
SNAP_ID = 'snap-bounded-audit-2026-11-04-r5rad1'
ROUND = 'R5'

PAIRS = [
    'P-Marcus-KashaVavilov', 'P-Marcus-EnergyGapLaw', 'P-Marcus-StokesShift',
    'P-Marcus-ICvsISC', 'P-Marcus-Forster', 'P-Marcus-Einstein',
    'P-Kasha-KashaVavilov', 'P-Kasha-EnergyGapLaw', 'P-Kasha-StokesShift',
    'P-Kasha-ICvsISC', 'P-Kasha-Forster', 'P-Kasha-Einstein',
    'P-KashaVavilov-SternVolmer', 'P-KashaVavilov-QuantumYield',
    'P-KashaVavilov-FluorPhos', 'P-KashaVavilov-EnergyGapLaw',
]

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']

PROBE_NS = 'PhotoLean.RelationAudit.BoundedAudit.RAD1.'
MKV_CMP_LEFT_DECL = 'PhotoLean.Marcus.barrier'


def sha_path(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha_rel(rel):
    return sha_path(os.path.join(ROOT, rel))


def load_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


def read_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return fh.read()


INV = load_rel(INV_REL)
QUEUE = load_rel(QUEUE_REL)
CLUSTER = load_rel(CLUSTER_REL)
REGISTRY = load_rel(REGISTRY_REL)
R2 = load_rel(R2_REL)
R3 = load_rel(R3_REL)
R4_E1 = load_rel(R4_E1_REL)
R4_E2 = load_rel(R4_E2_REL)
R4_CI = load_rel(R4_CI_REL)

INV_BY_ID = {row['id']: row for row in INV['statements']}
QUEUE_BY_ID = {row['pairId']: row for row in QUEUE['pairs']}
DANGLING_IDS = {d['id'] for d in INV.get('legacyDanglingStatements', [])}


def find_line(rel, declaration):
    """Locate the 1-based source line of a declaration inside an artifact."""
    short = declaration.rsplit('.', 1)[-1]
    pat = re.compile(r'(^|[\s(])(def|theorem|structure|inductive|abbrev)\s+' + re.escape(short) +
                     r'\b')
    for i, line in enumerate(read_rel(rel).splitlines(), start=1):
        if pat.search(line):
            return i
    raise SystemExit('cannot locate %s in %s' % (declaration, rel))


def endpoint(stmt_id, form):
    row = INV_BY_ID[stmt_id]
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


def underlying(declaration, rel, role):
    return {
        'declaration': declaration,
        'sourceArtifact': rel,
        'sourceLine': find_line(rel, declaration),
        'role': role,
    }


# --------------------------------------------------------------------------- context library

CONTEXTS = {
    'MarcusKvCtx': {
        'id': 'MarcusKvCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ', 'tol : ℝ',
                   'rad : ℕ → ℝ', 'ic : ℕ → ℝ'],
        'physicalReading': (
            'A two-level ladder (radiative rad, nonradiative ic) whose S₂→S₁ internal conversion '
            'is the Marcus-form activated step at reorganization energy lam and gap x, compared '
            'at tolerance tol. The Marcus barrier sets the squared-gap window; the ladder decides '
            'whether the upper block emits.'),
        'provenance': PROBE_REL + '#MarcusKvCtx',
    },
    'EglRateCtx': {
        'id': 'EglRateCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'One nonradiative step in the equal-curvature two-parabola model: pre-exponential A, '
            'reorganization energy lam, thermal energy kB*T and driving force x. Both theories '
            'evaluate their own rate law on this same parameter tuple.'),
        'provenance': PROBE_REL + '#EglRateCtx',
    },
    'EglZoneCtx': {
        'id': 'EglZoneCtx',
        'fields': ['lam : ℝ', 'x : ℝ'],
        'physicalReading': (
            'The reorganization energy and driving force of one step. The two theories classify '
            'this point into the same region: the gap larger than the reorganization energy.'),
        'provenance': PROBE_REL + '#EglZoneCtx',
    },
    'MarcusICCtx': {
        'id': 'MarcusICCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'One internal-conversion step: pre-exponential A, channel reorganization energy lam, '
            'thermal energy kB*T and the channel gap x. ICvsISC evaluates its IC rate law on this '
            'tuple; Marcus evaluates its activated rate on the same tuple.'),
        'provenance': PROBE_REL + '#MarcusICCtx',
    },
    'MarcusSSCtx': {
        'id': 'MarcusSSCtx',
        'fields': ['lam : ℝ', 'e00 : ℝ'],
        'physicalReading': (
            'The displaced-parabola pair of the same fluorophore: reorganization energy lam and '
            '0-0 energy e00. Marcus classifies (lam, e00); StokesShift computes the vertical '
            'absorption and emission energies from the same pair.'),
        'provenance': PROBE_REL + '#MarcusSSCtx',
    },
    'KashaVavCtx': {
        'id': 'KashaVavCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ'],
        'physicalReading': (
            'The Kasha ladder up to excitation level N: radiative and nonradiative rate arrays '
            'and the level N at which the excitation enters. Kasha states the exact rule as '
            'upperYield = 0; KashaVavilov states the spectral invariance of the same ladder.'),
        'provenance': PROBE_REL + '#KashaVavCtx',
    },
    'KashaEglCtx': {
        'id': 'KashaEglCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'One internal-conversion step in the Marcus form: pre-exponential A, reorganization '
            'energy lam, thermal energy kB*T and gap x. The Kasha ladder fills its inter-level IC '
            'channel with this rate; the energy-gap law writes its nonradiative rate on the same '
            'tuple.'),
        'provenance': PROBE_REL + '#KashaEglCtx',
    },
    'KashaEinsteinCtx': {
        'id': 'KashaEinsteinCtx',
        'fields': ['A : ℝ', 'kNR : ℝ'],
        'physicalReading': (
            'One excited state with radiative rate A and total nonradiative loss kNR. The Kasha '
            'ladder resolves it into a radiative and a nonradiative branch; the Einstein side '
            'writes the same radiative fraction as A times the observed lifetime 1/(A+kNR).'),
        'provenance': PROBE_REL + '#KashaEinsteinCtx',
    },
    'KvQyCtx': {
        'id': 'KvQyCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ'],
        'physicalReading': (
            'The Kasha ladder up to level N. The KashaVavilov total-yield row splits the '
            'fluorescence yield into the lowest-level emission and the upper-block leak; the '
            'QuantumYield calculus evaluates the lowest-level two-channel yield.'),
        'provenance': PROBE_REL + '#KvQyCtx',
    },
    'KvFpCtx': {
        'id': 'KvFpCtx',
        'fields': ['kF : ℝ', 'kISC : ℝ', 'kIC : ℝ'],
        'physicalReading': (
            'The S₁ state with fluorescence, intersystem-crossing and internal-conversion rates. '
            'FluorPhos keeps the three channels separate; the Kasha ladder resolves the same '
            'state into one radiative and one nonradiative channel, the latter carrying '
            'kISC + kIC.'),
        'provenance': PROBE_REL + '#KvFpCtx',
    },
    'KvSvCtx': {
        'id': 'KvSvCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ', 'kq : ℝ', 'q : ℝ'],
        'physicalReading': (
            'The Kasha ladder up to level N under a collisional quencher at concentration q with '
            'bimolecular rate kq. Dynamic quenching adds kq*q to the *level-0* total decay; the '
            'upper levels of the ladder are untouched.'),
        'provenance': PROBE_REL + '#KvSvCtx',
    },
    'MarcusForsterDisjointCtx': {
        'id': 'MarcusForsterDisjointCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ',
                   'tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'Candidate shared context only: the Marcus step carries an activation barrier with a '
            'driving-force coordinate, the Förster transfer carries a donor lifetime and a '
            'donor-acceptor separation with an R⁻⁶ rate law. No declared translation relates a '
            'separation to a driving force.'),
        'provenance': SCREENING_REL + '#MarcusForsterDisjointCtx (candidate context; no Lean structure)',
    },
    'MarcusEinsteinDisjointCtx': {
        'id': 'MarcusEinsteinDisjointCtx',
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ',
                   'h : ℝ', 'c : ℝ', 'nu : ℝ', 'B21 : ℝ'],
        'physicalReading': (
            'Candidate shared context only: the Marcus rate is an activated nonradiative step; '
            'the Einstein coefficients are radiative transition quantities with a radiation-'
            'density factor. The single symbol A means a pre-exponential on one side and a '
            'spontaneous-emission coefficient on the other; no translation is declared.'),
        'provenance': SCREENING_REL + '#MarcusEinsteinDisjointCtx (candidate context; no Lean structure)',
    },
    'KashaStokesDisjointCtx': {
        'id': 'KashaStokesDisjointCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ', 'lam : ℝ', 'e00 : ℝ'],
        'physicalReading': (
            'Candidate shared context only: the ladder carries rate arrays and yields; the Stokes '
            'description carries the two parabola offsets (lam, e00) and no rate array. No '
            'declared translation turns a rate array into a band position.'),
        'provenance': SCREENING_REL + '#KashaStokesDisjointCtx (candidate context; no Lean structure)',
    },
    'KashaICCandidateCtx': {
        'id': 'KashaICCandidateCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ',
                   'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'Candidate shared context: the ladder channelling S₂→S₁ conversion through the '
            'ICvsISC Arrhenius rate law at that step’s own reorganization energy and gap. The '
            'ladder leaves ic a free rate array, so the assignment ic 1 = icRate is a modelling '
            'premise that no delivered statement carries.'),
        'provenance': SCREENING_REL + '#KashaICCandidateCtx (candidate context; no Lean structure)',
    },
    'KashaForsterDisjointCtx': {
        'id': 'KashaForsterDisjointCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ', 'tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'Candidate shared context only: the ladder emits and converts between its own levels; '
            'the Förster description transfers excitation between two chromophores through a '
            'dipole geometry. No donor-acceptor pair and no donor lifetime occur in the ladder.'),
        'provenance': SCREENING_REL + '#KashaForsterDisjointCtx (candidate context; no Lean structure)',
    },
    'KvEglCandidateCtx': {
        'id': 'KvEglCandidateCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ',
                   'T : ℝ', 'x : ℝ'],
        'physicalReading': (
            'Candidate shared context: the energy-gap law’s nonradiative rate fills the ladder’s '
            'IC channel, which would decide whether the Vavilov invariance survives. The ladder '
            'carries no energy-gap parameter of its own, and the delivered window row is stated '
            'with the Kasha-side Marcus-form rate, not with the energy-gap-law rate.'),
        'provenance': SCREENING_REL + '#KvEglCandidateCtx (candidate context; no Lean structure)',
    },
}

# --------------------------------------------------------------------------- scope library

SCOPES = {
    'scope-RAD1-marcus-kv-window': {
        'id': 'scope-RAD1-marcus-kv-window',
        'description': 'Marcus window condition compared with the KashaVavilov anti-Kasha predicate.',
        'domain': ('all (A, lam, kB, T, x, tol, rad, ic) satisfying the seven declared premises; '
                   'the totalized divisions of the ladder are included under the positivity '
                   'premises'),
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-egl-rate': {
        'id': 'scope-RAD1-egl-rate',
        'description': 'The two rate laws evaluated on one parameter tuple.',
        'domain': 'all (A, lam, kB, T, x) in ℝ⁵; the totalized lam = 0 corner and kB*T = 0 are included',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-egl-zone': {
        'id': 'scope-RAD1-egl-zone',
        'description': 'The two region predicates evaluated on one (lam, x) pair.',
        'domain': 'all (lam, x) in ℝ²',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-ic-rate': {
        'id': 'scope-RAD1-ic-rate',
        'description': 'The IC channel rate law and the Marcus rate on one parameter tuple.',
        'domain': 'all (A, lam, kB, T, x) in ℝ⁵; totalized divisions included',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-ss-window': {
        'id': 'scope-RAD1-ss-window',
        'description': 'The inversion predicate and the sign of the emission energy.',
        'domain': 'all (lam, e00) in ℝ²; the e00 = lam zero-photon corner is included',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kasha-vav-spec': {
        'id': 'scope-RAD1-kasha-vav-spec',
        'description': 'Kasha rule implies spectral excitation-independence on the same ladder.',
        'domain': ('all ladders (rad, ic) and levels N satisfying RateData and the positive '
                   'fluorescence-yield hypotheses for every M ≤ N'),
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kasha-egl-rate': {
        'id': 'scope-RAD1-kasha-egl-rate',
        'description': 'The ladder IC rate law and the energy-gap-law rate on one tuple.',
        'domain': 'all (A, lam, kB, T, x) in ℝ⁵; totalized divisions included',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kasha-einstein': {
        'id': 'scope-RAD1-kasha-einstein',
        'description': 'The lowest-level radiative fraction read by Kasha and by Einstein.',
        'domain': 'all (A, kNR) in ℝ²; the A + kNR = 0 corner is included under totalized division',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kv-qy-decomp': {
        'id': 'scope-RAD1-kv-qy-decomp',
        'description': 'The KashaVavilov total-yield decomposition with the QuantumYield calculus.',
        'domain': 'all ladders (rad, ic) and levels N; totalized divisions included',
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kv-fp-lump': {
        'id': 'scope-RAD1-kv-fp-lump',
        'description': 'The bottom-level ladder yield against the FluorPhos fluorescence yield.',
        'domain': ('all (kF, kISC, kIC) in ℝ³ under the declared channel-lumping translation '
                   'rad 0 = kF, ic 0 = kISC + kIC'),
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-kv-sv-quench': {
        'id': 'scope-RAD1-kv-sv-quench',
        'description': 'The bottom-emission channel before and after a level-0 collisional quench.',
        'domain': ('all (rad, ic, N, kq, q) with 0 < rad 0 + ic 0 and 0 ≤ kq*q; the quench '
                   'channel is added to the level-0 decay only'),
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-candidate-bridge': {
        'id': 'scope-RAD1-candidate-bridge',
        'description': 'Scoped search for a delivered statement-level bridge; no negative claim outside it.',
        'domain': ('the named unresolved pairs and the statements, kinds and contexts recorded in '
                   'their search-log entries'),
        'snapshot': SNAP_ID,
    },
    'scope-RAD1-jurisdiction': {
        'id': 'scope-RAD1-jurisdiction',
        'description': 'Jurisdiction record for pairs with no shared context or declared translation.',
        'domain': ('the named outOfScope pairs and the statements, kinds and contexts recorded in '
                   'their search-log entries'),
        'snapshot': SNAP_ID,
    },
}

# --------------------------------------------------------------------------- shared query fields

PROBE_BUILD = 'proofs/scripts/lake env lean ' + PROBE_REL


def evidence_certified(cert_id, kind, declaration, theorem_list, justification):
    return {
        'type': 'rad1-probe-certificate',
        'certificateId': cert_id,
        'kind': kind,
        'probe': {
            'path': PROBE_REL,
            'sha256': sha_rel(PROBE_REL),
            'declaration': PROBE_NS + declaration,
            'kindCheckTheorem': PROBE_NS + declaration + '_kind',
            'buildCommand': PROBE_BUILD,
            'log': PROBE_LOG_REL,
        },
        'underlyingTheorems': theorem_list,
        'axiomFootprint': ALLOWED_AXIOMS,
        'allowedAxioms': ALLOWED_AXIOMS,
        'justification': justification,
    }


def provenance_certified(cert_id, declaration, legacy):
    return {
        'kind': 'rad1-probe-certificate',
        'certificateId': cert_id,
        'sourceArtifact': PROBE_REL,
        'locator': PROBE_NS + declaration,
        'legacyDisposition': legacy,
    }


def provenance_search(kind, search_id, legacy, statement=None):
    out = {
        'kind': kind,
        'sourceArtifact': SEARCH_REL,
        'locator': search_id,
    }
    if statement is not None:
        out['jurisdictionStatement'] = statement
    out['legacyDisposition'] = legacy
    return out


LEGACY_PAIR_ANCHOR = ('The legacy registry carries only a pair-level {status} anchor for this '
                      'pair; it is coverage history, not an audit verdict, and is not cited as '
                      'evidence.')

# --------------------------------------------------------------------------- queries

QUERIES = []


def add_query(pair_id, query):
    query['pairId'] = pair_id
    QUERIES.append(query)


# P-Marcus-KashaVavilov ------------------------------------------------------
add_query('P-Marcus-KashaVavilov', {
    'queryId': 'Q-RAD1-MKVV-01',
    'title': 'A gap outside the Marcus window makes anti-Kasha emission observable',
    'chemicalQuestion': (
        'If the ladder’s S₂→S₁ internal conversion obeys the Marcus rate at reorganization '
        'energy lam and gap x, does a squared gap outside the Kasha tolerance window force a '
        'positive emission yield from the upper block — i.e. an observable failure of the Kasha '
        'rule rather than Vavilov spectral invariance?'),
    'chemicalRationale': (
        'Marcus supplies the energy-gap control of an internal-conversion step: the barrier '
        '(lam − x)²/(4·lam) is smallest at x = lam, so the conversion rate is maximal there and '
        'falls quadratically as the gap leaves the reorganization energy. The KashaVavilov layer '
        'decides whether the ladder keeps the lowest-state spectrum (SpecSame, the Vavilov side) '
        'or leaks emission from above (anti-Kasha observable). The query composes the two '
        'statements: once the Marcus-controlled squared gap exceeds the Kasha window bound, the '
        'upper block necessarily retains emission. It is a cross-theory implication whose '
        'antecedent is a Marcus barrier condition and whose consequent is the KashaVavilov '
        'anti-Kasha predicate, not an identity of two rate notations.'),
    'endpoints': {
        'source': endpoint('marcus.barrier', 'definition'),
        'target': endpoint(
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-antiKasha_observable_iff', 'theorem'),
    },
    'sharedContext': CONTEXTS['MarcusKvCtx'],
    'translations': {
        'left': {
            'id': 'coordinate-map',
            'term': 'fun δ : MarcusKvCtx => δ',
            'requirement': ('The Marcus barrier is evaluated at the shared (lam, x); the '
                            'prefactor, thermal energy and tolerance are carried only as '
                            'premise parameters.'),
        },
        'right': {
            'id': 'descriptor-endpoint',
            'term': ('fun δ : MarcusKvCtx =>\n'
                     '  { rad := δ.rad, ic := δ.ic, N := 1 }'),
            'requirement': ('The KashaVavilov predicate is evaluated on the same ladder '
                            '(rad, ic) at level N = 1; its interpretation as “emission from '
                            'above the lowest state is observable” is the declared content of '
                            'the delivered D2 boundary row.'),
        },
    },
    'premises': {
        'predicate': (
            'fun δ : MarcusKvCtx =>\n'
            '  PhotoLean.Kasha.RateData δ.rad δ.ic 1 ∧\n'
            '  0 < δ.tol ∧ δ.tol < 1 ∧ 0 < δ.A ∧ 0 < δ.lam ∧ 0 < δ.kB * δ.T ∧\n'
            '  0 < δ.rad 0 ∧ 0 < δ.rad 1 ∧\n'
            '  δ.ic 1 = PhotoLean.Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x'),
        'premiseIds': ['mkv.rateData', 'mkv.tolerance', 'mkv.prefactorPositive',
                       'mkv.lamPositive', 'mkv.thermalPositive', 'mkv.ratesPositive',
                       'mkv.icIsMarcusRate'],
        'definitions': [
            {
                'id': 'mkv.rateData',
                'predicate': 'PhotoLean.Kasha.RateData δ.rad δ.ic 1',
                'statement': ('the ladder has positive total decay rates, nonnegative radiative '
                              'and nonnegative nonradiative rates up to level 1'),
                'loadBearing': ('consumed by the window row (decay positivity) and by the '
                                'anti-Kasha boundary row (RateData is its only hypothesis)'),
            },
            {
                'id': 'mkv.tolerance',
                'predicate': '0 < δ.tol ∧ δ.tol < 1',
                'statement': 'the tolerance is a physical fraction strictly between 0 and 1',
                'loadBearing': 'consumed by the window row and by the log-positivity of the threshold',
            },
            {
                'id': 'mkv.prefactorPositive',
                'predicate': '0 < δ.A',
                'statement': 'the Marcus pre-exponential factor is positive',
                'loadBearing': 'consumed by the window row (positivity of the gap threshold)',
            },
            {
                'id': 'mkv.lamPositive',
                'predicate': '0 < δ.lam',
                'statement': 'the reorganization energy is positive',
                'loadBearing': ('consumed by the window row; without it the barrier and the '
                                'threshold are not ordered'),
            },
            {
                'id': 'mkv.thermalPositive',
                'predicate': '0 < δ.kB * δ.T',
                'statement': 'the thermal energy is positive',
                'loadBearing': 'consumed by the window row’s logarithm and division steps',
            },
            {
                'id': 'mkv.ratesPositive',
                'predicate': '0 < δ.rad 0 ∧ 0 < δ.rad 1',
                'statement': 'the bottom and funnel radiative rates are positive',
                'loadBearing': ('consumed by the window row; also used to derive the positive '
                                'upper yield through the tolerance bound'),
            },
            {
                'id': 'mkv.icIsMarcusRate',
                'predicate': ('δ.ic 1 = PhotoLean.Kasha.marcusIC δ.A δ.lam δ.kB δ.T δ.x'),
                'statement': ('the ladder’s inter-level internal-conversion channel is the '
                              'Marcus-form activated rate at the same reorganization energy and gap'),
                'loadBearing': ('the declared modelling premise of the composition; without it '
                                'the ladder carries an arbitrary rate array'),
            },
        ],
        'note': ('All seven premises are consumed by the proof: the window row consumes six and '
                 'the seventh names the channel assignment. No premise is decorative.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-marcus-kv-window'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The obligation is one-way: a Marcus barrier condition entails the '
                              'KashaVavilov anti-Kasha predicate. The converse is not claimed '
                              '(anti-Kasha emission can arise from any fast upper conversion), '
                              'so the row is an implication, not an equivalence.'),
    'falsificationCondition': ('A context satisfying the seven premises at which the squared gap '
                               'exceeds the window bound yet the ladder still satisfies the Kasha '
                               'rule (upperYield rad ic 1 = 0) would refute the implication. The '
                               'probe proof is total, so no such context exists in the model.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `mkv_sound` derives the anti-Kasha predicate from the window '
                      'premises and the gap bound, consuming both the delivered window row '
                      '`Kasha.not_kashaWithin_of_gap_far` and the delivered D2 boundary row '
                      '`KashaVavilov.antiKasha_observable_iff`.'),
        'evidence': evidence_certified(
            'RC-RAD1-MKVV-01', 'implication', 'mkvBridge', [
                underlying('PhotoLean.Kasha.not_kashaWithin_of_gap_far',
                           'PhotoLean/Kasha/Compose.lean',
                           'delivered anti-Kasha direction of the Marcus window row'),
                underlying('PhotoLean.KashaVavilov.antiKasha_observable_iff',
                           'PhotoLean/KashaVavilov/Criterion.lean',
                           'delivered D2 boundary: positive upper yield ↔ the rule fails'),
                underlying('PhotoLean.Kasha.fluoYield_nonneg', 'PhotoLean/Kasha/Basic.lean',
                           'delivered nonnegativity consumed to turn the window violation into a '
                           'strict positivity'),
            ],
            ('The certificate is a typed implication. Its antecedent is a Marcus barrier '
             'condition; its consequent is the KashaVavilov predicate. The proof consumes the '
             'two delivered rows above, so the row is a composition of delivered statements, '
             'not a restatement of one.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-MKVV-01', 'mkvBridge',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished')),
})

# P-Marcus-EnergyGapLaw ------------------------------------------------------
add_query('P-Marcus-EnergyGapLaw', {
    'queryId': 'Q-RAD1-MEG-01',
    'title': 'The energy-gap-law nonradiative rate is the Marcus rate',
    'chemicalQuestion': (
        'Is the energy-gap law’s nonradiative rate — the Arrhenius rate over the equal-curvature '
        'crossing barrier — literally the Marcus rate at the same pre-exponential factor, '
        'reorganization energy, thermal energy and driving force?'),
    'chemicalRationale': (
        'The energy-gap law and the Marcus inverted region describe the same nonradiative step: '
        'an activated crossing of the two equal-curvature parabolas, with the gap as the driving '
        'force. The energy-gap-law module keeps its own copy of the barrier and rate for '
        'independence, and its delivered certificate pins that copy to the Marcus body. The '
        'query asks whether the two theories’ nonradiative rate is one and the same rate law, '
        'so that the gap-law’s gap dependence is the Marcus barrier’s quadratic dependence. The '
        'answer is yes, definitionally.'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
        'target': endpoint('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition'),
    },
    'sharedContext': CONTEXTS['EglRateCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : EglRateCtx => δ',
            'requirement': 'Both statement contexts are the shared parameter tuple; the translation is total.',
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : EglRateCtx => δ',
            'requirement': 'Both statement contexts are the shared parameter tuple; the translation is total.',
        },
    },
    'premises': {
        'predicate': 'fun _ : EglRateCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The two rate laws are definitionally the same total function of the tuple, '
                 'including the lam = 0 and kB*T = 0 totalized corners; no premise is '
                 'load-bearing, so none is declared.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-egl-rate'],
    'expectedKind': 'definitionalIdentity',
    'expectedKindRationale': ('The obligation is a fresh elaborator check that the two translated '
                              'rate terms are definitionally equal, not a propositional equality '
                              'and not a physical-identity claim.'),
    'falsificationCondition': ('A tuple (A, lam, kB, T, x) at which the two rate values differ '
                               'would refute the definitional identity; the probe pin is total.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe builds a `DefinitionalPin` whose two translated terms elaborate '
                      'by `rfl`; the pin is wrapped as a typed definitionalIdentity certificate.'),
        'evidence': evidence_certified(
            'RC-RAD1-MEG-01', 'definitionalIdentity', 'marcusEglRateBridge', [
                underlying('PhotoLean.EnergyGapLaw.cert_nrRate',
                           'PhotoLean/EnergyGapLaw/Basic.lean',
                           'delivered Marcus certificate of the energy-gap-law rate'),
                underlying('PhotoLean.Kernel.barrier', 'PhotoLean/Kernel.lean',
                           'shared equal-curvature barrier that both copies unfold to'),
            ],
            ('Both theory copies are pinned to the delivered kernel barrier; the probe performs '
             'the fresh `rfl` check of the two theory-owned terms. The row is the rate-level '
             'bridge between the gap law and the Marcus rate, and the legacy registry’s two '
             'certified records for this pair (rate identity and region equivalence) are '
             're-derived here at statement level.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-MEG-01', 'marcusEglRateBridge',
        ('The legacy registry carries two certified records for this pair '
         '(`rec-D-S12-eg-rate-eq-marcus`, `rec-D-S12-eg-invertedGap-iff-marcus`). They are '
         're-derived here from the delivered declarations, so the package does not depend on the '
         'legacy certificate objects.')),
})

add_query('P-Marcus-EnergyGapLaw', {
    'queryId': 'Q-RAD1-MEG-02',
    'title': 'The energy-gap-law inverted gap is the Marcus inverted region',
    'chemicalQuestion': (
        'Is the gap region in which the energy-gap law’s rate decreases with driving force — the '
        'inverted gap — exactly the Marcus inverted region?'),
    'chemicalRationale': (
        'Both predicates cut the (lam, x) plane at x = lam: above it the barrier grows with the '
        'gap, so the rate falls. The two theories state the same boundary for the same physical '
        'reason (the parabola crossing moves past the reactant minimum), and the energy-gap-law '
        'certificate pins its predicate to the Marcus one. The query asks for the region-level '
        'identity that the rate-level identity of the companion query presupposes.'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-InvertedRegion', 'definition'),
        'target': endpoint('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-InvertedGap', 'definition'),
    },
    'sharedContext': CONTEXTS['EglZoneCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : EglZoneCtx => δ',
            'requirement': 'Both region predicates are evaluated on the same (lam, x).',
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : EglZoneCtx => δ',
            'requirement': 'Both region predicates are evaluated on the same (lam, x).',
        },
    },
    'premises': {
        'predicate': 'fun _ : EglZoneCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The two predicates have the same body, so no premise is load-bearing; the '
                 'boundary point x = lam belongs to neither region on both sides.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-egl-zone'],
    'expectedKind': 'equivalence',
    'expectedKindRationale': ('Two propositions on the same plane are compared; the obligation '
                              'is a two-sided implication, i.e. an equivalence.'),
    'falsificationCondition': ('A pair (lam, x) in exactly one of the two regions would refute '
                               'the equivalence.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `marcusEglZone_iff` is the delivered `cert_invertedGap` read '
                      'backwards; the certificate wraps it as a typed equivalence.'),
        'evidence': evidence_certified(
            'RC-RAD1-MEG-02', 'equivalence', 'marcusEglZoneBridge', [
                underlying('PhotoLean.EnergyGapLaw.cert_invertedGap',
                           'PhotoLean/EnergyGapLaw/Basic.lean',
                           'delivered Marcus certificate of the inverted-gap predicate'),
            ],
            ('The equivalence is delivered at statement level by the energy-gap-law module and '
             're-exported through the probe; the probe does not weaken or strengthen the '
             'predicates.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-MEG-02', 'marcusEglZoneBridge',
        ('The legacy registry’s `rec-D-S12-eg-invertedGap-iff-marcus` is re-derived; the legacy '
         'object is not cited as evidence.')),
})

# P-Marcus-StokesShift ------------------------------------------------------
add_query('P-Marcus-StokesShift', {
    'queryId': 'Q-RAD1-MSS-01',
    'title': 'The emission window is open exactly in the Marcus inverted region',
    'chemicalQuestion': (
        'Does the Stokes emission energy become positive (`0 < emEnergy`) — a vertical photon above '
        'the 0-0 energy — exactly in the Marcus inverted region (`InvertedRegion`, lam < e00), '
        'and is it negative or zero outside that region (normal region e00 < lam, and the '
        'zero-photon corner e00 = lam)?'),
    'chemicalRationale': (
        'The Stokes module computes the vertical absorption and emission energies from the same '
        'displaced-parabola pair that Marcus classifies. Its emission energy is e00 − lam, which '
        'changes sign at e00 = lam — exactly the Marcus region boundary. The delivered row SS-C9 '
        'records the sign identity against `Marcus.InvertedRegion`. The query asks whether the '
        'optical emission-window sign is the Marcus region predicate, which is the one genuine '
        'Marcus/StokesShift statement-level contact (the surfaces are only kernel copies).'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-InvertedRegion', 'definition'),
        'target': endpoint('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition'),
    },
    'sharedContext': CONTEXTS['MarcusSSCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : MarcusSSCtx => δ',
            'requirement': 'The Marcus region predicate is evaluated on (lam, e00) as the driving force pair.',
        },
        'right': {
            'id': 'energy-window',
            'term': 'fun δ : MarcusSSCtx => (δ.lam, δ.e00)',
            'requirement': ('The Stokes emission energy takes the reorganization energy lam and '
                            'the 0-0 energy e00 as its two arguments; the optical observable is '
                            'the sign of that energy, not its magnitude.'),
        },
    },
    'premises': {
        'predicate': 'fun _ : MarcusSSCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The sign identity is total in (lam, e00); the e00 = lam corner has emission '
                 'energy exactly zero on both sides. No premise is load-bearing.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-ss-window'],
    'expectedKind': 'equivalence',
    'expectedKindRationale': ('The obligation is two-sided: the optical sign predicate and the '
                              'region predicate hold at exactly the same points.'),
    'falsificationCondition': ('A pair (lam, e00) at which exactly one of `0 < emEnergy lam e00` '
                               'and `InvertedRegion lam e00` holds — e.g. positive emission '
                               'energy on the normal side, or negative emission energy in the '
                               'inverted region — would refute the equivalence; the corner '
                               'e00 = lam gives emEnergy = 0 on both sides, so it is not a '
                               'counterexample.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `marcusSS_iff` is the delivered `emEnergy_pos_iff_inverted` '
                      'read backwards; the certificate wraps it as a typed equivalence.'),
        'evidence': evidence_certified(
            'RC-RAD1-MSS-01', 'equivalence', 'marcusSSBridge', [
                underlying('PhotoLean.StokesShift.emEnergy_pos_iff_inverted',
                           'PhotoLean/StokesShift/Criterion.lean',
                           'delivered SS-C9 sign row against the Marcus inverted region'),
            ],
            ('The row is the one content-level Marcus/StokesShift contact: the optical '
             'observation channel of the emission window is the Marcus region predicate. It is '
             'not a claim that the Stokes shift magnitude is a Marcus rate or barrier.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-MSS-01', 'marcusSSBridge',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished')),
})

# P-Marcus-ICvsISC ----------------------------------------------------------
add_query('P-Marcus-ICvsISC', {
    'queryId': 'Q-RAD1-MIC-01',
    'title': 'The IC channel rate is the Marcus activated rate',
    'chemicalQuestion': (
        'Is the spin-conserving internal-conversion channel’s rate — Arrhenius over its own '
        'Franck–Condon barrier — the Marcus activated rate at the same pre-exponential factor, '
        'reorganization energy, thermal energy and gap?'),
    'chemicalRationale': (
        'The IC-vs-ISC competition model builds the internal-conversion channel on the same '
        'equal-curvature Franck–Condon barrier that Marcus generalizes, and states its rate in '
        'the Marcus form. The query asks whether the IC channel rate is the Marcus rate, which '
        'is what licenses reading the IC channel’s gap dependence as the Marcus inverted-region '
        'behaviour. It is the rate-level half of the nonradiative-channel identification; the '
        'spin-forbidden ISC channel is explicitly not part of the claim.'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
        'target': endpoint('stmt-ICvsISC-PhotoLean-ICvsISC-icRate', 'definition'),
    },
    'sharedContext': CONTEXTS['MarcusICCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : MarcusICCtx => δ',
            'requirement': 'Both rates are evaluated on the shared parameter tuple.',
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : MarcusICCtx => δ',
            'requirement': ('The IC channel’s reorganization energy and gap are the shared lam '
                            'and x; the IC prefactor is the shared A.'),
        },
    },
    'premises': {
        'predicate': 'fun _ : MarcusICCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The two rate laws are definitionally the same total function; the totalized '
                 'lam = 0 and kB*T = 0 corners are included, so no premise is load-bearing.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-ic-rate'],
    'expectedKind': 'definitionalIdentity',
    'expectedKindRationale': ('The obligation is a fresh `rfl` check of the two translated rate '
                              'terms. The physical claim is the channel identification; the '
                              'certificate records it as a definitional rate identity.'),
    'falsificationCondition': ('A tuple at which the IC rate and the Marcus rate differ would '
                               'refute the identity.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe builds a `DefinitionalPin` of the two translated rate terms and '
                      'wraps it as a typed definitionalIdentity certificate.'),
        'evidence': evidence_certified(
            'RC-RAD1-MIC-01', 'definitionalIdentity', 'marcusICRateBridge', [
                underlying('PhotoLean.ICvsISC.cert_icRate', 'PhotoLean/ICvsISC/Basic.lean',
                           'delivered Marcus certificate of the IC rate'),
                underlying('PhotoLean.Kernel.barrier', 'PhotoLean/Kernel.lean',
                           'shared equal-curvature barrier that both copies unfold to'),
            ],
            ('The IC module’s delivered certificate pins its own barrier and rate copies to the '
             'kernel and Marcus bodies; the probe adds the fresh `rfl` check of the two '
             'theory-owned terms. The legacy registry’s certified record for this pair '
             '(`rec-D-S12-icvscic-icRate-eq-marcus`) is re-derived, not cited.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-MIC-01', 'marcusICRateBridge',
        ('The legacy registry’s certified record is re-derived from the delivered declarations; '
         'the legacy object itself is not cited as evidence.')),
})

# P-Marcus-Forster ----------------------------------------------------------
add_query('P-Marcus-Forster', {
    'queryId': 'Q-RAD1-MFO-01',
    'title': 'Is the Förster transfer rate an activated Marcus step?',
    'chemicalQuestion': (
        'Is the Förster resonance transfer rate — a through-space dipolar process with an R⁻⁶ '
        'distance law and a donor lifetime — the Marcus activated rate at the same driving '
        'force?'),
    'chemicalRationale': (
        'Förster transfer is not an activated crossing: its rate is set by the spectral overlap '
        'and the donor–acceptor separation, and its only energy is the donor transition energy. '
        'Marcus’s rate is an activated barrier over a reaction coordinate with a reorganization '
        'energy and a driving force. The two models share no scalar: a translation from '
        '(tauD, r6, R) to (lam, x) is not a coordinate change of either declared model. The '
        'question is outside the declared jurisdiction, not logically false — and an Arrhenius '
        'shape alone must not be read as identifying a barrier with a transfer geometry.'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
        'target': endpoint('stmt-Forster-PhotoLean-Forster-fretRate', 'definition'),
    },
    'sharedContext': CONTEXTS['MarcusForsterDisjointCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : MarcusForsterDisjointCtx => (δ.A, δ.lam, δ.kB, δ.T, δ.x)',
            'requirement': 'The Marcus tuple is read off the candidate context.',
        },
        'right': {
            'id': 'none-declared',
            'reason': ('No delivered translation maps (tauD, r6, R) to (lam, x): the Förster '
                       'descriptors are a lifetime and a separation, the Marcus descriptors a '
                       'reorganization energy and a driving force.'),
            'requirement': ('The right-side translation is undeclared, which is the jurisdiction '
                            'boundary; the query is therefore recorded as outOfScope rather than '
                            'searched further.'),
        },
    },
    'premises': {
        'predicate': 'fun _ : MarcusForsterDisjointCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('No premise is declared because no comparison is in scope; the candidate '
                 'context exists only to record the two descriptor sets side by side.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-jurisdiction'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The only relation a user could assert is the one-way reading '
                              '“Förster transfer is an activated step”; the record states that '
                              'this reading has no statement-level context.'),
    'falsificationCondition': ('A delivered statement that equates a Förster descriptor with a '
                               'Marcus barrier/rate descriptor would move this pair into scope; '
                               'none exists in the frozen inventory.'),
    'outcome': {
        'status': 'outOfScope',
        'rationale': ('Neither theory’s statements contain the other’s descriptors: Marcus’s '
                      'rate takes (A, lam, kB, T, x); Förster’s takes (tauD, r6, R) and returns '
                      'an R⁻⁶ transfer rate. The delivered §16 registration records the pair as '
                      '“no edge” for exactly this reason.'),
        'evidence': {
            'type': 'jurisdiction',
            'searchLogRef': 'SL-RAD1-MFO-01',
            'jurisdictionRationale': (
                'Statement-level jurisdiction: `PhotoLean.Marcus.rate` is a function of '
                '(A, lam, kB, T, x) only (PhotoLean/Marcus/Basic.lean:55), while '
                '`PhotoLean.Forster.fretRate` is a function of (tauD, r6, R) only '
                '(PhotoLean/Forster/Basic.lean:54). The frozen inventory has no statement whose '
                'signature accepts both descriptor sets, and `PhotoLean/Relations.lean` §16 '
                '(line 964) registers “Forster ↔ Marcus … — no edge” with the reason “the '
                'transfer geometry shares no scalar with the energy-surface family”. A '
                'translation between a donor–acceptor separation and a driving force is not a '
                'coordinate change of either delivered model, so the question lies outside the '
                'declared jurisdiction; this is a jurisdiction record, not a claim that no '
                'physical connection exists.'),
        },
    },
    'provenance': provenance_search(
        'jurisdiction', 'SL-RAD1-MFO-01',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished'),
        statement=('No shared context or declared translation exists: the Marcus rate takes a '
                   'reorganization energy and a driving force, the Forster rate takes a donor '
                   'lifetime and an R^-6 separation. The absence is jurisdictional, not a '
                   'refutation or a logical non-existence claim.')),
})

# P-Marcus-Einstein ---------------------------------------------------------
add_query('P-Marcus-Einstein', {
    'queryId': 'Q-RAD1-MEB-01',
    'title': 'Is the Marcus rate an Einstein spontaneous-emission coefficient?',
    'chemicalQuestion': (
        'Is the Marcus activation-controlled rate the Einstein A coefficient of the same '
        'transition — i.e. is the nonradiative activated step the radiative spontaneous-emission '
        'process?'),
    'chemicalRationale': (
        'The Einstein coefficients describe radiative transitions: A₂₁ is fixed by the radiation-'
        'density factor and the B coefficient, and the radiative lifetime is 1/A. The Marcus '
        'rate is an activated nonradiative step whose scale is set by a barrier and a '
        'pre-exponential factor. The symbol A means a pre-exponential on one side and a '
        'spontaneous-emission coefficient on the other — a notation collision, not a shared '
        'object. The two models have no shared scalar; the only machine contact of the Einstein '
        'side runs through the QuantumYield calculus, which is a different pair.'),
    'endpoints': {
        'source': endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
        'target': endpoint('stmt-Einstein-PhotoLean-Einstein-aOfB', 'definition'),
    },
    'sharedContext': CONTEXTS['MarcusEinsteinDisjointCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : MarcusEinsteinDisjointCtx => (δ.A, δ.lam, δ.kB, δ.T, δ.x)',
            'requirement': 'The Marcus tuple is read off the candidate context.',
        },
        'right': {
            'id': 'none-declared',
            'reason': ('No delivered translation maps (h, c, nu, B21) to (lam, x); the '
                       'radiation-density factor and the driving force are different kinds of '
                       'quantity.'),
            'requirement': 'The right-side translation is undeclared; the query is a jurisdiction record.',
        },
    },
    'premises': {
        'predicate': 'fun _ : MarcusEinsteinDisjointCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': 'No comparison is in scope, so no premise is declared.',
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-jurisdiction'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The candidate relation is the one-way reading “the activated rate '
                              'is the radiative coefficient”; the record states it has no '
                              'statement-level context.'),
    'falsificationCondition': ('A delivered statement equating a Marcus rate/barrier descriptor '
                               'with an Einstein coefficient or radiation factor would move the '
                               'pair into scope; none exists.'),
    'outcome': {
        'status': 'outOfScope',
        'rationale': ('Marcus’s rate is a function of (A, lam, kB, T, x); the Einstein aOfB row '
                      'is a function of (K, B21) where K is the radiation-density factor '
                      '8πhν³/c³. The delivered §16 registration records “no edge” and the only '
                      'Einstein machine contact is the QuantumYield anchor.'),
        'evidence': {
            'type': 'jurisdiction',
            'searchLogRef': 'SL-RAD1-MEB-01',
            'jurisdictionRationale': (
                'Statement-level jurisdiction: `PhotoLean.Marcus.rate` '
                '(PhotoLean/Marcus/Basic.lean:55) takes a barrier and a thermal energy; '
                '`PhotoLean.Einstein.aOfB` (PhotoLean/Einstein/Basic.lean:49) takes a collected '
                'radiation-density factor and a B coefficient. The frozen inventory has no '
                'statement whose signature accepts both, and `PhotoLean/Relations.lean` §16 '
                '(line 969) registers “Einstein ↔ Marcus … — no edge”. The one Einstein row that '
                'touches a rate-level object is `einstein_yield_via_qy` '
                '(PhotoLean/Relations.lean §15), which is a QuantumYield composition, i.e. the '
                'Einstein–QuantumYield pair, not this one. The question is a jurisdiction '
                'boundary, not a refuted claim.'),
        },
    },
    'provenance': provenance_search(
        'jurisdiction', 'SL-RAD1-MEB-01',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished'),
        statement=('No shared context or declared translation exists: the Marcus rate is an '
                   'activated nonradiative step, the Einstein rows are radiative transition '
                   'quantities built from a radiation-density factor. The absence is '
                   'jurisdictional, not a refutation.')),
})

# P-Kasha-KashaVavilov ------------------------------------------------------
add_query('P-Kasha-KashaVavilov', {
    'queryId': 'Q-RAD1-KKV-01',
    'title': 'Kasha’s rule entails the spectral Vavilov rule',
    'chemicalQuestion': (
        'If the ladder satisfies the exact Kasha rule — no emission from levels above the lowest '
        '— do the normalized emission spectra at all excitation levels up to N coincide, i.e. '
        'does Vavilov’s excitation-independence follow?'),
    'chemicalRationale': (
        'Kasha’s rule confines all emission to the lowest excited state; Vavilov’s rule says the '
        'emission spectrum does not depend on the excitation wavelength. The D2 layer separates '
        'these two statements and proves that the first entails the second under the ladder’s '
        'standing physical premises and positive yields: if every upper level has zero radiative '
        'rate, the normalized spectrum is the delta at level 0 at every excitation level. The '
        'query is the pair’s statement-level bridge between the rule and the spectral '
        'invariance, and it is exactly the delivered KV-B7 row.'),
    'endpoints': {
        'source': endpoint('kasha.kashaRule', 'definition'),
        'target': endpoint('stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaVavCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KashaVavCtx => δ',
            'requirement': 'The rule is evaluated on the same ladder and level N.',
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : KashaVavCtx => δ',
            'requirement': ('The spectral predicate is evaluated on the same ladder for every '
                            'M ≤ N against level N.'),
        },
    },
    'premises': {
        'predicate': ('fun δ : KashaVavCtx =>\n'
                      '  PhotoLean.Kasha.RateData δ.rad δ.ic δ.N ∧\n'
                      '  (∀ M, M ≤ δ.N → 0 < PhotoLean.Kasha.fluoYield δ.rad δ.ic M)'),
        'premiseIds': ['kv.rateData', 'kv.fluoYieldPositive'],
        'definitions': [
            {
                'id': 'kv.rateData',
                'predicate': 'PhotoLean.Kasha.RateData δ.rad δ.ic δ.N',
                'statement': ('positive total decay up to N, nonnegative radiative and '
                              'nonradiative rates'),
                'loadBearing': ('consumed to descend the rule to every M ≤ N and to rewrite '
                                'rad i = 0 on the upper levels'),
            },
            {
                'id': 'kv.fluoYieldPositive',
                'predicate': ('∀ M, M ≤ δ.N → 0 < PhotoLean.Kasha.fluoYield δ.rad δ.ic M'),
                'statement': 'the total fluorescence yield is positive at every lower level',
                'loadBearing': ('consumed as the nonvanishing denominator of the normalized '
                                'spectral fraction; without it the fractions are totalized '
                                'divisions with no defined ratio'),
            },
        ],
        'note': ('Both premises are consumed by the delivered KV-B7 proof; the positivity is '
                 'load-bearing exactly because `specFrac` is a totalized division.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-kasha-vav-spec'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The certificate is the one-way implication `KashaRule → SpecSame`: '
                              'the exact Kasha rule entails equality of the normalized spectral '
                              'shapes, and the converse is not claimed. `SpecSame` is a statement '
                              'about spectral shape only; it does not assert that the fluorescence '
                              'yield is constant across excitation levels, and no '
                              'VavilovAt/VavilovUpTo yield-independence claim is attached to it.'),
    'falsificationCondition': ('A ladder satisfying the two premises and the Kasha rule at which '
                               'two levels M ≤ N have different normalized spectra would refute '
                               'the implication.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `kashaVav_sound` applies the delivered KV-B7 row '
                      '`KashaVavilov.specSame_of_kashaRule`; the certificate is a typed '
                      'implication carrying both premises by ID.'),
        'evidence': evidence_certified(
            'RC-RAD1-KKV-01', 'implication', 'kashaVavBridge', [
                underlying('PhotoLean.KashaVavilov.specSame_of_kashaRule',
                           'PhotoLean/KashaVavilov/Basic.lean',
                           'delivered KV-B7 spectral Vavilov row'),
                underlying('PhotoLean.KashaVavilov.specFrac_zero_of_kashaRule',
                           'PhotoLean/KashaVavilov/Basic.lean',
                           'delivered bottom-level spectral fraction used by KV-B7'),
                underlying('PhotoLean.Kasha.kashaRule_iff_rad_zero',
                           'PhotoLean/Kasha/Criterion.lean',
                           'delivered rule-to-radiative-rate form used to descend the rule'),
            ],
            ('The probe consumes the delivered KV-B7 row with its two premises; the row is the '
             'D2 layer’s own statement-level bridge between Kasha’s rule and Vavilov’s spectral '
             'invariance.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-KKV-01', 'kashaVavBridge',
        ('The legacy registry’s certified `rec-kasha-vavilov` D2 record is re-derived here at '
         'the spectral row; the legacy object is not cited as evidence.')),
})

# P-Kasha-EnergyGapLaw ------------------------------------------------------
add_query('P-Kasha-EnergyGapLaw', {
    'queryId': 'Q-RAD1-KEG-01',
    'title': 'The ladder’s Marcus-form IC rate is the energy-gap-law rate',
    'chemicalQuestion': (
        'Is the internal-conversion rate that the Kasha ladder’s Marcus bridge quantifies over — '
        '`marcusIC A lam kB T x` — the energy-gap law’s nonradiative rate at the same '
        'pre-exponential factor, reorganization energy, thermal energy and gap?'),
    'chemicalRationale': (
        'The ladder’s IC channel and the energy-gap law’s nonradiative channel are the same '
        'physical process: an activated crossing whose rate falls as the gap leaves the '
        'reorganization energy. The Kasha module states its channel in the Marcus form '
        '(`marcusIC`) so that its window theorem can speak about gap control; the energy-gap-law '
        'module states the nonradiative rate on the same barrier. The query asks whether the two '
        'are one rate law, which is what lets the Kasha window be read as an energy-gap criterion.'),
    'endpoints': {
        'source': endpoint('stmt-Kasha-PhotoLean-Kasha-marcusIC', 'definition'),
        'target': endpoint('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaEglCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KashaEglCtx => δ',
            'requirement': 'The ladder IC rate is evaluated on the shared parameter tuple.',
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : KashaEglCtx => δ',
            'requirement': 'The energy-gap-law rate is evaluated on the shared parameter tuple.',
        },
    },
    'premises': {
        'predicate': 'fun _ : KashaEglCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('Both bodies are total functions of the same tuple with the same totalized '
                 'divisions; no premise is load-bearing.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-kasha-egl-rate'],
    'expectedKind': 'definitionalIdentity',
    'expectedKindRationale': ('The obligation is a fresh `rfl` check of the two translated rate '
                              'terms, not a propositional equality.'),
    'falsificationCondition': ('A tuple at which the ladder’s Marcus-form IC rate and the '
                               'energy-gap-law rate differ would refute the identity.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe builds a `DefinitionalPin` of the two translated terms and '
                      'wraps it as a typed definitionalIdentity certificate.'),
        'evidence': evidence_certified(
            'RC-RAD1-KEG-01', 'definitionalIdentity', 'kashaEglRateBridge', [
                underlying('PhotoLean.Kasha.marcusIC', 'PhotoLean/Kasha/Compose.lean',
                           'the ladder’s declared Marcus-form IC rate'),
                underlying('PhotoLean.EnergyGapLaw.nrRate', 'PhotoLean/EnergyGapLaw/Basic.lean',
                           'the energy-gap-law nonradiative rate'),
                underlying('PhotoLean.Kernel.barrier', 'PhotoLean/Kernel.lean',
                           'shared equal-curvature barrier that both bodies unfold to'),
            ],
            ('Both theory copies reduce to the same delivered kernel barrier, so the identity is '
             'a genuine model identification of one nonradiative channel, not a comparison of '
             'two unrelated formulas: the IC channel of the ladder is the channel the gap law '
             'describes.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-KEG-01', 'kashaEglRateBridge',
        ('The legacy registry carries only a pair-level notEstablished anchor '
         '(`rec-notestablished-P-Kasha-EnergyGapLaw`); it is coverage history, not an audit '
         'verdict.')),
})

# P-Kasha-StokesShift -------------------------------------------------------
add_query('P-Kasha-StokesShift', {
    'queryId': 'Q-RAD1-KSS-01',
    'title': 'Does the ladder’s radiative emission specify the Stokes band separation?',
    'chemicalQuestion': (
        'Does the Kasha ladder’s radiative channel determine the Stokes band separation of the '
        'same fluorophore — i.e. is the ladder’s emission yield the Stokes-shifted band '
        'position?'),
    'chemicalRationale': (
        'The ladder is a rate-array model: it says how much emission comes from each level and '
        'how the population funnels. The Stokes shift is a band-position observable of the '
        'displaced-parabola pair, computed from the reorganization energy and the 0-0 energy. '
        'The two descriptions have different kinds of arguments (rate arrays versus energy '
        'offsets), and the ladder carries no energy coordinate at all. The question is a '
        'jurisdiction question: no statement-level translation from a rate array to a band '
        'position is declared, so the pair is recorded as outside the frozen query protocol '
        'rather than searched for a forced edge.'),
    'endpoints': {
        'source': endpoint('stmt-Kasha-PhotoLean-Kasha-radBranch', 'definition'),
        'target': endpoint('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaStokesDisjointCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KashaStokesDisjointCtx => (δ.rad, δ.ic)',
            'requirement': 'The ladder is read off the candidate context.',
        },
        'right': {
            'id': 'none-declared',
            'reason': ('No delivered translation maps a rate array (rad, ic) to a pair of '
                       'energies (lam, e00); the codomains have different physical dimensions '
                       'and the ladder has no energy argument.'),
            'requirement': 'The right-side translation is undeclared; the query is a jurisdiction record.',
        },
    },
    'premises': {
        'predicate': 'fun _ : KashaStokesDisjointCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': 'No comparison is in scope, so no premise is declared.',
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-jurisdiction'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The only candidate relation is the one-way reading “the ladder’s '
                              'emission fixes the band separation”; the record states it has no '
                              'statement-level context.'),
    'falsificationCondition': ('A delivered statement taking both a rate array and the parabola '
                               'offsets would move the pair into scope; none exists.'),
    'outcome': {
        'status': 'outOfScope',
        'rationale': ('Kasha’s statements are functions of rate arrays; the Stokes statements '
                      'are functions of (lam, e00). The delivered §16 registration records “no '
                      'edge” for this pair, with the reason “positions of band maxima vs '
                      'rates/ladders”.'),
        'evidence': {
            'type': 'jurisdiction',
            'searchLogRef': 'SL-RAD1-KSS-01',
            'jurisdictionRationale': (
                'Statement-level jurisdiction: `PhotoLean.Kasha.radBranch` '
                '(PhotoLean/Kasha/Basic.lean:79) takes two rate arrays and a level index; '
                '`PhotoLean.StokesShift.emEnergy` (PhotoLean/StokesShift/Basic.lean:80) takes the '
                'reorganization energy and the 0-0 energy. The frozen inventory has no statement '
                'whose signature accepts both, and `PhotoLean/Relations.lean` §16 (line 956) '
                'registers “StokesShift ↔ Kasha … — no edge” because band positions and ladder '
                'rates are different observables. A rate array cannot be translated into a band '
                'position by a coordinate change of either model, so the pair is outside the '
                'declared jurisdiction; the record does not claim that the two descriptions are '
                'physically unrelated.'),
        },
    },
    'provenance': provenance_search(
        'jurisdiction', 'SL-RAD1-KSS-01',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished'),
        statement=('No shared context or declared translation exists: the ladder is a rate-array '
                   'model with no energy coordinate, the Stokes rows are band positions of the '
                   'displaced-parabola pair. The absence is jurisdictional, not a refutation.')),
})

# P-Kasha-ICvsISC -----------------------------------------------------------
add_query('P-Kasha-ICvsISC', {
    'queryId': 'Q-RAD1-KIC-01',
    'title': 'Does the ICvsISC rate law fill the ladder’s inter-level IC channel?',
    'chemicalQuestion': (
        'If the ladder’s inter-level internal-conversion rate is the ICvsISC Arrhenius rate law '
        'evaluated at that step’s own reorganization energy and gap, does Kasha conformance '
        'become an explicit bound on the squared gap?'),
    'chemicalRationale': (
        'Both theories model internal conversion: the ladder as a free per-level rate, the '
        'IC-vs-ISC competition as an Arrhenius law over a Franck–Condon barrier. A bridge needs '
        'the channel assignment `ic 1 = icRate …` as a modelling premise; the delivered ladder '
        'leaves `ic` an arbitrary rate array, so no delivered statement carries that premise. '
        'The candidate composition is precisely the Kasha window theorem (which takes '
        '`ic 1 = marcusIC …`) preceded by the ICvsISC rate certificate. The query is recorded '
        'as unresolved because the missing object is the channel assignment, not a search '
        'result.'),
    'endpoints': {
        'source': endpoint('stmt-Kasha-PhotoLean-Kasha-icBranch', 'definition'),
        'target': endpoint('stmt-ICvsISC-PhotoLean-ICvsISC-icRate', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaICCandidateCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KashaICCandidateCtx => (δ.rad, δ.ic)',
            'requirement': 'The ladder is read off the candidate context.',
        },
        'right': {
            'id': 'candidate-not-total',
            'reason': ('The candidate translation evaluates the ICvsISC rate law at the ladder '
                       'step’s own (lam, x); it is not total because the ladder has no declared '
                       'energy parameters, so the assignment is a modelling premise.'),
            'requirement': ('The translation is recorded as a candidate, which is why the query '
                            'is unresolved rather than certified.'),
        },
    },
    'premises': {
        'predicate': ('fun δ : KashaICCandidateCtx =>\n'
                      '  PhotoLean.Kasha.RateData δ.rad δ.ic δ.N ∧\n'
                      '  δ.ic 1 = PhotoLean.ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x'),
        'premiseIds': ['kic.rateData', 'kic.channelAssignment'],
        'definitions': [
            {
                'id': 'kic.rateData',
                'predicate': 'PhotoLean.Kasha.RateData δ.rad δ.ic δ.N',
                'statement': 'the ladder’s standing physical premises',
                'loadBearing': 'the window row is stated only under RateData',
            },
            {
                'id': 'kic.channelAssignment',
                'predicate': ('δ.ic 1 = PhotoLean.ICvsISC.icRate δ.A δ.lam δ.kB δ.T δ.x'),
                'statement': ('the ladder’s S₂→S₁ channel is the ICvsISC channel law at the '
                              'step’s own reorganization energy and gap'),
                'loadBearing': ('this is the premise the delivery is missing: no delivered row '
                                'instantiates the ladder’s `ic` with a rate law'),
            },
        ],
        'note': ('The second premise is a candidate, not a delivered fact; it is listed so the '
                 'remaining gap is machine-visible.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-candidate-bridge'],
    'expectedKind': 'conditionalComposition',
    'expectedKindRationale': ('The candidate is a two-step entailment: the ICvsISC rate '
                              'certificate followed by the Kasha window row. The record states '
                              'which parent is missing rather than asserting the child.'),
    'falsificationCondition': ('A delivered statement that instantiates the ladder’s `ic` with '
                               'the ICvsISC rate (or otherwise identifies the two channel laws) '
                               'would close the gap and permit the composition.'),
    'outcome': {
        'status': 'unresolved',
        'rationale': ('The two theories share the internal-conversion channel, but the ladder '
                      'stores it as an unconstrained rate array and the ICvsISC module stores it '
                      'as an Arrhenius law. The bridge needs the channel assignment as a '
                      'modelling premise, which no delivered statement states; the search log '
                      'records the searched statements and the exact remaining gap.'),
        'evidence': {
            'type': 'scoped-search',
            'searchLogRef': 'SL-RAD1-KIC-01',
            'candidateSummary': (
                'Candidate: `ic 1 = ICvsISC.icRate A lam kB T x` followed by the delivered Kasha '
                'window row (which accepts `ic 1 = marcusIC …`). The ICvsISC delivered '
                'certificate `cert_icRate` would supply the rate half; the channel assignment '
                'itself is the missing premise.'),
        },
    },
    'provenance': provenance_search(
        'scoped-search', 'SL-RAD1-KIC-01',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished')),
})

# P-Kasha-Forster -----------------------------------------------------------
add_query('P-Kasha-Forster', {
    'queryId': 'Q-RAD1-KFO-01',
    'title': 'Is the ladder’s emission yield the Förster transfer efficiency?',
    'chemicalQuestion': (
        'Is the Kasha ladder’s emission yield of one level the Förster transfer efficiency of '
        'the same excited state — i.e. does the ladder describe energy transfer between two '
        'chromophores?'),
    'chemicalRationale': (
        'The ladder is a single-molecule branching model: excitation enters at level N and '
        'cascades down. Förster transfer is a two-chromophore process controlled by a donor '
        'lifetime, an orientation factor and an R⁻⁶ separation. The ladder has no '
        'donor–acceptor pair, no separation and no lifetime in its arguments, and the Förster '
        'rows have no level structure. The question is outside the declared jurisdiction: the '
        'two models answer different questions, and no statement-level translation turns a level '
        'yield into a transfer efficiency.'),
    'endpoints': {
        'source': endpoint('stmt-Kasha-PhotoLean-Kasha-emitYield', 'definition'),
        'target': endpoint('stmt-Forster-PhotoLean-Forster-fretRate', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaForsterDisjointCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KashaForsterDisjointCtx => (δ.rad, δ.ic)',
            'requirement': 'The ladder is read off the candidate context.',
        },
        'right': {
            'id': 'none-declared',
            'reason': ('No delivered translation maps a level yield (a function of rate arrays '
                       'and two level indices) to a transfer rate (a function of tauD, r6, R).'),
            'requirement': 'The right-side translation is undeclared; the query is a jurisdiction record.',
        },
    },
    'premises': {
        'predicate': 'fun _ : KashaForsterDisjointCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': 'No comparison is in scope, so no premise is declared.',
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-jurisdiction'],
    'expectedKind': 'implication',
    'expectedKindRationale': ('The candidate relation is the one-way reading “the ladder’s '
                              'emission is the transfer process”; the record states it has no '
                              'statement-level context.'),
    'falsificationCondition': ('A delivered statement that gives the ladder a donor–acceptor '
                               'pair or a lifetime would move the pair into scope; none exists.'),
    'outcome': {
        'status': 'outOfScope',
        'rationale': ('Kasha’s emission yields are functions of rate arrays and level indices; '
                      'Förster’s transfer rate is a function of a donor lifetime and an R⁻⁶ '
                      'separation. The delivered §16 registration records “no edge”.'),
        'evidence': {
            'type': 'jurisdiction',
            'searchLogRef': 'SL-RAD1-KFO-01',
            'jurisdictionRationale': (
                'Statement-level jurisdiction: `PhotoLean.Kasha.emitYield` '
                '(PhotoLean/Kasha/Basic.lean:91) takes two rate arrays and two level indices; '
                '`PhotoLean.Forster.fretRate` (PhotoLean/Forster/Basic.lean:54) takes (tauD, r6, '
                'R). The frozen inventory has no statement accepting both, and '
                '`PhotoLean/Relations.lean` §16 (line 964) registers “Forster ↔ … Kasha … — no '
                'edge” because the transfer geometry shares no scalar with the ladder. The '
                'record is a jurisdiction boundary: the ladder is not claimed to be unable to '
                'participate in transfer, only that the frozen statements declare no such '
                'relation.'),
        },
    },
    'provenance': provenance_search(
        'jurisdiction', 'SL-RAD1-KFO-01',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished'),
        statement=('No shared context or declared translation exists: the ladder is a '
                   'single-molecule branching model with no donor-acceptor pair, the Forster rows '
                   'are a two-chromophore transfer geometry. The absence is jurisdictional, not a '
                   'refutation.')),
})

# P-Kasha-Einstein ----------------------------------------------------------
add_query('P-Kasha-Einstein', {
    'queryId': 'Q-RAD1-KEB-01',
    'title': 'The lowest-level radiative branch is the Einstein A·τ radiative fraction',
    'chemicalQuestion': (
        'Is the Kasha ladder’s radiative branch at the lowest level — with radiative rate A and '
        'total nonradiative loss kNR — the Einstein-side radiative fraction A·τ, where τ = '
        '1/(A + kNR) is the observed lifetime?'),
    'chemicalRationale': (
        'The ladder’s bottom level decays radiatively at A and nonradiatively at kNR, so its '
        'radiative branch is A/(A + kNR). The Einstein description writes the same fraction as '
        'the spontaneous-emission coefficient times the observed lifetime. The query asks '
        'whether the two theories report the same radiative fraction of the same two-channel '
        'decay — an optical observable — rather than whether the ladder’s emission rate is the '
        'A coefficient itself (which the Marcus/Einstein jurisdiction record rejects).'),
    'endpoints': {
        'source': endpoint('stmt-Kasha-PhotoLean-Kasha-radBranch', 'definition'),
        'target': endpoint('stmt-Einstein-PhotoLean-Einstein-tauR', 'definition'),
    },
    'sharedContext': CONTEXTS['KashaEinsteinCtx'],
    'translations': {
        'left': {
            'id': 'descriptor-endpoint',
            'term': ('fun δ : KashaEinsteinCtx =>\n'
                     '  (fun _ : ℕ => δ.A, fun _ : ℕ => δ.kNR, 0)'),
            'requirement': ('The ladder’s rate arrays are the constant radiative and '
                            'nonradiative channels of one state, evaluated at level 0.'),
        },
        'right': {
            'id': 'descriptor-endpoint',
            'term': 'fun δ : KashaEinsteinCtx => (δ.A, δ.A + δ.kNR)',
            'requirement': ('The Einstein A coefficient is the ladder’s radiative rate; the '
                            'lifetime denominator is the same total decay A + kNR.'),
        },
    },
    'premises': {
        'predicate': 'fun _ : KashaEinsteinCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The identity holds at every (A, kNR) as a totalized-division identity; the '
                 'A + kNR = 0 corner is included, so no positivity premise is load-bearing.'),
    },
    'observationChannels': [
        {
            'id': 'lowestLevelRadiativeFraction',
            'name': 'lowestLevelRadiativeFraction',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': ('fun δ _ => PhotoLean.Kasha.radBranch\n'
                        '  (fun _ => δ.A) (fun _ => δ.kNR) 0'),
            'rightObs': 'fun δ _ => δ.A * PhotoLean.Einstein.tauR (δ.A + δ.kNR)',
        },
    ],
    'scope': SCOPES['scope-RAD1-kasha-einstein'],
    'expectedKind': 'observationalEquivalence',
    'expectedKindRationale': ('Both sides are real-valued observables on the same context; the '
                              'certificate is equality of the declared radiative-fraction '
                              'channel at every context point.'),
    'falsificationCondition': ('A pair (A, kNR) at which the radiative branch and A·τ differ '
                               'would refute the observational equivalence.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `kashaEinstein_eq` proves the channel equality by `mul_one_div` '
                      'after unfolding both definitions; the certificate is a typed '
                      'observationalEquivalence with one channel.'),
        'evidence': evidence_certified(
            'RC-RAD1-KEB-01', 'observationalEquivalence', 'kashaEinsteinBridge', [
                underlying('PhotoLean.Kasha.radBranch', 'PhotoLean/Kasha/Basic.lean',
                           'the ladder’s radiative branch definition'),
                underlying('PhotoLean.Einstein.tauR', 'PhotoLean/Einstein/Basic.lean',
                           'the Einstein radiative lifetime 1/A'),
            ],
            ('The equality is the algebraic content of “A·τ is the radiative yield”; it is a '
             'real observation-channel identity on the same two-channel decay, and the '
             'translation names the two channel assignments explicitly.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-KEB-01', 'kashaEinsteinBridge',
        LEGACY_PAIR_ANCHOR.format(status='notEstablished')),
})

# P-KashaVavilov-SternVolmer ------------------------------------------------
add_query('P-KashaVavilov-SternVolmer', {
    'queryId': 'Q-RAD1-VSV-01',
    'title': 'Dynamic quenching dilutes only the ladder’s bottom emission channel',
    'chemicalQuestion': (
        'Does a collisional quencher that adds kq·[Q] to the ladder’s level-0 decay dilute the '
        'bottom emission channel by exactly the Stern–Volmer ratio of the unquenched level-0 '
        'decay, while leaving the upper-block leak — the quantity Vavilov’s law is about — '
        'unchanged?'),
    'chemicalRationale': (
        'Dynamic quenching competes with the bottom level’s own decay; the upper levels of the '
        'ladder relax internally and are not quenched. The ladder’s total yield splits (the '
        'delivered KashaVavilov row) into the bottom emission and the upper leak. Since the leak '
        'is invariant and the bottom radiative branch is diluted by (k0 + kq·q)/k0 with k0 the '
        'unquenched level-0 decay, the bottom-emission channel is exactly quench-covariant. This '
        'is the statement-level form of the SternVolmer–QuantumYield dilution row, read on the '
        'ladder’s own decomposition: it tells which part of the KashaVavilov yield the quencher '
        'moves.'),
    'endpoints': {
        'source': endpoint(
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-fluoYield_eq_emitYield_zero_add_upperYield',
            'theorem'),
        'target': endpoint('sternvolmer.intensityDyn', 'definition'),
    },
    'sharedContext': CONTEXTS['KvSvCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KvSvCtx => δ',
            'requirement': 'The ladder is evaluated on the shared context; the upper leak term is shared.',
        },
        'right': {
            'id': 'observational-setup',
            'term': ('fun δ : KvSvCtx =>\n'
                     '  (PhotoLean.Kasha.decay δ.rad δ.ic 0, δ.kq, δ.q)'),
            'requirement': ('The Stern–Volmer ratio is evaluated at the *unquenched* level-0 '
                            'total decay, the quencher rate and the concentration.'),
        },
    },
    'premises': {
        'predicate': ('fun δ : KvSvCtx =>\n'
                      '  0 < δ.rad 0 + δ.ic 0 ∧ 0 ≤ δ.kq * δ.q'),
        'premiseIds': ['kvSv.levelZeroDecayPositive', 'kvSv.quenchChannelNonnegative'],
        'definitions': [
            {
                'id': 'kvSv.levelZeroDecayPositive',
                'predicate': '0 < δ.rad 0 + δ.ic 0',
                'statement': 'the unquenched level-0 total decay is positive',
                'loadBearing': ('consumed as the nonzero denominator of the Stern–Volmer ratio '
                                'and of the radiative branch'),
            },
            {
                'id': 'kvSv.quenchChannelNonnegative',
                'predicate': '0 ≤ δ.kq * δ.q',
                'statement': 'the collisional channel is a loss channel',
                'loadBearing': ('consumed to keep the quenched level-0 decay positive so the '
                                'quenched radiative branch has a nonzero denominator'),
            },
        ],
        'note': ('Both premises are consumed by `kvSv_branch`; neither is decorative.'),
    },
    'observationChannels': [
        {
            'id': 'bottomEmissionChannelUnderQuench',
            'name': 'bottomEmissionChannelUnderQuench',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': ('fun δ _ => PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N -\n'
                        '  PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N'),
            'rightObs': ('fun δ _ =>\n'
                         '  (PhotoLean.Kasha.fluoYield δ.rad\n'
                         '      (PhotoLean.RelationAudit.BoundedAudit.RAD1.quenchIC δ.ic δ.kq δ.q) δ.N -\n'
                         '    PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N) *\n'
                         '  PhotoLean.SternVolmer.svRatioDyn (δ.rad 0 + δ.ic 0) δ.kq δ.q'),
        },
    ],
    'scope': SCOPES['scope-RAD1-kv-sv-quench'],
    'expectedKind': 'observationalEquivalence',
    'expectedKindRationale': ('Both sides are real-valued observables on the same ladder; the '
                              'certificate is equality of the declared bottom-emission channel '
                              'at every context point satisfying the two premises.'),
    'falsificationCondition': ('A context at which the bottom-emission channel and the '
                               'Stern–Volmer-diluted quenched channel differ would refute the '
                               'observational equivalence.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe proves the upper-leak invariance (`kvSv_upper_invariant`), the '
                      'funnel-transmission invariance (`kvSv_cascade_invariant`), the branch '
                      'dilution (`kvSv_branch`) and the channel equality (`kvSv_dilution`); the '
                      'certificate is a typed observationalEquivalence with one channel.'),
        'evidence': evidence_certified(
            'RC-RAD1-VSV-01', 'observationalEquivalence', 'kvSvBridge', [
                underlying('PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield',
                           'PhotoLean/KashaVavilov/Basic.lean',
                           'delivered KV-B2 total-yield split consumed on both quench states'),
                underlying('PhotoLean.SternVolmer.svRatioDyn', 'PhotoLean/SternVolmer/Basic.lean',
                           'the dynamic Stern–Volmer ratio (decay ratio)'),
                underlying('PhotoLean.Relations.sv_quench_dilutes_yield',
                           'PhotoLean/Relations.lean',
                           'delivered SternVolmer→QuantumYield dilution row (source coherence '
                           'for the same physical claim at the QY level)'),
            ],
            ('The certificate proves the ladder-level composition directly: the leak is '
             'invariant because it sums levels 1..N, the funnel transmission is invariant '
             'because it multiplies levels 1..N, and the bottom branch scales by the '
             'Stern–Volmer ratio. It is not a wrapper around the QY-level dilution row; that '
             'row is cited for coherence only.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-VSV-01', 'kvSvBridge',
        ('The legacy registry carries only a pair-level undelivered-candidate anchor '
         '(`rec-candidate-P-KashaVavilov-SternVolmer`); it is coverage history, not an audit '
         'verdict.')),
})

# P-KashaVavilov-QuantumYield -----------------------------------------------
add_query('P-KashaVavilov-QuantumYield', {
    'queryId': 'Q-RAD1-VQY-01',
    'title': 'The ladder yield is the level-0 quantum yield transported by the funnel plus the leak',
    'chemicalQuestion': (
        'Is the KashaVavilov total fluorescence yield the two-channel quantum yield of the '
        'lowest level, multiplied by the funnel transmission to that level, plus the upper-block '
        'leak?'),
    'chemicalRationale': (
        'The KashaVavilov total-yield row splits the fluorescence yield into the lowest level’s '
        'emission and the upper leak. The lowest level’s emission is a radiative branch times '
        'the probability of reaching level 0 without emitting — and that branch is exactly the '
        'two-channel quantum yield of the level-0 rate pair (the delivered Kasha–QuantumYield '
        'row). The query asks whether the ladder’s yield is therefore an algebraic composition '
        'of the QuantumYield calculus and the ladder’s own funnel transmission. It is a '
        'decomposition identity, not a new yield law.'),
    'endpoints': {
        'source': endpoint(
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-fluoYield_eq_emitYield_zero_add_upperYield',
            'theorem'),
        'target': endpoint('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf', 'definition'),
    },
    'sharedContext': CONTEXTS['KvQyCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KvQyCtx => δ',
            'requirement': 'The ladder is evaluated on the shared context.',
        },
        'right': {
            'id': 'descriptor-endpoint',
            'term': ('fun δ : KvQyCtx =>\n'
                     '  (![δ.rad 0, δ.ic 0], (0 : Fin 2))'),
            'requirement': ('The quantum-yield calculus is applied to the level-0 rate pair and '
                            'its radiative channel 0.'),
        },
    },
    'premises': {
        'predicate': 'fun _ : KvQyCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The decomposition holds as a totalized-division identity at every ladder and '
                 'level; no premise is load-bearing.'),
    },
    'observationChannels': [
        {
            'id': 'ladderYieldDecomposition',
            'name': 'ladderYieldDecomposition',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': 'fun δ _ => PhotoLean.Kasha.fluoYield δ.rad δ.ic δ.N',
            'rightObs': ('fun δ _ =>\n'
                         '  PhotoLean.QuantumYield.yieldOf ![δ.rad 0, δ.ic 0] 0 *\n'
                         '    PhotoLean.Kasha.cascade δ.rad δ.ic 0 δ.N +\n'
                         '  PhotoLean.Kasha.upperYield δ.rad δ.ic δ.N'),
        },
    ],
    'scope': SCOPES['scope-RAD1-kv-qy-decomp'],
    'expectedKind': 'observationalEquivalence',
    'expectedKindRationale': ('Both sides are real-valued observables on the same ladder; the '
                              'certificate is equality of the declared decomposition channel at '
                              'every context point.'),
    'falsificationCondition': ('A ladder and level at which the total yield differs from the '
                               'composed expression would refute the decomposition.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `kvQy_decomposition` rewrites the delivered KV-B2 split and '
                      'the delivered Kasha→QuantumYield branch row; the certificate is a typed '
                      'observationalEquivalence with one channel.'),
        'evidence': evidence_certified(
            'RC-RAD1-VQY-01', 'observationalEquivalence', 'kvQyBridge', [
                underlying('PhotoLean.KashaVavilov.fluoYield_eq_emitYield_zero_add_upperYield',
                           'PhotoLean/KashaVavilov/Basic.lean',
                           'delivered KV-B2 total-yield split'),
                underlying('PhotoLean.Relations.kasha_radBranch_eq_yieldOf',
                           'PhotoLean/Relations.lean',
                           'delivered Kasha→QuantumYield two-channel yield row'),
                underlying('PhotoLean.Kasha.cascade', 'PhotoLean/Kasha/Basic.lean',
                           'the ladder’s funnel transmission to level 0'),
            ],
            ('The certificate consumes the two delivered rows; the decomposition is the '
             'yield-level content of the KashaVavilov/QuantumYield contact. It states how the '
             'ladder’s yield is built from the QuantumYield calculus, and it makes explicit that '
             'the upper-block leak is not part of the level-0 quantum yield.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-VQY-01', 'kvQyBridge',
        ('The legacy registry carries only a pair-level undelivered-candidate anchor '
         '(`rec-candidate-P-KashaVavilov-QuantumYield`); it is coverage history, not an audit '
         'verdict.')),
})

# P-KashaVavilov-FluorPhos ------------------------------------------------
add_query('P-KashaVavilov-FluorPhos', {
    'queryId': 'Q-RAD1-VFP-01',
    'title': 'The coarse-grained ladder yield is the FluorPhos fluorescence yield',
    'chemicalQuestion': (
        'Under the channel-lumping translation — the ladder’s radiative channel is the '
        'fluorescence rate kF and its nonradiative channel carries the summed ISC + IC loss — is '
        'the ladder’s bottom-level fluorescence yield the FluorPhos S₁ fluorescence yield?'),
    'chemicalRationale': (
        'FluorPhos resolves the S₁ decay into three channels (kF, kISC, kIC); the Kasha ladder '
        'resolves it into two (radiative, nonradiative). Lumping the two nonradiative channels '
        'into the ladder’s single loss rate gives rad 0 = kF and ic 0 = kISC + kIC, and then the '
        'ladder’s total yield at level 0 — which is just its bottom-level radiative branch — is '
        'kF/(kF + kISC + kIC), the FluorPhos fluorescence yield. The query asks whether the '
        'coarse-grained ladder and the three-channel competition model report the same '
        'fluorescence yield, which is the exact content of the lumping hypothesis.'),
    'endpoints': {
        'source': endpoint(
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-fluoYield_eq_emitYield_zero_add_upperYield',
            'theorem'),
        'target': endpoint('stmt-FluorPhos-PhotoLean-FluorPhos-phiF', 'definition'),
    },
    'sharedContext': CONTEXTS['KvFpCtx'],
    'translations': {
        'left': {
            'id': 'descriptor-endpoint',
            'term': ('fun δ : KvFpCtx =>\n'
                     '  (fun n => if n = 0 then δ.kF else 0,\n'
                     '   fun n => if n = 0 then δ.kISC + δ.kIC else 0, 0)'),
            'requirement': ('The ladder’s rate arrays are the lumped S₁ channels; the level is 0, '
                            'where no upper level exists.'),
        },
        'right': {
            'id': 'identity',
            'term': 'fun δ : KvFpCtx => δ',
            'requirement': 'The FluorPhos yield is evaluated on the three S₁ channels.',
        },
    },
    'premises': {
        'predicate': 'fun _ : KvFpCtx => True',
        'premiseIds': [],
        'definitions': [],
        'note': ('The identity holds at every (kF, kISC, kIC) as a totalized-division identity; '
                 'the lumping is carried by the translation, not by a premise, because it is '
                 'the declared channel correspondence.'),
    },
    'observationChannels': [
        {
            'id': 'bottomLevelFluorescenceYield',
            'name': 'bottomLevelFluorescenceYield',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': ('fun δ _ =>\n'
                        '  PhotoLean.Kasha.fluoYield\n'
                        '    (fun n => if n = 0 then δ.kF else 0)\n'
                        '    (fun n => if n = 0 then δ.kISC + δ.kIC else 0) 0'),
            'rightObs': 'fun δ _ => PhotoLean.FluorPhos.phiF δ.kF δ.kISC δ.kIC',
        },
    ],
    'scope': SCOPES['scope-RAD1-kv-fp-lump'],
    'expectedKind': 'observationalEquivalence',
    'expectedKindRationale': ('Both sides are real-valued observables on the same S₁ state; the '
                              'certificate is equality of the declared fluorescence-yield '
                              'channel under the stated lumping translation.'),
    'falsificationCondition': ('A triple (kF, kISC, kIC) at which the lumped ladder yield and '
                               'the FluorPhos yield differ would refute the equivalence.'),
    'outcome': {
        'status': 'certified',
        'rationale': ('The probe’s `kvFp_lumped` unfolds both yields and closes the identity '
                      'by `ring`; the certificate is a typed observationalEquivalence with one '
                      'channel.'),
        'evidence': evidence_certified(
            'RC-RAD1-VFP-01', 'observationalEquivalence', 'kvFpBridge', [
                underlying('PhotoLean.Kasha.fluoYield', 'PhotoLean/Kasha/Basic.lean',
                           'the ladder total yield (at level 0 the single bottom branch)'),
                underlying('PhotoLean.FluorPhos.phiF', 'PhotoLean/FluorPhos/Basic.lean',
                           'the three-channel S₁ fluorescence yield'),
                underlying('PhotoLean.FluorPhos.s1Decay', 'PhotoLean/FluorPhos/Basic.lean',
                           'the S₁ total decay kF + kISC + kIC'),
            ],
            ('The row is the exact statement-level content of the coarse-graining hypothesis: '
             'the ladder’s two-channel bottom branch with the lumped loss is the three-channel '
             'FluorPhos yield. The lumping is in the translation, so a reader can reject the '
             'translation without rejecting the algebra.')),
    },
    'provenance': provenance_certified(
        'RC-RAD1-VFP-01', 'kvFpBridge',
        ('The legacy registry carries only a pair-level undelivered-candidate anchor '
         '(`rec-candidate-P-KashaVavilov-FluorPhos`); it is coverage history, not an audit '
         'verdict.')),
})

# P-KashaVavilov-EnergyGapLaw ---------------------------------------------
add_query('P-KashaVavilov-EnergyGapLaw', {
    'queryId': 'Q-RAD1-VEG-01',
    'title': 'Does the energy-gap law decide when the Vavilov invariance breaks?',
    'chemicalQuestion': (
        'Does the energy-gap law’s nonradiative rate, once it fills the ladder’s conversion '
        'channel, decide whether the ladder keeps the Vavilov invariance or becomes anti-Kasha?'),
    'chemicalRationale': (
        'The energy-gap law is the gap dependence of the nonradiative rate; the KashaVavilov '
        'layer states when the ladder departs from the lowest-state spectrum. Their composition '
        'would be: gap-law rate → ladder conversion rate → upper yield → anti-Kasha observable. '
        'The delivered pieces are the gap-law rate identity to Marcus (in the EnergyGapLaw '
        'module), the Kasha window row (stated with the Kasha-side `marcusIC` object), and the '
        'D2 anti-Kasha boundary. What is missing is a delivered statement that carries the '
        'gap-law rate into the ladder and out to the Vavilov predicate; the delivered '
        'EnergyGapLaw§16 registration lists KashaVavilov as an undelivered composition '
        'candidate. The query is therefore unresolved with the gap recorded precisely.'),
    'endpoints': {
        'source': endpoint(
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-antiKasha_observable_iff', 'theorem'),
        'target': endpoint('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition'),
    },
    'sharedContext': CONTEXTS['KvEglCandidateCtx'],
    'translations': {
        'left': {
            'id': 'identity',
            'term': 'fun δ : KvEglCandidateCtx => (δ.rad, δ.ic)',
            'requirement': 'The ladder is read off the candidate context.',
        },
        'right': {
            'id': 'candidate-not-total',
            'reason': ('The gap-law rate is a function of (A, lam, kB, T, x); the ladder is a '
                       'function of rate arrays. The candidate translation fills the ladder’s '
                       'channel with the gap-law rate, which no delivered statement declares.'),
            'requirement': ('The translation is a candidate, which is why the query is '
                            'unresolved rather than certified.'),
        },
    },
    'premises': {
        'predicate': ('fun δ : KvEglCandidateCtx =>\n'
                      '  PhotoLean.Kasha.RateData δ.rad δ.ic δ.N ∧\n'
                      '  δ.ic 1 = PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x'),
        'premiseIds': ['veg.rateData', 'veg.channelAssignment'],
        'definitions': [
            {
                'id': 'veg.rateData',
                'predicate': 'PhotoLean.Kasha.RateData δ.rad δ.ic δ.N',
                'statement': 'the ladder’s standing physical premises',
                'loadBearing': 'the window and boundary rows are stated only under RateData',
            },
            {
                'id': 'veg.channelAssignment',
                'predicate': ('δ.ic 1 = PhotoLean.EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x'),
                'statement': 'the ladder’s conversion channel is the energy-gap-law rate',
                'loadBearing': ('the missing delivered row: no statement instantiates the '
                                'ladder’s channel with the gap-law rate'),
            },
        ],
        'note': ('The second premise is the exact remaining gap; it is listed so the search '
                 'result is machine-visible rather than prose only.'),
    },
    'observationChannels': [],
    'scope': SCOPES['scope-RAD1-candidate-bridge'],
    'expectedKind': 'conditionalComposition',
    'expectedKindRationale': ('The candidate is a multi-step entailment (gap-law rate → ladder '
                              'channel → window → anti-Kasha). The record states which parent '
                              'is missing rather than asserting the child.'),
    'falsificationCondition': ('A delivered statement that fills the ladder’s channel with the '
                               'gap-law rate, or that states the Vavilov predicate directly in '
                               'terms of the gap-law rate, would close the gap.'),
    'outcome': {
        'status': 'unresolved',
        'rationale': ('The composition is chemically well posed but the delivered rows do not '
                      'carry it: the window theorem is stated with `Kasha.marcusIC`, the '
                      'gap-law rate lives in `EnergyGapLaw.nrRate`, and no statement bridges the '
                      'ladder’s `ic` array to either. The search log records the searched '
                      'statements and the exact missing parent.'),
        'evidence': {
            'type': 'scoped-search',
            'searchLogRef': 'SL-RAD1-VEG-01',
            'candidateSummary': (
                'Candidate: `ic 1 = EnergyGapLaw.nrRate A lam kB T x`, then the delivered '
                'Kasha window row (after the definitional gap-law/Marcus rate identity), then '
                '`KashaVavilov.antiKasha_observable_iff`. The missing parent is the ladder '
                'channel assignment; no delivered statement states it.'),
        },
    },
    'provenance': provenance_search(
        'scoped-search', 'SL-RAD1-VEG-01',
        ('The legacy registry carries only a pair-level undelivered-candidate anchor '
         '(`rec-candidate-P-KashaVavilov-EnergyGapLaw`); it is coverage history, not an audit '
         'verdict.')),
})


# --------------------------------------------------------------------------- search log

def search_entry(query_id, search_id, statements, kinds, contexts, deps, commands,
                 strategies, candidates, gap, recompute, rationale, jurisdiction=None):
    pair_id = next(q['pairId'] for q in QUERIES if q['queryId'] == query_id)
    status = next(q['outcome']['status'] for q in QUERIES if q['queryId'] == query_id)
    entry = {
        'searchId': search_id,
        'queryId': query_id,
        'pairId': pair_id,
        'status': status,
        'scope': SCOPES['scope-RAD1-jurisdiction' if status == 'outOfScope'
                        else 'scope-RAD1-candidate-bridge']['id'],
        'snapshot': SNAP_ID,
        'searchedStatements': statements,
        'searchedKinds': kinds,
        'contextsConsidered': contexts,
        'dependenciesConsulted': deps,
        'commands': commands,
        'strategiesAttempted': strategies,
        'candidateEvidence': candidates,
        'remainingGap': gap,
        'recomputeCommands': recompute,
        'rationale': rationale,
    }
    if jurisdiction is not None:
        entry['jurisdictionReason'] = jurisdiction
    return entry


SEARCH_ENTRIES = [
    search_entry(
        'Q-RAD1-MFO-01', 'SL-RAD1-MFO-01',
        ['stmt-Marcus-PhotoLean-Marcus-rate', 'marcus.barrier',
         'stmt-Forster-PhotoLean-Forster-fretRate', 'stmt-Forster-PhotoLean-Forster-fretEff6'],
        ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence',
         'conditionalComposition'],
        ['MarcusForsterDisjointCtx (A, lam, kB, T, x | tauD, r6, R): two descriptor sets with no '
         'declared translation'],
        [
            {'artifact': 'PhotoLean/Marcus/Basic.lean', 'locator': 'lines 50-55 (barrier, rate)',
             'finding': 'The Marcus descriptors are the reorganization energy, the thermal energy '
                        'and the driving force; there is no distance or lifetime argument.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'lines 44-57 (kappaSq, fretRate, fretEff6)',
             'finding': 'The Förster descriptors are an orientation factor, a donor lifetime and '
                        'an R^-6 separation; there is no barrier, driving force or reorganization '
                        'energy argument.'},
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 964: Forster / Marcus no edge',
             'finding': 'The delivered register states that the transfer geometry shares no scalar '
                        'with the energy-surface family; the only Forster machine rows are the SV '
                        'look-alike and the QuantumYield composition.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Marcus-Forster',
             'finding': 'The legacy record is a pair-level notEstablished anchor, not a named query.'},
        ],
        [
            {'command': "grep -rn 'Forster' PhotoLean/Marcus --include='*.lean'",
             'purpose': 'Search the Marcus modules for any delivered Förster statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Marcus' PhotoLean/Forster --include='*.lean'",
             'purpose': 'Search the Förster modules for any delivered Marcus statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rh '^import' PhotoLean/Marcus/*.lean PhotoLean/Forster/*.lean | sort -u",
             'purpose': 'Measure the module dependency closure of both sides.',
             'result': 'Mathlib plus each theory’s own modules only; no cross import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Marcus-Forster',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False; no disposition row."},
        ],
        [
            {'strategy': 'Read the Marcus rate as an activated transfer step by identifying the '
                         'driving force with the donor-acceptor separation.',
             'outcome': 'The identification is a dimensional mismatch: a separation is not a '
                        'driving force, and no delivered statement declares the map.'},
            {'strategy': 'Look for a barrier or reorganization energy inside the Förster rate.',
             'outcome': 'The Förster rate has no barrier term; its gap dependence enters only '
                        'through the spectral overlap, which the module collects into r0six.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        [
            {'kind': 'dipolar-transfer-versus-activated-step candidate',
             'statement': 'Marcus.rate A lam kB T x versus Forster.fretRate tauD r6 R; both are '
                          'rate laws, so a rate-level comparison looks plausible.',
             'status': 'candidate rejected: the shared word “rate” is not a shared object, and '
                       'the Arrhenius shape does not identify a barrier with a transfer geometry.'},
        ],
        ('A delivered statement that accepts both a Marcus descriptor and a Förster descriptor, '
         'or that derives a Marcus barrier from tauD, r6, R, is missing; until it exists the pair '
         'has no statement-level context to compare.'),
        ["grep -rn 'Forster' PhotoLean/Marcus --include='*.lean'",
         "grep -rn 'Marcus' PhotoLean/Forster --include='*.lean'",
         'python3 tools/relation_audit_registry.py --explain-pair P-Marcus-Forster'],
        ('The two models answer different questions and share no scalar. The honest status is '
         'outOfScope with a statement-level jurisdiction record, not refuted and not unresolved: '
         'there is no candidate bridge whose missing premise could be stated inside either '
         'theory.'),
        jurisdiction=('PhotoLean.Marcus.rate (A, lam, kB, T, x) and '
                      'PhotoLean.Forster.fretRate (tauD, r6, R) have disjoint descriptor sets; '
                      'no inventory statement accepts both, and §16 line 964 registers the pair '
                      'as no edge. A translation between a separation and a driving force is not '
                      'a coordinate change of either delivered model.'),

    ),
    search_entry(
        'Q-RAD1-MEB-01', 'SL-RAD1-MEB-01',
        ['stmt-Marcus-PhotoLean-Marcus-rate', 'stmt-Einstein-PhotoLean-Einstein-aOfB',
         'stmt-Einstein-PhotoLean-Einstein-tauR', 'stmt-Einstein-PhotoLean-Einstein-radFactor'],
        ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence',
         'conditionalComposition'],
        ['MarcusEinsteinDisjointCtx (A, lam, kB, T, x | h, c, nu, B21): the symbol A is a '
         'pre-exponential on one side and a spontaneous-emission coefficient on the other'],
        [
            {'artifact': 'PhotoLean/Marcus/Basic.lean', 'locator': 'lines 50-55 (barrier, rate)',
             'finding': 'The Marcus rate is A * exp(-barrier/(kB*T)); its A is a free prefactor, '
                        'not the Einstein A coefficient.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'lines 44-65 (radFactor, aOfB, tauR)',
             'finding': 'The Einstein rows build the spontaneous-emission coefficient from a '
                        'radiation-density factor and a B coefficient; no thermal activation or '
                        'driving force occurs.'},
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 969: Einstein / Marcus no edge',
             'finding': 'The register states the only Einstein machine contact is the '
                        'QuantumYield anchor (einstein_yield_via_qy), i.e. a different pair.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Marcus-Einstein',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        [
            {'command': "grep -rn 'Einstein' PhotoLean/Marcus --include='*.lean'",
             'purpose': 'Search the Marcus modules for any delivered Einstein statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Marcus' PhotoLean/Einstein --include='*.lean'",
             'purpose': 'Search the Einstein modules for any delivered Marcus statement.',
             'result': 'One docstring reference in RatModel.lean:22 (a norm_num remark); no '
                       'declaration and no import.'},
            {'command': "grep -rh '^import' PhotoLean/Einstein/*.lean | sort -u",
             'purpose': 'Measure the Einstein module dependencies.',
             'result': 'Mathlib plus Einstein’s own modules only; no Marcus import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Marcus-Einstein',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False; no disposition row."},
        ],
        [
            {'strategy': 'Read the Marcus rate as the spontaneous-emission rate of the same '
                         'transition (A_prefactor = A_Einstein).',
             'outcome': 'The two As have different roles: one is an overall prefactor of an '
                        'activated rate, the other is the radiative decay coefficient built from '
                        'a radiation-density factor. No delivered statement equates them.'},
            {'strategy': 'Compose through QuantumYield (the Einstein yield anchor) and then to '
                         'the Marcus rate as a channel rate.',
             'outcome': 'The composition exists for the Einstein-QuantumYield pair '
                        '(einstein_yield_via_qy) and for the Marcus-QuantumYield pair, but that '
                        'is a different edge; using it here would substitute a third theory for '
                        'the pair’s own statements.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        [
            {'kind': 'radiative-versus-activated rate candidate',
             'statement': 'Marcus.rate and Einstein.aOfB are both real-valued rate-like laws, so a '
                          'rate-level identity looks possible.',
             'status': 'candidate rejected: the shared codomain ℝ is not a shared observable; the '
                       'radiation-density factor has no Marcus counterpart.'},
        ],
        ('A delivered statement that identifies the Marcus prefactor with the Einstein A '
         'coefficient, or that derives one from the other, is missing; the pair has no '
         'statement-level context.'),
        ["grep -rn 'Einstein' PhotoLean/Marcus --include='*.lean'",
         "grep -rn 'Marcus' PhotoLean/Einstein --include='*.lean'",
         'python3 tools/relation_audit_registry.py --explain-pair P-Marcus-Einstein'],
        ('No shared descriptor exists between the activated step and the radiative coefficients '
         'in the delivered statements; the correct status is outOfScope with a statement-level '
         'jurisdiction record.'),
        jurisdiction=('PhotoLean.Marcus.rate (A, lam, kB, T, x) versus '
                      'PhotoLean.Einstein.aOfB (K, B21) with K the radiation-density factor '
                      '8πhν³/c³: disjoint descriptor sets, no inventory statement accepting both, '
                      'and §16 line 969 registers no edge. The single Einstein rate-level contact '
                      'runs through QuantumYield and belongs to a different pair.'),

    ),
    search_entry(
        'Q-RAD1-KSS-01', 'SL-RAD1-KSS-01',
        ['stmt-Kasha-PhotoLean-Kasha-radBranch', 'stmt-Kasha-PhotoLean-Kasha-fluoYield',
         'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
         'stmt-StokesShift-PhotoLean-StokesShift-stokesShift'],
        ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence',
         'conditionalComposition'],
        ['KashaStokesDisjointCtx (rad, ic, N | lam, e00): rate arrays on one side, energy offsets '
         'on the other'],
        [
            {'artifact': 'PhotoLean/Kasha/Basic.lean', 'locator': 'lines 76-115 (decay, branches, yields)',
             'finding': 'Every Kasha observable is built from rate arrays and level indices; no '
                        'energy, wavelength or band position occurs in the module.'},
            {'artifact': 'PhotoLean/StokesShift/Basic.lean', 'locator': 'lines 55-83 (surfaces, absEnergy, emEnergy, stokesShift)',
             'finding': 'Every Stokes observable is built from (lam, e00); no rate array or level '
                        'index occurs.'},
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 956: StokesShift / Kasha no edge',
             'finding': 'The register states that band positions and ladder rates are different '
                        'observables; the Stokes module’s only content edge is with Marcus.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Kasha-StokesShift',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        [
            {'command': "grep -rn 'StokesShift' PhotoLean/Kasha --include='*.lean'",
             'purpose': 'Search the Kasha modules for any delivered Stokes statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Kasha' PhotoLean/StokesShift --include='*.lean'",
             'purpose': 'Search the Stokes modules for any delivered Kasha statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/StokesShift/*.lean | sort -u",
             'purpose': 'Measure the Stokes module dependencies.',
             'result': 'Mathlib, Kernel, Marcus.Basic and StokesShift’s own modules; no Kasha import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-StokesShift',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False."},
        ],
        [
            {'strategy': 'Read the ladder’s emission spectrum energy as the Stokes band position.',
             'outcome': 'The ladder’s spectrum is normalized by photon counts (specFrac), not by '
                        'energy; no delivered statement assigns an energy to a level.'},
            {'strategy': 'Use the reorganization energy of the Stokes pair as the ladder’s '
                         'nonradiative driving force.',
             'outcome': 'The ladder’s ic array is not a function of lam; the identification would '
                        'be a new modelling premise, not a statement-level relation.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        [
            {'kind': 'position-versus-yield candidate',
             'statement': 'The ladder’s lowest-level emission could be read as the emission band '
                          'position of the Stokes pair.',
             'status': 'candidate rejected: the two statements have different kinds of argument '
                       '(rate array versus energy offset) and different codomains (yield versus '
                       'energy).'},
        ],
        ('A delivered statement that assigns band energies to ladder levels, or that computes a '
         'spectral position from rate arrays, is missing; the pair has no statement-level context.'),
        ["grep -rn 'StokesShift' PhotoLean/Kasha --include='*.lean'",
         "grep -rn 'Kasha' PhotoLean/StokesShift --include='*.lean'",
         'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-StokesShift'],
        ('Band positions and ladder rates are different observables in the delivered statements; '
         'the honest status is outOfScope with a statement-level jurisdiction record rather than '
         'a forced identity.'),
        jurisdiction=('PhotoLean.Kasha.radBranch (rate arrays, level index) versus '
                      'PhotoLean.StokesShift.emEnergy (lam, e00): disjoint descriptor sets, no '
                      'inventory statement accepting both, and §16 line 956 registers no edge. '
                      'No coordinate change turns a rate array into a band position.'),

    ),
    search_entry(
        'Q-RAD1-KIC-01', 'SL-RAD1-KIC-01',
        ['stmt-Kasha-PhotoLean-Kasha-icBranch', 'stmt-Kasha-PhotoLean-Kasha-marcusIC',
         'stmt-ICvsISC-PhotoLean-ICvsISC-icRate', 'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
         'stmt-ICvsISC-PhotoLean-ICvsISC-cert_icRate'],
        ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence'],
        ['KashaICCandidateCtx: the ladder’s free `ic` array versus the ICvsISC Arrhenius channel '
         'law at the step’s own (lam, x)'],
        [
            {'artifact': 'PhotoLean/Kasha/Basic.lean', 'locator': 'lines 76-83 (decay, radBranch, icBranch)',
             'finding': 'The ladder stores the nonradiative channel as an arbitrary rate array; '
                        'no law constrains ic n.'},
            {'artifact': 'PhotoLean/Kasha/Compose.lean', 'locator': 'lines 98-101 (marcusIC)',
             'finding': 'The only rate law attached to the ladder is the Kasha-side marcusIC; the '
                        'window theorem takes `ic 1 = marcusIC …` as an explicit premise, i.e. '
                        'the ladder’s own `ic` is never instantiated by a delivered statement.'},
            {'artifact': 'PhotoLean/ICvsISC/Basic.lean', 'locator': 'lines 63-79 (fcBarrier, icRate, cert_icRate)',
             'finding': 'The ICvsISC channel law is an Arrhenius rate over its own Franck–Condon '
                        'barrier, with a delivered certificate to the Marcus rate.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Kasha-ICvsISC',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        [
            {'command': "grep -rn 'ICvsISC' PhotoLean/Kasha --include='*.lean'",
             'purpose': 'Search the Kasha modules for any delivered ICvsISC statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Kasha' PhotoLean/ICvsISC --include='*.lean'",
             'purpose': 'Search the ICvsISC modules for any delivered Kasha statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -n 'marcusIC\\|ic 1' PhotoLean/Kasha/Compose.lean | head -20",
             'purpose': 'Locate the ladder’s only rate-law premise on `ic 1`.',
             'result': 'The premise `ic 1 = marcusIC A lam kB T x` appears in the window rows; no '
                       'row instantiates `ic` with an external rate law.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-ICvsISC',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False."},
        ],
        [
            {'strategy': 'Fill the ladder’s `ic 1` with `ICvsISC.icRate` and reuse the delivered '
                         'window row.',
             'outcome': 'The window row accepts `ic 1 = marcusIC …`; the ICvsISC certificate gives '
                        '`icRate = Marcus.rate`, so the two are definitionally the same body. The '
                        'remaining object is the channel assignment `ic 1 = icRate`, which no '
                        'delivered statement states: the ladder’s `ic` is a free array, and the '
                        'ICvsISC law is about its own molecule, not about a ladder level.'},
            {'strategy': 'Read the ICvsISC S₁→S₀ channel as the ladder’s S₂→S₁ channel.',
             'outcome': 'This is exactly the modelling premise that would be needed; the '
                        'delivered theories do not state it, and the package must not manufacture '
                        'it.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        [
            {'kind': 'channel-assignment candidate',
             'statement': 'ic 1 = ICvsISC.icRate A lam kB T x, then the delivered Kasha window '
                          'row (after `cert_icRate`).',
             'status': 'candidate only: the rate half is delivered, the channel assignment is not.'},
        ],
        ('The missing object is a delivered statement that instantiates the ladder’s `ic` array '
         'with a rate law (here the ICvsISC law). Once such a row exists, the composition with '
         'the Kasha window row closes mechanically; without it the bridge would be an invented '
         'premise.'),
        ["grep -rn 'ICvsISC' PhotoLean/Kasha --include='*.lean'",
         "grep -rn 'Kasha' PhotoLean/ICvsISC --include='*.lean'",
         "grep -n 'marcusIC\\|ic 1' PhotoLean/Kasha/Compose.lean",
         'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-ICvsISC'],
        ('Both theories model internal conversion, so the pair is in scope; the bridge needs the '
         'channel assignment as a modelling premise that no delivered statement carries. The '
         'honest status is unresolved with the exact missing parent recorded.'),
    ),
    search_entry(
        'Q-RAD1-KFO-01', 'SL-RAD1-KFO-01',
        ['stmt-Kasha-PhotoLean-Kasha-emitYield', 'stmt-Kasha-PhotoLean-Kasha-cascade',
         'stmt-Forster-PhotoLean-Forster-fretRate', 'stmt-Forster-PhotoLean-Forster-fretEff6'],
        ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence',
         'conditionalComposition'],
        ['KashaForsterDisjointCtx (rad, ic, N | tauD, r6, R): a single-molecule ladder versus a '
         'two-chromophore transfer geometry'],
        [
            {'artifact': 'PhotoLean/Kasha/Basic.lean', 'locator': 'lines 87-101 (cascade, emitYield, fluoYield)',
             'finding': 'The ladder has one molecule, one excitation level and no donor or '
                        'acceptor; its arguments are rate arrays and indices.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'lines 44-57 (kappaSq, fretRate, fretEff6)',
             'finding': 'The Förster model has two chromophores, an orientation factor, a donor '
                        'lifetime and an R^-6 separation; no level structure.'},
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 964: Forster / Kasha no edge',
             'finding': 'The register states the transfer geometry shares no scalar with the '
                        'ladder.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Kasha-Forster',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        [
            {'command': "grep -rn 'Forster' PhotoLean/Kasha --include='*.lean'",
             'purpose': 'Search the Kasha modules for any delivered Förster statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Kasha' PhotoLean/Forster --include='*.lean'",
             'purpose': 'Search the Förster modules for any delivered Kasha statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/Forster/*.lean | sort -u",
             'purpose': 'Measure the Förster module dependencies.',
             'result': 'Mathlib plus Förster’s own modules only; no Kasha import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-Forster',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False."},
        ],
        [
            {'strategy': 'Read the ladder’s inter-level cascade as excitation transfer between '
                         'chromophores.',
             'outcome': 'The cascade is an intra-molecular internal-conversion chain; no second '
                        'chromophore, no separation and no lifetime occur in its arguments.'},
            {'strategy': 'Equate a level yield with a transfer efficiency.',
             'outcome': 'The transfer efficiency is R^-6-controlled and defined for a donor-'
                        'acceptor pair; the ladder yield is a branching probability. No delivered '
                        'statement relates them.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        [
            {'kind': 'yield-versus-transfer-efficiency candidate',
             'statement': 'Kasha.emitYield rad ic i N versus Forster.fretEff6 r6 R: both are '
                          'dimensionless fractions of excitation.',
             'status': 'candidate rejected: the fractions describe different systems (one molecule '
                       'versus a donor-acceptor pair).'},
        ],
        ('A delivered statement that gives the ladder a donor-acceptor pair or a lifetime is '
         'missing; the pair has no statement-level context.'),
        ["grep -rn 'Forster' PhotoLean/Kasha --include='*.lean'",
         "grep -rn 'Kasha' PhotoLean/Forster --include='*.lean'",
         'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-Forster'],
        ('The ladder is a single-molecule branching model and the Förster rows are a '
         'two-chromophore transfer model; no statement-level translation exists. The status is '
         'outOfScope with a jurisdiction record.'),
        jurisdiction=('PhotoLean.Kasha.emitYield (rate arrays, level indices) versus '
                      'PhotoLean.Forster.fretRate or fretEff6 (tauD, r6, R): disjoint descriptor '
                      'sets, no inventory statement accepting both, and §16 line 964 registers no '
                      'edge. The ladder declares no donor-acceptor pair to translate into.'),

    ),
    search_entry(
        'Q-RAD1-VEG-01', 'SL-RAD1-VEG-01',
        ['stmt-KashaVavilov-PhotoLean-KashaVavilov-antiKasha_observable_iff',
         'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
         'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-lnRate',
         'stmt-Kasha-PhotoLean-Kasha-marcusIC',
         'stmt-KashaVavilov-PhotoLean-KashaVavilov-fluoYield_eq_emitYield_zero_add_upperYield'],
        ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence'],
        ['KvEglCandidateCtx: the gap-law rate filling the ladder’s conversion channel, with the '
         'Vavilov predicate downstream'],
        [
            {'artifact': 'PhotoLean/EnergyGapLaw/Basic.lean', 'locator': 'lines 62-100 (nrBarrier, nrRate, InvertedGap, lnRate)',
             'finding': 'The gap-law rows are the rate, its logarithm and the region predicate; '
                        'none mentions a ladder, a level or a yield.'},
            {'artifact': 'PhotoLean/KashaVavilov/Criterion.lean', 'locator': 'line 333 (antiKasha_observable_iff)',
             'finding': 'The Vavilov-side predicate is stated in terms of the ladder’s upper '
                        'yield; it carries no energy parameters.'},
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 991-993 (EnergyGapLaw / KashaVavilov no edge)',
             'finding': 'The register states that KashaVavilov appears in the EnergyGapLaw plan '
                        'only as an undelivered composition candidate.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-candidate-P-KashaVavilov-EnergyGapLaw',
             'finding': 'The legacy record is a pair-level undelivered-candidate anchor with '
                        'status unresolved.'},
        ],
        [
            {'command': "grep -rn 'EnergyGapLaw' PhotoLean/KashaVavilov --include='*.lean'",
             'purpose': 'Search the KashaVavilov modules for any delivered gap-law statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'KashaVavilov' PhotoLean/EnergyGapLaw --include='*.lean'",
             'purpose': 'Search the EnergyGapLaw modules for any delivered KashaVavilov statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'marcusIC' PhotoLean/EnergyGapLaw PhotoLean/KashaVavilov --include='*.lean'",
             'purpose': 'Check whether either side already carries the bridging rate object.',
             'result': 'No matches (grep exit 1): the window row that uses marcusIC lives in '
                       'PhotoLean/Kasha/Compose.lean, not in either partner module.'},
            {'command': "grep -h '^import' PhotoLean/EnergyGapLaw/*.lean | sort -u",
             'purpose': 'Measure the EnergyGapLaw module dependencies.',
             'result': 'Mathlib, Kernel, Marcus.Basic and EnergyGapLaw’s own modules; no '
                       'Kasha/KashaVavilov import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-EnergyGapLaw',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='undelivered-candidate'; candidate=True."},
        ],
        [
            {'strategy': 'Compose gap-law rate → ladder channel → Kasha window → anti-Kasha.',
             'outcome': 'Every downstream piece exists except the ladder channel assignment: the '
                        'window row takes `ic 1 = marcusIC`, the gap-law module never speaks about '
                        'a ladder, and no statement identifies the two.'},
            {'strategy': 'Use the delivered definitional identity nrRate = Marcus.rate to reach '
                         'the window row’s marcusIC.',
             'outcome': 'The rate identity is delivered (cert_nrRate) and the bodies agree, but '
                        'the ladder still needs the explicit premise `ic 1 = nrRate`; without a '
                        'delivered statement carrying it, the composition would be the package’s '
                        'invented premise, not a delivered row.'},
            {'strategy': 'Look for a gap-law statement about yields or Vavilov invariance.',
             'outcome': 'The EnergyGapLaw rows are rates, logs and a region predicate; no yield '
                        'or spectral row exists.'},
        ],
        [
            {'kind': 'gap-law-to-Vavilov composition candidate',
             'statement': 'ic 1 = EnergyGapLaw.nrRate A lam kB T x, then the Kasha window row, '
                          'then antiKasha_observable_iff.',
             'status': 'candidate only: the gap-law rate and the Vavilov predicate are both '
                       'delivered, but the ladder channel assignment between them is not.'},
        ],
        ('A delivered statement that fills the ladder’s conversion channel with the energy-gap-law '
         'rate — or that states the Vavilov predicate directly in terms of the gap-law rate — is '
         'missing. The nearest delivered rows are the Kasha window theorem (stated with the '
         'Kasha-side marcusIC) and the gap-law/Marcus rate identity.'),
        ["grep -rn 'EnergyGapLaw' PhotoLean/KashaVavilov --include='*.lean'",
         "grep -rn 'KashaVavilov' PhotoLean/EnergyGapLaw --include='*.lean'",
         "grep -rn 'marcusIC' PhotoLean/EnergyGapLaw PhotoLean/KashaVavilov --include='*.lean'",
         'python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-EnergyGapLaw'],
        ('The composition is chemically well posed and the legacy plan registers it as an '
         'undelivered candidate; the precise missing parent is the ladder channel assignment. '
         'The honest status is unresolved, not notEstablished (the search is bounded and names '
         'the missing row) and not certified (the premise is not delivered).'),
    ),
]


# --------------------------------------------------------------------------- assemble

def status_counts(queries):
    out = {}
    for q in queries:
        status = q['outcome']['status']
        out[status] = out.get(status, 0) + 1
    return {k: out[k] for k in STATUSES if k in out}


def kind_counts(queries):
    out = {}
    for q in queries:
        kind = q['expectedKind']
        out[kind] = out.get(kind, 0) + 1
    return {k: out[k] for k in KINDS if k in out}


PAIR_THEORY = {p: QUEUE_BY_ID[p]['theories'] for p in PAIRS}


def build_search_log():
    counts = {'entries': len(SEARCH_ENTRIES)}
    doc = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': WORK_PACKAGE,
        'snapshot': SNAP_ID,
        'entries': SEARCH_ENTRIES,
        'counts': counts,
        'nonClaims': [
            'Each entry records a bounded search inside the frozen inventory; it is not a claim '
            'that no relation exists outside the sixteen-theory delivered statements.',
            'A failed search is not a refutation: no entry carries a negative existence claim.',
            'The compatibility of the outOfScope entries is a jurisdiction judgment about '
            'statement-level vocabulary, not a claim that the physical processes are unrelated.',
        ],
    }
    return doc


def build_screening(search_sha):
    pairs = []
    for pid in PAIRS:
        qs = [q for q in QUERIES if q['pairId'] == pid]
        pairs.append({
            'pairId': pid,
            'theories': PAIR_THEORY[pid],
            'primaryCluster': PRIMARY_CLUSTER,
            'queryIds': [q['queryId'] for q in qs],
            'queries': qs,
        })
    all_queries = [q for p in pairs for q in p['queries']]
    sc = status_counts(all_queries)
    kc = kind_counts(all_queries)
    accepted_packages = [R2, R3, R4_E1, R4_E2, R4_CI]
    accepted_pair_count = sum(len(pkg['pairs']) for pkg in accepted_packages)
    doc = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WORK_PACKAGE,
            'title': 'Radiative and energy-transfer relations, first half: Marcus/Kasha ladders, '
                     'energy-gap law, Stokes window, IC channel, Einstein radiative fraction and '
                     'the quenching contact',
            'source': 'loop/计划.md R5, Package RAD1',
            'pairIds': PAIRS,
            'pairCount': len(PAIRS),
            'note': 'Exactly the sixteen pairs of R1 work package WP-radiative-energy-transfer-01. '
                    'No accepted R2/R3/R4 pair is rescreened and no other R5 package pair appears.',
        },
        'statusVocabulary': STATUSES,
        'kindVocabulary': KINDS,
        'allowedAxioms': ALLOWED_AXIOMS,
        'snapshot': {
            'id': SNAP_ID,
            'date': '2026-11-04',
            'round': ROUND,
            'inventory': INV_REL,
            'inventorySha256': sha_rel(INV_REL),
            'pairQueue': QUEUE_REL,
            'pairQueueSha256': sha_rel(QUEUE_REL),
            'clusterPlan': CLUSTER_REL,
            'clusterPlanSha256': sha_rel(CLUSTER_REL),
            'boundary': BOUNDARY_REL,
            'boundarySha256': sha_rel(BOUNDARY_REL),
            'legacyRegistry': REGISTRY_REL,
            'legacyRegistrySha256': sha_rel(REGISTRY_REL),
            'acceptedR2Package': R2_REL,
            'acceptedR2Sha256': sha_rel(R2_REL),
            'acceptedR3Package': R3_REL,
            'acceptedR3Sha256': sha_rel(R3_REL),
            'acceptedR4E1Package': R4_E1_REL,
            'acceptedR4E1Sha256': sha_rel(R4_E1_REL),
            'acceptedR4E2Package': R4_E2_REL,
            'acceptedR4E2Sha256': sha_rel(R4_E2_REL),
            'acceptedR4CIPackage': R4_CI_REL,
            'acceptedR4CISha256': sha_rel(R4_CI_REL),
            'leanToolchain': 'leanprover/lean4:v4.17.0',
            'deliveredLeanFileCount': 102,
            'note': 'The mutable R5 cumulative coverage ledger is deliberately not pinned by this '
                    'package; prior coverage is derived from the five accepted screening packages.',
        },
        'inventoryReference': {
            'path': INV_REL,
            'sha256': sha_rel(INV_REL),
            'statementRows': len(INV['statements']),
            'screeningEligibleRows': sum(1 for s in INV['statements'] if s['screeningEligible']),
        },
        'legacyRegistryReference': {
            'path': REGISTRY_REL,
            'sha256': sha_rel(REGISTRY_REL),
            'certificateCount': len(REGISTRY['certificates']),
            'queryCount': len(REGISTRY['queries']),
            'recordCount': len(REGISTRY['records']),
        },
        'acceptedCoverageReference': {
            'acceptedPairs': accepted_pair_count,
            'sources': [R2_REL, R3_REL, R4_E1_REL, R4_E2_REL, R4_CI_REL],
            'note': 'Derived by reading the five accepted screening packages directly; the mutable '
                    'R5 ledger is not read and not pinned.',
        },
        'searchLogReference': {
            'path': SEARCH_REL,
            'sha256': search_sha,
            'entryCount': len(SEARCH_ENTRIES),
        },
        'probeReference': {
            'path': PROBE_REL,
            'sha256': sha_rel(PROBE_REL),
            'declarationCount': len([q for q in all_queries
                                     if q['outcome']['status'] == 'certified']),
            'log': PROBE_LOG_REL,
        },
        'contextLibrary': CONTEXTS,
        'scopeLibrary': SCOPES,
        'pairs': pairs,
        'counts': {
            'pairs': len(pairs),
            'queries': len(all_queries),
            'byStatus': sc,
            'byExpectedKind': kc,
            'certified': sc.get('certified', 0),
            'refuted': sc.get('refuted', 0),
            'unresolved': sc.get('unresolved', 0),
            'notEstablished': sc.get('notEstablished', 0),
            'outOfScope': sc.get('outOfScope', 0),
        },
        'nonClaims': [
            'Sixteen pairs, seventeen queries: one query per pair except P-Marcus-EnergyGapLaw, '
            'which carries two chemically distinct statement-level queries.',
            'Screened is not the same as certified; the package records pair coverage separately '
            'from outcome counts.',
            'One query per pair does not exhaust all conceivable relations between the theories '
            'outside the frozen bounded query protocol.',
            'The certified rows are probe-level Lean certificates over delivered statements; they '
            'are not claims that the delivered theories are complete models of the chemistry.',
            'The outOfScope rows are jurisdiction records about statement-level vocabulary; they '
            'do not claim that the physical processes are unrelated.',
            'No R5 acceptance is claimed: the package stays submitted until independent review.',
        ],
    }
    return doc


def build_fragment(screening_sha):
    all_queries = [q for p in [{'queries': [q for q in QUERIES if q['pairId'] == pid]}
                               for pid in PAIRS] for q in p['queries']]
    sc = status_counts(all_queries)
    kc = kind_counts(all_queries)
    rows = []
    for pid in PAIRS:
        qs = [q for q in QUERIES if q['pairId'] == pid]
        rows.append({
            'pairId': pid,
            'theories': PAIR_THEORY[pid],
            'primaryCluster': PRIMARY_CLUSTER,
            'queryCount': len(qs),
            'byStatus': status_counts(qs),
        })
    return {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': ROUND,
        'generatedOn': '2026-11-04',
        'workPackage': WORK_PACKAGE,
        'packagePath': SCREENING_REL,
        'screeningSha256': screening_sha,
        'pairCount': len(PAIRS),
        'queryCount': len(QUERIES),
        'byStatus': sc,
        'byExpectedKind': kc,
        'primaryCluster': PRIMARY_CLUSTER,
        'screenedPairs': rows,
        'acceptance': 'submitted-R5-pending-review',
        'nonClaims': [
            'This fragment contributes sixteen pairs to the R5 cumulative ledger; it does not '
            'itself edit the ledger.',
            'Screened is not the same as certified.',
            'The fragment records the package status as submitted-R5-pending-review until '
            'independent review.',
            'The fragment does not pin the mutable R5 ledger and carries no cumulative count.',
        ],
    }


def write_json(rel, doc):
    path = os.path.join(ROOT, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write('\n')
    print('wrote %s (%s)' % (rel, sha_path(path)))


def check_probe_statement_ref():
    """Fail closed if the MKVV comparison's left StatementRef drifts from the query endpoint."""
    text = read_rel(PROBE_REL)
    match = re.search(r'def\s+mkvCmp\b.*?(?=\n(def|theorem)\s)', text, re.S)
    if match is None:
        raise SystemExit('cannot locate def mkvCmp in %s' % PROBE_REL)
    block = match.group(0)
    if ('mkRef "PhotoLean.Marcus" "%s"' % MKV_CMP_LEFT_DECL) not in block:
        raise SystemExit('mkvCmp left StatementRef is not %s' % MKV_CMP_LEFT_DECL)
    if '"PhotoLean.Kasha.marcusIC"' in block:
        raise SystemExit('mkvCmp left StatementRef still names PhotoLean.Kasha.marcusIC')
    if 'PhotoLean/Marcus/Basic.lean#barrier' not in block:
        raise SystemExit('mkvCmp left StatementRef provenance is not the Marcus barrier source')
    mkvv = next(q for q in QUERIES if q['queryId'] == 'Q-RAD1-MKVV-01')
    left = mkvv['endpoints']['source']
    if left['declaration'] != MKV_CMP_LEFT_DECL:
        raise SystemExit('MKVV source endpoint %r is not %s'
                         % (left['declaration'], MKV_CMP_LEFT_DECL))


def main():
    if not os.path.exists(os.path.join(ROOT, PROBE_REL)):
        raise SystemExit('probe missing: %s' % PROBE_REL)
    check_probe_statement_ref()
    # sanity: every query id unique, every pair covered exactly once in the work package
    qids = [q['queryId'] for q in QUERIES]
    if len(qids) != len(set(qids)):
        raise SystemExit('duplicate query id')
    if sorted({q['pairId'] for q in QUERIES}) != sorted(PAIRS):
        raise SystemExit('query pair set differs from the assigned sixteen')
    for q in QUERIES:
        for side in ('source', 'target'):
            ep = q['endpoints'][side]
            if ep['statementId'] in DANGLING_IDS:
                raise SystemExit('dangling endpoint in %s' % q['queryId'])
        theories = {q['endpoints']['source']['theory'], q['endpoints']['target']['theory']}
        if theories != set(PAIR_THEORY[q['pairId']]):
            raise SystemExit('endpoint theories do not match pair %s' % q['pairId'])
        if q['outcome']['status'] == 'certified':
            if q['outcome']['evidence']['probe']['sha256'] != sha_rel(PROBE_REL):
                raise SystemExit('probe hash drift while building %s' % q['queryId'])

    write_json(SEARCH_REL, build_search_log())
    search_sha = sha_rel(SEARCH_REL)
    screening = build_screening(search_sha)
    # the screening pins the probe; refresh it explicitly after the probe is final
    write_json(SCREENING_REL, screening)
    write_json(FRAGMENT_REL, build_fragment(sha_rel(SCREENING_REL)))
    print('pairs=%d queries=%d byStatus=%s' %
          (screening['counts']['pairs'], screening['counts']['queries'],
           screening['counts']['byStatus']))


if __name__ == '__main__':
    main()
