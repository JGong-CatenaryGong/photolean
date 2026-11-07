#!/usr/bin/env python3
"""Deterministic builder for the R5 Package RAD2 submission artifacts.

The builder expands the sixteen statement-level queries of WP-radiative-energy-transfer-02
from the frozen R1 inventory (endpoint metadata), writes the package search log, the
screening package and the coverage fragment, and pins the probe / search-log / screening
hashes. It is a reproducibility helper, not an audit verdict: `validate.py` re-derives
every fact and is the gate.

Order (hash dependency):
    1. search-log.json          (pins neither probe nor screening)
    2. screening.json           (pins search-log and probe hashes)
    3. coverage-fragment.json   (pins the screening hash)

Usage:
    python3 bounded_audit/r5/radiative-02/build_package.py
"""

import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
PKG_REL = 'bounded_audit/r5/radiative-02'
SNAP = 'snap-bounded-audit-2026-11-04-r5rad2'
WP_ID = 'WP-radiative-energy-transfer-02'

SCREENING_REL = PKG_REL + '/screening.json'
SEARCH_REL = PKG_REL + '/search-log.json'
FRAGMENT_REL = PKG_REL + '/coverage-fragment.json'
PROBE_REL = PKG_REL + '/probes/RAD2-probe.lean'
PROBE_LOG_REL = PKG_REL + '/probes/compile.log'
INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
ACCEPTED = [
    ('R2', 'bounded_audit/wp-surface-01/screening.json'),
    ('R3', 'bounded_audit/r3/screening.json'),
    ('R4-E1', 'bounded_audit/r4/excited-01/screening.json'),
    ('R4-E2', 'bounded_audit/r4/excited-02/screening.json'),
    ('R4-CI', 'bounded_audit/r4/conical-01/screening.json'),
]

PAIR_IDS = [
    'P-KashaVavilov-StokesShift',
    'P-KashaVavilov-ICvsISC',
    'P-KashaVavilov-Forster',
    'P-KashaVavilov-Einstein',
    'P-SternVolmer-EnergyGapLaw',
    'P-SternVolmer-StokesShift',
    'P-SternVolmer-ICvsISC',
    'P-SternVolmer-Forster',
    'P-SternVolmer-Einstein',
    'P-QuantumYield-EnergyGapLaw',
    'P-QuantumYield-StokesShift',
    'P-QuantumYield-ICvsISC',
    'P-QuantumYield-Forster',
    'P-QuantumYield-Einstein',
    'P-FluorPhos-EnergyGapLaw',
    'P-FluorPhos-StokesShift',
]

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha_rel(rel):
    return sha(os.path.join(ROOT, rel))


def load_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


INV = load_rel(INV_REL)
QUEUE = load_rel(QUEUE_REL)
CLUSTER = load_rel(CLUSTER_REL)
INV_BY_ID = {row['id']: row for row in INV['statements']}
QUEUE_BY_ID = {row['pairId']: row for row in QUEUE['pairs']}
PROBE_SHA = sha(os.path.join(ROOT, PROBE_REL))


def endpoint(statement_id, form):
    row = INV_BY_ID[statement_id]
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


# --------------------------------------------------------------------------- contexts
CONTEXTS = {
    'KvSsDisjointCtx': {
        'id': 'KvSsDisjointCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'M : ℕ', 'N : ℕ', 'lam : ℝ', 'e00 : ℝ'],
        'physicalReading': 'Disjoint observables: KashaVavilov compares the normalized emission fraction of ladder levels across excitation levels (a dimensionless photon partition over electronic levels); StokesShift compares vertical absorption and emission energies of one displaced-parabola surface pair (band positions in energy). No total translation maps a ladder level index to a nuclear coordinate or a spectral fraction to an energy.',
        'provenance': PKG_REL + '/screening.json#KvSsDisjointCtx (candidate context; no Lean structure)',
    },
    'KvIcCandidateCtx': {
        'id': 'KvIcCandidateCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ',
                   'AI : ℝ', 'AS : ℝ', 'lamI : ℝ', 'lamS : ℝ', 'kB : ℝ', 'T : ℝ',
                   'xI : ℝ', 'xS : ℝ', 'HSO : ℝ'],
        'physicalReading': 'Candidate shared context: the ladder level-1 loss rate `ic 1` would be the ICvsISC internal-conversion channel `icRate AI lamI kB T xI` at the same gap. The ladder leaves `ic` a free rate function, so the identification is a candidate, not a total translation.',
        'provenance': PKG_REL + '/screening.json#KvIcCandidateCtx (candidate context; no Lean structure)',
    },
    'KvFoDisjointCtx': {
        'id': 'KvFoDisjointCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'M : ℕ', 'N : ℕ',
                   'tauD : ℝ', 'r6 : ℝ', 'R : ℝ', 'thetaD : ℝ', 'thetaA : ℝ', 'phi : ℝ'],
        'physicalReading': 'Disjoint coordinate sets: the ladder is indexed by an electronic level and partitioned over normalized spectra; Förster is indexed by a donor-acceptor separation and an orientation geometry (R^-6 rate, kappa^2). No total translation maps a level index to a distance or an orientation angle.',
        'provenance': PKG_REL + '/screening.json#KvFoDisjointCtx (candidate context; no Lean structure)',
    },
    'KvEbCandidateCtx': {
        'id': 'KvEbCandidateCtx',
        'fields': ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'M : ℕ', 'N : ℕ', 'K : ℝ', 'B21 : ℝ'],
        'physicalReading': 'Candidate shared context: the ladder per-level radiative rate `rad n` would be the Einstein A coefficient `aOfB K B21` of the same transition. Both are radiative rates, so a scalar-level identification is expressible; the ladder quantifies over an arbitrary rate function, so no total translation is declared.',
        'provenance': PKG_REL + '/screening.json#KvEbCandidateCtx (candidate context; no Lean structure)',
    },
    'SvEgCandidateCtx': {
        'id': 'SvEgCandidateCtx',
        'fields': ['k0 : ℝ', 'kq : ℝ', 'q : ℝ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': 'Candidate shared context: the Stern-Volmer quencher channel `kq * q` would be the energy-gap-law nonradiative rate `nrRate A lam kB T x` at a quencher-induced gap. SV carries no gap coordinate and EGL carries no concentration axis; the identification is a candidate.',
        'provenance': PKG_REL + '/screening.json#SvEgCandidateCtx (candidate context; no Lean structure)',
    },
    'SvSsDisjointCtx': {
        'id': 'SvSsDisjointCtx',
        'fields': ['k0 : ℝ', 'kq : ℝ', 'q : ℝ', 'lam : ℝ', 'e00 : ℝ'],
        'physicalReading': 'Disjoint observables: the Stern-Volmer ratio is a dimensionless intensity/lifetime ratio over a quencher-concentration axis; the Stokes shift is an energy difference between vertical absorption and emission over a nuclear-coordinate surface pair. No total translation exists.',
        'provenance': PKG_REL + '/screening.json#SvSsDisjointCtx (candidate context; no Lean structure)',
    },
    'SvIcCandidateCtx': {
        'id': 'SvIcCandidateCtx',
        'fields': ['k0 : ℝ', 'kq : ℝ', 'q : ℝ', 'AI : ℝ', 'AS : ℝ', 'lamI : ℝ', 'lamS : ℝ',
                   'kB : ℝ', 'T : ℝ', 'xI : ℝ', 'xS : ℝ', 'HSO : ℝ'],
        'physicalReading': 'Candidate shared context: the Stern-Volmer quencher channel `kq * q` would be an ICvsISC internal-conversion or intersystem-crossing channel at the encounter geometry. Both are nonradiative decay channels; SV has no gap/spin coordinate and ICvsISC has no concentration axis.',
        'provenance': PKG_REL + '/screening.json#SvIcCandidateCtx (candidate context; no Lean structure)',
    },
    'SvFoShapeCtx': {
        'id': 'SvFoShapeCtx',
        'fields': ['k0 : ℝ', 'kq : ℝ', 'q : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': 'Shape-only context: the Stern-Volmer inverse ratio reads `1 + KSV*q` and the inverse Förster efficiency reads `1 + R^6/r6`; the two controls are a concentration times a rate constant and a sixth-power distance ratio. The shared `1 + control` form is a shape, not a shared physical coordinate.',
        'provenance': PKG_REL + '/screening.json#SvFoShapeCtx (candidate context; no Lean structure)',
    },
    'SvEbCandidateCtx': {
        'id': 'SvEbCandidateCtx',
        'fields': ['k0 : ℝ', 'kq : ℝ', 'q : ℝ', 'A : ℝ', 'kNR : ℝ'],
        'physicalReading': 'Candidate shared context: the Stern-Volmer intrinsic total decay `k0` would be split into a radiative Einstein coefficient `A` and a nonradiative rate `kNR` (k0 = A + kNR). SV keeps `k0` whole and never splits it; the identification is a candidate.',
        'provenance': PKG_REL + '/screening.json#SvEbCandidateCtx (candidate context; no Lean structure)',
    },
    'QyEgCtx': {
        'id': 'QyEgCtx',
        'fields': ['kr : ℝ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': 'One excited state with a radiative channel `kr` and an energy-gap-law nonradiative channel `nrRate A lam kB T x`; the quantum-yield partition of the two channels is compared with the EGL rate ratio written through `nrBarrier`.',
        'provenance': PKG_REL + '/probes/RAD2-probe.lean#QyEgCtx',
    },
    'QySsDisjointCtx': {
        'id': 'QySsDisjointCtx',
        'fields': ['kr : ℝ', 'knr : ℝ', 'lam : ℝ', 'e00 : ℝ'],
        'physicalReading': 'Disjoint observables: the quantum-yield partition is dimensionless over decay channels; the Stokes shift is an energy difference over a displaced-parabola surface pair. No channel rate is a band energy and no total translation exists.',
        'provenance': PKG_REL + '/screening.json#QySsDisjointCtx (candidate context; no Lean structure)',
    },
    'QyIcCtx': {
        'id': 'QyIcCtx',
        'fields': ['AI : ℝ', 'AS : ℝ', 'lamI : ℝ', 'lamS : ℝ', 'kB : ℝ', 'T : ℝ',
                   'xI : ℝ', 'xS : ℝ', 'HSO : ℝ'],
        'physicalReading': 'One excited state with an IC channel `icRate AI lamI kB T xI` and an ISC channel `iscRate HSO AS lamS kB T xS`; the quantum-yield ISC/IC partition is compared with the ICvsISC spin/prefactor times Franck-Condon rate ratio.',
        'provenance': PKG_REL + '/probes/RAD2-probe.lean#QyIcCtx',
    },
    'QyFoCtx': {
        'id': 'QyFoCtx',
        'fields': ['kD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': 'A donor with radiative rate `kD` and an added FRET channel `kD * (r6 / R^6)`; the transfer efficiency `fretEff6 r6 R` is compared with one minus the donor retained radiative yield.',
        'provenance': PKG_REL + '/probes/RAD2-probe.lean#QyFoCtx',
    },
    'QyEbCtx': {
        'id': 'QyEbCtx',
        'fields': ['A : ℝ', 'kNR : ℝ'],
        'physicalReading': 'One radiative channel `A` and one nonradiative channel `kNR`; the Einstein radiative fraction `A * tauR (A + kNR)` is compared with the two-channel quantum yield of the radiative channel.',
        'provenance': PKG_REL + '/probes/RAD2-probe.lean#QyEbCtx',
    },
    'FpEgCandidateCtx': {
        'id': 'FpEgCandidateCtx',
        'fields': ['kF : ℝ', 'kISC : ℝ', 'kIC : ℝ', 'kP : ℝ', 'kNR : ℝ',
                   'A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': 'Candidate shared context: the FluorPhos S1 internal-conversion rate `kIC` would be the energy-gap-law nonradiative rate `nrRate A lam kB T x` at the S1->S0 gap. FP leaves `kIC` a free rate; the identification is a candidate.',
        'provenance': PKG_REL + '/screening.json#FpEgCandidateCtx (candidate context; no Lean structure)',
    },
    'FpSsDisjointCtx': {
        'id': 'FpSsDisjointCtx',
        'fields': ['kF : ℝ', 'kISC : ℝ', 'kIC : ℝ', 'kP : ℝ', 'kNR : ℝ', 'lam : ℝ', 'e00 : ℝ'],
        'physicalReading': 'Disjoint observables: the fluorescence/phosphorescence competition is a partition of branch probabilities over decay channels; the Stokes shift is an energy difference over a displaced-parabola surface pair. No total translation exists.',
        'provenance': PKG_REL + '/screening.json#FpSsDisjointCtx (candidate context; no Lean structure)',
    },
}

SCOPES = {
    'scope-RAD2-qy-eg-branch': {
        'id': 'scope-RAD2-qy-eg-branch',
        'description': 'Two-channel quantum-yield branch ratio against the energy-gap-law nonradiative rate.',
        'domain': 'all (kr, A, lam, kB, T, x) in R^6 with kr > 0 and A > 0; the totalized division makes kB*T > 0 non-load-bearing for the identity.',
        'snapshot': SNAP,
    },
    'scope-RAD2-qy-ic-branch': {
        'id': 'scope-RAD2-qy-ic-branch',
        'description': 'Quantum-yield ISC/IC branch ratio against the ICvsISC spin/FC rate ratio.',
        'domain': 'all ICvsISC parameter tuples satisfying FCData with HSO > 0.',
        'snapshot': SNAP,
    },
    'scope-RAD2-qy-fo-efficiency': {
        'id': 'scope-RAD2-qy-fo-efficiency',
        'description': 'Förster transfer efficiency against one minus the donor retained radiative yield.',
        'domain': 'all (kD, r6, R) with kD > 0, r6 >= 0 and R != 0.',
        'snapshot': SNAP,
    },
    'scope-RAD2-qy-eb-radiative': {
        'id': 'scope-RAD2-qy-eb-radiative',
        'description': 'Einstein radiative fraction against the two-channel radiative quantum yield.',
        'domain': 'all (A, kNR) in R^2; the identity is totalized and carries no premise.',
        'snapshot': SNAP,
    },
    'scope-RAD2-candidate-bridge': {
        'id': 'scope-RAD2-candidate-bridge',
        'description': 'Scoped search for a delivered statement-level bridge; no negative claim outside the named search.',
        'domain': 'the six named unresolved pairs and the statements/kinds/contexts recorded in their search-log entries.',
        'snapshot': SNAP,
    },
    'scope-RAD2-jurisdiction': {
        'id': 'scope-RAD2-jurisdiction',
        'description': 'Jurisdiction record for pairs with no shared context or declared translation.',
        'domain': 'the six named outOfScope pairs and the statements/kinds/contexts recorded in their search-log entries.',
        'snapshot': SNAP,
    },
}


def ctx(cid):
    return dict(CONTEXTS[cid])


def scope(sid):
    return dict(SCOPES[sid])


def trans_identity():
    return {
        'left': {'id': 'identity', 'term': 'fun δ => δ',
                 'requirement': 'Both statement contexts are the shared context; the translation is total.'},
        'right': {'id': 'identity', 'term': 'fun δ => δ',
                  'requirement': 'Both statement contexts are the shared context; the translation is total.'},
    }


def trans_none(reason):
    return {
        'left': {'id': 'none-declared', 'term': '',
                 'requirement': 'none-declared', 'reason': reason},
        'right': {'id': 'none-declared', 'term': '',
                  'requirement': 'none-declared', 'reason': reason},
    }


def trans_candidate(left_reason, right_reason):
    return {
        'left': {'id': 'candidate-not-total', 'term': '',
                 'requirement': 'candidate-not-total', 'reason': left_reason},
        'right': {'id': 'candidate-not-total', 'term': '',
                  'requirement': 'candidate-not-total', 'reason': right_reason},
    }


def premises_true(note):
    return {'predicate': 'fun _ : Δ => True', 'premiseIds': [], 'definitions': [],
            'note': note}


def premises_defs(predicate, defs, note):
    return {'predicate': predicate,
            'premiseIds': [d['id'] for d in defs],
            'definitions': defs,
            'note': note}


def certified_evidence(cert_id, decl, kind_thm, underlying, justification):
    return {
        'type': 'rad2-probe-certificate',
        'certificateId': cert_id,
        'kind': 'observationalEquivalence',
        'probe': {
            'path': PROBE_REL,
            'sha256': PROBE_SHA,
            'declaration': 'PhotoLean.RelationAudit.BoundedAudit.RAD2.' + decl,
            'kindCheckTheorem': 'PhotoLean.RelationAudit.BoundedAudit.RAD2.' + kind_thm,
            'buildCommand': 'proofs/scripts/lake env lean ' + PROBE_REL,
            'log': PROBE_LOG_REL,
        },
        'underlyingTheorems': underlying,
        'axiomFootprint': list(ALLOWED_AXIOMS),
        'allowedAxioms': list(ALLOWED_AXIOMS),
        'justification': justification,
    }


def thm(decl, rel, line, role):
    return {'declaration': decl, 'sourceArtifact': rel, 'sourceLine': line, 'role': role}


# --------------------------------------------------------------------------- queries
QUERIES = [
    # ---------------------------------------------------------------- KV / StokesShift
    {
        'queryId': 'Q-RAD2-KVS-01',
        'pairId': 'P-KashaVavilov-StokesShift',
        'title': 'Does the Kasha-Vavilov spectral fraction determine the Stokes band separation?',
        'chemicalQuestion': 'Do the Kasha-Vavilov normalized spectral fractions, which partition the emitted photons over ladder levels, constrain the Stokes shift, the energy separation of the absorption and emission band maxima?',
        'chemicalRationale': 'SpecSame compares normalized emission fractions `specFrac` across excitation levels: a dimensionless photon partition over electronic levels. StokesShift compares vertical absorption and emission energies: dimensioned band positions of one displaced-parabola surface pair. A photon-count fraction and an energy are different observables; no declared translation maps a ladder level index to a nuclear coordinate or a fraction to an energy. The delivered extended no-edge register records "StokesShift <-> Kasha / KashaVavilov ... no edge (positions of band maxima vs rates/ladders/geometries)". The question is outside the declared jurisdiction, not logically false.',
        'endpoints': {'source': ('stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame', 'definition'),
                      'target': ('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition')},
        'sharedContext': 'KvSsDisjointCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication from a spectral-agreement premise to a band-position equality; the jurisdiction record denies the shared translation.',
        'falsificationCondition': 'A delivered statement deriving a band energy from a normalized spectral fraction would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared context or declared translation exists: KashaVavilov partitions normalized photon fractions over ladder levels, StokesShift compares band-position energies of one surface pair. The absence is jurisdictional, not a refutation or a logical non-existence claim.',
        'searchLogRef': 'SL-RAD2-KVS-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: KashaVavilov partitions normalized photon fractions over ladder levels, StokesShift compares band-position energies of one surface pair. The absence is jurisdictional, not a refutation.',
        'provenanceKind': 'jurisdiction',
    },
    # ---------------------------------------------------------------- KV / ICvsISC
    {
        'queryId': 'Q-RAD2-KVI-01',
        'pairId': 'P-KashaVavilov-ICvsISC',
        'title': "Is the ladder's upper-level IC loss the ICvsISC Franck-Condon rate at the same gap?",
        'chemicalQuestion': 'Is the internal-conversion rate that drives the Kasha-Vavilov ladder upper-level loss the ICvsISC channel rate `icRate` at the same reorganization energy and gap?',
        'chemicalRationale': 'KashaVavilov reuses Kasha\'s ladder (`rad`, `ic`), whose `ic` is an arbitrary rate function; its D2 adjudication quantifies over that function. ICvsISC supplies a concrete Franck-Condon-controlled IC rate `icRate = AI * exp(-fcBarrier/(kB*T))` and the competition law `rate_ratio_eq`. Chemically the ladder S2->S1 loss is the IC channel, so an "internal-conversion rate" scalar is shared; the question is whether the delivered declarations identify the two.',
        'endpoints': {'source': ('stmt-KashaVavilov-PhotoLean-KashaVavilov-d2_verdict', 'theorem'),
                      'target': ('stmt-ICvsISC-PhotoLean-ICvsISC-icRate', 'definition')},
        'sharedContext': 'KvIcCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate premise `hic : ic 1 = icRate ...` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate is a composition of the ladder verdict (KashaRule/Vavilov over the free `ic`) with the ICvsISC IC rate law through the missing `hic` identification.',
        'falsificationCondition': 'A delivered statement identifying the ladder `ic` with `icRate` (or a delivered conditional composition carrying the D2 verdict to the IC rate law) would move the row toward certified; a ladder and IC parameter set at which the two rates differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered `hic : ic 1 = ICvsISC.icRate AI lamI kB T xI` identification (and a conditional composition carrying it to SpecSame/KashaRule) is missing. KashaVavilov imports only Kasha.Basic/Criterion, never Kasha.Compose where the Marcus-form IC rate lives; ICvsISC proves `rate_ratio_eq` but no delivered statement instantiates a ladder level with `icRate`.',
        'searchLogRef': 'SL-RAD2-KVI-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- KV / Forster
    {
        'queryId': 'Q-RAD2-KVF-01',
        'pairId': 'P-KashaVavilov-Forster',
        'title': 'Does the ladder spectral partition constrain the Förster transfer geometry?',
        'chemicalQuestion': 'Do the Kasha-Vavilov normalized spectral fractions constrain the Förster rate or efficiency of a donor-acceptor pair?',
        'chemicalRationale': 'SpecSame is an excitation-independence predicate over normalized spectra on a level ladder. Förster objects are functions of the donor-acceptor separation (R^-6) and the orientation geometry (kappa^2). A level index and a donor-acceptor distance are different coordinates; the delivered register records no edge and the two modules import disjoint vocabularies. No total translation exists.',
        'endpoints': {'source': ('stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame', 'definition'),
                      'target': ('stmt-Forster-PhotoLean-Forster-fretRate', 'definition')},
        'sharedContext': 'KvFoDisjointCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication from a spectral-agreement premise to a transfer-rate premise; the jurisdiction record denies the shared translation.',
        'falsificationCondition': 'A delivered statement mapping a ladder level to a donor-acceptor geometry would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared context or declared translation exists: the ladder is indexed by a level and partitioned over normalized spectra, Förster is indexed by a separation and an orientation geometry. The absence is jurisdictional, not a refutation.',
        'searchLogRef': 'SL-RAD2-KVF-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: a ladder level index cannot be mapped to a donor-acceptor distance or orientation angle, and no delivered declaration relates the two.',
        'provenanceKind': 'jurisdiction',
    },
    # ---------------------------------------------------------------- KV / Einstein
    {
        'queryId': 'Q-RAD2-KVE-01',
        'pairId': 'P-KashaVavilov-Einstein',
        'title': "Is the ladder's radiative branch the Einstein A coefficient?",
        'chemicalQuestion': 'Is the per-level radiative rate `rad` of the Kasha-Vavilov ladder the Einstein A coefficient of the same electronic transition?',
        'chemicalRationale': 'The ladder carries a free radiative rate function `rad : N -> R`; the Einstein theory supplies radiative conversion coefficients `aOfB`, `radFactor` and the radiative lifetime `tauR`. Both are radiative rates, so a scalar-level identification is expressible at a chosen transition; the question is whether any delivered declaration makes it and carries the KV spectral predicates to the Einstein coefficient.',
        'endpoints': {'source': ('stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame', 'definition'),
                      'target': ('stmt-Einstein-PhotoLean-Einstein-aOfB', 'definition')},
        'sharedContext': 'KvEbCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate identification `rad 0 = aOfB K B21` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate composes the ladder spectral predicates with the Einstein coefficient through a missing `rad = A` identification.',
        'falsificationCondition': 'A delivered statement identifying a ladder radiative rate with an Einstein coefficient would move the row toward certified; a ladder and coefficient at which they differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered identification of the ladder radiative rate `rad n` with an Einstein coefficient (`aOfB K B21`) and a composition carrying it to SpecSame is missing; KashaVavilov quantifies over an arbitrary `rad` and never references the Einstein module.',
        'searchLogRef': 'SL-RAD2-KVE-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- SV / EnergyGapLaw
    {
        'queryId': 'Q-RAD2-SVE-01',
        'pairId': 'P-SternVolmer-EnergyGapLaw',
        'title': 'Is the Stern-Volmer quencher channel an energy-gap-law nonradiative channel?',
        'chemicalQuestion': 'Is the concentration-dependent Stern-Volmer channel `kq * q` the energy-gap-law nonradiative rate `nrRate` of the same excited state?',
        'chemicalRationale': 'SternVolmer models dynamic quenching as an added decay channel `kq * q`, linear in quencher concentration with a free rate constant `kq`. EnergyGapLaw gives a nonradiative rate exponential in the gap and barrier, `nrRate = A * exp(-nrBarrier/(kB*T))`. Both are nonradiative decay rates, but SternVolmer carries no gap coordinate and EnergyGapLaw carries no quencher concentration. A candidate bridge would equip `kq` with the EGL law at a quencher-induced gap; no delivered statement does so.',
        'endpoints': {'source': ('stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay', 'definition'),
                      'target': ('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition')},
        'sharedContext': 'SvEgCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate `kq * q = nrRate ...` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate composes the Stern-Volmer decay law with the energy-gap-law rate through a missing concentration-to-gap translation.',
        'falsificationCondition': 'A delivered statement identifying `kq * q` with `nrRate` at a declared gap would move the row toward certified; a quencher channel and an EGL rate at which they differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered identification of the Stern-Volmer channel `kq * q` with the energy-gap-law rate `nrRate A lam kB T x` at a declared quencher-induced gap is missing; SternVolmer has no gap coordinate and EnergyGapLaw has no concentration axis.',
        'searchLogRef': 'SL-RAD2-SVE-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- SV / StokesShift
    {
        'queryId': 'Q-RAD2-SVS-01',
        'pairId': 'P-SternVolmer-StokesShift',
        'title': 'Does the Stern-Volmer intensity ratio constrain the Stokes band separation?',
        'chemicalQuestion': 'Does the Stern-Volmer intensity ratio, a function of quencher concentration, constrain the Stokes shift, the energy separation of the absorption and emission maxima?',
        'chemicalRationale': 'The Stern-Volmer observable is a dimensionless intensity/lifetime ratio over a concentration axis; the Stokes shift is an energy difference over a nuclear-coordinate surface pair. The two objects have different dimensions, axes and units, and no total translation exists. The delivered register records no edge.',
        'endpoints': {'source': ('sternvolmer.intensityDyn', 'definition'),
                      'target': ('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition')},
        'sharedContext': 'SvSsDisjointCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication from a Stern-Volmer ratio premise to a band-energy premise; the jurisdiction record denies the shared translation.',
        'falsificationCondition': 'A delivered statement deriving a band energy from a Stern-Volmer ratio would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared context or declared translation exists: a concentration-dependent dimensionless ratio and a band-position energy are different observables with no declared map. The absence is jurisdictional, not a refutation.',
        'searchLogRef': 'SL-RAD2-SVS-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: the Stern-Volmer ratio is a dimensionless function of quencher concentration, the Stokes shift an energy difference over a nuclear coordinate.',
        'provenanceKind': 'jurisdiction',
    },
    # ---------------------------------------------------------------- SV / ICvsISC
    {
        'queryId': 'Q-RAD2-SVI-01',
        'pairId': 'P-SternVolmer-ICvsISC',
        'title': 'Is the quencher-added decay channel an IC or ISC channel?',
        'chemicalQuestion': 'Is the Stern-Volmer quencher channel `kq * q` an internal-conversion or intersystem-crossing channel of the ICvsISC competition at the same gap?',
        'chemicalRationale': 'Both theories add or compare nonradiative decay channels: SternVolmer adds `kq * q` to the excited-state decay, ICvsISC compares the FC-controlled `icRate` and the spin-controlled `iscRate`. A candidate translation equips the quencher channel with the ICvsISC rate law at the encounter geometry; SternVolmer keeps `kq` a free constant and ICvsISC has no concentration axis, so no delivered statement closes it.',
        'endpoints': {'source': ('sternvolmer.intensityDyn', 'definition'),
                      'target': ('stmt-ICvsISC-PhotoLean-ICvsISC-icRate', 'definition')},
        'sharedContext': 'SvIcCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate `kq * q = icRate ...` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate composes the Stern-Volmer decay law with the ICvsISC channel rate through a missing concentration-to-gap/spin translation.',
        'falsificationCondition': 'A delivered statement identifying `kq * q` with `icRate` or `iscRate` would move the row toward certified; a quencher channel and a channel rate at which they differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered identification of the Stern-Volmer channel `kq * q` with the ICvsISC `icRate`/`iscRate` at a declared encounter geometry is missing; SternVolmer has no gap or spin coordinate and ICvsISC has no concentration axis.',
        'searchLogRef': 'SL-RAD2-SVI-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- SV / Forster
    {
        'queryId': 'Q-RAD2-SVF-01',
        'pairId': 'P-SternVolmer-Forster',
        'title': 'Is the apparent 1 + control identity a shared physical law or a shape coincidence?',
        'chemicalQuestion': 'Does the inverse Förster efficiency form `1 + R^6/r0^6` identify the Stern-Volmer concentration control `1 + KSV*[Q]` with a Förster distance control?',
        'chemicalRationale': 'The delivered shape row `fretEff6_inv_eq_one_plus` and the Stern-Volmer linear ratio both read `1 + control`, but the controls are physically and dimensionally different: quencher concentration times a rate constant versus a sixth-power distance ratio. The legacy registry classifies the pair as look-alike / shape-note (`D-S15-fretEff6_inv_eq_one_plus`), not an edge. A shape identity is not a shared physical coordinate; declaring one would be exactly the forced shape-only relation the audit forbids.',
        'endpoints': {'source': ('sternvolmer.intensityDyn', 'definition'),
                      'target': ('stmt-Forster-PhotoLean-Forster-fretEff6', 'definition')},
        'sharedContext': 'SvFoShapeCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication identifying the two `1 + control` curves; the jurisdiction record denies that the shared shape is a shared physical coordinate.',
        'falsificationCondition': 'A delivered statement translating quencher concentration into a donor-acceptor sixth-power ratio would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared physical context or declared translation exists: the shared `1 + control` form is a shape coincidence between a concentration control and a distance control, and the legacy ledger itself records it as a shape note, not an edge. The finding is jurisdictional, not logical absence.',
        'searchLogRef': 'SL-RAD2-SVF-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: `KSV*q` (concentration x rate constant) and `R^6/r6` (sixth-power distance ratio) are different controls that happen to share the `1 + control` shape; the delivered shape row is not a physical identity.',
        'provenanceKind': 'jurisdiction',
    },
    # ---------------------------------------------------------------- SV / Einstein
    {
        'queryId': 'Q-RAD2-SVEb-01',
        'pairId': 'P-SternVolmer-Einstein',
        'title': "Is the intrinsic decay's radiative part the Einstein A coefficient?",
        'chemicalQuestion': 'Is the radiative part of the Stern-Volmer intrinsic decay `k0` the Einstein A coefficient of the same transition?',
        'chemicalRationale': 'SternVolmer keeps `k0` as the total intrinsic decay and `KSV = kq/k0`; it never splits `k0` into radiative and nonradiative parts. Einstein supplies the radiative coefficient `A` and the radiative lifetime `tauR A = 1/A`. Physically k0 = kr + knr with kr = A, but no delivered SternVolmer statement performs that split or identifies kr with A; the Stern-Volmer lifetime ratio uses k0 whole.',
        'endpoints': {'source': ('sternvolmer.intensityDyn', 'definition'),
                      'target': ('stmt-Einstein-PhotoLean-Einstein-tauR', 'definition')},
        'sharedContext': 'SvEbCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate split `k0 = A + kNR` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate composes the Stern-Volmer decay ratio with the Einstein radiative rate through a missing split of `k0`.',
        'falsificationCondition': 'A delivered statement splitting `k0` into `A + kNR` and identifying the radiative part with an Einstein coefficient would move the row toward certified; a SternVolmer decay and an Einstein rate at which they differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered split of the Stern-Volmer intrinsic decay `k0` into a radiative Einstein coefficient `A` and a nonradiative rate `kNR` is missing; SternVolmer treats `k0` as an indivisible free parameter.',
        'searchLogRef': 'SL-RAD2-SVEb-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- QY / EnergyGapLaw (certified)
    {
        'queryId': 'Q-RAD2-QYE-01',
        'pairId': 'P-QuantumYield-EnergyGapLaw',
        'title': 'The radiative/nonradiative branching ratio is the energy-gap-law rate ratio',
        'chemicalQuestion': 'When the nonradiative channel of a two-channel excited state is governed by the energy-gap law, does the quantum-yield branching ratio of the radiative channel equal the EGL rate ratio written through its barrier?',
        'chemicalRationale': 'QuantumYield is the parallel-channel calculus: `yieldOf k i = k i / sum k`, and its relative-yield law `yieldOf_div_yieldOf` makes a branch ratio a rate ratio. EnergyGapLaw supplies the nonradiative rate `nrRate = A * exp(-nrBarrier/(kB*T))`. Composing them turns a spectroscopic branching observable into the EGL barrier exponential: the statement-level bridge between the yield algebra and the energy-gap law.',
        'endpoints': {'source': ('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf_div_yieldOf', 'theorem'),
                      'target': ('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition')},
        'sharedContext': 'QyEgCtx',
        'translations': 'identity',
        'premises': premises_defs(
            'fun δ : QyEgCtx => 0 < δ.kr ∧ 0 < δ.A',
            [
                {'id': 'qyEg.krPositive', 'predicate': 'fun δ => 0 < δ.kr',
                 'statement': 'the radiative rate is positive',
                 'loadBearing': 'the relative-yield law divides by the radiative channel and field_simp clears the 1/kr denominator'},
                {'id': 'qyEg.preFactorPositive', 'predicate': 'fun δ => 0 < δ.A',
                 'statement': 'the EGL pre-exponential factor is positive',
                 'loadBearing': 'makes nrRate positive and clears the 1/A denominator in the barrier-exponential form'},
            ],
            'The totalized division makes kB*T > 0 non-load-bearing for this identity, so it is not declared.'),
        'channels': [{
            'id': 'radiativeToNonradiativeBranchRatio',
            'name': 'radiativeToNonradiativeBranchRatio',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': 'fun δ _ => QuantumYield.yieldOf ![δ.kr, EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x] 0 / QuantumYield.yieldOf ![δ.kr, EnergyGapLaw.nrRate δ.A δ.lam δ.kB δ.T δ.x] 1',
            'rightObs': 'fun δ _ => (δ.kr / δ.A) * Real.exp (EnergyGapLaw.nrBarrier δ.lam δ.x / (δ.kB * δ.T))',
        }],
        'scope': 'scope-RAD2-qy-eg-branch',
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': 'Both readings are real-valued observables on the shared context; the certificate is equality of the declared branch-ratio channel against the barrier-exponential channel.',
        'falsificationCondition': 'A context (kr, A, lam, kB, T, x) with kr > 0 and A > 0 at which the QY branch ratio differs from (kr/A)*exp(nrBarrier/(kB*T)) would refute the equality; the certificate covers every such context.',
        'status': 'certified',
        'outcomeRationale': 'The probe theorem qyEgBranchRatio and the observational channel certificate qyEgBridge are checked; the equality holds for every kr > 0, A > 0 and every lam, kB, T, x.',
        'evidence': certified_evidence(
            'RAD2-QYE-01', 'qyEgBridge', 'qyEgBridge_kind',
            [
                thm('PhotoLean.QuantumYield.yieldOf_div_yieldOf', 'PhotoLean/QuantumYield/Criterion.lean', 96,
                    'relative-yield law: the branch ratio is the rate ratio'),
                thm('PhotoLean.EnergyGapLaw.cert_nrRate', 'PhotoLean/EnergyGapLaw/Basic.lean', 80,
                    'delivered EGL rate / Marcus rate pin'),
                thm('PhotoLean.EnergyGapLaw.cert_nrBarrier', 'PhotoLean/EnergyGapLaw/Basic.lean', 67,
                    'delivered EGL barrier / kernel barrier pin'),
            ],
            'The probe composes the delivered relative-yield law with the delivered EGL rate law and rewrites the rate ratio through nrBarrier. It is not a pair-anchor reuse and not a shape identity: the two sides are the QY branch observable and the EGL barrier exponential.'),
        'provenanceKind': 'certificate',
    },
    # ---------------------------------------------------------------- QY / StokesShift
    {
        'queryId': 'Q-RAD2-QYS-01',
        'pairId': 'P-QuantumYield-StokesShift',
        'title': 'Does the quantum-yield partition constrain the Stokes band separation?',
        'chemicalQuestion': 'Does the quantum-yield partition of an excited state constrain the Stokes shift of the same chromophore?',
        'chemicalRationale': 'QuantumYield is a dimensionless branching partition `k i / sum k` over decay channels. StokesShift is an energy difference between vertical absorption and emission on a displaced-parabola pair. The yield algebra contains no band energy and the surface model contains no channel partition; no total translation exists. The delivered register records no edge.',
        'endpoints': {'source': ('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf', 'definition'),
                      'target': ('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition')},
        'sharedContext': 'QySsDisjointCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication from a yield-partition premise to a band-energy premise; the jurisdiction record denies the shared translation.',
        'falsificationCondition': 'A delivered statement deriving a band energy from a channel partition would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared context or declared translation exists: a dimensionless channel partition and a band-position energy are different observables. The absence is jurisdictional, not a refutation.',
        'searchLogRef': 'SL-RAD2-QYS-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: `yieldOf` is a dimensionless partition over decay rates, `emEnergy` is an energy difference over a nuclear coordinate.',
        'provenanceKind': 'jurisdiction',
    },
    # ---------------------------------------------------------------- QY / ICvsISC (certified)
    {
        'queryId': 'Q-RAD2-QYI-01',
        'pairId': 'P-QuantumYield-ICvsISC',
        'title': 'The ISC/IC branch ratio is the ICvsISC spin/FC rate ratio',
        'chemicalQuestion': 'Is the quantum-yield branching ratio of the intersystem-crossing channel over the internal-conversion channel the ICvsISC spin/prefactor times Franck-Condon rate ratio?',
        'chemicalRationale': 'The quantum-yield relative-yield law makes the ISC/IC branch ratio a rate ratio. ICvsISC rate_ratio_eq factors that ratio into `HSO^2 * AS / AI` times the Franck-Condon exponential. The composition is the statement-level bridge between the branching observable and the IC/ISC competition law; the spin-orbit coupling enters squared, exactly as the ICvsISC theory states.',
        'endpoints': {'source': ('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf_div_yieldOf', 'theorem'),
                      'target': ('stmt-ICvsISC-PhotoLean-ICvsISC-rate_ratio_eq', 'theorem')},
        'sharedContext': 'QyIcCtx',
        'translations': 'identity',
        'premises': premises_defs(
            'fun δ : QyIcCtx => ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T ∧ 0 < δ.HSO',
            [
                {'id': 'qyIc.fcData', 'predicate': 'fun δ => ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T',
                 'statement': 'the ICvsISC premise bundle (positive prefactors, reorganization energies and kB*T)',
                 'loadBearing': 'rate_ratio_eq consumes FCData to clear AI and the exponentials; positivity makes both channel rates positive'},
                {'id': 'qyIc.hsoPositive', 'predicate': 'fun δ => 0 < δ.HSO',
                 'statement': 'the spin-orbit coupling is positive',
                 'loadBearing': 'makes the ISC rate `HSO^2 * AS * exp(...)` positive so the relative-yield law can divide by it'},
            ],
            'Both premises are consumed: FCData by rate_ratio_eq and by IC positivity, HSO > 0 by ISC positivity.'),
        'channels': [{
            'id': 'iscToIcBranchRatio',
            'name': 'iscToIcBranchRatio',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': 'fun δ _ => QuantumYield.yieldOf ![ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI, ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS] 1 / QuantumYield.yieldOf ![ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI, ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS] 0',
            'rightObs': 'fun δ _ => (δ.HSO ^ 2 * δ.AS / δ.AI) * Real.exp ((ICvsISC.fcBarrier δ.lamI δ.xI - ICvsISC.fcBarrier δ.lamS δ.xS) / (δ.kB * δ.T))',
        }],
        'scope': 'scope-RAD2-qy-ic-branch',
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': 'Both readings are real-valued observables on the shared context; the certificate is equality of the QY branch-ratio channel against the ICvsISC spin/FC ratio channel.',
        'falsificationCondition': 'An ICvsISC parameter tuple satisfying FCData with HSO > 0 at which the QY ISC/IC branch ratio differs from `(HSO^2*AS/AI)*exp((fcBarrier_I - fcBarrier_S)/(kB*T))` would refute the equality; the certificate covers every such tuple.',
        'status': 'certified',
        'outcomeRationale': 'The probe theorem qyIcBranchRatio and the observational channel certificate qyIcBridge are checked; the QY branch ratio equals the delivered ICvsISC rate_ratio_eq right-hand side for every FCData tuple with HSO > 0.',
        'evidence': certified_evidence(
            'RAD2-QYI-01', 'qyIcBridge', 'qyIcBridge_kind',
            [
                thm('PhotoLean.QuantumYield.yieldOf_div_yieldOf', 'PhotoLean/QuantumYield/Criterion.lean', 96,
                    'relative-yield law: the branch ratio is the rate ratio'),
                thm('PhotoLean.ICvsISC.rate_ratio_eq', 'PhotoLean/ICvsISC/Criterion.lean', 80,
                    'delivered IC/ISC spin x FC competition law'),
                thm('PhotoLean.ICvsISC.icRate', 'PhotoLean/ICvsISC/Basic.lean', 72,
                    'delivered IC channel rate (consumed by the QY vector)'),
                thm('PhotoLean.ICvsISC.iscRate', 'PhotoLean/ICvsISC/Basic.lean', 85,
                    'delivered ISC channel rate with the explicit HSO^2 prefactor'),
            ],
            'The probe composes the delivered relative-yield law with the delivered rate_ratio_eq. The result is a genuine branching-observable / competition-law bridge, not a renaming: the left side is the QY partition and the right side is the ICvsISC factorization.'),
        'provenanceKind': 'certificate',
    },
    # ---------------------------------------------------------------- QY / Forster (certified)
    {
        'queryId': 'Q-RAD2-QYF-01',
        'pairId': 'P-QuantumYield-Forster',
        'title': "The Förster transfer efficiency is one minus the donor's retained yield",
        'chemicalQuestion': "Is the Förster transfer efficiency of a donor-acceptor pair one minus the donor's retained radiative quantum yield in the added-channel model?",
        'chemicalRationale': 'FRET is an added donor decay channel `kD * (r0^6/R^6)`. The quantum-yield algebra gives the donor retained radiative share in the enlarged channel vector. The delivered composition `fretEff6_eq_one_sub_yieldOf` states that the transfer efficiency is the complement; the certificate reads it as an equality of the transfer-efficiency observable and the retained-yield observable.',
        'endpoints': {'source': ('stmt-Forster-PhotoLean-Forster-fretEff6', 'definition'),
                      'target': ('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf', 'definition')},
        'sharedContext': 'QyFoCtx',
        'translations': 'identity',
        'premises': premises_defs(
            'fun δ : QyFoCtx => 0 < δ.kD ∧ 0 ≤ δ.r6 ∧ δ.R ≠ 0',
            [
                {'id': 'qyFo.donorRatePositive', 'predicate': 'fun δ => 0 < δ.kD',
                 'statement': 'the donor radiative rate is positive',
                 'loadBearing': 'makes the donor total rate positive in the added-channel yield'},
                {'id': 'qyFo.r6Nonnegative', 'predicate': 'fun δ => 0 ≤ δ.r6',
                 'statement': 'the Förster sixth power is nonnegative',
                 'loadBearing': 'makes the added FRET channel nonnegative so the denominator stays positive'},
                {'id': 'qyFo.separationNonzero', 'predicate': 'fun δ => δ.R ≠ 0',
                 'statement': 'the donor-acceptor separation is nonzero',
                 'loadBearing': 'makes R^6 positive so the FRET channel is finite and the field_simp denominator is nonzero'},
            ],
            'These are exactly the premises of the delivered fretEff6_eq_one_sub_yieldOf row.'),
        'channels': [{
            'id': 'transferEfficiencyVersusRetainedDonorYield',
            'name': 'transferEfficiencyVersusRetainedDonorYield',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': 'fun δ _ => Forster.fretEff6 δ.r6 δ.R',
            'rightObs': 'fun δ _ => 1 - QuantumYield.yieldOf ![δ.kD, δ.kD * (δ.r6 / δ.R ^ 6)] 0',
        }],
        'scope': 'scope-RAD2-qy-fo-efficiency',
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': 'Both readings are real-valued observables on the shared context; the certificate is equality of the transfer-efficiency channel against the retained-yield channel.',
        'falsificationCondition': "A context (kD, r6, R) with kD > 0, r6 >= 0 and R != 0 at which the Förster efficiency differs from one minus the donor retained yield would refute the equality; the certificate covers every such context.",
        'status': 'certified',
        'outcomeRationale': 'The probe theorem qyFoEfficiency and the observational channel certificate qyFoBridge are checked; the equality is the delivered §15 composition `fretEff6_eq_one_sub_yieldOf` read as a channel equality.',
        'evidence': certified_evidence(
            'RAD2-QYF-01', 'qyFoBridge', 'qyFoBridge_kind',
            [
                thm('PhotoLean.Relations.fretEff6_eq_one_sub_yieldOf', 'PhotoLean/Relations.lean', 836,
                    'delivered composition row: FRET efficiency = 1 - donor yield'),
                thm('PhotoLean.Forster.fretEff6', 'PhotoLean/Forster/Basic.lean', 57,
                    'delivered Förster efficiency definition'),
                thm('PhotoLean.QuantumYield.yieldOf', 'PhotoLean/QuantumYield/Basic.lean', 44,
                    'delivered quantum-yield definition'),
            ],
            'The certificate consumes the delivered cross-theory composition row verbatim; the probe is a channel-level restatement, not a new axiom or a pair anchor.'),
        'provenanceKind': 'certificate',
    },
    # ---------------------------------------------------------------- QY / Einstein (certified)
    {
        'queryId': 'Q-RAD2-QYEB-01',
        'pairId': 'P-QuantumYield-Einstein',
        'title': 'The Einstein radiative fraction is the radiative quantum yield',
        'chemicalQuestion': 'Is the Einstein radiative fraction `A * tauR(A + kNR)` of a two-channel decay the quantum yield of the radiative channel?',
        'chemicalRationale': 'Einstein tauR A = 1/A is the radiative lifetime. In a two-channel decay with total rate A + kNR the observed lifetime is 1/(A + kNR), so the radiative fraction is A/(A + kNR); the quantum yield of the radiative channel is exactly that share. The delivered composition `einstein_yield_via_qy` makes the identification, and the certificate reads it as an equality of the radiative-fraction observable and the QY yield.',
        'endpoints': {'source': ('stmt-Einstein-PhotoLean-Einstein-tauR', 'definition'),
                      'target': ('stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf', 'definition')},
        'sharedContext': 'QyEbCtx',
        'translations': 'identity',
        'premises': premises_true('The delivered identity `A * tauR (A + kNR) = yieldOf ![A, kNR] 0` is totalized over R^2 and carries no premise, so none is declared.'),
        'channels': [{
            'id': 'radiativeFractionVersusRadiativeYield',
            'name': 'radiativeFractionVersusRadiativeYield',
            'observedValueType': 'ℝ',
            'inputDomain': 'Unit (the single declared configuration)',
            'domainNonempty': True,
            'leftObs': 'fun δ _ => δ.A * Einstein.tauR (δ.A + δ.kNR)',
            'rightObs': 'fun δ _ => QuantumYield.yieldOf ![δ.A, δ.kNR] 0',
        }],
        'scope': 'scope-RAD2-qy-eb-radiative',
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': 'Both readings are real-valued observables on the shared context; the certificate is equality of the radiative-fraction channel and the radiative-yield channel.',
        'falsificationCondition': 'A context (A, kNR) at which the Einstein radiative fraction differs from the two-channel radiative yield would refute the equality; the totalized identity covers all of R^2.',
        'status': 'certified',
        'outcomeRationale': 'The probe theorem qyEbRadiativeYield and the observational channel certificate qyEbBridge are checked; the equality is the delivered §15 composition `einstein_yield_via_qy` read as a channel equality.',
        'evidence': certified_evidence(
            'RAD2-QYEB-01', 'qyEbBridge', 'qyEbBridge_kind',
            [
                thm('PhotoLean.Relations.einstein_yield_via_qy', 'PhotoLean/Relations.lean', 826,
                    'delivered composition row: radiative fraction = radiative quantum yield'),
                thm('PhotoLean.Einstein.tauR', 'PhotoLean/Einstein/Basic.lean', 65,
                    'delivered radiative lifetime definition'),
                thm('PhotoLean.QuantumYield.yieldOf', 'PhotoLean/QuantumYield/Basic.lean', 44,
                    'delivered quantum-yield definition'),
            ],
            'The certificate consumes the delivered cross-theory composition row verbatim; the probe is a channel-level restatement, not a new axiom or a pair anchor.'),
        'provenanceKind': 'certificate',
    },
    # ---------------------------------------------------------------- FP / EnergyGapLaw
    {
        'queryId': 'Q-RAD2-FPE-01',
        'pairId': 'P-FluorPhos-EnergyGapLaw',
        'title': 'Is the S1 internal-conversion rate an energy-gap-law rate?',
        'chemicalQuestion': 'Is the FluorPhos S1 internal-conversion rate `kIC` the energy-gap-law nonradiative rate at the S1->S0 gap?',
        'chemicalRationale': 'FluorPhos leaves `kIC` a free rate in `phiF = kF/(kF + kISC + kIC)`. EnergyGapLaw supplies `nrRate = A * exp(-nrBarrier/(kB*T))` for a nonradiative electronic relaxation. Chemically the S1->S0 internal-conversion channel is exactly such a relaxation, so a candidate translation `kIC = nrRate` exists; no delivered statement instantiates it, and FluorPhos carries no barrier or gap premise.',
        'endpoints': {'source': ('stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay', 'definition'),
                      'target': ('stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate', 'definition')},
        'sharedContext': 'FpEgCandidateCtx',
        'translations': 'candidate',
        'premises': premises_true('No certificate is claimed; the candidate `kIC = nrRate ...` is not load-bearing for any delivered disposition.'),
        'channels': [],
        'scope': 'scope-RAD2-candidate-bridge',
        'expectedKind': 'conditionalComposition',
        'expectedKindRationale': 'The candidate composes the FluorPhos S1 decay law with the EGL rate through the missing `kIC = nrRate` identification.',
        'falsificationCondition': 'A delivered statement identifying `kIC` with `nrRate` at a declared S1->S0 gap would move the row toward certified; a FluorPhos rate vector and an EGL rate at which they differ would refute the identification.',
        'status': 'unresolved',
        'candidateSummary': 'A delivered identification of the FluorPhos S1 internal-conversion rate `kIC` with the energy-gap-law rate `nrRate A lam kB T x` at the S1->S0 gap is missing; FluorPhos treats `kIC` as a free rate and has no barrier/gap premise.',
        'searchLogRef': 'SL-RAD2-FPE-01',
        'provenanceKind': 'scoped-search',
    },
    # ---------------------------------------------------------------- FP / StokesShift
    {
        'queryId': 'Q-RAD2-FPS-01',
        'pairId': 'P-FluorPhos-StokesShift',
        'title': 'Do the fluorescence/phosphorescence branch probabilities constrain the Stokes band separation?',
        'chemicalQuestion': 'Do the S1/T1 branch probabilities of the fluorescence-phosphorescence competition constrain the Stokes shift of the same chromophore?',
        'chemicalRationale': 'FluorPhos objects are branch probabilities over decay channels (`phiF`, `iscBranch`, `phiP`). StokesShift objects are band-position energies from a displaced-parabola surface pair. A probability partition and an energy difference share no scalar; the delivered register records no edge and no total translation exists.',
        'endpoints': {'source': ('stmt-FluorPhos-PhotoLean-FluorPhos-phiF', 'definition'),
                      'target': ('stmt-StokesShift-PhotoLean-StokesShift-emEnergy', 'definition')},
        'sharedContext': 'FpSsDisjointCtx',
        'translations': 'none',
        'premises': premises_true('No certificate is claimed; the jurisdiction record does not consume a premise.'),
        'channels': [],
        'scope': 'scope-RAD2-jurisdiction',
        'expectedKind': 'implication',
        'expectedKindRationale': 'The would-be form is an implication from a branch-probability premise to a band-energy premise; the jurisdiction record denies the shared translation.',
        'falsificationCondition': 'A delivered statement deriving a band energy from a branch probability would refute the jurisdiction boundary; none exists.',
        'status': 'outOfScope',
        'outcomeRationale': 'No shared context or declared translation exists: FluorPhos partitions branch probabilities over decay channels, StokesShift compares band-position energies. The absence is jurisdictional, not a refutation.',
        'searchLogRef': 'SL-RAD2-FPS-01',
        'jurisdictionRationale': 'No shared context or declared translation exists: a branch probability is a dimensionless partition over rates, a band position is an energy over a nuclear coordinate.',
        'provenanceKind': 'jurisdiction',
    },
]

# pair -> query (sanity)
assert [q['pairId'] for q in QUERIES] == PAIR_IDS, [q['pairId'] for q in QUERIES]

# Explicit disposition rationales for the unresolved rows (the candidate is not a verdict).
_UNRESOLVED_RATIONALE = {
    'Q-RAD2-KVI-01': 'No disposition has been reached: the ladder IC channel and the ICvsISC FC rate law are chemically the same scalar, but no delivered statement identifies them and KashaVavilov has no import path to the Marcus-form IC rate.',
    'Q-RAD2-KVE-01': 'No disposition has been reached: both sides carry radiative rates, but no delivered statement identifies the free ladder rate function with an Einstein coefficient.',
    'Q-RAD2-SVE-01': 'No disposition has been reached: both sides are nonradiative decay rates, but no delivered translation connects the quencher concentration to a driving force or the EGL barrier to a concentration channel.',
    'Q-RAD2-SVI-01': 'No disposition has been reached: both sides are nonradiative decay channels, but no delivered statement identifies the quencher channel with an ICvsISC IC/ISC channel at a declared geometry.',
    'Q-RAD2-SVEb-01': 'No disposition has been reached: both sides carry decay rates, but no delivered statement splits the Stern-Volmer intrinsic decay into a radiative Einstein coefficient and a nonradiative rate.',
    'Q-RAD2-FPE-01': 'No disposition has been reached: the FluorPhos S1 internal-conversion rate is chemically a candidate for the EGL rate, but no delivered statement instantiates it.',
}
for _q in QUERIES:
    if _q['status'] == 'unresolved':
        _q.setdefault('outcomeRationale', _UNRESOLVED_RATIONALE[_q['queryId']])


def expand_query(q):
    out = dict(q)
    out['endpoints'] = {
        side: endpoint(sid, form)
        for side, (sid, form) in q['endpoints'].items()
    }
    cid = q['sharedContext']
    out['sharedContext'] = ctx(cid)
    if q['translations'] == 'identity':
        out['translations'] = trans_identity()
    elif q['translations'] == 'none':
        out['translations'] = trans_none(
            'No total translation between the two disjoint descriptor sets is declared.')
    elif q['translations'] == 'candidate':
        out['translations'] = trans_candidate(
            'No delivered total translation from the shared candidate context to this statement context is declared; the identification is a candidate.',
            'No delivered total translation from the partner statement context to the shared candidate context is declared; the identification is a candidate.')
    else:
        raise AssertionError(q['translations'])
    out['scope'] = scope(q['scope'])
    out['observationChannels'] = list(q['channels'])
    status = q['status']
    if status == 'certified':
        evidence = q['evidence']
    elif status in ('unresolved', 'notEstablished'):
        evidence = {
            'type': 'scoped-search',
            'searchLogRef': q['searchLogRef'],
            'candidateSummary': q['candidateSummary'],
        }
    elif status == 'outOfScope':
        evidence = {
            'type': 'jurisdiction',
            'searchLogRef': q['searchLogRef'],
            'jurisdictionRationale': q['jurisdictionRationale'],
        }
    else:
        raise AssertionError(status)
    out['outcome'] = {
        'status': status,
        'rationale': q['outcomeRationale'],
        'evidence': evidence,
    }
    if status == 'certified':
        out['provenance'] = {
            'kind': 'rad2-probe-certificate',
            'certificateId': evidence['certificateId'],
            'sourceArtifact': PROBE_REL,
            'locator': evidence['probe']['declaration'],
            'legacyDisposition': 'The legacy record for this pair is a pair-level notEstablished anchor; it is coverage history, not an audit verdict, and is not cited as evidence.',
        }
    elif status == 'outOfScope':
        out['provenance'] = {
            'kind': 'jurisdiction',
            'sourceArtifact': SEARCH_REL,
            'locator': q['searchLogRef'],
            'jurisdictionStatement': q['jurisdictionRationale'],
            'legacyDisposition': 'The legacy record for this pair is a pair-level notEstablished anchor (or a shape-note disposition); it is coverage history, not an audit verdict, and is not cited as evidence.',
        }
    else:
        out['provenance'] = {
            'kind': 'scoped-search',
            'sourceArtifact': SEARCH_REL,
            'locator': q['searchLogRef'],
            'legacyDisposition': 'The legacy record for this pair is a pair-level notEstablished anchor; it is coverage history, not an audit verdict, and is not cited as evidence.',
        }
    for helper in ('status', 'outcomeRationale', 'evidence', 'searchLogRef',
                   'candidateSummary', 'jurisdictionRationale', 'provenanceKind',
                   'channels'):
        out.pop(helper, None)
    return out


def search_entry(q):
    """Build the search-log entry for one non-certified query."""
    return SEARCH[q['queryId']]


def build_search_log():
    entries = [SEARCH[q['queryId']] for q in QUERIES
               if q['status'] in ('unresolved', 'notEstablished', 'outOfScope')]
    doc = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': WP_ID,
        'snapshot': SNAP,
        'counts': {
            'entries': len(entries),
            'byStatus': {
                'unresolved': sum(1 for e in entries if e['status'] == 'unresolved'),
                'outOfScope': sum(1 for e in entries if e['status'] == 'outOfScope'),
            },
        },
        'entries': entries,
        'nonClaims': [
            'A search entry records a scoped, machine-recomputable search; it is not a negative claim outside the named statements, kinds, and contexts.',
            'The outOfScope entries record jurisdiction, not logical absence.',
            'No failed proof attempt is relabelled as a refutation.',
        ],
    }
    path = os.path.join(ROOT, SEARCH_REL)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write('\n')
    return sha(path)


def build_screening(search_sha):
    pairs = []
    all_queries = []
    for pid in PAIR_IDS:
        qs = [q for q in QUERIES if q['pairId'] == pid]
        expanded = [expand_query(q) for q in qs]
        all_queries.extend(expanded)
        qrow = QUEUE_BY_ID[pid]
        pairs.append({
            'pairId': pid,
            'theories': list(qrow['theories']),
            'primaryCluster': qrow['screeningCluster'],
            'queryIds': [q['queryId'] for q in expanded],
            'queries': expanded,
        })
    status_counts = {}
    kind_counts = {}
    for q in all_queries:
        status = q['outcome']['status']
        status_counts[status] = status_counts.get(status, 0) + 1
        kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1
    doc = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WP_ID,
            'title': 'Radiative and energy-transfer relations, second block: Kasha-Vavilov, Stern-Volmer, quantum yield and fluorescence/phosphorescence bridges',
            'source': 'R5 plan file, Package RAD2',
            'pairIds': list(PAIR_IDS),
            'pairCount': len(PAIR_IDS),
            'note': 'Exactly the sixteen pairs assigned by R1 WP-radiative-energy-transfer-02. No accepted R2/R3/R4 pair is rescreened.',
        },
        'statusVocabulary': STATUSES,
        'kindVocabulary': KINDS,
        'allowedAxioms': ALLOWED_AXIOMS,
        'snapshot': {
            'id': SNAP,
            'date': '2026-11-04',
            'round': 'R5',
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
            'acceptedPackages': {name: {'path': rel, 'sha256': sha_rel(rel)} for name, rel in ACCEPTED},
            'leanToolchain': 'leanprover/lean4:v4.17.0',
            'deliveredLeanFileCount': 102,
            'note': 'The mutable R5 cumulative ledger is deliberately not pinned by this package; prior coverage is derived from the accepted screening packages themselves.',
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
            'certificateCount': len(load_rel(REGISTRY_REL)['certificates']),
            'queryCount': len(load_rel(REGISTRY_REL)['queries']),
            'recordCount': len(load_rel(REGISTRY_REL)['records']),
        },
        'acceptedCoverageReference': {
            'acceptedPairs': sum(len(load_rel(rel)['pairs']) for _name, rel in ACCEPTED),
            'sources': [rel for _name, rel in ACCEPTED],
            'sourceShas': {rel: sha_rel(rel) for _name, rel in ACCEPTED},
            'note': 'Derived directly from the five accepted screening packages (R2, R3, R4-E1, R4-E2, R4-CI); the mutable R5 ledger is not read.',
        },
        'searchLogReference': {
            'path': SEARCH_REL,
            'sha256': search_sha,
            'entryCount': sum(1 for q in QUERIES if q['status'] != 'certified'),
        },
        'probeReference': {
            'path': PROBE_REL,
            'sha256': PROBE_SHA,
            'declarationCount': 4,
            'log': PROBE_LOG_REL,
        },
        'contextLibrary': {k: dict(v) for k, v in CONTEXTS.items()},
        'scopeLibrary': {k: dict(v) for k, v in SCOPES.items()},
        'aliasResolutions': [],
        'pairs': pairs,
        'counts': {
            'pairs': len(pairs),
            'queries': len(all_queries),
            'byStatus': status_counts,
            'byExpectedKind': kind_counts,
            'certified': status_counts.get('certified', 0),
            'refuted': status_counts.get('refuted', 0),
            'unresolved': status_counts.get('unresolved', 0),
            'notEstablished': status_counts.get('notEstablished', 0),
            'outOfScope': status_counts.get('outOfScope', 0),
        },
        'nonClaims': [
            'The package screens exactly the sixteen R1 WP-radiative-energy-transfer-02 pairs; it does not write the R5 cumulative ledger.',
            'Screened is not the same as certified; a certified row is model-internal under its declared context and premises.',
            'Unresolved rows are candidate registrations, not negative claims; outOfScope rows are jurisdiction findings, not logical absence.',
            'The package makes no pair-count or edge-count target claim and no claim that one query per pair exhausts all conceivable relations.',
        ],
    }
    path = os.path.join(ROOT, SCREENING_REL)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write('\n')
    return sha(path)


def build_fragment(screening_sha):
    status_counts = {}
    kind_counts = {}
    for q in QUERIES:
        status_counts[q['status']] = status_counts.get(q['status'], 0) + 1
        kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1
    rows = []
    for pid in PAIR_IDS:
        qrow = QUEUE_BY_ID[pid]
        qs = [q for q in QUERIES if q['pairId'] == pid]
        counts = {}
        for q in qs:
            counts[q['status']] = counts.get(q['status'], 0) + 1
        rows.append({
            'pairId': pid,
            'theories': list(qrow['theories']),
            'primaryCluster': qrow['screeningCluster'],
            'queryCount': len(qs),
            'byStatus': counts,
        })
    doc = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': WP_ID,
        'packagePath': SCREENING_REL,
        'screeningSha256': screening_sha,
        'pairCount': len(PAIR_IDS),
        'queryCount': len(QUERIES),
        'byStatus': status_counts,
        'byExpectedKind': kind_counts,
        'primaryCluster': 'radiative-energy-transfer',
        'screenedPairs': rows,
        'acceptance': 'submitted-R5-pending-review',
        'nonClaims': [
            'This fragment contributes sixteen pairs to the R5 cumulative ledger; it does not itself edit the ledger.',
            'Screened is not the same as certified.',
            'The fragment records the package status as submitted-R5-pending-review until independent K3 review.',
        ],
    }
    path = os.path.join(ROOT, FRAGMENT_REL)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write('\n')
    return sha(path)


SEARCH = {}


def _s(queryId, pairId, status, scope_id, searched, kinds, contexts, deps, commands,
       strategies, candidates, gap, recompute, rationale, jurisdiction=None):
    e = {
        'searchId': 'SL-RAD2-' + queryId.split('Q-RAD2-')[1],
        'queryId': queryId,
        'pairId': pairId,
        'status': status,
        'scope': scope_id,
        'snapshot': SNAP,
        'searchedStatements': searched,
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
    if jurisdiction:
        e['jurisdictionReason'] = jurisdiction
    SEARCH[queryId] = e


def dep(artifact, locator, finding):
    return {'artifact': artifact, 'locator': locator, 'finding': finding}


def cmd(command, purpose, result):
    return {'command': command, 'purpose': purpose, 'result': result}


def strat(strategy, outcome):
    return {'strategy': strategy, 'outcome': outcome}


def cand(kind, statement, status):
    return {'kind': kind, 'statement': statement, 'status': status}


_C_IMPORTS = 'Mathlib; the theory\'s own Basic/Criterion/RatModel modules (see the imports listing in evidence/search-commands.log).'
_C16 = 'PhotoLean/Relations.lean §16 extended no-edge register'

# ---- KV / StokesShift (outOfScope)
_s('Q-RAD2-KVS-01', 'P-KashaVavilov-StokesShift', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'stmt-KashaVavilov-PhotoLean-KashaVavilov-specFrac_zero_of_kashaRule',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'stmt-StokesShift-PhotoLean-StokesShift-absEnergy',
    'stmt-StokesShift-PhotoLean-StokesShift-stokesShift'],
   ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence'],
   ['KvSsDisjointCtx (rad, ic, M, N, lam, e00): a normalized spectral fraction on a level ladder versus a band-position energy on a surface pair; no total translation.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 956',
        'StokesShift <-> Kasha / KashaVavilov / ... no edge (positions of band maxima vs rates/ladders/geometries).'),
    dep('PhotoLean/KashaVavilov/Basic.lean', 'PhotoLean/KashaVavilov/Basic.lean#SpecSame',
        'SpecSame is a dimensionless normalized-spectrum predicate over ladder levels; it contains no energy coordinate.'),
    dep('PhotoLean/StokesShift/Basic.lean', 'PhotoLean/StokesShift/Basic.lean#emEnergy',
        'emEnergy is a vertical-transition energy difference; it contains no level index or photon fraction.'),
    dep('relation_audit/registry.json', 'rec-notestablished-P-KashaVavilov-StokesShift',
        'Pair-level notEstablished anchor only; no certificate and no named proposition-level query.')],
   [cmd('grep -rnE "StokesShift|emEnergy|absEnergy|stokesShift" PhotoLean/KashaVavilov --include=*.lean',
        'Search the KashaVavilov modules for a delivered StokesShift/energy statement.',
        'No matches (exit 1): the KashaVavilov vocabulary contains no band-energy symbol.'),
    cmd('grep -rnE "SpecSame|specFrac|KashaRule" PhotoLean/StokesShift --include=*.lean',
        'Search the StokesShift modules for a ladder/spectral-fraction statement.',
        'No matches (exit 1): the StokesShift vocabulary contains no ladder/spectral-fraction symbol.'),
    cmd('grep -h "^import" PhotoLean/KashaVavilov/*.lean PhotoLean/StokesShift/*.lean | sort -u',
        'Measure the two dependency closures.',
        'KashaVavilov: Mathlib + Kasha.Basic/Criterion + its own modules. StokesShift: Mathlib + Kernel + Marcus.Basic + its own modules. Neither imports the other.'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-StokesShift',
        'Recompute the accepted legacy disposition for the pair.',
        "label='absence' subtype='registered-absence'; record rec-notestablished-P-KashaVavilov-StokesShift status='notEstablished', kind=None, certificate=None.")],
   [strat('Search for a delivered theorem deriving a band energy from a normalized spectral fraction.', 'No match in either module.'),
    strat('Try the shared surface model: read the spectral fraction as an emission-energy weight.', 'A normalized fraction is dimensionless and the band energy is an energy; the two are not in the same codomain, so no total translation is available.'),
    strat('Search the legacy registry for a named query or certificate.', 'Only a pair-level notEstablished anchor.')],
   [cand('candidate context', 'A hypothetical map from a ladder level to an emission energy would need a per-level energy table; no such table is declared.', 'not delivered')],
   'No delivered statement maps a ladder level or a normalized spectral fraction to a band-position energy; the two descriptor sets are disjoint.',
   ['grep -rnE "StokesShift|emEnergy|absEnergy|stokesShift" PhotoLean/KashaVavilov --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-StokesShift'],
   'The delivered register records no edge for positions vs ladders, and the two modules share no declaration. The honest status is outOfScope with a statement-level jurisdiction reason, not a negative claim.',
   'No shared context or declared translation exists: a normalized spectral fraction over ladder levels cannot be mapped to a band-position energy of a surface pair.')

# ---- KV / ICvsISC (unresolved)
_s('Q-RAD2-KVI-01', 'P-KashaVavilov-ICvsISC', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['stmt-KashaVavilov-PhotoLean-KashaVavilov-d2_verdict',
    'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
    'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
    'stmt-ICvsISC-PhotoLean-ICvsISC-rate_ratio_eq'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['KvIcCandidateCtx (rad, ic, N, AI, AS, lamI, lamS, kB, T, xI, xS, HSO): the ladder level-1 loss `ic 1` would be `icRate`; the ladder leaves `ic` free, so the translation is not total.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 960',
        'ICvsISC <-> Kasha / KashaVavilov / ... no edge: the spin-discount competition contacts are the kernel/EG certificates and a premise-level link to FluorPhos kISC.'),
    dep('PhotoLean/KashaVavilov/Criterion.lean', 'lines 58-61 (imports)',
        'KashaVavilov imports only Mathlib, Kasha.Basic and Kasha.Criterion; it never imports Kasha.Compose where the Marcus-form marcusIC lives.'),
    dep('PhotoLean/ICvsISC/Criterion.lean', 'PhotoLean/ICvsISC/Criterion.lean#rate_ratio_eq',
        'ICvsISC proves the spin x FC rate ratio, but no delivered statement instantiates a ladder level with icRate.'),
    dep('PhotoLean/Kasha/Compose.lean', 'PhotoLean/Kasha/Compose.lean#marcusIC',
        'The Marcus-form IC rate exists on the Kasha side (and the Relations §7 hic premise), but KashaVavilov is not in its import closure.')],
   [cmd('grep -rnE "icRate|fcBarrier|FCData" PhotoLean/KashaVavilov --include=*.lean',
        'Search the KashaVavilov modules for any ICvsISC rate/barrier symbol.',
        'No matches (exit 1).'),
    cmd('grep -rn "marcusIC|kashaWithin_one_marcus|KashaWithin" PhotoLean/KashaVavilov --include=*.lean',
        'Search the KashaVavilov modules for the Kasha-side Marcus-form IC bridge.',
        'No matches (exit 1): KashaVavilov cannot see marcusIC because it does not import Kasha.Compose.'),
    cmd('grep -rnE "SpecSame|KashaRule|vavilov" PhotoLean/ICvsISC --include=*.lean',
        'Search the ICvsISC modules for a ladder/spectral predicate.',
        'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-ICvsISC',
        'Recompute the accepted legacy disposition.',
        "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered identification `ic 1 = icRate`.', 'No match; the ladder rate is a free function.'),
    strat('Reuse the Kasha §7 `hic : ic 1 = Kasha.marcusIC` composition.', 'The premise and composition live in Kasha.Compose/Relations §7, outside the KashaVavilov import closure, and target Kasha rather than the KashaVavilov D2 predicates.'),
    strat('Compose ICvsISC.rate_ratio_eq with the ladder D2 verdict.', 'The D2 verdict uses only KashaRule/Vavilov predicates over the free `ic`; no delivered link carries the IC law into them.')],
   [cand('candidate composition', 'Add `hic : ic 1 = ICvsISC.icRate AI lamI kB T xI` to the KashaVavilov D2 context; the ladder verdict would then carry the FC rate law.', 'candidate only; no delivered composition')],
   'A delivered `hic : ic 1 = icRate` identification (or a conditional composition carrying the D2 verdict to the IC rate law) is missing; KashaVavilov has no import path to the Marcus-form IC rate.',
   ['grep -rnE "icRate|fcBarrier|FCData" PhotoLean/KashaVavilov --include=*.lean',
    'grep -rn "marcusIC|kashaWithin_one_marcus|KashaWithin" PhotoLean/KashaVavilov --include=*.lean'],
   'The two theories share the physical scalar "internal-conversion rate", so the pair is not outOfScope; the delivered declarations do not identify the ladder function with the ICvsISC rate law, so the honest status is unresolved.')

# ---- KV / Forster (outOfScope)
_s('Q-RAD2-KVF-01', 'P-KashaVavilov-Forster', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'stmt-Forster-PhotoLean-Forster-fretRate',
    'stmt-Forster-PhotoLean-Forster-fretEff6'],
   ['definitionalIdentity', 'implication', 'equivalence'],
   ['KvFoDisjointCtx (rad, ic, M, N, tauD, r6, R, thetaD, thetaA, phi): a level-indexed spectral ladder versus a donor-acceptor distance/orientation geometry; no total translation.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 964',
        'Forster <-> Marcus / ... / KashaVavilov / ... no edge: the transfer geometry shares no scalar with the energy-surface family.'),
    dep('PhotoLean/KashaVavilov/Basic.lean', 'PhotoLean/KashaVavilov/Basic.lean#SpecSame',
        'The ladder predicate is over a level index; it has no distance or orientation coordinate.'),
    dep('PhotoLean/Forster/Basic.lean', 'PhotoLean/Forster/Basic.lean#fretRate',
        'The Förster rate is a function of donor lifetime, sixth power and separation; it has no ladder index.')],
   [cmd('grep -rnE "Forster|fretRate|kappaSq" PhotoLean/KashaVavilov --include=*.lean',
        'Search the KashaVavilov modules for a Förster symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SpecSame|specFrac" PhotoLean/Forster --include=*.lean',
        'Search the Förster modules for a ladder/spectral-fraction symbol.', 'No matches (exit 1).'),
    cmd('grep -h "^import" PhotoLean/KashaVavilov/*.lean PhotoLean/Forster/*.lean | sort -u',
        'Measure the two dependency closures.', 'Neither closure imports the other; Forster imports Mathlib plus its own modules.'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-Forster',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered map from a ladder level to a distance.', 'No match; the codomains differ.'),
    strat('Read the Förster rate as a per-level radiative rate.', 'FRET is an intermolecular transfer channel, not a per-level emitter decay rate; the identification would be a forced relation.')],
   [cand('candidate context', 'A level-to-distance map would be needed; no delivered declaration supplies one.', 'not delivered')],
   'No delivered statement maps a ladder level to a donor-acceptor distance or orientation angle.',
   ['grep -rnE "Forster|fretRate|kappaSq" PhotoLean/KashaVavilov --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-Forster'],
   'The delivered register records no edge and the two modules share no coordinate. The finding is jurisdictional, not a negative claim.',
   'No shared context or declared translation exists: a ladder level index cannot be mapped to a donor-acceptor distance or orientation angle.')

# ---- KV / Einstein (unresolved)
_s('Q-RAD2-KVE-01', 'P-KashaVavilov-Einstein', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'stmt-KashaVavilov-PhotoLean-KashaVavilov-d2_verdict',
    'stmt-Einstein-PhotoLean-Einstein-aOfB',
    'stmt-Einstein-PhotoLean-Einstein-tauR',
    'stmt-Einstein-PhotoLean-Einstein-radFactor'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['KvEbCandidateCtx (rad, ic, M, N, K, B21): the ladder radiative rate `rad n` would be an Einstein coefficient; the ladder quantifies over an arbitrary function, so the translation is a candidate.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 969',
        'Einstein <-> ... / KashaVavilov / ... no edge: the radiative conversions contact the graph only through the QuantumYield anchor.'),
    dep('PhotoLean/KashaVavilov/Basic.lean', 'PhotoLean/KashaVavilov/Basic.lean#SpecSame',
        'SpecSame is stated over an arbitrary `rad`; no Einstein coefficient occurs.'),
    dep('PhotoLean/Einstein/Basic.lean', 'PhotoLean/Einstein/Basic.lean#aOfB',
        'aOfB is a radiative coefficient map; no ladder index occurs.')],
   [cmd('grep -rnE "Einstein|aOfB|tauR|radFactor" PhotoLean/KashaVavilov --include=*.lean',
        'Search the KashaVavilov modules for an Einstein coefficient symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SpecSame|KashaRule|vavilov" PhotoLean/Einstein --include=*.lean',
        'Search the Einstein modules for a ladder/spectral predicate.', 'No matches (exit 1).'),
    cmd('grep -n "Einstein" PhotoLean/Relations.lean',
        'Locate the delivered no-edge registration.', 'Line 969: Einstein <-> ... KashaVavilov ... no edge; only the QuantumYield anchor (line 826).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-KashaVavilov-Einstein',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered identification `rad n = aOfB K B21`.', 'No match; the ladder rate is free.'),
    strat('Compose through QuantumYield (the delivered Einstein anchor).', 'The delivered anchor `einstein_yield_via_qy` is QuantumYield <-> Einstein; no KashaVavilov endpoint occurs in it.')],
   [cand('candidate composition', 'Identify `rad 0` with `aOfB K B21` and carry the KV spectral predicates; the identification is chemically natural but not delivered.', 'candidate only')],
   'A delivered identification of the ladder radiative rate with an Einstein coefficient and a composition carrying it to SpecSame is missing.',
   ['grep -rnE "Einstein|aOfB|tauR|radFactor" PhotoLean/KashaVavilov --include=*.lean',
    'grep -n "Einstein" PhotoLean/Relations.lean'],
   'Both sides carry radiative rates, so the pair is not outOfScope; no delivered statement identifies the free ladder rate function with an Einstein coefficient, so the honest status is unresolved.')

# ---- SV / EnergyGapLaw (unresolved)
_s('Q-RAD2-SVE-01', 'P-SternVolmer-EnergyGapLaw', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
    'sternvolmer.intensityDyn',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['SvEgCandidateCtx (k0, kq, q, A, lam, kB, T, x): the quencher channel `kq*q` would be `nrRate`; SV has no gap coordinate, EGL has no concentration axis.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 991',
        'EnergyGapLaw <-> ... / SternVolmer / ... no edge: none of the partner scalars occurs in nrBarrier/nrRate/lnRate/egZoneQ.'),
    dep('PhotoLean/SternVolmer/Basic.lean', 'PhotoLean/SternVolmer/Basic.lean#dynDecay',
        'The quencher channel is `k0 + kq*q`; kq is a free constant with no gap dependence.'),
    dep('PhotoLean/EnergyGapLaw/Basic.lean', 'PhotoLean/EnergyGapLaw/Basic.lean#nrRate',
        'The nonradiative rate is an Arrhenius exponential in nrBarrier; there is no concentration variable.')],
   [cmd('grep -rnE "nrRate|nrBarrier|EnergyGap" PhotoLean/SternVolmer --include=*.lean',
        'Search the SternVolmer modules for an EGL symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SternVolmer|svRatio|KSV" PhotoLean/EnergyGapLaw --include=*.lean',
        'Search the EnergyGapLaw modules for a Stern-Volmer symbol.',
        'One prose mention only: EnergyGapLaw/RatModel.lean:29 cites the SternVolmer batch pitfall; no delivered declaration.'),
    cmd('grep -n "EnergyGapLaw" PhotoLean/Relations.lean',
        'Locate the delivered no-edge registration.', 'Line 991: EnergyGapLaw <-> ... SternVolmer ... no edge.'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-EnergyGapLaw',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered identification `kq*q = nrRate`.', 'No match; SV has no gap coordinate.'),
    strat('Read the quencher channel as an EGL relaxation at a quencher-induced gap.', 'A translation from concentration to a driving force would be needed; none is declared.')],
   [cand('candidate composition', 'Equip `kq` with `nrRate A lam kB T x` at a declared quencher-induced gap x(q); no delivered statement does so.', 'candidate only')],
   'A delivered identification of the quencher-added channel with an energy-gap-law rate at a declared gap is missing.',
   ['grep -rnE "nrRate|nrBarrier|EnergyGap" PhotoLean/SternVolmer --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-EnergyGapLaw'],
   'Both sides are nonradiative decay rates, so the pair is not outOfScope; neither side declares the other coordinate, so the honest status is unresolved.')

# ---- SV / StokesShift (outOfScope)
_s('Q-RAD2-SVS-01', 'P-SternVolmer-StokesShift', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['sternvolmer.intensityDyn',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'stmt-StokesShift-PhotoLean-StokesShift-stokesShift'],
   ['definitionalIdentity', 'implication', 'equivalence'],
   ['SvSsDisjointCtx (k0, kq, q, lam, e00): a dimensionless concentration-dependent ratio versus a band-position energy; no total translation.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 956',
        'StokesShift <-> ... SternVolmer ... no edge (positions of band maxima vs rates/ladders/geometries).'),
    dep('PhotoLean/SternVolmer/Basic.lean', 'PhotoLean/SternVolmer/Basic.lean#svRatioDyn',
        'svRatioDyn is a dimensionless ratio of decay rates over a concentration axis.'),
    dep('PhotoLean/StokesShift/Basic.lean', 'PhotoLean/StokesShift/Basic.lean#emEnergy',
        'emEnergy is a vertical-transition energy; it has no concentration variable.')],
   [cmd('grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/SternVolmer --include=*.lean',
        'Search the SternVolmer modules for a Stokes/energy symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SternVolmer|svRatio|KSV" PhotoLean/StokesShift --include=*.lean',
        'Search the StokesShift modules for a Stern-Volmer symbol.', 'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-StokesShift',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered implication from a Stern-Volmer ratio to a band energy.', 'No match; the codomains differ (dimensionless vs energy).'),
    strat('Read the concentration axis as a nuclear coordinate.', 'No such translation is declared and the units differ.')],
   [cand('candidate context', 'A concentration-to-coordinate map would be needed; none is declared.', 'not delivered')],
   'No delivered statement maps a Stern-Volmer ratio to a band-position energy; the descriptor sets are disjoint.',
   ['grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/SternVolmer --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-StokesShift'],
   'The delivered register records no edge and the observables are dimensionally distinct. The finding is jurisdictional, not logical absence.',
   'No shared context or declared translation exists: a dimensionless concentration-dependent ratio cannot be mapped to a band-position energy.')

# ---- SV / ICvsISC (unresolved)
_s('Q-RAD2-SVI-01', 'P-SternVolmer-ICvsISC', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['sternvolmer.intensityDyn',
    'stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
    'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
    'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
    'stmt-ICvsISC-PhotoLean-ICvsISC-rate_ratio_eq'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['SvIcCandidateCtx (k0, kq, q, AI, AS, lamI, lamS, kB, T, xI, xS, HSO): the quencher channel would be an IC/ISC channel at the encounter geometry; neither side declares the other coordinate.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 960',
        'ICvsISC <-> ... SternVolmer ... no edge: the competition contacts are the kernel/EG certificates and a FluorPhos premise.'),
    dep('PhotoLean/SternVolmer/Basic.lean', 'PhotoLean/SternVolmer/Basic.lean#dynDecay',
        'The quencher channel is `kq*q`; no gap/spin coordinate occurs.'),
    dep('PhotoLean/ICvsISC/Criterion.lean', 'PhotoLean/ICvsISC/Criterion.lean#rate_ratio_eq',
        'The IC/ISC competition law has no concentration axis.')],
   [cmd('grep -rnE "icRate|iscRate|fcBarrier" PhotoLean/SternVolmer --include=*.lean',
        'Search the SternVolmer modules for an IC/ISC symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SternVolmer|svRatio|KSV" PhotoLean/ICvsISC --include=*.lean',
        'Search the ICvsISC modules for a Stern-Volmer symbol.',
        'One prose mention only: ICvsISC/RatModel.lean:23 cites the SternVolmer batch pitfall; no delivered declaration.'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-ICvsISC',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered identification `kq*q = icRate` or `kq*q = iscRate`.', 'No match; SV has no gap/spin coordinate.'),
    strat('Compose the ICvsISC rate ratio with the Stern-Volmer dilution law.', 'No delivered statement links the two theories; the composition would need a concentration-to-gap translation.')],
   [cand('candidate composition', 'Equip the quencher channel with the ICvsISC `icRate`/`iscRate` at a declared encounter geometry; no delivered statement does so.', 'candidate only')],
   'A delivered identification of the quencher channel with an ICvsISC channel rate at a declared geometry is missing.',
   ['grep -rnE "icRate|iscRate|fcBarrier" PhotoLean/SternVolmer --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-ICvsISC'],
   'Both sides are nonradiative decay channels, so the pair is not outOfScope; no delivered translation closes the concentration/gap gap, so the honest status is unresolved.')

# ---- SV / Forster (outOfScope)
_s('Q-RAD2-SVF-01', 'P-SternVolmer-Forster', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['sternvolmer.intensityDyn',
    'stmt-SternVolmer-PhotoLean-SternVolmer-KSV',
    'stmt-Forster-PhotoLean-Forster-fretEff6',
    'stmt-Forster-PhotoLean-Forster-fretRate'],
   ['definitionalIdentity', 'implication', 'observationalEquivalence'],
   ['SvFoShapeCtx (k0, kq, q, r6, R): the shared `1 + control` form is a shape between `KSV*q` and `R^6/r6`; the controls are physically and dimensionally different.'],
   [dep('PhotoLean/Relations.lean', 'line 908 (shape row) and line 966 (register)',
        'theorem fretEff6_inv_eq_one_plus is a delivered shape row; §16 line 966 registers the SV look-alike as a shape registration, not an edge.'),
    dep('PhotoLean/Relations.lean', _C16 + ', line 964',
        'Forster <-> ... SternVolmer ... no edge: the transfer geometry shares no scalar with the energy-surface family.'),
    dep('relation_audit/registry.json', 'D-S15-fretEff6_inv_eq_one_plus',
        'The legacy disposition ledger records the pair as look-alike / shape-note (metadata-only), not an edge.'),
    dep('PhotoLean/SternVolmer/Basic.lean', 'PhotoLean/SternVolmer/Basic.lean#svRatioDyn',
        'svRatioDyn = 1 + KSV*q: the control is concentration times a rate constant.'),
    dep('PhotoLean/Forster/Basic.lean', 'PhotoLean/Forster/Basic.lean#fretEff6',
        'The inverse efficiency control is R^6/r6: a sixth-power distance ratio.')],
   [cmd('grep -n "fretEff6_inv_eq_one_plus" PhotoLean/Relations.lean',
        'Locate the delivered shape row.', 'Line 908: theorem fretEff6_inv_eq_one_plus ... (1 + R^6/r6). Line 967 cites it as a shape registration.'),
    cmd('grep -rnE "Forster|fret|kappa" PhotoLean/SternVolmer --include=*.lean',
        'Search the SternVolmer modules for a Förster symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "SternVolmer|svRatio|KSV" PhotoLean/Forster --include=*.lean',
        'Search the Förster modules for a Stern-Volmer symbol.', 'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-Forster',
        'Recompute the accepted legacy disposition.',
        "label='absence' subtype='look-alike'; disposition D-S15-fretEff6_inv_eq_one_plus role='shape-note' outcome='fragment'; record rec-notestablished-P-SternVolmer-Forster.")],
   [strat('Test whether the two `1 + control` forms share a physical coordinate.', 'They do not: one control is KSV*q (concentration), the other R^6/r6 (distance); only the functional shape coincides.'),
    strat('Treat the shape identity as an observational equivalence.', 'Rejected: a shape-only identity is exactly the forced relation the audit forbids; no shared channel exists.')],
   [cand('shape note', 'The delivered row `fretEff6_inv_eq_one_plus` shows the shared algebraic form; it is a shape, not a physical identity.', 'shape only; not a translation')],
   'No shared physical context or declared translation exists; the shared `1 + control` form is a shape coincidence between a concentration control and a distance control.',
   ['grep -n "fretEff6_inv_eq_one_plus" PhotoLean/Relations.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-Forster'],
   'The legacy ledger itself classifies the pair as look-alike / shape-note, and the delivered register calls it a shape registration. The honest status is outOfScope, not a forced shape identity.',
   'No shared context or declared translation exists: `KSV*q` and `R^6/r6` are different controls that only share the `1 + control` shape; the delivered shape row is not a physical identity.')

# ---- SV / Einstein (unresolved)
_s('Q-RAD2-SVEb-01', 'P-SternVolmer-Einstein', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['sternvolmer.intensityDyn',
    'stmt-SternVolmer-PhotoLean-SternVolmer-KSV',
    'stmt-Einstein-PhotoLean-Einstein-tauR',
    'stmt-Einstein-PhotoLean-Einstein-aOfB'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['SvEbCandidateCtx (k0, kq, q, A, kNR): the intrinsic decay `k0` would split into `A + kNR`; SV keeps k0 whole.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 969',
        'Einstein <-> ... SternVolmer — no edge: both reach the batch only through QuantumYield.'),
    dep('PhotoLean/SternVolmer/Basic.lean', 'PhotoLean/SternVolmer/Basic.lean#KSV',
        'KSV = kq/k0 consumes k0 whole; there is no radiative/nonradiative split.'),
    dep('PhotoLean/Einstein/Basic.lean', 'PhotoLean/Einstein/Basic.lean#tauR',
        'tauR A = 1/A is the radiative lifetime; no total decay k0 occurs.')],
   [cmd('grep -rnE "tauR|aOfB|radFactor|Einstein" PhotoLean/SternVolmer --include=*.lean',
        'Search the SternVolmer modules for an Einstein symbol.',
        'Only the theory\'s own tauRatio* names match; no Einstein coefficient or tauR occurs.'),
    cmd('grep -rnE "SternVolmer|svRatio|KSV" PhotoLean/Einstein --include=*.lean',
        'Search the Einstein modules for a Stern-Volmer symbol.', 'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-Einstein',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered split of k0.', 'No match; k0 is a free parameter.'),
    strat('Compose through QuantumYield (the delivered Einstein anchor).', 'The delivered anchor is QuantumYield <-> Einstein; no SternVolmer endpoint occurs in it.')],
   [cand('candidate composition', 'Split `k0 = A + kNR` and identify the radiative part with `aOfB`; no delivered statement does so.', 'candidate only')],
   'A delivered split of the Stern-Volmer intrinsic decay `k0` into a radiative Einstein coefficient and a nonradiative rate is missing.',
   ['grep -rnE "tauR|aOfB|radFactor|Einstein" PhotoLean/SternVolmer --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-SternVolmer-Einstein'],
   'Both sides carry decay rates, so the pair is not outOfScope; no delivered statement splits k0 or identifies its radiative part with an Einstein coefficient, so the honest status is unresolved.')

# ---- QY / StokesShift (outOfScope)
_s('Q-RAD2-QYS-01', 'P-QuantumYield-StokesShift', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'stmt-StokesShift-PhotoLean-StokesShift-stokesShift'],
   ['definitionalIdentity', 'implication', 'equivalence'],
   ['QySsDisjointCtx (kr, knr, lam, e00): a dimensionless channel partition versus a band-position energy; no total translation.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 956',
        'StokesShift <-> ... QuantumYield ... no edge (positions of band maxima vs rates/ladders/geometries).'),
    dep('PhotoLean/QuantumYield/Basic.lean', 'PhotoLean/QuantumYield/Basic.lean#yieldOf',
        'yieldOf is a dimensionless partition over decay rates; no energy coordinate.'),
    dep('PhotoLean/StokesShift/Basic.lean', 'PhotoLean/StokesShift/Basic.lean#emEnergy',
        'emEnergy is a vertical-transition energy; no channel partition.')],
   [cmd('grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/QuantumYield --include=*.lean',
        'Search the QuantumYield modules for a Stokes/energy symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "yieldOf|QuantumYield" PhotoLean/StokesShift --include=*.lean',
        'Search the StokesShift modules for a yield symbol.', 'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-QuantumYield-StokesShift',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered implication from a yield partition to a band energy.', 'No match; the codomains differ (dimensionless vs energy).'),
    strat('Read the emission energy as a yield weight.', 'A weight is dimensionless and the energy is an energy; no total translation.')],
   [cand('candidate context', 'A per-channel energy table would be needed; none is declared.', 'not delivered')],
   'No delivered statement maps a channel partition to a band-position energy.',
   ['grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/QuantumYield --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-QuantumYield-StokesShift'],
   'The delivered register records no edge and the observables are dimensionally distinct. The finding is jurisdictional, not logical absence.',
   'No shared context or declared translation exists: a dimensionless channel partition cannot be mapped to a band-position energy.')

# ---- FP / EnergyGapLaw (unresolved)
_s('Q-RAD2-FPE-01', 'P-FluorPhos-EnergyGapLaw', 'unresolved', 'scope-RAD2-candidate-bridge',
   ['stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier'],
   ['definitionalIdentity', 'implication', 'conditionalComposition'],
   ['FpEgCandidateCtx (kF, kISC, kIC, kP, kNR, A, lam, kB, T, x): the S1 internal-conversion rate kIC would be nrRate; FP has no barrier/gap premise.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 991',
        'EnergyGapLaw <-> ... FluorPhos ... no edge: none of the partner scalars occurs in nrBarrier/nrRate/lnRate/egZoneQ.'),
    dep('PhotoLean/FluorPhos/Basic.lean', 'PhotoLean/FluorPhos/Basic.lean#s1Decay',
        's1Decay = kF + kISC + kIC leaves kIC a free rate.'),
    dep('PhotoLean/EnergyGapLaw/Basic.lean', 'PhotoLean/EnergyGapLaw/Basic.lean#nrRate',
        'nrRate is an Arrhenius exponential in nrBarrier; no branching model occurs.')],
   [cmd('grep -rnE "nrRate|nrBarrier|EnergyGap" PhotoLean/FluorPhos --include=*.lean',
        'Search the FluorPhos modules for an EGL symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "FluorPhos|phiF|kIC" PhotoLean/EnergyGapLaw --include=*.lean',
        'Search the EnergyGapLaw modules for a FluorPhos symbol.', 'No matches (exit 1).'),
    cmd('grep -n "EnergyGapLaw" PhotoLean/Relations.lean',
        'Locate the delivered no-edge registration.', 'Line 991: EnergyGapLaw <-> ... FluorPhos ... no edge.'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-FluorPhos-EnergyGapLaw',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered identification `kIC = nrRate`.', 'No match; FP has no gap coordinate.'),
    strat('Compose the EGL rate into the FP S1 decay.', 'A delivered link is required; none exists (the FP -> QY rows do not consume EGL).')],
   [cand('candidate composition', 'Set `kIC = nrRate A lam kB T x` at the S1->S0 gap; no delivered statement does so.', 'candidate only')],
   'A delivered identification of the FluorPhos S1 internal-conversion rate with an energy-gap-law rate at the S1->S0 gap is missing.',
   ['grep -rnE "nrRate|nrBarrier|EnergyGap" PhotoLean/FluorPhos --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-FluorPhos-EnergyGapLaw'],
   'Both sides are nonradiative decay rates, so the pair is not outOfScope; no delivered statement fills the FP internal-conversion channel with the EGL rate, so the honest status is unresolved.')

# ---- FP / StokesShift (outOfScope)
_s('Q-RAD2-FPS-01', 'P-FluorPhos-StokesShift', 'outOfScope', 'scope-RAD2-jurisdiction',
   ['stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'stmt-StokesShift-PhotoLean-StokesShift-stokesShift'],
   ['definitionalIdentity', 'implication', 'equivalence'],
   ['FpSsDisjointCtx (kF, kISC, kIC, kP, kNR, lam, e00): a branch-probability partition versus a band-position energy; no total translation.'],
   [dep('PhotoLean/Relations.lean', _C16 + ', line 952',
        'FluorPhos <-> ... StokesShift ... no edge except through QuantumYield.'),
    dep('PhotoLean/FluorPhos/Basic.lean', 'PhotoLean/FluorPhos/Basic.lean#phiF',
        'phiF is a dimensionless branch probability; no energy coordinate.'),
    dep('PhotoLean/StokesShift/Basic.lean', 'PhotoLean/StokesShift/Basic.lean#emEnergy',
        'emEnergy is a vertical-transition energy; no branch probability.')],
   [cmd('grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/FluorPhos --include=*.lean',
        'Search the FluorPhos modules for a Stokes/energy symbol.', 'No matches (exit 1).'),
    cmd('grep -rnE "FluorPhos|phiF" PhotoLean/StokesShift --include=*.lean',
        'Search the StokesShift modules for a FluorPhos symbol.', 'No matches (exit 1).'),
    cmd('python3 tools/relation_audit_registry.py --explain-pair P-FluorPhos-StokesShift',
        'Recompute the accepted legacy disposition.', "label='absence' subtype='registered-absence'; no named query or certificate.")],
   [strat('Search for a delivered implication from a branch probability to a band energy.', 'No match; the codomains differ (dimensionless vs energy).'),
    strat('Read the Stokes shift as the S1/T1 branching weight.', 'No such translation is declared.')],
   [cand('candidate context', 'A branch-to-energy map would be needed; none is declared.', 'not delivered')],
   'No delivered statement maps a fluorescence/phosphorescence branch probability to a band-position energy.',
   ['grep -rnE "StokesShift|emEnergy|absEnergy" PhotoLean/FluorPhos --include=*.lean',
    'python3 tools/relation_audit_registry.py --explain-pair P-FluorPhos-StokesShift'],
   'The delivered register records no edge and the observables are dimensionally distinct. The finding is jurisdictional, not logical absence.',
   'No shared context or declared translation exists: a dimensionless branch probability cannot be mapped to a band-position energy.')


def main():
    search_sha = build_search_log()
    screening_sha = build_screening(search_sha)
    fragment_sha = build_fragment(screening_sha)
    print('search-log  %s  %s' % (search_sha, SEARCH_REL))
    print('screening   %s  %s' % (screening_sha, SCREENING_REL))
    print('fragment    %s  %s' % (fragment_sha, FRAGMENT_REL))
    print('probe       %s  %s' % (PROBE_SHA, PROBE_REL))


if __name__ == '__main__':
    main()
