#!/usr/bin/env python3
"""Deterministic builder for the R5 RAD3 package artifacts.

Usage (from the repository root):

    python3 bounded_audit/r5/radiative-03/build_package.py

It writes, next to this file:

* `screening.json`         — the thirteen-pair, fifteen-query screening package;
* `search-log.json`        — the six scoped search/jurisdiction records;
* `coverage-fragment.json` — the immutable submission fragment.

The builder reads only the frozen R1 boundary artifacts and the delivered Lean
sources/probe. It never reads `bounded_audit/coverage.json` (the mutable R5 ledger) and it
writes nothing outside this package directory. Every hash in the emitted artifacts is
recomputed from the current bytes, so a later edit to any input shows up as a validator
failure rather than as silent drift.
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
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
PROBE_REL = REL + '/probes/RAD3-probe.lean'
PROBE_LOG_REL = REL + '/probes/compile.log'
SCREENING_REL = REL + '/screening.json'
SEARCH_REL = REL + '/search-log.json'
FRAGMENT_REL = REL + '/coverage-fragment.json'

SNAP = 'snap-bounded-audit-2026-11-04'
STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
BUILD_COMMAND = 'proofs/scripts/lake env lean ' + PROBE_REL
WORK_PACKAGE = 'WP-radiative-energy-transfer-03'

PAIR_IDS = [
    'P-FluorPhos-ICvsISC',
    'P-FluorPhos-Forster',
    'P-FluorPhos-Einstein',
    'P-EnergyGapLaw-StokesShift',
    'P-EnergyGapLaw-ICvsISC',
    'P-EnergyGapLaw-Forster',
    'P-EnergyGapLaw-Einstein',
    'P-StokesShift-ICvsISC',
    'P-StokesShift-Forster',
    'P-StokesShift-Einstein',
    'P-ICvsISC-Forster',
    'P-ICvsISC-Einstein',
    'P-Forster-Einstein',
]

PRIOR_PACKAGES = [
    'bounded_audit/wp-surface-01/screening.json',
    'bounded_audit/r3/screening.json',
    'bounded_audit/r4/excited-01/screening.json',
    'bounded_audit/r4/excited-02/screening.json',
    'bounded_audit/r4/conical-01/screening.json',
]


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha_rel(rel):
    return sha_file(os.path.join(ROOT, rel))


def load_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


INV = load_rel(INV_REL)
QUEUE = load_rel(QUEUE_REL)
CLUSTER = load_rel(CLUSTER_REL)
REGISTRY = load_rel(REGISTRY_REL)
INV_BY_ID = {row['id']: row for row in INV['statements']}
QUEUE_BY_ID = {row['pairId']: row for row in QUEUE['pairs']}
DANGLING_IDS = {row['id'] for row in INV.get('legacyDanglingStatements', [])}


def endpoint(statement_id):
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
        'endpointForm': 'definition' if row['declarationKind'] == 'def' else 'theorem',
    }


CONTEXTS = {
    'FiBranchCtx': {
        'fields': ['HSO : ℝ', 'AS : ℝ', 'lamS : ℝ', 'AI : ℝ', 'lamI : ℝ',
                   'kB : ℝ', 'T : ℝ', 'xS : ℝ', 'xI : ℝ'],
        'physicalReading': (
            'One S1 state with a spin-orbit ISC channel and an IC channel, each written as its '
            'own Marcus-form rate over its own gap and reorganization energy; the FluorPhos '
            'branching ratio is read at the same two channel rates with the radiative channel '
            'shut.'),
        'provenance': REL + '/probes/RAD3-probe.lean#FiBranchCtx',
    },
    'FiElSayedCtx': {
        'fields': ['kF : ℝ', 'kIC : ℝ', 'kP : ℝ', 'kNR : ℝ', 'AS : ℝ', 'lamS : ℝ',
                   'kB : ℝ', 'T : ℝ', 'xS : ℝ', 'HSO : ℝ'],
        'physicalReading': (
            'The FluorPhos S1->T1->T1 radiative cascade with the ICvsISC theory-owned spin-orbit '
            'ISC rate in the intersystem-crossing slot: a live triplet radiative channel, a live '
            'S1 decay, and the explicit spin-orbit prefactor HSO^2*AS.'),
        'provenance': REL + '/probes/RAD3-probe.lean#FiElSayedCtx',
    },
    'FfTransferCtx': {
        'fields': ['tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'A donor with excited-state lifetime tauD, Forster radius sixth power r6 and '
            'donor-acceptor separation R. The transfer channel rate is '
            '(1/tauD)*(r6/R^6) and the survival channel rate is 1/tauD.'),
        'provenance': REL + '/probes/RAD3-probe.lean#FfTransferCtx',
    },
    'FpEinsCtx': {
        'fields': ['A : ℝ', 'kNR : ℝ'],
        'physicalReading': (
            'A two-channel emitter whose radiative decay rate is the Einstein A coefficient A '
            'and whose only loss channel is the nonradiative rate kNR.'),
        'provenance': REL + '/probes/RAD3-probe.lean#FpEinsCtx',
    },
    'EsGapCtx': {
        'fields': ['lam : ℝ', 'x : ℝ'],
        'physicalReading': (
            'The equal-curvature two-parabola model read at reorganization energy lam and gap '
            'x: the kinetic crossing barrier is (lam - x)^2/(4 lam), the vertical emission '
            'energy is x - lam, and the barrierless/closed-window corner is x = lam.'),
        'provenance': REL + '/probes/RAD3-probe.lean#EsGapCtx',
    },
    'EiRateCtx': {
        'fields': ['AI : ℝ', 'lamI : ℝ', 'kB : ℝ', 'T : ℝ', 'xI : ℝ'],
        'physicalReading': (
            'One internal-conversion channel: prefactor AI, reorganization energy lamI, thermal '
            'energy kB*T and gap xI. The ICvsISC icRate and the EnergyGapLaw nrRate are read at '
            'the same five parameters.'),
        'provenance': REL + '/probes/RAD3-probe.lean#EiRateCtx',
    },
    'EiCrossCtx': {
        'fields': ['AI : ℝ', 'AS : ℝ', 'lamI : ℝ', 'lamS : ℝ', 'kB : ℝ', 'T : ℝ',
                   'xI : ℝ', 'xS : ℝ', 'HSO : ℝ'],
        'physicalReading': (
            'The IC-vs-ISC competition: IC channel (AI, lamI, xI) against the spin-orbit ISC '
            'channel (HSO, AS, lamS, xS) at thermal energy kB*T. The IC side is read both with '
            'the ICvsISC icRate and with the EnergyGapLaw nrRate at the same parameters.'),
        'provenance': REL + '/probes/RAD3-probe.lean#EiCrossCtx',
    },
    'SiSurfaceCtx': {
        'fields': ['lam : ℝ'],
        'physicalReading': (
            'The equal-curvature two-parabola model at reorganization energy lam and '
            'thermoneutral gap 0, with the crossing coordinate q = 1/2 of the Stokes surfaces.'),
        'provenance': REL + '/probes/RAD3-probe.lean#SiSurfaceCtx',
    },
    'FoEinCtx': {
        'fields': ['A : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'A donor whose excited-state lifetime is the Einstein radiative lifetime tauR A = '
            '1/A, with Forster radius sixth power r6 and donor-acceptor separation R.'),
        'provenance': REL + '/probes/RAD3-probe.lean#FoEinCtx',
    },
    'EgForsterDisjointCtx': {
        'fields': ['lam : ℝ', 'x : ℝ', 'tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'Candidate context only: the gap-law activated coordinate (lam, x) placed beside '
            'the Forster transfer coordinates (tauD, r6, R). The two descriptor sets are '
            'disjoint and no total translation between them is delivered.'),
        'provenance': REL + '/screening.json#EgForsterDisjointCtx (candidate context; no Lean structure)',
    },
    'EgEinsteinDisjointCtx': {
        'fields': ['lam : ℝ', 'x : ℝ', 'K : ℝ', 'B21 : ℝ'],
        'physicalReading': (
            'Candidate context only: the gap-law activated coordinate (lam, x) placed beside '
            'the Einstein coefficient algebra (K, B21). The symbol A denotes a nonradiative '
            'prefactor in one theory and a radiative coefficient in the other; no shared '
            'descriptor is delivered.'),
        'provenance': REL + '/screening.json#EgEinsteinDisjointCtx (candidate context; no Lean structure)',
    },
    'SfOverlapCandidateCtx': {
        'fields': ['lam : ℝ', 'e00 : ℝ', 'C : ℝ', 'kappasq : ℝ', 'Phi : ℝ', 'J : ℝ', 'n : ℝ'],
        'physicalReading': (
            'Candidate context only: the Stokes band maxima (lam, e00) placed beside the '
            'Forster radius parameters (C, kappasq, Phi, J, n). A relation would need a '
            'delivered line-shape or overlap object; the frozen statement set has none.'),
        'provenance': REL + '/screening.json#SfOverlapCandidateCtx (candidate context; no Lean structure)',
    },
    'SeSpectralDisjointCtx': {
        'fields': ['lam : ℝ', 'e00 : ℝ', 'h : ℝ', 'c : ℝ', 'nu : ℝ'],
        'physicalReading': (
            'Candidate context only: the Stokes band maxima (lam, e00) placed beside the '
            'Einstein radiation-density parameters (h, c, nu). No delivered statement '
            'identifies the emission energy with h*nu.'),
        'provenance': REL + '/screening.json#SeSpectralDisjointCtx (candidate context; no Lean structure)',
    },
    'IfThirdChannelCandidateCtx': {
        'fields': ['AI : ℝ', 'AS : ℝ', 'lamI : ℝ', 'lamS : ℝ', 'kB : ℝ', 'T : ℝ',
                   'xI : ℝ', 'xS : ℝ', 'HSO : ℝ', 'tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'physicalReading': (
            'Candidate context only: the two-channel IC-vs-ISC competition with a Forster '
            'transfer channel (1/tauD)*(r6/R^6) added as a third decay channel.'),
        'provenance': REL + '/screening.json#IfThirdChannelCandidateCtx (candidate context; no Lean structure)',
    },
    'IeSpinRadDisjointCtx': {
        'fields': ['HSO : ℝ', 'AS : ℝ', 'lamS : ℝ', 'kB : ℝ', 'T : ℝ', 'xS : ℝ',
                   'g1 : ℝ', 'g2 : ℝ', 'B21 : ℝ'],
        'physicalReading': (
            'Candidate context only: the spin-orbit ISC channel (HSO, AS, lamS, xS) placed '
            'beside the Einstein degeneracy/coefficient algebra (g1, g2, B21). The spin-orbit '
            'amplitude is not a radiation-density factor and no shared descriptor is delivered.'),
        'provenance': REL + '/screening.json#IeSpinRadDisjointCtx (candidate context; no Lean structure)',
    },
}

SCOPES = {
    'scope-RAD3-branching': {
        'description': 'Channel-branching identity at fixed microscopic channel rates.',
        'domain': 'all real channel parameters of the shared context; no claim outside the declared branching fraction.',
    },
    'scope-RAD3-el-sayed': {
        'description': 'El-Sayed boundary of the FluorPhos phosphorescence cascade against the ICvsISC spin-orbit ISC channel.',
        'domain': 'all real cascade parameters satisfying the four live-channel premises; the totalized dead-channel corners are the falsification witnesses.',
    },
    'scope-RAD3-transfer-efficiency': {
        'description': 'Forster transfer-efficiency identity against the donor radiative branch.',
        'domain': 'all real (tauD, r6, R) under the two declared nonzero premises; the totalized corners are the falsification witnesses, not part of the scope.',
    },
    'scope-RAD3-radiative-yield': {
        'description': 'Two-channel fluorescence-yield identity against the Einstein radiative yield.',
        'domain': 'all real (A, kNR); division is totalized, so no positivity premise is load-bearing.',
    },
    'scope-RAD3-gap-window': {
        'description': 'Gap-law barrier against the Stokes emission window under a nonzero reorganization energy.',
        'domain': 'all real (lam, x) with lam != 0; the lam = 0 totalized corner is excluded by a load-bearing premise.',
    },
    'scope-RAD3-rate-identity': {
        'description': 'Definitional rate identity between the IC channel and the gap-law nonradiative channel.',
        'domain': 'all real (AI, lamI, kB, T, xI); division is totalized, so no positivity premise is load-bearing.',
    },
    'scope-RAD3-surface-height': {
        'description': 'Thermoneutral IC barrier against the Stokes ground surface at the crossing coordinate.',
        'domain': 'all real lam; both sides vanish at lam = 0, so no premise is needed.',
    },
    'scope-RAD3-jurisdiction': {
        'description': 'Jurisdiction record for pairs with no shared context or declared translation.',
        'domain': 'the named pairs and the statements/kinds/contexts recorded in their search-log entries.',
    },
    'scope-RAD3-scoped-search': {
        'description': 'Machine-recomputable scoped search over the frozen statement authorities.',
        'domain': 'the named theory statement sets of the frozen snapshot and the delivered module imports.',
    },
}


def build_context(context_id):
    spec = CONTEXTS[context_id]
    return {
        'id': context_id,
        'fields': list(spec['fields']),
        'physicalReading': spec['physicalReading'],
        'provenance': spec['provenance'],
    }


def build_scope(scope_id):
    spec = SCOPES[scope_id]
    return {
        'id': scope_id,
        'description': spec['description'],
        'domain': spec['domain'],
        'snapshot': SNAP,
    }


def identity_translation(context_id, note=None):
    return {
        'id': 'identity',
        'term': 'fun δ : %s => δ' % context_id,
        'requirement': note or 'Both statements are read on the shared context; the translation is total.',
    }


def none_translation(side, reason):
    return {
        'id': 'none-declared',
        'term': '',
        'requirement': 'none-declared',
        'reason': reason,
    }


def candidate_translation(side, reason):
    return {
        'id': 'candidate-not-total',
        'term': '',
        'requirement': 'candidate-not-total',
        'reason': reason,
    }


def channel(channel_id, value_type, domain, left_obs, right_obs, name=None):
    return {
        'id': channel_id,
        'name': name or channel_id,
        'observedValueType': value_type,
        'inputDomain': domain,
        'domainNonempty': True,
        'leftObs': left_obs,
        'rightObs': right_obs,
    }


def premise(predicate, definitions, note=None, premise_ids=None):
    ids = premise_ids if premise_ids is not None else [d['id'] for d in definitions]
    out = {
        'predicate': predicate,
        'premiseIds': ids,
        'definitions': definitions,
    }
    if note:
        out['note'] = note
    return out


def probe_evidence(decl, certificate_kind, underlying, justification, composition=None):
    evidence = {
        'type': 'r5-rad3-probe-certificate',
        'certificateId': None,  # filled by make_query
        'kind': certificate_kind,
        'probe': {
            'path': PROBE_REL,
            'sha256': sha_rel(PROBE_REL),
            'declaration': decl,
            'kindCheckTheorem': decl + '_kind',
            'buildCommand': BUILD_COMMAND,
            'log': PROBE_LOG_REL,
        },
        'underlyingTheorems': underlying,
        'axiomFootprint': list(ALLOWED_AXIOMS),
        'allowedAxioms': list(ALLOWED_AXIOMS),
        'justification': justification,
    }
    if composition is not None:
        evidence['composition'] = composition
    return evidence


def make_query(qid, pair_id, title, question, rationale, source, target,
               context_id, premises, channels, scope_id, kind, kind_rationale,
               falsification, status, outcome_rationale, evidence,
               legacy_disposition, translations=None):
    if evidence.get('type') == 'r5-rad3-probe-certificate':
        evidence = dict(evidence)
        evidence['certificateId'] = qid
        provenance = {
            'kind': 'r5-rad3-probe-certificate',
            'certificateId': qid,
            'sourceArtifact': PROBE_REL,
            'locator': evidence['probe']['declaration'],
            'legacyDisposition': legacy_disposition,
        }
    else:
        locator = evidence['searchLogRef']
        provenance = {
            'kind': evidence['type'],
            'sourceArtifact': SEARCH_REL,
            'locator': locator,
            'legacyDisposition': legacy_disposition,
        }
    return {
        'queryId': qid,
        'pairId': pair_id,
        'title': title,
        'chemicalQuestion': question,
        'chemicalRationale': rationale,
        'endpoints': {
            'source': endpoint(source),
            'target': endpoint(target),
        },
        'sharedContext': build_context(context_id),
        'translations': translations or {
            'left': identity_translation(context_id),
            'right': identity_translation(context_id),
        },
        'premises': premises,
        'observationChannels': channels,
        'scope': build_scope(scope_id),
        'expectedKind': kind,
        'expectedKindRationale': kind_rationale,
        'falsificationCondition': falsification,
        'outcome': {
            'status': status,
            'rationale': outcome_rationale,
            'evidence': evidence,
        },
        'provenance': provenance,
    }


def theorem(declaration, source_artifact, source_line, role):
    return {
        'declaration': declaration,
        'sourceArtifact': source_artifact,
        'sourceLine': source_line,
        'role': role,
    }


def premise_def(pid, ptype, predicate, statement, load_bearing):
    return {
        'id': pid,
        'context': None,
        'predicate': predicate,
        'statement': statement,
        'loadBearing': load_bearing,
    }


# --------------------------------------------------------------------------- queries

QUERIES = []

# Q-RAD3-FI-01 — FluorPhos / ICvsISC branching ratio.
QUERIES.append(make_query(
    'Q-RAD3-FI-01', 'P-FluorPhos-ICvsISC',
    'The S1 intersystem-crossing branch is the normalized spin-orbit ISC channel',
    'With the S1 radiative channel shut, is the FluorPhos intersystem-crossing branching ratio '
    'kISC/(kISC+kIC) the normalized spin-orbit ISC channel iscRate/(iscRate+icRate) of the '
    'IC-vs-ISC competition, when the FluorPhos rate constants are the ICvsISC theory-owned '
    'channel rates?',
    'Both theories describe the same S1 state as a set of competing decay channels. FluorPhos '
    'reports the triplet cascade as the branching ratio kISC/(kF+kISC+kIC), with kISC standing '
    'for the intersystem-crossing rate constant. ICvsISC reports the two nonradiative channel '
    'rates explicitly, with the spin-orbit factor HSO^2*AS in the ISC channel. Shutting the '
    'radiative channel and substituting the two theory-owned rates makes the FluorPhos branch '
    'the normalized ISC channel of the competition. The query asks whether the phenomenological '
    'branch is the theory-owned channel ratio, not whether two symbols share a name.',
    'stmt-FluorPhos-PhotoLean-FluorPhos-iscBranch',
    'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
    'FiBranchCtx',
    premise('fun _ : FiBranchCtx => True', [],
            note='The branching-ratio identity is unconditional; the ICvsISC dominance premises '
                 'are not consumed by a ratio identity, so none is declared.'),
    [channel('quantum-yield', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => FluorPhos.iscBranch 0 (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) '
             '(ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)',
             'fun δ _ => ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS / '
             '(ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS + '
             'ICvsISC.icRate δ.AI δ.lamI δ.kB δ.T δ.xI)')],
    'scope-RAD3-branching', 'observationalEquivalence',
    'Both sides are real-valued branching fractions on the same channel pair; the certificate is '
    'equality of the quantum-yield channel at the single declared input.',
    'A parameter tuple at which the FluorPhos branch and the normalized ISC channel differ would '
    'refute the equivalence.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint and its premise list is empty, matching the declared unconditional scope.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.fiBranchBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.FluorPhos.iscBranch', 'PhotoLean/FluorPhos/Basic.lean', 54,
                 'definition of the S1 intersystem-crossing branch consumed by the probe'),
         theorem('PhotoLean.ICvsISC.iscRate', 'PhotoLean/ICvsISC/Basic.lean', 85,
                 'theory-owned ISC channel rate substituted into the branch'),
         theorem('PhotoLean.ICvsISC.icRate', 'PhotoLean/ICvsISC/Basic.lean', 72,
                 'theory-owned IC channel rate in the competition denominator')],
        'The probe declares the shared context of one S1 state with the two microscopic channel '
        'rates, states the quantum-yield channel as the FluorPhos branch at kF = 0 against the '
        'normalized ICvsISC ISC rate, and proves the equality by unfolding the branch and the '
        'S1 total decay. The proof is unconditional, so no positivity premise is consumed.'),
    'The legacy §16 row is a premise-level notEstablished anchor for the kISC identification; '
    'this query is the statement-level comparison that anchor describes and is not derived from '
    'it (legacy labels are census metadata, not audit verdicts).'))


# Q-RAD3-FI-02 — FluorPhos / ICvsISC El-Sayed boundary.
QUERIES.append(make_query(
    'Q-RAD3-FI-02', 'P-FluorPhos-ICvsISC',
    'The El-Sayed boundary of phosphorescence is the vanishing of the ICvsISC spin-orbit ISC channel',
    'At a live triplet radiative channel and a live S1 decay, is the FluorPhos phosphorescence '
    'yield zero exactly when the ICvsISC spin-orbit ISC channel rate is zero, i.e. exactly when '
    'the spin-orbit amplitude HSO vanishes?',
    'The El-Sayed rule says phosphorescence requires intersystem crossing, and the ICvsISC theory '
    'writes the ISC channel with the explicit spin-orbit prefactor HSO^2*AS. FluorPhos writes the '
    'phosphorescence yield as the S1->T1 branch times the T1 radiative branch, with kISC the '
    'abstract intersystem-crossing rate. Substituting the theory-owned iscRate for kISC makes the '
    'El-Sayed boundary a statement-level equivalence: at a live triplet radiative channel and a '
    'live S1 decay, the phosphorescence yield vanishes exactly when the spin-orbit ISC channel '
    'vanishes. This is the substantive cross-theory content of the El-Sayed premise, not a shared '
    'notation.',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiP',
    'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
    'FiElSayedCtx',
    premise(
        'fun δ : FiElSayedCtx => δ.kP ≠ 0 ∧ δ.kP + δ.kNR ≠ 0 ∧ δ.AS ≠ 0 ∧ '
        'FluorPhos.s1Decay δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) δ.kIC ≠ 0',
        [premise_def('RAD3-FIES-kP-nonzero', 'positivity',
                     'fun δ : FiElSayedCtx => δ.kP ≠ 0',
                     'The triplet radiative rate is nonzero: a live phosphorescence channel.',
                     'At kP = 0 the T1 radiative branch kP/(kP+kNR) is 0, so the yield vanishes '
                     'even with a nonzero spin-orbit channel; the equivalence would fail.'),
         premise_def('RAD3-FIES-triplet-total-nonzero', 'positivity',
                     'fun δ : FiElSayedCtx => δ.kP + δ.kNR ≠ 0',
                     'The total triplet decay is nonzero: the T1 branch divides by kP + kNR.',
                     'At kP + kNR = 0 the totalized T1 branch is 0 whatever kP is, so a zero '
                     'yield would not force HSO = 0.'),
         premise_def('RAD3-FIES-AS-nonzero', 'positivity',
                     'fun δ : FiElSayedCtx => δ.AS ≠ 0',
                     'The ISC base prefactor is nonzero, so HSO^2*AS = 0 forces HSO = 0.',
                     'At AS = 0 the channel vanishes at every HSO, so a zero yield would not '
                     'force a zero spin-orbit amplitude.'),
         premise_def('RAD3-FIES-s1decay-nonzero', 'positivity',
                     'fun δ : FiElSayedCtx => '
                     'FluorPhos.s1Decay δ.kF (ICvsISC.iscRate δ.HSO δ.AS δ.lamS δ.kB δ.T δ.xS) '
                     'δ.kIC ≠ 0',
                     'The S1 total decay is nonzero: the ISC branch divides by s1Decay.',
                     'At a zero totalized S1 decay the branch is the totalized 0 whatever the ISC '
                     'rate is, so a zero yield would not force HSO = 0.')],
        note='All four premises are load-bearing; each is consumed by the div_eq_zero_iff / '
             'mul_eq_zero chain in the probe proof.'),
    [],
    'scope-RAD3-el-sayed', 'equivalence',
    'Both sides are propositions about the same cascade context; the certificate is the '
    'equivalence of zero phosphorescence and a zero spin-orbit amplitude under the declared '
    'premises.',
    'A context satisfying the four premises at which HSO = 0 but the phosphorescence yield is '
    'nonzero, or HSO != 0 but the yield is zero, would refute the equivalence.',
    'certified',
    'The package-local typed Lean equivalence certificate is checked; it carries only the allowed '
    'axiom footprint and its four premises are the same live-channel conditions the screening '
    'record declares (machine-checked by the probe premise witness).',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.fiElSayedBridge',
        'equivalence',
        [theorem('PhotoLean.FluorPhos.phiP', 'PhotoLean/FluorPhos/Basic.lean', 61,
                 'definition of the phosphorescence cascade consumed by the probe'),
         theorem('PhotoLean.ICvsISC.iscRate', 'PhotoLean/ICvsISC/Basic.lean', 85,
                 'theory-owned spin-orbit ISC channel rate substituted for kISC'),
         theorem('PhotoLean.FluorPhos.s1Decay', 'PhotoLean/FluorPhos/Basic.lean', 48,
                 'S1 total decay in the ISC branch denominator'),
         theorem('PhotoLean.ICvsISC.fcBarrier', 'PhotoLean/ICvsISC/Basic.lean', 63,
                 'nuclear barrier inside the spin-orbit ISC channel')],
        'The probe declares the cascade context with the theory-owned ISC rate, states zero '
        'phosphorescence against a zero spin-orbit amplitude, and proves the equivalence by the '
        'mul_eq_zero / div_eq_zero_iff chain: a zero yield forces either the ISC branch or the T1 '
        'branch to vanish, and the four live-channel premises rule out every branch except '
        'HSO = 0.'),
    'The legacy §16 premise-level kISC identification anchor is the census row for this pair; '
    'this query is a statement-level El-Sayed comparison of the two delivered statements and is '
    'not derived from the anchor.'))

# Q-RAD3-FF-01 — FluorPhos / Forster efficiency.
QUERIES.append(make_query(
    'Q-RAD3-FF-01', 'P-FluorPhos-Forster',
    'The Forster transfer efficiency is the donor fluorescence branch with the transfer channel in the radiative slot',
    'For a donor of lifetime tauD whose transfer channel has rate kT = (1/tauD)*(r6/R^6), is the '
    'Forster transfer efficiency r6/(r6+R^6) the FluorPhos fluorescence branch kF/(kF+kIC) '
    'evaluated at kF = kT and kIC = 1/tauD?',
    'The Forster efficiency is the fraction of donor excitations that leave through the transfer '
    'channel, E = kT/(kT+kD) with kD = 1/tauD; the FluorPhos fluorescence yield is the matching '
    'branch kF/(kF+kIC). Putting the transfer rate in the radiative slot and the donor decay in '
    'the loss slot is the physically meaningful reading: both are normalized two-channel '
    'competition fractions of the same excited state. The query asks whether the Forster '
    'efficiency is that branch, not whether the two formulas look alike.',
    'stmt-Forster-PhotoLean-Forster-fretEff6',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'FfTransferCtx',
    premise(
        'fun δ : FfTransferCtx => δ.tauD ≠ 0 ∧ δ.R ≠ 0',
        [premise_def('RAD3-FF-tauD-nonzero', 'positivity',
                     'fun δ : FfTransferCtx => δ.tauD ≠ 0',
                     'The donor lifetime is nonzero: it is the reciprocal of the decay rate 1/tauD.',
                     'At tauD = 0, 1/tauD is the totalized 0, the FluorPhos branch collapses to 0, '
                     'while the Forster efficiency is r6/(r6+R^6); the premise is consumed by the '
                     'field normalisation in the probe.'),
         premise_def('RAD3-FF-R-nonzero', 'positivity',
                     'fun δ : FfTransferCtx => δ.R ≠ 0',
                     'The donor-acceptor separation is nonzero: R^6 is inverted in the transfer rate.',
                     'At R = 0, r6/R^6 is the totalized 0, so the branch is 0 while the efficiency '
                     'is 1 when r6 != 0; the premise is consumed by the R^6 nonzero side condition.')],
        note='Both premises are load-bearing; the lam-free totalized corner is a falsification '
             'witness for the unpremised form.'),
    [channel('transfer-efficiency', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => Forster.fretEff6 δ.r6 δ.R',
             'fun δ _ => FluorPhos.phiF ((1 / δ.tauD) * (δ.r6 / δ.R ^ 6)) 0 (1 / δ.tauD)')],
    'scope-RAD3-transfer-efficiency', 'observationalEquivalence',
    'Both sides are real-valued transfer fractions on the same donor pair; the certificate is '
    'equality of the transfer-efficiency channel at the single declared input.',
    'A tuple (tauD, r6, R) satisfying the premises at which the efficiency and the FluorPhos '
    'branch differ would refute the identity.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint, and its two premises are the same nonzero conditions the screening record '
    'declares (machine-checked by the probe premise witness).',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.ffTransferBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.Forster.fretEff6', 'PhotoLean/Forster/Basic.lean', 57,
                 'definition of the transfer efficiency consumed by the probe'),
         theorem('PhotoLean.FluorPhos.phiF', 'PhotoLean/FluorPhos/Basic.lean', 51,
                 'definition of the donor fluorescence branch compared with the efficiency')],
        'The probe reads the transfer channel rate (1/tauD)*(r6/R^6) and the survival rate '
        '1/tauD, states the efficiency channel against the FluorPhos branch, and proves the '
        'identity by a case split on r6 + R^6 plus field normalisation; the tauD != 0 and '
        'R != 0 premises discharge the nonzero side conditions.'),
    'The legacy §16 row is a registered-absence anchor for this pair; it is coverage history, not '
    'an audit verdict, and is not cited as evidence.'))

# Q-RAD3-FE-01 — FluorPhos / Einstein yield.
QUERIES.append(make_query(
    'Q-RAD3-FE-01', 'P-FluorPhos-Einstein',
    'The two-channel fluorescence yield is the Einstein radiative yield',
    'With the IC and ISC channels shut, is the FluorPhos fluorescence quantum yield '
    'kF/(kF+kNR) the Einstein radiative yield A*(1/(A+kNR)) at kF = A?',
    'The Einstein EB-C8 row states the radiative yield of a two-channel decay; FluorPhos states '
    'the S1 radiative branch. When the only loss channel is the nonradiative one and the '
    'radiative rate is the Einstein A coefficient, the two are the same competition fraction of '
    'the same excited state. The query asks whether the FluorPhos yield specializes to the '
    'Einstein radiative-yield anchor, not whether the letter A is shared.',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'stmt-Einstein-PhotoLean-Einstein-yield_radiative',
    'FpEinsCtx',
    premise('fun _ : FpEinsCtx => True', [],
            note='Division is totalized in both modules, so the identity holds at every '
                 '(A, kNR), including A + kNR = 0; no positivity premise is load-bearing.'),
    [channel('quantum-yield', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => FluorPhos.phiF δ.A 0 δ.kNR',
             'fun δ _ => δ.A * (1 / (δ.A + δ.kNR))')],
    'scope-RAD3-radiative-yield', 'observationalEquivalence',
    'Both sides are real-valued radiative fractions of the same two-channel decay; the '
    'certificate is equality of the quantum-yield channel at the single declared input.',
    'A pair (A, kNR) at which the two-channel fluorescence yield and the Einstein radiative '
    'yield differ would refute the identity.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint and consumes the delivered Einstein yield row in its proof.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.fpEinsBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.FluorPhos.phiF', 'PhotoLean/FluorPhos/Basic.lean', 51,
                 'definition of the two-channel fluorescence yield consumed by the probe'),
         theorem('PhotoLean.Einstein.yield_radiative', 'PhotoLean/Einstein/Criterion.lean', 152,
                 'delivered Einstein radiative-yield row rewritten by the probe proof'),
         theorem('PhotoLean.FluorPhos.s1Decay', 'PhotoLean/FluorPhos/Basic.lean', 48,
                 'S1 total decay whose kISC = 0 specialization is unfolded')],
        'The probe declares the two-channel context, states the quantum-yield channel as the '
        'FluorPhos yield at kISC = 0 against the Einstein radiative yield, rewrites by the '
        'delivered yield_radiative row and clears the zero IC slot.'),
    'The legacy §16 row is a registered-absence anchor; it is coverage history, not an audit '
    'verdict, and is not cited as evidence.'))

# Q-RAD3-ES-01 — EnergyGapLaw / StokesShift zero set.
QUERIES.append(make_query(
    'Q-RAD3-ES-01', 'P-EnergyGapLaw-StokesShift',
    'The gap-law barrier vanishes exactly when the vertical emission window closes',
    'At nonzero reorganization energy, does the energy-gap-law nonradiative barrier '
    'nrBarrier lam x vanish exactly when the Stokes vertical emission energy emEnergy lam x '
    'vanishes, i.e. at the barrierless gap x = lam?',
    'Both theories read the same equal-curvature two-parabola model: the gap law kinetically '
    'through the crossing barrier (lam-x)^2/(4lam), StokesShift optically through the vertical '
    'emission energy e00-lam. The barrierless kinetic point and the closed optical window are '
    'the same corner x = lam. The legacy §15 edge asserted this equivalence through two endpoint '
    'aliases that are not delivered declarations; this query restates it with the delivered '
    'nrBarrier and emEnergy and a load-bearing lam != 0 premise.',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'EsGapCtx',
    premise(
        'fun δ : EsGapCtx => δ.lam ≠ 0',
        [premise_def('RAD3-ES-lam-nonzero', 'positivity',
                     'fun δ : EsGapCtx => δ.lam ≠ 0',
                     'The reorganization energy is nonzero: the crossing barrier divides by 4*lam.',
                     'At lam = 0 the totalized barrier is 0 at every gap while the emission energy '
                     'is x, so the equivalence fails at x != 0; the premise is consumed by the '
                     'div_eq_zero_iff step in the probe.')]),
    [],
    'scope-RAD3-gap-window', 'equivalence',
    'Both sides are propositions about the same (lam, x) point; the certificate is the '
    'equivalence of the two zero predicates under the declared premise.',
    'A pair (lam, x) with lam != 0 at which exactly one of the barrier and the emission energy '
    'vanishes would refute the equivalence; the lam = 0 corner refutes only the unpremised form.',
    'certified',
    'The package-local typed equivalence certificate is checked; it carries only the allowed '
    'axiom footprint and its premise list is the declared nonzero reorganization energy.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.esZeroBarrierBridge',
        'equivalence',
        [theorem('PhotoLean.EnergyGapLaw.nrBarrier', 'PhotoLean/EnergyGapLaw/Basic.lean', 62,
                 'definition of the gap-law crossing barrier consumed by the probe'),
         theorem('PhotoLean.StokesShift.emEnergy', 'PhotoLean/StokesShift/Basic.lean', 80,
                 'definition of the vertical emission energy compared with the barrier'),
         theorem('PhotoLean.StokesShift.emEnergy_eq', 'PhotoLean/StokesShift/Criterion.lean', 54,
                 'delivered closed form emEnergy = e00 - lam consumed by the probe')],
        'The probe states the two zero predicates on the shared (lam, x) context, rewrites the '
        'emission energy by the delivered closed form, and proves the equivalence by clearing the '
        'nonzero barrier denominator and the square.'),
    'This query resolves the legacy §15 record q-D-S15-egBarrier-zero-iff-emEnergy-zero: its two '
    'endpoints were dangling aliases, and the statement-level content is re-certified here on the '
    'delivered nrBarrier and emEnergy declarations without citing the aliases or the legacy '
    'certificate.'))

# Q-RAD3-ES-02 — EnergyGapLaw / StokesShift quantitative barrier.
QUERIES.append(make_query(
    'Q-RAD3-ES-02', 'P-EnergyGapLaw-StokesShift',
    'The gap-law barrier is the squared emission gap over four times the reorganization energy',
    'Is the energy-gap-law barrier nrBarrier lam x equal to emEnergy lam x ^ 2 / (4*lam) at '
    'nonzero reorganization energy, i.e. is the kinetic barrier the squared optical emission gap '
    'over four times the shared reorganization energy?',
    'This is the quantitative form of the same two-parabola reading: with x the driving-force gap '
    'and emEnergy = x - lam, the crossing barrier (lam-x)^2/(4lam) is the emission gap squared '
    'over 4lam. It links the kinetic barrier to the optical observable beyond the shared zero '
    'set, and it names the reorganization energy that both theories parameterize. The '
    'lam != 0 premise is load-bearing.',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'EsGapCtx',
    premise(
        'fun δ : EsGapCtx => δ.lam ≠ 0',
        [premise_def('RAD3-ES-lam-nonzero', 'positivity',
                     'fun δ : EsGapCtx => δ.lam ≠ 0',
                     'The reorganization energy is nonzero: the barrier and the squared-gap '
                     'quotient both divide by 4*lam.',
                     'At lam = 0 the totalized barrier is 0 while emEnergy^2/(4*lam) is the '
                     'totalized 0 only when x = 0; the premise is consumed by field_simp.')]),
    [channel('barrier-height', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => EnergyGapLaw.nrBarrier δ.lam δ.x',
             'fun δ _ => StokesShift.emEnergy δ.lam δ.x ^ 2 / (4 * δ.lam)')],
    'scope-RAD3-gap-window', 'observationalEquivalence',
    'Both sides are real-valued barrier-height expressions on the same (lam, x) point; the '
    'certificate is equality of the barrier-height channel at the single declared input.',
    'A pair (lam, x) with lam != 0 at which the barrier and the squared emission gap over 4*lam '
    'differ would refute the identity.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint and the declared nonzero reorganization energy premise.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.esBarrierEmissionBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.EnergyGapLaw.nrBarrier', 'PhotoLean/EnergyGapLaw/Basic.lean', 62,
                 'definition of the gap-law crossing barrier consumed by the probe'),
         theorem('PhotoLean.StokesShift.emEnergy', 'PhotoLean/StokesShift/Basic.lean', 80,
                 'definition of the vertical emission energy squared in the channel'),
         theorem('PhotoLean.StokesShift.emEnergy_eq', 'PhotoLean/StokesShift/Criterion.lean', 54,
                 'delivered closed form emEnergy = e00 - lam consumed by the probe')],
        'The probe states the barrier as the barrier-height channel against the squared emission '
        'gap over 4*lam, rewrites emEnergy by its closed form and closes the field normalisation.'),
    'The legacy §15 record covers the zero-set edge only; this quantitative equality is a new, '
    'independent statement-level query and is not derived from the legacy certificate.'))

# Q-RAD3-EI-01 — EnergyGapLaw / ICvsISC rate identity.
QUERIES.append(make_query(
    'Q-RAD3-EI-01', 'P-EnergyGapLaw-ICvsISC',
    'The internal-conversion channel rate is the energy-gap-law nonradiative rate',
    'Are the ICvsISC internal-conversion rate AI*exp(-fcBarrier(lamI,xI)/(kB*T)) and the '
    'energy-gap-law nonradiative rate AI*exp(-nrBarrier(lamI,xI)/(kB*T)) the same function of '
    'the same parameters, so that the IC channel is the gap-law channel?',
    'ICvsISC writes its IC channel as a Marcus-form rate over its own Franck-Condon barrier; the '
    'energy-gap law writes the nonradiative rate as the same Arrhenius form over the crossing '
    'barrier. Both barriers are the same body (lam-x)^2/(4lam) in the delivered kernel copies, so '
    'the two rates are definitionally the same function. This is a genuine channel '
    'identification: the IC channel of the competition is the gap-law nonradiative channel, not '
    'merely a rate law with a similar shape.',
    'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'EiRateCtx',
    premise('fun _ : EiRateCtx => True', [],
            note='The two barriers are the same body, so the rates are definitionally equal at '
                 'every parameter; the totalized division makes the identity hold also at '
                 'lamI = 0, so no positivity premise is load-bearing for the pin.'),
    [],
    'scope-RAD3-rate-identity', 'definitionalIdentity',
    'After unfolding the two delivered definitions, the two terms are definitionally equal; the '
    'certificate is a fresh kernel rfl pin, not a propositional equality.',
    'A parameter tuple at which the two rates differ would refute the identity; the kernel rfl '
    'check is the falsification gate.',
    'certified',
    'The package-local typed definitional pin is checked by a fresh kernel rfl elaboration and '
    'carries only the allowed axiom footprint.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.eiRateDefinition',
        'definitionalIdentity',
        [theorem('PhotoLean.ICvsISC.icRate', 'PhotoLean/ICvsISC/Basic.lean', 72,
                 'IC channel rate unfolded by the definitional pin'),
         theorem('PhotoLean.EnergyGapLaw.nrRate', 'PhotoLean/EnergyGapLaw/Basic.lean', 74,
                 'gap-law nonradiative rate unfolded by the definitional pin'),
         theorem('PhotoLean.ICvsISC.fcBarrier', 'PhotoLean/ICvsISC/Basic.lean', 63,
                 'IC channel barrier copy sharing the kernel barrier body'),
         theorem('PhotoLean.EnergyGapLaw.nrBarrier', 'PhotoLean/EnergyGapLaw/Basic.lean', 62,
                 'gap-law barrier copy sharing the kernel barrier body')],
        'The probe declares the five-parameter IC context and pins the two rates with a fresh '
        'DefEq.refl; the two barrier definitions have the same body, so the kernel accepts the '
        'definitional equality without a propositional rewrite.'),
    'The legacy §15 record rec-D-S15-icvscic-icRate-eq-eg-nrRate is a certified pair row on the '
    'same two delivered declarations; this query re-certifies it statement-first in a '
    'package-local probe and does not cite the legacy certificate as evidence.'))

# Q-RAD3-EI-02 — EnergyGapLaw / ICvsISC conditional composition.
QUERIES.append(make_query(
    'Q-RAD3-EI-02', 'P-EnergyGapLaw-ICvsISC',
    'The IC-vs-ISC crossover reads with the gap-law nonradiative rate on the IC side',
    'Does the delivered IC-vs-ISC crossover isc_dominates_iff remain true when its IC rate is '
    'replaced by the energy-gap-law nonradiative rate at the same parameters, i.e. is the gap-law '
    'rate below the ISC rate exactly when the ISC barrier deficit beats the spin/prefactor '
    'threshold?',
    'The ICvsISC crossover compares the spin-orbit ISC rate with the IC rate through a log-ratio '
    'inequality. Replacing the IC rate by the gap-law rate is licensed by the definitional '
    'identity Q-RAD3-EI-01, and the resulting statement is the crossover of the gap-law channel '
    'against the ISC channel. The query is a typed composition of the two delivered rows, not a '
    'restatement of either: it transfers the ICvsISC decision law to the gap-law endpoint with '
    'the premises of the decision law.',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'stmt-ICvsISC-PhotoLean-ICvsISC-isc_dominates_iff',
    'EiCrossCtx',
    premise(
        'fun δ : EiCrossCtx => ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T ∧ 0 < δ.HSO',
        [premise_def('RAD3-EI-fcdata', 'positivity',
                     'fun δ : EiCrossCtx => ICvsISC.FCData δ.AI δ.AS δ.lamI δ.lamS δ.kB δ.T',
                     'The IC-vs-ISC positivity bundle: positive prefactors, reorganization '
                     'energies and thermal energy.',
                     'The delivered isc_dominates_iff consumes this bundle for the strict '
                     'positivity of the IC rate; the composition inherits it from the second '
                     'parent.'),
         premise_def('RAD3-EI-hso-positive', 'positivity',
                     'fun δ : EiCrossCtx => 0 < δ.HSO',
                     'The spin-orbit amplitude is positive, so its logarithm is defined.',
                     'The delivered isc_dominates_iff consumes 0 < HSO to move the race to the '
                     'log side; the composition inherits it from the second parent.')],
        note='The child premise list is exactly the premise list of the isc_dominates_iff parent; '
             'the first parent (the definitional rate identification) has no premises.'),
    [],
    'scope-RAD3-rate-identity', 'conditionalComposition',
    'Two typed parents: the definitional identity between the IC and gap-law rates, and the '
    'delivered crossover isc_dominates_iff. Both are equivalences, so the computed child form is '
    'an equivalence; the composition consumes the typed parents, inherits their premises and has '
    'an empty bridge.',
    'A context satisfying FCData and 0 < HSO at which the gap-law rate is below the ISC rate but '
    'the barrier threshold fails (or conversely) would refute the composition.',
    'certified',
    'The package-local typed conditional composition is checked; the child conclusion is '
    'computed from the two typed parents and their alignment, not supplied independently. The '
    'probe witness pins the parent IDs, the empty bridge and the child premise list.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.eiCrossoverComposition',
        'conditionalComposition',
        [theorem('PhotoLean.ICvsISC.isc_dominates_iff', 'PhotoLean/ICvsISC/Criterion.lean', 124,
                 'second typed parent: the delivered IC-vs-ISC crossover'),
         theorem('PhotoLean.ICvsISC.icRate', 'PhotoLean/ICvsISC/Basic.lean', 72,
                 'middle endpoint: the IC rate replaced by the gap-law rate'),
         theorem('PhotoLean.EnergyGapLaw.nrRate', 'PhotoLean/EnergyGapLaw/Basic.lean', 74,
                 'child left endpoint: the gap-law nonradiative rate'),
         theorem('PhotoLean.ICvsISC.fcBarrier', 'PhotoLean/ICvsISC/Basic.lean', 63,
                 'barrier argument of the crossover threshold')],
        'The probe builds a first equivalence parent from the definitional rate identification, a '
        'second equivalence parent from the delivered isc_dominates_iff, aligns the middle IC-rate '
        'predicate by Iff.rfl, inherits both parent premises from the child premise list and '
        'derives the child conclusion through ConditionalComposition.sound.',
        composition={
            'parents': [
                {'id': 'RAD3-EI-rate-identification', 'kind': 'equivalence',
                 'statementId': 'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate'},
                {'id': 'RAD3-EI-isc-dominance', 'kind': 'equivalence',
                 'statementId': 'stmt-ICvsISC-PhotoLean-ICvsISC-isc_dominates_iff'},
            ],
            'childPremiseIds': ['RAD3-EI-fcdata', 'RAD3-EI-hso-positive'],
            'bridgeIds': [],
            'dischargeIds': [],
            'mediatingStatementId': 'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
            'form': 'equivalence',
        }),
    'The legacy §15 record covers the direct IC-rate identity only; this composition transfers '
    'the crossover law to the gap-law endpoint and is a new statement-level query.'))

# Q-RAD3-SI-01 — StokesShift / ICvsISC surface height.
QUERIES.append(make_query(
    'Q-RAD3-SI-01', 'P-StokesShift-ICvsISC',
    'The thermoneutral IC barrier is the Stokes ground surface at the crossing coordinate',
    'At zero driving force, is the IC channel Franck-Condon barrier fcBarrier lam 0 the Stokes '
    'ground-state surface s0Surface lam (1/2) at the equal-curvature crossing coordinate q = 1/2?',
    'Both theories read the same equal-curvature parabolas. The IC barrier at thermoneutrality is '
    'lam/4; the Stokes ground surface at the crossing coordinate q = 1/2 is lam/4. The query asks '
    'whether the kinetic barrier is the optical surface height at the crossing, a shared '
    'two-parabola quantity, not a notation match.',
    'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
    'stmt-StokesShift-PhotoLean-StokesShift-s0Surface',
    'SiSurfaceCtx',
    premise('fun _ : SiSurfaceCtx => True', [],
            note='Both sides vanish at lam = 0, so the identity is unconditional; no positivity '
                 'premise is load-bearing.'),
    [channel('barrier-height', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => ICvsISC.fcBarrier δ.lam 0',
             'fun δ _ => StokesShift.s0Surface δ.lam (1 / 2)')],
    'scope-RAD3-surface-height', 'observationalEquivalence',
    'Both sides are real-valued surface heights on the same reorganization energy; the '
    'certificate is equality of the barrier-height channel at the single declared input.',
    'A reorganization energy at which the thermoneutral IC barrier and the crossing surface height '
    'differ would refute the identity.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint and is unconditional, matching the declared scope.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.siSurfaceBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.ICvsISC.fcBarrier', 'PhotoLean/ICvsISC/Basic.lean', 63,
                 'definition of the IC channel barrier consumed by the probe'),
         theorem('PhotoLean.StokesShift.s0Surface', 'PhotoLean/StokesShift/Basic.lean', 55,
                 'definition of the Stokes ground surface at the crossing coordinate')],
        'The probe states the thermoneutral barrier against the Stokes ground surface at q = 1/2 '
        'and closes the equality by a case split on lam = 0 with field normalisation.'),
    'The legacy §16 row is a registered-absence anchor; it is coverage history, not an audit '
    'verdict, and is not cited as evidence.'))

# Q-RAD3-FoE-01 — Forster / Einstein rate.
QUERIES.append(make_query(
    'Q-RAD3-FoE-01', 'P-Forster-Einstein',
    'At the Einstein radiative lifetime the Forster rate is the A coefficient times the geometric factor',
    'When the donor lifetime in the Forster rate is the Einstein radiative lifetime tauR A = 1/A, '
    'is the transfer rate (1/tauD)*(r6/R^6) the Einstein stimulated-emission term '
    'aOfB A (r6/R^6)?',
    'The Forster rate is the donor decay rate times the sixth-power geometric factor; the '
    'Einstein A coefficient is the radiative decay rate of one transition. Setting the donor '
    'lifetime to the radiative lifetime makes the Forster rate A*(r6/R^6), i.e. the Einstein A '
    'term aOfB at the geometric factor. The query connects the transfer-rate law to the radiative '
    'coefficient without claiming that the Forster radius is an A coefficient; both reciprocal '
    'maps are totalized, so the identity is unconditional.',
    'stmt-Forster-PhotoLean-Forster-fretRate',
    'stmt-Einstein-PhotoLean-Einstein-aOfB',
    'FoEinCtx',
    premise('fun _ : FoEinCtx => True', [],
            note='Both reciprocal maps are totalized, so the identity covers A = 0 and R = 0 as '
                 'well; no positivity premise is load-bearing.'),
    [channel('rate-constant', 'ℝ', 'Unit (the single declared configuration)',
             'fun δ _ => Forster.fretRate (Einstein.tauR δ.A) δ.r6 δ.R',
             'fun δ _ => Einstein.aOfB δ.A (δ.r6 / δ.R ^ 6)')],
    'scope-RAD3-rate-identity', 'observationalEquivalence',
    'Both sides are real-valued rate constants on the same (A, r6, R) context; the certificate is '
    'equality of the rate-constant channel at the single declared input.',
    'A tuple (A, r6, R) at which the radiative-lifetime Forster rate and the A-coefficient term '
    'differ would refute the identity.',
    'certified',
    'The package-local typed Lean certificate is checked; it carries only the allowed axiom '
    'footprint and its unconditional scope matches the empty premise list.',
    probe_evidence(
        'PhotoLean.RelationAudit.BoundedAudit.Rad3.foEinBridge',
        'observationalEquivalence',
        [theorem('PhotoLean.Forster.fretRate', 'PhotoLean/Forster/Basic.lean', 54,
                 'definition of the Forster transfer rate consumed by the probe'),
         theorem('PhotoLean.Einstein.tauR', 'PhotoLean/Einstein/Basic.lean', 65,
                 'definition of the radiative lifetime substituted for the donor lifetime'),
         theorem('PhotoLean.Einstein.aOfB', 'PhotoLean/Einstein/Basic.lean', 49,
                 'definition of the Einstein A coefficient from B consumed by the probe')],
        'The probe substitutes tauR A for the donor lifetime, normalises the reciprocal maps '
        'with one_div/inv_inv and closes the equality against aOfB.'),
    'The legacy §16 row is a registered-absence anchor; it is coverage history, not an audit '
    'verdict, and is not cited as evidence.'))

# --------------------------------------------------------------------------- non-certified

# Q-RAD3-EF-01 — EnergyGapLaw / Forster jurisdiction.
QUERIES.append(make_query(
    'Q-RAD3-EF-01', 'P-EnergyGapLaw-Forster',
    'Is the Forster transfer rate an activated energy-gap-law process?',
    'Is the Forster resonance transfer rate an activated nonradiative rate whose barrier is the '
    'energy-gap-law barrier at the same driving force?',
    'Forster transfer is a through-space dipolar process with an R^-6 distance law and a donor '
    'lifetime; the energy-gap law is an activated nonradiative crossing with a reorganization '
    'energy and a gap coordinate. The two models share no energy coordinate and no delivered '
    'statement maps (tauD, r6, R) to (lam, x). The question is outside the declared jurisdiction, '
    'not logically false.',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'stmt-Forster-PhotoLean-Forster-fretRate',
    'EgForsterDisjointCtx',
    premise('fun _ : EgForsterDisjointCtx => True', [],
            note='No certificate is claimed; the jurisdiction record does not consume a premise.'),
    [],
    'scope-RAD3-jurisdiction', 'implication',
    'The would-be form is an implication from a gap-law barrier premise to a Forster rate '
    'premise; the jurisdiction record denies the shared translation the implication would need.',
    'A delivered statement identifying the Forster R^-6 rate with a gap-law barrier or rate '
    'would remove the jurisdiction boundary; none exists.',
    'outOfScope',
    'No shared context or declared translation exists: the gap-law rate is a function of '
    '(A, lam, kB, T, x) and the Forster rate of (tauD, r6, R). The absence is jurisdictional, not '
    'a refutation or a logical non-existence claim.',
    {
        'type': 'jurisdiction',
        'searchLogRef': 'SL-RAD3-EF-01',
        'jurisdictionRationale': 'The gap-law rate is an activated nonradiative crossing over a '
                                 'reorganization barrier; the Forster rate is a through-space '
                                 'transfer law in the separation R. No delivered statement maps '
                                 'one descriptor set to the other.',
        'statementLevelReason': 'The endpoints EnergyGapLaw.nrRate and Forster.fretRate have '
                                'disjoint argument sets (lam, kB, T, x) versus (tauD, r6, R); '
                                'the EnergyGapLaw and Forster modules share no statement, and no '
                                'translation is declared in the frozen contract.',
    },
    'The legacy §16 row is a registered-absence anchor; the jurisdiction record is independently '
    'argued and does not rely on that legacy label.',
    translations={
        'left': none_translation('left',
            'No total translation from the gap-law (lam, x) coordinate to the Forster '
            '(tauD, r6, R) transfer descriptor is delivered; the descriptor sets are disjoint.'),
        'right': none_translation('right',
            'No total translation from the Forster (tauD, r6, R) transfer descriptor to the '
            'gap-law (lam, x) coordinate is delivered; the descriptor sets are disjoint.'),
    }))

# Q-RAD3-EE-01 — EnergyGapLaw / Einstein jurisdiction.
QUERIES.append(make_query(
    'Q-RAD3-EE-01', 'P-EnergyGapLaw-Einstein',
    'Is the gap-law prefactor the Einstein A coefficient?',
    'Is the energy-gap-law nonradiative prefactor A the Einstein A coefficient, so that the '
    'gap-law rate at the barrierless point is the radiative coefficient?',
    'The two theories use the same letter A for different quantities: the gap law A is a '
    'nonradiative pre-exponential factor of a crossing rate, while the Einstein A is the '
    'spontaneous-emission coefficient of a radiative transition. The gap-law rate is '
    'nonradiative (its barrier is a nuclear reorganization barrier) and the Einstein coefficients '
    'are radiative detailed-balance objects. No delivered statement identifies the two, and the '
    'shared symbol is a naming coincidence that must not be read as a relation. The question is '
    'outside the declared jurisdiction, not logically false.',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
    'stmt-Einstein-PhotoLean-Einstein-aOfB',
    'EgEinsteinDisjointCtx',
    premise('fun _ : EgEinsteinDisjointCtx => True', [],
            note='No certificate is claimed; the jurisdiction record does not consume a premise.'),
    [],
    'scope-RAD3-jurisdiction', 'implication',
    'The would-be form is an implication identifying the gap-law prefactor with a radiative '
    'coefficient; the jurisdiction record denies the shared descriptor the implication would '
    'need.',
    'A delivered statement identifying the gap-law prefactor A with aOfB, or the nonradiative '
    'gap with a radiative photon energy, would remove the boundary; none exists.',
    'outOfScope',
    'The gap-law prefactor is a nonradiative pre-exponential factor and the Einstein A is a '
    'radiative coefficient; the shared symbol A is a naming coincidence with no delivered '
    'descriptor in common. The absence is jurisdictional, not a refutation.',
    {
        'type': 'jurisdiction',
        'searchLogRef': 'SL-RAD3-EE-01',
        'jurisdictionRationale': 'The gap-law rate is an activated nonradiative rate over a '
                                 'nuclear reorganization barrier; the Einstein A/B algebra is a '
                                 'radiative detailed-balance chain over degeneracies and a '
                                 'radiation density. No delivered statement identifies the two '
                                 'prefactors or the gap coordinate with a photon energy.',
        'statementLevelReason': 'EnergyGapLaw.nrRate carries the prefactor A as a nonradiative '
                                'frequency factor; Einstein.aOfB maps a radiative B coefficient '
                                'to A through the radiation-density factor. The two declarations '
                                'share a symbol but no argument and no delivered bridge.',
    },
    'The legacy §16 completion row is a registered-absence anchor; the jurisdiction record is '
    'independently argued and does not rely on that legacy label.',
    translations={
        'left': none_translation('left',
            'No total translation from the gap-law (lam, x) coordinate to the Einstein '
            '(K, B21) coefficient algebra is delivered; the shared symbol A denotes different '
            'quantities.'),
        'right': none_translation('right',
            'No total translation from the Einstein (K, B21) coefficient algebra to the gap-law '
            '(lam, x) coordinate is delivered; the shared symbol A denotes different quantities.'),
    }))

# Q-RAD3-SF-01 — StokesShift / Forster scoped search.
QUERIES.append(make_query(
    'Q-RAD3-SF-01', 'P-StokesShift-Forster',
    'Is the Forster spectral overlap integral determined by the Stokes shift?',
    'Is the Forster spectral-overlap integral J, which enters r0six as a free parameter, a '
    'delivered function of the Stokes-shifted absorption and emission energies, so that the '
    'transfer efficiency is determined by the Stokes shift?',
    'In FRET practice the overlap integral J is the overlap of the donor emission with the '
    'acceptor absorption, and the Stokes shift sets where the donor emission band sits, so a '
    'relation between J and the Stokes parameters is physically meaningful. In the delivered '
    'corpus, however, Forster.r0six takes J as a free parameter and StokesShift declares only '
    'band maxima; the scoped search over the two statement authorities found no line-shape or '
    'overlap statement. A candidate bridge exists, but no certificate of the requested kind is '
    'delivered within the frozen snapshot.',
    'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
    'stmt-Forster-PhotoLean-Forster-r0six',
    'SfOverlapCandidateCtx',
    premise('fun _ : SfOverlapCandidateCtx => True', [],
            note='No certificate is claimed; the scoped-search record does not consume a premise.'),
    [],
    'scope-RAD3-scoped-search', 'implication',
    'The candidate form is an implication from the Stokes band maxima to a value of the overlap '
    'integral; no delivered statement of the requested kind was found in the frozen snapshot.',
    'A delivered statement defining J as a function of the Stokes parameters, or a line-shape or '
    'overlap object, would remove the gap; its absence is not a refutation.',
    'notEstablished',
    'Within the frozen snapshot the declared search over the StokesShift and Forster statement '
    'authorities found no declaration of a spectral overlap, line shape or J-defining function; '
    'J remains a free parameter of r0six. This is a scoped negative registration, not a logical '
    'absence.',
    {
        'type': 'scoped-search',
        'searchLogRef': 'SL-RAD3-SF-01',
        'candidateSummary': 'Candidate: J = J(stokesShift lam e00), or J as the overlap of two '
                            'declared band shapes. Missing: any delivered line-shape, band-width '
                            'or overlap declaration; both module layers state that they model '
                            'band maxima only.',
    },
    'The legacy §16 row is a registered-absence anchor; the scoped-search record is independently '
    'recomputed and does not rely on that legacy label.',
    translations={
        'left': candidate_translation('left',
            'No total translation from the Stokes band maxima (lam, e00) to the Forster radius '
            'parameters is delivered: the overlap integral J is a free parameter and no band '
            'shape is declared.'),
        'right': candidate_translation('right',
            'No total translation from the Forster radius parameters to the Stokes band maxima '
            'is delivered: no delivered statement defines J in terms of (lam, e00).'),
    }))

# Q-RAD3-SE-01 — StokesShift / Einstein jurisdiction.
QUERIES.append(make_query(
    'Q-RAD3-SE-01', 'P-StokesShift-Einstein',
    'Is the Stokes emission energy a transition frequency of the Einstein coefficients?',
    'Is the Stokes vertical emission energy the transition energy h*nu that fixes the Einstein '
    'radiation-density factor, so that the radiative coefficient is evaluated at the '
    'Stokes-shifted frequency?',
    'The Stokes statements are band maxima of the two surfaces (lam+e00 and e00-lam); the '
    'Einstein statements are detailed-balance algebra over a transition frequency, degeneracies '
    'and a radiation density. No delivered statement identifies e00 or emEnergy with h*nu, and '
    'the Strickler-Berg leg aOfInt takes an integrated absorption I that has no Stokes '
    'counterpart. Identifying I with a band maximum would be a dimensional category error, not a '
    'translation. The question is outside the declared jurisdiction.',
    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
    'stmt-Einstein-PhotoLean-Einstein-radFactor',
    'SeSpectralDisjointCtx',
    premise('fun _ : SeSpectralDisjointCtx => True', [],
            note='No certificate is claimed; the jurisdiction record does not consume a premise.'),
    [],
    'scope-RAD3-jurisdiction', 'implication',
    'The would-be form is an implication from a Stokes band maximum to the frequency argument of '
    'the Einstein radiation factor; the jurisdiction record denies the shared descriptor the '
    'implication would need.',
    'A delivered statement identifying emEnergy or e00 with h*nu, or the integrated absorption I '
    'with a band maximum, would remove the boundary; none exists.',
    'outOfScope',
    'The Stokes statements are band maxima of two surfaces; the Einstein statements are '
    'coefficient algebra over a transition frequency and a radiation density. No delivered '
    'translation identifies the two, and the only absorption-like Einstein argument (the '
    'integrated absorption I) is not a band maximum. The absence is jurisdictional.',
    {
        'type': 'jurisdiction',
        'searchLogRef': 'SL-RAD3-SE-01',
        'jurisdictionRationale': 'StokesShift quantifies band maxima (vertical absorption and '
                                 'emission energies); Einstein quantifies radiative coefficients '
                                 'over a transition frequency and a radiation density. No '
                                 'delivered statement equates a band maximum with h*nu or with '
                                 'the integrated absorption I.',
        'statementLevelReason': 'StokesShift.emEnergy is x - lam in surface coordinates; '
                                'Einstein.radFactor is 8*pi*h*nu^3/c^3. The argument sets and '
                                'the physical quantities differ, and no bridge declaration '
                                'exists in the frozen statement set.',
    },
    'The legacy §16 row is a registered-absence anchor; the jurisdiction record is independently '
    'argued and does not rely on that legacy label.',
    translations={
        'left': none_translation('left',
            'No total translation from the Stokes band maxima (lam, e00) to the Einstein '
            '(h, c, nu) radiation factor is delivered; no statement equates a band maximum with '
            'a photon energy.'),
        'right': none_translation('right',
            'No total translation from the Einstein (h, c, nu) radiation factor to the Stokes '
            'band maxima is delivered; no statement equates h*nu with an emission energy.'),
    }))

# Q-RAD3-IF-01 — ICvsISC / Forster unresolved candidate.
QUERIES.append(make_query(
    'Q-RAD3-IF-01', 'P-ICvsISC-Forster',
    'Is the Forster transfer channel a third channel in the IC-vs-ISC competition?',
    'Does the Forster transfer channel enter the IC-vs-ISC competition as an additional '
    'nonradiative channel, so that the ISC dominance condition is read against the sum of the IC '
    'and transfer rates?',
    'ICvsISC compares two nonradiative channels of one excited state; FRET adds a '
    'distance-dependent decay channel to that state. A relation would compose isc_dominates_iff '
    'with the Forster rate, replacing the IC denominator by icRate + fretRate. The candidate is '
    'physically meaningful, but the corpus delivers no statement that the donor decay rate is the '
    'IC rate and no statement that adds the transfer rate to the IC channel, so the composition '
    'bridge is missing.',
    'stmt-ICvsISC-PhotoLean-ICvsISC-isc_dominates_iff',
    'stmt-Forster-PhotoLean-Forster-fretRate',
    'IfThirdChannelCandidateCtx',
    premise('fun _ : IfThirdChannelCandidateCtx => True', [],
            note='No certificate is claimed; the candidate record does not consume a premise.'),
    [],
    'scope-RAD3-scoped-search', 'conditionalComposition',
    'The candidate form is a conditional composition of isc_dominates_iff with a Forster channel '
    'term; the parent bridge that would license the composition is not delivered.',
    'A delivered bridge equating the donor decay rate with the IC rate (and the transfer rate '
    'with an added channel) would remove the gap; its absence is not a refutation.',
    'unresolved',
    'The composition needs a delivered donor-lifetime bridge (1/tauD = icRate) and a delivered '
    'three-channel competition statement; the corpus states neither, and the legacy register '
    'records no shared scalar. The candidate remains open and is not a negative claim.',
    {
        'type': 'scoped-search',
        'searchLogRef': 'SL-RAD3-IF-01',
        'candidateSummary': 'Candidate: isc_dominates_iff with icRate replaced by '
                            'icRate + fretRate. Missing: a delivered bridge that the donor decay '
                            'rate is the IC channel rate and that the Forster channel adds to the '
                            'IC channel.',
    },
    'The legacy §16 row is a registered-absence anchor; the candidate record is independently '
    'searched and does not rely on that legacy label.',
    translations={
        'left': candidate_translation('left',
            'No total translation from the IC-vs-ISC channel context to the Forster transfer '
            'descriptor is delivered: the donor lifetime and separation have no ICvsISC '
            'counterpart.'),
        'right': candidate_translation('right',
            'No total translation from the Forster transfer descriptor to the IC-vs-ISC channel '
            'context is delivered: no statement equates 1/tauD with icRate.'),
    }))

# Q-RAD3-IE-01 — ICvsISC / Einstein jurisdiction.
QUERIES.append(make_query(
    'Q-RAD3-IE-01', 'P-ICvsISC-Einstein',
    'Is the spin-orbit ISC channel a radiative Einstein coefficient?',
    'Is the ICvsISC spin-orbit ISC channel rate HSO^2*AS*exp(-fcBarrier/(kB*T)) an Einstein '
    'radiative coefficient or a stimulated-emission term?',
    'The ICvsISC ISC channel is a nonradiative spin-forbidden crossing: its prefactor HSO^2*AS '
    'carries a spin-orbit amplitude and a channel prefactor, and its Boltzmann factor carries a '
    'nuclear barrier. The Einstein coefficients are radiative detailed-balance objects with '
    'degeneracies and a radiation density. No delivered statement identifies HSO^2*AS with aOfB, '
    'nor the spin-orbit coupling with a radiation-density factor; the two mechanisms are '
    'different and their descriptor sets are disjoint. The question is outside the declared '
    'jurisdiction.',
    'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
    'stmt-Einstein-PhotoLean-Einstein-aOfB',
    'IeSpinRadDisjointCtx',
    premise('fun _ : IeSpinRadDisjointCtx => True', [],
            note='No certificate is claimed; the jurisdiction record does not consume a premise.'),
    [],
    'scope-RAD3-jurisdiction', 'implication',
    'The would-be form is an implication from a spin-orbit ISC channel premise to a radiative '
    'coefficient premise; the jurisdiction record denies the shared descriptor.',
    'A delivered statement identifying HSO^2*AS with a radiative coefficient, or the nuclear '
    'ISC barrier with a photon energy, would remove the boundary; none exists.',
    'outOfScope',
    'The ISC channel is a nonradiative spin-forbidden crossing with a spin-orbit prefactor and a '
    'nuclear barrier; the Einstein A/B coefficients are radiative detailed-balance objects. No '
    'delivered statement identifies the two prefactors or the two energies. The absence is '
    'jurisdictional, not a refutation.',
    {
        'type': 'jurisdiction',
        'searchLogRef': 'SL-RAD3-IE-01',
        'jurisdictionRationale': 'The ICvsISC ISC prefactor HSO^2*AS is a spin-orbit channel '
                                 'strength over a nuclear Franck-Condon barrier; the Einstein '
                                 'coefficient aOfB is a radiative transition strength over a '
                                 'radiation density. No delivered statement identifies them.',
        'statementLevelReason': 'ICvsISC.iscRate and Einstein.aOfB have disjoint argument sets '
                                '(HSO, AS, lamS, kB, T, xS) versus (K, B21); no bridge '
                                'declaration exists in the frozen statement set.',
    },
    'The legacy §16 row is a registered-absence anchor; the jurisdiction record is independently '
    'argued and does not rely on that legacy label.',
    translations={
        'left': none_translation('left',
            'No total translation from the spin-orbit ISC channel (HSO, AS, lamS, kB, T, xS) to '
            'the Einstein coefficient algebra (K, B21) is delivered.'),
        'right': none_translation('right',
            'No total translation from the Einstein coefficient algebra (K, B21) to the '
            'spin-orbit ISC channel is delivered.'),
    }))


def build_screening():
    pairs = []
    for pair_id in PAIR_IDS:
        qrows = [q for q in QUERIES if q['pairId'] == pair_id]
        qrow = QUEUE_BY_ID[pair_id]
        pairs.append({
            'pairId': pair_id,
            'theories': list(qrow['theories']),
            'primaryCluster': qrow['screeningCluster'],
            'queryIds': [q['queryId'] for q in qrows],
            'queries': qrows,
        })

    status_counts = {}
    kind_counts = {}
    for q in QUERIES:
        status_counts[q['outcome']['status']] = status_counts.get(q['outcome']['status'], 0) + 1
        kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1

    search_log_path = os.path.join(ROOT, SEARCH_REL)
    search_sha = sha_file(search_log_path) if os.path.exists(search_log_path) else 'PENDING'
    search_count = len(SEARCH_ENTRIES) if 'SEARCH_ENTRIES' in globals() else 0

    return {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WORK_PACKAGE,
            'title': 'Radiative energy transfer: the six non-Marcus photophysical theories',
            'source': 'loop/计划.md R5, Package RAD3',
            'pairIds': list(PAIR_IDS),
            'pairCount': len(PAIR_IDS),
            'note': ('Exactly the thirteen R1 WP-radiative-energy-transfer-03 pairs. No '
                     'accepted R2/R3/R4 pair is rescreened, and no pair outside the thirteen is '
                     'touched.'),
        },
        'statusVocabulary': list(STATUSES),
        'kindVocabulary': list(KINDS),
        'allowedAxioms': list(ALLOWED_AXIOMS),
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
            'acceptedPriorPackageCount': len(PRIOR_PACKAGES),
            'acceptedPriorScreenedPairCount': 67,
            'leanToolchain': 'leanprover/lean4:v4.17.0',
            'deliveredLeanFileCount': 102,
        },
        'inventoryReference': {
            'path': INV_REL,
            'sha256': sha_rel(INV_REL),
            'statementRows': len(INV['statements']),
            'screeningEligibleRows': sum(1 for s in INV['statements'] if s['screeningEligible']),
            'version': '1.0.0',
        },
        'legacyRegistryReference': {
            'path': REGISTRY_REL,
            'sha256': sha_rel(REGISTRY_REL),
            'certificateCount': len(REGISTRY.get('certificates', [])),
            'queryCount': len(REGISTRY.get('queries', [])),
            'recordCount': len(REGISTRY.get('records', [])),
        },
        'coverageReference': {
            'derivedFrom': list(PRIOR_PACKAGES),
            'acceptedScreenedPairCount': 67,
            'pin': 'not-pinned',
            'note': ('Prior coverage is derived directly from the accepted screening packages '
                     'listed in derivedFrom. The mutable R5 cumulative ledger is neither read '
                     'nor pinned by this package or its validator.'),
        },
        'searchLogReference': {
            'path': SEARCH_REL,
            'sha256': search_sha,
            'entryCount': search_count,
        },
        'probeReference': {
            'path': PROBE_REL,
            'sha256': sha_rel(PROBE_REL),
            'declarationCount': 10,
            'log': PROBE_LOG_REL,
            'buildCommand': BUILD_COMMAND,
        },
        'aliasResolutions': [
            {
                'legacyRecordId': 'rec-D-S15-egBarrier-zero-iff-emEnergy-zero',
                'legacyQueryId': 'q-D-S15-egBarrier-zero-iff-emEnergy-zero',
                'danglingEndpoints': [
                    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier-eq-zero',
                    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy-eq-zero',
                ],
                'resolvedStatements': [
                    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
                    'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
                ],
                'resolution': ('The legacy certificate used two endpoint aliases that are not '
                               'delivered declarations. Its statement-level content is the '
                               'zero-set equivalence, restated as Q-RAD3-ES-01 on the delivered '
                               'nrBarrier and emEnergy with a new package-local certificate. The '
                               'legacy aliases are not cited as endpoints anywhere in this '
                               'package.'),
            },
        ],
        'contextLibrary': {cid: build_context(cid) for cid in CONTEXTS},
        'scopeLibrary': {sid: build_scope(sid) for sid in SCOPES},
        'pairs': pairs,
        'counts': {
            'pairs': len(pairs),
            'queries': len(QUERIES),
            'byStatus': status_counts,
            'byExpectedKind': kind_counts,
            'certified': status_counts.get('certified', 0),
            'refuted': status_counts.get('refuted', 0),
            'unresolved': status_counts.get('unresolved', 0),
            'notEstablished': status_counts.get('notEstablished', 0),
            'outOfScope': status_counts.get('outOfScope', 0),
        },
        'nonClaims': [
            'This package is not a completeness claim about any pair.',
            'A certified row is a checked relation under its declared context, premises and snapshot; it is not a claim of physical universality.',
            'A rate or barrier identity is not an identification of the two theories microscopic coordinates, mechanisms or parameters beyond the declared translation.',
            'An unresolved row is not a negative claim and is not a refutation.',
            'A notEstablished or outOfScope row is a scoped registration, not logical non-existence.',
            'No pair was forced into a relation to increase an edge count: the six non-certified pairs record the missing bridge or the jurisdiction reason explicitly.',
            'The legacy registry and the accepted R1-R4 artifacts are read-only in R5; the cumulative R5 ledger is written by the integration agent, not by this package.',
        ],
    }


SEARCH_ENTRIES = [
    {
        'searchId': 'SL-RAD3-EF-01',
        'queryId': 'Q-RAD3-EF-01',
        'pairId': 'P-EnergyGapLaw-Forster',
        'status': 'outOfScope',
        'scope': 'scope-RAD3-jurisdiction',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the Forster transfer rate an activated energy-gap-law process?',
        'searchedStatements': [
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-lnRate',
            'stmt-Forster-PhotoLean-Forster-fretRate',
            'stmt-Forster-PhotoLean-Forster-fretEff6',
            'stmt-Forster-PhotoLean-Forster-r0six',
            'stmt-Forster-PhotoLean-Forster-kappaSq',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'EgForsterDisjointCtx (candidate: gap coordinate (lam, x) beside transfer coordinates (tauD, r6, R))',
            'two-parabola activated-rate context',
            'through-space transfer context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/EnergyGapLaw/Basic.lean', 'locator': 'nrRate (line 74)',
             'finding': 'The gap-law rate is A*exp(-nrBarrier(lam,x)/(kB*T)); its arguments are '
                        'a gap coordinate, a reorganization energy and a thermal energy. No '
                        'distance or lifetime parameter occurs.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'fretRate (line 54)',
             'finding': 'The Forster rate is (1/tauD)*(r6/R^6); its arguments are a donor '
                        'lifetime, a sixth-power radius and a separation. No barrier or '
                        'reorganization energy occurs.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'module docstring (line 21)',
             'finding': 'The module registers C, Phi, J, n as free positive parameters and '
                        'states that no spectral-overlap theory is derived.'},
        ],
        'commands': [
            {'command': 'grep -rn "fretRate\\|fretEff\\|r0six\\|kappaSq\\|tauD" PhotoLean/EnergyGapLaw/',
             'purpose': 'Find any Forster descriptor inside the energy-gap-law theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rn "nrBarrier\\|nrRate\\|lnRate\\|InvertedGap" PhotoLean/Forster/',
             'purpose': 'Find any gap-law descriptor inside the Forster theory.',
             'result': '(no match; exit 1)'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"EnergyGapLaw\",\"Forster\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('EnergyGapLaw', 25), ('Forster', 32)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Compare the argument sets of the two rate laws directly.',
             'outcome': 'Disjoint: (A, lam, kB, T, x) versus (tauD, r6, R); no coordinate is '
                        'shared.'},
            {'strategy': 'Search the gap-law module for a distance or lifetime parameter.',
             'outcome': 'No occurrence.'},
            {'strategy': 'Search the Forster module for a barrier or reorganization energy.',
             'outcome': 'No occurrence.'},
        ],
        'candidateEvidence': [
            {'kind': 'implication',
             'description': 'A would-be identification of the Forster R^-6 rate with an activated '
                            'gap-law rate at a shared coordinate; no such coordinate exists.'},
        ],
        'remainingGap': 'No shared coordinate or declared translation exists: the gap-law rate '
                        'is a function of (A, lam, kB, T, x) and the Forster rate of '
                        '(tauD, r6, R). The jurisdiction record therefore denies a translation '
                        'rather than reporting a missing proof.',
        'recomputeCommands': [
            'grep -rn "fretRate\\|fretEff\\|r0six\\|kappaSq\\|tauD" PhotoLean/EnergyGapLaw/',
            'grep -rn "nrBarrier\\|nrRate\\|lnRate\\|InvertedGap" PhotoLean/Forster/',
        ],
        'rationale': 'The scoped search confirms that the two delivered vocabularies never meet: '
                     'no statement of either theory mentions a descriptor of the other. The '
                     'outcome is jurisdictional, not a refutation and not a logical absence.',
    },
    {
        'searchId': 'SL-RAD3-EE-01',
        'queryId': 'Q-RAD3-EE-01',
        'pairId': 'P-EnergyGapLaw-Einstein',
        'status': 'outOfScope',
        'scope': 'scope-RAD3-jurisdiction',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the gap-law prefactor the Einstein A coefficient?',
        'searchedStatements': [
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrRate',
            'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-lnRate',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-aOfB',
            'stmt-Einstein-PhotoLean-Einstein-b12OfB21',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
            'stmt-Einstein-PhotoLean-Einstein-yield_radiative',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'EgEinsteinDisjointCtx (candidate: gap coordinate (lam, x) beside coefficient algebra (K, B21))',
            'activated nonradiative rate context',
            'radiative detailed-balance context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/EnergyGapLaw/Basic.lean', 'locator': 'nrRate (line 74)',
             'finding': 'The prefactor A multiplies exp(-nrBarrier/(kB*T)); it is a '
                        'nonradiative frequency factor over a nuclear reorganization barrier.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'aOfB (line 49)',
             'finding': 'aOfB K B21 = K * B21: the Einstein A coefficient is a radiative '
                        'coefficient built from the radiation-density factor and B21.'},
            {'artifact': 'PhotoLean/Einstein/Criterion.lean',
             'locator': 'yield_radiative (line 152)',
             'finding': 'The delivered yield row is a two-channel radiative yield; it carries no '
                        'gap-law prefactor.'},
        ],
        'commands': [
            {'command': 'grep -rn "radFactor\\|aOfB\\|b12OfB21\\|tauR\\|B21\\|g1\\|g2" PhotoLean/EnergyGapLaw/',
             'purpose': 'Find any Einstein coefficient inside the energy-gap-law theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rn "nrBarrier\\|nrRate\\|lnRate\\|InvertedGap\\|EGZone" PhotoLean/Einstein/',
             'purpose': 'Find any gap-law descriptor inside the Einstein theory.',
             'result': '(no match; exit 1)'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"EnergyGapLaw\",\"Einstein\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('EnergyGapLaw', 25), ('Einstein', 33)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Substitute the Einstein A coefficient for the gap-law prefactor A.',
             'outcome': 'Not licensed: the gap-law A is a nonradiative frequency factor, the '
                        'Einstein A a radiative coefficient; no delivered statement equates '
                        'them.'},
            {'strategy': 'Look for a delivered identification of the gap x with h*nu.',
             'outcome': 'None; radFactor takes h, c, nu but no statement connects nu to x.'},
            {'strategy': 'Check whether the shared symbol A is used with the same type and role.',
             'outcome': 'Both are real numbers, but the roles differ (prefactor versus '
                        'coefficient); the shared spelling is a naming coincidence.'},
        ],
        'candidateEvidence': [
            {'kind': 'implication',
             'description': 'A would-be identification A_gap = aOfB (radFactor h c nu) B21 '
                            'requiring a bridge premise that neither theory delivers.'},
        ],
        'remainingGap': 'The shared symbol A denotes different quantities; no statement-level '
                        'bridge and no shared coordinate exists. The jurisdiction record denies '
                        'the translation; it does not claim the physical channels are unrelated.',
        'recomputeCommands': [
            'grep -rn "radFactor\\|aOfB\\|b12OfB21\\|tauR\\|B21\\|g1\\|g2" PhotoLean/EnergyGapLaw/',
            'grep -rn "nrBarrier\\|nrRate\\|lnRate\\|InvertedGap\\|EGZone" PhotoLean/Einstein/',
        ],
        'rationale': 'The scoped search confirms the notation trap: the two theories share the '
                     'letter A but no descriptor. The outcome is jurisdictional.',
    },
    {
        'searchId': 'SL-RAD3-SF-01',
        'queryId': 'Q-RAD3-SF-01',
        'pairId': 'P-StokesShift-Forster',
        'status': 'notEstablished',
        'scope': 'scope-RAD3-scoped-search',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the Forster spectral overlap integral determined by the Stokes shift?',
        'searchedStatements': [
            'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
            'stmt-StokesShift-PhotoLean-StokesShift-absEnergy',
            'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
            'stmt-StokesShift-PhotoLean-StokesShift-s0Surface',
            'stmt-StokesShift-PhotoLean-StokesShift-s1Surface',
            'stmt-Forster-PhotoLean-Forster-r0six',
            'stmt-Forster-PhotoLean-Forster-fretRate',
            'stmt-Forster-PhotoLean-Forster-fretEff6',
            'stmt-Forster-PhotoLean-Forster-kappaSq',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'SfOverlapCandidateCtx (candidate: band maxima (lam, e00) beside radius parameters (C, kappasq, Phi, J, n))',
            'band-maxima optical context',
            'donor-acceptor transfer context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'r0six (line 65)',
             'finding': 'r0six C kappasq Phi J n = C*kappasq*Phi*J/n^4; J is a free parameter '
                        'and no definition of J or of a line shape exists in the module.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'module docstring (line 21)',
             'finding': 'Registered non-goal: C, Phi, J, n are free positive parameters and no '
                        'spectral-overlap theory is derived.'},
            {'artifact': 'PhotoLean/StokesShift/Basic.lean', 'locator': 'module docstring (line 28)',
             'finding': 'Registered scope: no vibronic structure and no lineshape widths; the '
                        'rows are about band maxima only.'},
            {'artifact': 'PhotoLean/StokesShift/Basic.lean', 'locator': 'stokesShift (line 83)',
             'finding': 'stokesShift is a pure band-maximum difference, with no line-shape or '
                        'overlap argument.'},
        ],
        'commands': [
            {'command': 'grep -rnw "r0six\\|fretRate\\|fretEff6\\|kappaSq" PhotoLean/StokesShift/',
             'purpose': 'Find any Forster descriptor inside the Stokes-shift theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rnw "stokesShift\\|absEnergy\\|emEnergy\\|e00" PhotoLean/Forster/',
             'purpose': 'Find any Stokes descriptor inside the Forster theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rn "overlap\\|spectral\\|lineshape\\|lineShape" PhotoLean/StokesShift/ PhotoLean/Forster/',
             'purpose': 'Find a delivered overlap or line-shape declaration.',
             'result': 'Only two module-docstring lines (StokesShift/Basic.lean:28 and '
                       'Forster/Basic.lean:21), both recording the non-goal; no declaration.'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"StokesShift\",\"Forster\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('StokesShift', 35), ('Forster', 32)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Define J as an integral of the donor emission against the acceptor '
                         'absorption.',
             'outcome': 'Neither theory declares a band shape or an integrable spectrum; J stays '
                        'free.'},
            {'strategy': 'Relate the Stokes shift 2*lam to the Forster radius through kappaSq or '
                         'Phi_D.',
             'outcome': 'r0six Phi_D is a free parameter, not the FluorPhos yield; no delivered '
                        'bridge.'},
            {'strategy': 'Search every delivered declaration for overlap/spectral/line-shape '
                         'content.',
             'outcome': 'No delivered declaration; only module prose records the non-goal.'},
        ],
        'candidateEvidence': [
            {'kind': 'implication',
             'description': 'Candidate: J = J(stokesShift lam e00), or J as the overlap of two '
                            'declared band shapes. The corpus has no band-shape object, so the '
                            'implication has no deliverable antecedent.'},
        ],
        'remainingGap': 'No line-shape or overlap declaration exists in the frozen statement set; '
                        'J is a free parameter of r0six and the Stokes rows are band maxima. This '
                        'is a scoped negative registration for the requested implication, not a '
                        'claim that no physical relation exists.',
        'recomputeCommands': [
            'grep -rnw "r0six\\|fretRate\\|fretEff6\\|kappaSq" PhotoLean/StokesShift/',
            'grep -rnw "stokesShift\\|absEnergy\\|emEnergy\\|e00" PhotoLean/Forster/',
            'grep -rn "overlap\\|spectral\\|lineshape\\|lineShape" PhotoLean/StokesShift/ PhotoLean/Forster/',
        ],
        'rationale': 'The scoped search is machine-recomputable and finds no statement of the '
                     'requested kind. The candidate remains a physically meaningful but '
                     'undelivered bridge, so the outcome is notEstablished rather than '
                     'outOfScope.',
    },
    {
        'searchId': 'SL-RAD3-SE-01',
        'queryId': 'Q-RAD3-SE-01',
        'pairId': 'P-StokesShift-Einstein',
        'status': 'outOfScope',
        'scope': 'scope-RAD3-jurisdiction',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the Stokes emission energy a transition frequency of the Einstein coefficients?',
        'searchedStatements': [
            'stmt-StokesShift-PhotoLean-StokesShift-emEnergy',
            'stmt-StokesShift-PhotoLean-StokesShift-absEnergy',
            'stmt-StokesShift-PhotoLean-StokesShift-stokesShift',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-aOfB',
            'stmt-Einstein-PhotoLean-Einstein-aOfInt',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'SeSpectralDisjointCtx (candidate: band maxima (lam, e00) beside radiation parameters (h, c, nu))',
            'optical band-maxima context',
            'radiative coefficient context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/StokesShift/Basic.lean', 'locator': 'emEnergy (line 80)',
             'finding': 'emEnergy is the vertical emission energy built from the two surfaces; '
                        'it is a band maximum, not a frequency.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'radFactor (line 45)',
             'finding': 'radFactor h c nu = 8*pi*h*nu^3/c^3: a radiation-density factor over a '
                        'transition frequency.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'aOfInt (line 62)',
             'finding': 'aOfInt Ci I = Ci * I uses an integrated absorption I; there is no '
                        'Stokes counterpart and I is not a band maximum.'},
        ],
        'commands': [
            {'command': 'grep -rnw "radFactor\\|aOfB\\|aOfInt\\|tauR" PhotoLean/StokesShift/',
             'purpose': 'Find any Einstein coefficient inside the Stokes-shift theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rnw "stokesShift\\|absEnergy\\|emEnergy\\|e00" PhotoLean/Einstein/',
             'purpose': 'Find any Stokes descriptor inside the Einstein theory.',
             'result': '(no match; exit 1)'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"StokesShift\",\"Einstein\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('StokesShift', 35), ('Einstein', 33)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Identify the emission energy with h*nu.',
             'outcome': 'No delivered statement connects emEnergy to nu; a translation would '
                        'have to be declared, not assumed.'},
            {'strategy': 'Identify the integrated absorption I of aOfInt with absEnergy.',
             'outcome': 'Rejected as a category error: I is an integrated absorption, absEnergy '
                        'a band maximum.'},
            {'strategy': 'Look for a delivered statement equating a surface coordinate with a '
                         'transition frequency.',
             'outcome': 'None.'},
        ],
        'candidateEvidence': [
            {'kind': 'implication',
             'description': 'A would-be evaluation of radFactor at nu = emEnergy/h; no delivered '
                            'premise supports the substitution.'},
        ],
        'remainingGap': 'No shared descriptor: StokesShift quantifies band maxima, Einstein '
                        'quantifies radiative coefficients over a transition frequency. The '
                        'jurisdiction record denies the translation; it does not claim the '
                        'emission is non-radiative.',
        'recomputeCommands': [
            'grep -rnw "radFactor\\|aOfB\\|aOfInt\\|tauR" PhotoLean/StokesShift/',
            'grep -rnw "stokesShift\\|absEnergy\\|emEnergy\\|e00" PhotoLean/Einstein/',
        ],
        'rationale': 'The scoped search finds no bridge between a band maximum and a transition '
                     'frequency. The outcome is jurisdictional, not a refutation.',
    },
    {
        'searchId': 'SL-RAD3-IF-01',
        'queryId': 'Q-RAD3-IF-01',
        'pairId': 'P-ICvsISC-Forster',
        'status': 'unresolved',
        'scope': 'scope-RAD3-scoped-search',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the Forster transfer channel a third channel in the IC-vs-ISC competition?',
        'searchedStatements': [
            'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
            'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
            'stmt-ICvsISC-PhotoLean-ICvsISC-isc_dominates_iff',
            'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
            'stmt-Forster-PhotoLean-Forster-fretRate',
            'stmt-Forster-PhotoLean-Forster-fretEff6',
            'stmt-Forster-PhotoLean-Forster-r0six',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'IfThirdChannelCandidateCtx (candidate: two IC/ISC channels plus a Forster channel (tauD, r6, R))',
            'IC-vs-ISC competition context',
            'donor-acceptor transfer context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/ICvsISC/Criterion.lean',
             'locator': 'isc_dominates_iff (line 124)',
             'finding': 'The delivered crossover compares exactly two channels, icRate and '
                        'iscRate; no third channel and no total decay appear.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'fretRate (line 54)',
             'finding': 'The Forster rate is (1/tauD)*(r6/R^6); the donor lifetime tauD and the '
                        'separation R have no ICvsISC counterpart.'},
            {'artifact': 'PhotoLean/ICvsISC/Basic.lean', 'locator': 'FCData (line 91)',
             'finding': 'The premise bundle carries prefactors, reorganization energies and the '
                        'thermal energy; no lifetime or separation occurs.'},
        ],
        'commands': [
            {'command': 'grep -rnw "fretRate\\|fretEff6\\|r0six\\|kappaSq\\|tauD" PhotoLean/ICvsISC/',
             'purpose': 'Find any Forster descriptor inside the IC-vs-ISC theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rnw "icRate\\|iscRate\\|fcBarrier\\|HSO\\|FCData" PhotoLean/Forster/',
             'purpose': 'Find any IC/ISC descriptor inside the Forster theory.',
             'result': '(no match; exit 1)'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"ICvsISC\",\"Forster\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('ICvsISC', 19), ('Forster', 32)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Add the transfer rate to the IC denominator of isc_dominates_iff.',
             'outcome': 'No delivered statement defines a total or a three-channel competition; '
                        'isc_dominates_iff has exactly two channels.'},
            {'strategy': 'Identify the donor decay rate 1/tauD with the IC rate.',
             'outcome': 'Not delivered; no statement equates them.'},
            {'strategy': 'Compose the delivered crossover with a Forster parent.',
             'outcome': 'No typed parent exists: the Forster module has no dominance predicate.'},
        ],
        'candidateEvidence': [
            {'kind': 'conditionalComposition',
             'description': 'Candidate: isc_dominates_iff with icRate replaced by '
                            'icRate + fretRate. Missing: a delivered bridge that the donor decay '
                            'rate is the IC channel rate and that the transfer channel adds to '
                            'the IC channel.'},
        ],
        'remainingGap': 'The composition needs two delivered bridges (1/tauD = icRate and the '
                        'transfer channel added to the IC channel); the corpus states neither, '
                        'and the legacy register records no shared scalar. The candidate remains '
                        'open.',
        'recomputeCommands': [
            'grep -rnw "fretRate\\|fretEff6\\|r0six\\|kappaSq\\|tauD" PhotoLean/ICvsISC/',
            'grep -rnw "icRate\\|iscRate\\|fcBarrier\\|HSO\\|FCData" PhotoLean/Forster/',
        ],
        'rationale': 'The candidate is chemically meaningful (a third decay channel) but not '
                     'delivered; the record names the exact missing bridges and makes no negative '
                     'claim.',
    },
    {
        'searchId': 'SL-RAD3-IE-01',
        'queryId': 'Q-RAD3-IE-01',
        'pairId': 'P-ICvsISC-Einstein',
        'status': 'outOfScope',
        'scope': 'scope-RAD3-jurisdiction',
        'snapshot': SNAP,
        'chemicalQuestion': 'Is the spin-orbit ISC channel a radiative Einstein coefficient?',
        'searchedStatements': [
            'stmt-ICvsISC-PhotoLean-ICvsISC-iscRate',
            'stmt-ICvsISC-PhotoLean-ICvsISC-icRate',
            'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
            'stmt-Einstein-PhotoLean-Einstein-aOfB',
            'stmt-Einstein-PhotoLean-Einstein-b12OfB21',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'IeSpinRadDisjointCtx (candidate: spin-orbit channel (HSO, AS, lamS, xS) beside coefficient algebra (g1, g2, B21))',
            'nonradiative spin-forbidden channel context',
            'radiative detailed-balance context',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/ICvsISC/Basic.lean', 'locator': 'iscRate (line 85)',
             'finding': 'iscRate HSO AS lamS kB T xS = HSO^2 * AS * '
                        'exp(-fcBarrier(lamS,xS)/(kB*T)): a spin-orbit prefactor over a nuclear '
                        'Franck-Condon barrier.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'aOfB (line 49)',
             'finding': 'aOfB K B21 = K * B21: a radiative coefficient over a radiation-density '
                        'factor.'},
            {'artifact': 'PhotoLean/ICvsISC/Criterion.lean', 'locator': 'spin_discount (line 164)',
             'finding': 'The spin-orbit factor is a nonradiative threshold (log HSO); it is not '
                        'a radiative coefficient.'},
        ],
        'commands': [
            {'command': 'grep -rnw "radFactor\\|aOfB\\|b12OfB21\\|tauR\\|degeneracy" PhotoLean/ICvsISC/',
             'purpose': 'Find any Einstein coefficient inside the IC-vs-ISC theory.',
             'result': '(no match; exit 1)'},
            {'command': 'grep -rnw "icRate\\|iscRate\\|fcBarrier\\|HSO\\|FCData" PhotoLean/Einstein/',
             'purpose': 'Find any IC/ISC descriptor inside the Einstein theory.',
             'result': '(no match; exit 1)'},
            {'command': "python3 -c 'import json; inv=json.load(open(\"audit_boundary/statement-inventory.json\")); print([(t, sum(1 for s in inv[\"statements\"] if s[\"theory\"]==t and s[\"screeningEligible\"])) for t in [\"ICvsISC\",\"Einstein\"]])'",
             'purpose': 'Count the eligible statements searched on both sides.',
             'result': "[('ICvsISC', 19), ('Einstein', 33)]"},
        ],
        'strategiesAttempted': [
            {'strategy': 'Identify HSO^2*AS with aOfB or with radFactor*B21.',
             'outcome': 'No delivered statement; the spin-orbit amplitude is not a '
                        'radiation-density factor.'},
            {'strategy': 'Identify the nuclear ISC barrier with an Einstein transition energy.',
             'outcome': 'No delivered statement; a reorganization barrier is not a photon '
                        'energy.'},
            {'strategy': 'Look for a delivered total-decay or radiative-yield row in ICvsISC.',
             'outcome': 'None; ICvsISC has no yield, total or radiative channel.'},
        ],
        'candidateEvidence': [
            {'kind': 'implication',
             'description': 'A would-be identification of the spin-orbit ISC prefactor with a '
                            'radiative coefficient; no delivered premise supports it.'},
        ],
        'remainingGap': 'No shared descriptor: the ISC channel is a nonradiative spin-forbidden '
                        'crossing with a nuclear barrier, the Einstein coefficients describe '
                        'radiative detailed balance. The jurisdiction record denies the '
                        'translation; it does not claim the two channels cannot coexist.',
        'recomputeCommands': [
            'grep -rnw "radFactor\\|aOfB\\|b12OfB21\\|tauR\\|degeneracy" PhotoLean/ICvsISC/',
            'grep -rnw "icRate\\|iscRate\\|fcBarrier\\|HSO\\|FCData" PhotoLean/Einstein/',
        ],
        'rationale': 'The scoped search finds no bridge between a spin-orbit channel strength and '
                     'a radiative coefficient. The outcome is jurisdictional, not a refutation.',
    },
]


def build_search_log():
    status_counts = {}
    for entry in SEARCH_ENTRIES:
        status_counts[entry['status']] = status_counts.get(entry['status'], 0) + 1
    return {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': WORK_PACKAGE,
        'snapshot': SNAP,
        'description': ('Scoped search and jurisdiction records for the six non-certified '
                        'queries of the RAD3 package; each record is recomputable with the '
                        'listed commands.'),
        'entries': SEARCH_ENTRIES,
        'counts': {
            'entries': len(SEARCH_ENTRIES),
            'byStatus': status_counts,
        },
        'nonClaims': [
            'A search record is scoped to the named statements, kinds and contexts; it is not a completeness claim.',
            'A missing certificate is not a refutation.',
            'An outOfScope record denies a declared translation; it does not assert logical non-existence.',
            'The legacy registry is read-only and its pair labels are census metadata, not audit verdicts.',
        ],
    }


def build_fragment(screening_sha, screening_counts, pairs):
    prior_pairs = set()
    for rel in PRIOR_PACKAGES:
        pkg = load_rel(rel)
        prior_pairs |= {row['pairId'] for row in pkg['pairs']}
    return {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': 'R5',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': WORK_PACKAGE,
            'path': SCREENING_REL,
            'pairCount': len(PAIR_IDS),
            'sha256': screening_sha,
        },
        'packageState': 'submitted-R5-pending-review',
        'primaryCluster': 'radiative-energy-transfer',
        'universe': {
            'pairCount': len(QUEUE['pairs']),
            'source': QUEUE_REL,
            'sourceSha256': sha_rel(QUEUE_REL),
        },
        'pairs': [
            {
                'pairId': row['pairId'],
                'theories': row['theories'],
                'primaryCluster': row['primaryCluster'],
                'queryCount': len(row['queries']),
                'byStatus': _status_counts(row['queries']),
            }
            for row in pairs
        ],
        'counts': {
            'pairs': screening_counts['pairs'],
            'queries': screening_counts['queries'],
            'byStatus': screening_counts['byStatus'],
            'screenedDelta': len(PAIR_IDS),
        },
        'overlapWithAccepted': {
            'derivedFrom': list(PRIOR_PACKAGES),
            'acceptedScreenedPairCount': len(prior_pairs),
            'intersection': sorted(set(PAIR_IDS) & prior_pairs),
        },
        'nonClaims': [
            'This fragment is an immutable submission snapshot, not the cumulative R5 ledger.',
            'It lists only the thirteen RAD3 pairs and makes no claim about the other 123 pairs.',
            'It does not pin or hash the mutable R5 cumulative ledger.',
        ],
    }


def _status_counts(queries):
    counts = {}
    for q in queries:
        status = q['outcome']['status']
        counts[status] = counts.get(status, 0) + 1
    return counts


def write_json(rel, data):
    path = os.path.join(ROOT, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)
        fh.write('\n')
    return path


def main():
    search_log = build_search_log()
    write_json(SEARCH_REL, search_log)

    screening = build_screening()
    write_json(SCREENING_REL, screening)
    screening_sha = sha_rel(SCREENING_REL)

    fragment = build_fragment(screening_sha, screening['counts'], screening['pairs'])
    write_json(FRAGMENT_REL, fragment)

    print('wrote %s' % SCREENING_REL)
    print('wrote %s' % SEARCH_REL)
    print('wrote %s' % FRAGMENT_REL)
    print('screening sha256: %s' % screening_sha)
    print('search-log sha256: %s' % sha_rel(SEARCH_REL))
    print('fragment sha256: %s' % sha_rel(FRAGMENT_REL))
    print('pairs: %d queries: %d' % (screening['counts']['pairs'],
                                     screening['counts']['queries']))
    print('byStatus: %r' % (screening['counts']['byStatus'],))


if __name__ == '__main__':
    main()
