#!/usr/bin/env python3
"""Build the R2 WP-SURFACE-01 screening package.

The script is deterministic: it reads the frozen R1 inventory and the accepted
legacy registry, embeds the fixed query specifications, and writes
``screening.json`` and ``search-log.json`` next to itself.  The acceptance gate is
``validate_screening.py``; this builder is kept only for reproducibility.
"""

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
PROBE_REL = 'bounded_audit/wp-surface-01/probes/Surface-probe.lean'
SCREENING_REL = 'bounded_audit/wp-surface-01/screening.json'

inv = load(INV_REL)
queue = load(QUEUE_REL)
cluster = load(CLUSTER_REL)
registry = load(REGISTRY_REL)

INV_BY_ID = {row['id']: row for row in inv['statements']}
REG_CERTS = {c['id']: c for c in registry['certificates']}
QUEUE_BY_ID = {row['pairId']: row for row in queue['pairs']}

SNAPSHOT_ID = 'snap-bounded-audit-2026-11-04'
SNAPSHOT = {
    'id': SNAPSHOT_ID,
    'date': '2026-11-04',
    'round': 'R2',
    'inventory': INV_REL,
    'inventorySha256': sha_file(os.path.join(ROOT, INV_REL)),
    'pairQueue': QUEUE_REL,
    'pairQueueSha256': sha_file(os.path.join(ROOT, QUEUE_REL)),
    'clusterPlan': CLUSTER_REL,
    'clusterPlanSha256': sha_file(os.path.join(ROOT, CLUSTER_REL)),
    'boundary': BOUNDARY_REL,
    'boundarySha256': sha_file(os.path.join(ROOT, BOUNDARY_REL)),
    'legacyRegistry': REGISTRY_REL,
    'legacyRegistrySha256': sha_file(os.path.join(ROOT, REGISTRY_REL)),
    'leanToolchain': 'leanprover/lean4:v4.17.0',
    'deliveredLeanFileCount': 102,
}

PAIRS = [
    'P-Marcus-Hammond',
    'P-Marcus-BEP',
    'P-Marcus-Sabatier',
    'P-Hammond-BEP',
    'P-Hammond-Sabatier',
    'P-Hammond-SymmetryFactor',
    'P-BEP-Sabatier',
    'P-BEP-SymmetryFactor',
    'P-Kasha-Sabatier',
    'P-Sabatier-SymmetryFactor',
]

CONTEXTS = {
    'TwoParabolaCtx': {
        'fields': ['lam : ℝ', 'x : ℝ'],
        'physicalReading': 'Equal-curvature two-parabola step: reorganization energy lam and '
                           'driving force x = -ΔG°. The transition state is at q = (lam - x)/(2 lam).',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#TwoParabolaCtx',
    },
    'BarrierCtx': {
        'fields': ['lam : ℝ', 'x : ℝ'],
        'physicalReading': 'The R1 pilot context for the Marcus/Hammond/BEP barrier family: '
                           'curvature lam and driving force x.',
        'provenance': 'PhotoLean/RelationAudit/Pilot.lean#BarrierCtx',
    },
    'SecantCtx': {
        'fields': ['lam : ℝ', 'x1 : ℝ', 'x2 : ℝ'],
        'physicalReading': 'Two driving forces x1 and x2 on the same equal-curvature barrier; '
                           'the Leffler secant is the finite-difference Brønsted coefficient.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#SecantCtx',
    },
    'RatCtx': {
        'fields': ['lam : ℚ', 'x : ℚ'],
        'physicalReading': 'Exact-rational copy of the two-parabola context, used for the '
                           'decidable zone classifiers.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#RatCtx',
    },
    'HammondMarcusSharpCtx': {
        'fields': ['A : ℝ', 'kB : ℝ', 'T : ℝ', 'lam : ℝ'],
        'physicalReading': 'Marcus rate parameters (pre-exponential A, Boltzmann constant kB, '
                           'temperature T) together with the curvature lam.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections06_10.lean#HammondMarcusSharpCtx',
    },
    'RateCtx': {
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': 'Marcus/BEP rate context: pre-exponential factor, curvature, thermal '
                           'energy and driving force.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#RateCtx',
    },
    'RateActivityCtx': {
        'fields': ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
        'physicalReading': 'Shared Arrhenius context of the Marcus rate and the Sabatier '
                           'activity functional of the same two-parabola barrier.',
        'provenance': 'bounded_audit/wp-surface-01/probes/Surface-probe.lean#RateActivityCtx',
    },
    'TransferCtx': {
        'fields': ['lam : ℝ'],
        'physicalReading': 'Curvature of the step; the driving force is the observation-channel '
                           'input, so the transfer coefficient and the transition-state '
                           'coordinate are compared at every x.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#TransferCtx',
    },
    'SlopeCtx': {
        'fields': ['lam : ℝ'],
        'physicalReading': 'Curvature of the step; the driving-force window (x, h) is the '
                           'observation-channel input.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#SlopeCtx',
    },
    'WindowCtx': {
        'fields': ['lam : ℝ', 'tol : ℝ', 'a : ℝ', 'b : ℝ'],
        'physicalReading': 'BEP conformance window: curvature, tolerance, and the two window '
                           'endpoints in driving force.',
        'provenance': 'PhotoLean/RelationAudit/Full/Sections01_05.lean#WindowCtx',
    },
    'SymFactorHammondCtx': {
        'fields': ['lam : ℝ'],
        'physicalReading': 'Equal-curvature diagonal of the SymmetryFactor model, identified '
                           'with the Hammond/Marcus kernel curvature lam.',
        'provenance': 'bounded_audit/wp-surface-01/probes/Surface-probe.lean#SymFactorHammondCtx',
    },
    'SymFactorBepCtx': {
        'fields': ['lam : ℝ'],
        'physicalReading': 'Equal-curvature diagonal of the SymmetryFactor model, identified '
                           'with the BEP kernel curvature lam.',
        'provenance': 'bounded_audit/wp-surface-01/probes/Surface-probe.lean#SymFactorBepCtx',
    },
    'BepSabatierCtx': {
        'fields': ['lam1 : ℝ', 'lam2 : ℝ'],
        'physicalReading': 'Two branch curvatures of the two-parabola volcano; the descriptor '
                           'dE is the observation-channel input.',
        'provenance': 'bounded_audit/wp-surface-01/probes/Surface-probe.lean#BepSabatierCtx',
    },
    'HammondSabatierCandidateCtx': {
        'fields': ['lam : ℝ', 'x : ℝ'],
        'physicalReading': 'Candidate shared context: the Hammond curvature/driving-force pair, '
                           'with the Sabatier descriptor profile instantiated on the Hammond '
                           'barrier. The translation is a candidate only; no delivered '
                           'statement-level bridge realizes it.',
        'provenance': 'candidate context declared in this R2 package',
        'translationStatus': 'candidate-not-total',
    },
    'KashaSabatierCandidateCtx': {
        'fields': ['x : ℝ', 'A : ℝ', 'kB : ℝ', 'T : ℝ'],
        'physicalReading': 'Candidate shared context: the Kasha energy gap/Marcus rate '
                           'parameters, with the Sabatier descriptor axis read as the same gap. '
                           'The translation is a candidate only; the two theories declare '
                           'different target quantities (ladder yield vs volcano barrier).',
        'provenance': 'candidate context declared in this R2 package',
        'translationStatus': 'candidate-not-total',
    },
    'SabatierSymmetryCandidateCtx': {
        'fields': ['lam1 : ℝ', 'lam2 : ℝ'],
        'physicalReading': 'Candidate shared context: the two branch curvatures, read both as '
                           'Sabatier descriptor-axis parameters and as SymmetryFactor force '
                           'constants. The translation is a candidate only; the descriptor axis '
                           'and the reaction coordinate are different physical coordinates.',
        'provenance': 'candidate context declared in this R2 package',
        'translationStatus': 'candidate-not-total',
    },
}

SCOPES = {
    'scope-WPS01-two-parabola': {
        'description': 'Global equal-curvature two-parabola scope of the Marcus/Hammond/BEP '
                       'barrier family.',
        'domain': 'all (lam, x) in ℝ²; a premise may restrict to 0 < lam.',
    },
    'scope-WPS01-secant': {
        'description': 'Global Leffler-secant scope over two distinct driving forces.',
        'domain': 'all (lam, x1, x2) in ℝ³ with 0 < lam and x1 ≠ x2 where the premise requires it.',
    },
    'scope-WPS01-rational': {
        'description': 'Exact-rational classifier scope.',
        'domain': 'all (lam, x) in ℚ² with 0 < lam where the premise requires it.',
    },
    'scope-WPS01-sharp': {
        'description': 'Global sharp-descriptor scope under positive rate parameters.',
        'domain': 'all (A, kB, T, lam) in ℝ⁴ with 0 < A, 0 < kB, 0 < T.',
    },
    'scope-WPS01-rate': {
        'description': 'Global Marcus/BEP rate-law scope.',
        'domain': 'all (A, lam, kB, T, x) in ℝ⁵.',
    },
    'scope-WPS01-transfer': {
        'description': 'BEP transfer/Hammond coordinate scope at nonzero curvature.',
        'domain': 'all lam ≠ 0 and all driving forces x.',
    },
    'scope-WPS01-slope': {
        'description': 'BEP observable-slope / Hammond Leffler-secant scope.',
        'domain': 'all lam and all driving-force windows (x, h) in ℝ².',
    },
    'scope-WPS01-window': {
        'description': 'BEP window-conformance scope.',
        'domain': 'all (lam, tol, a, b) in ℝ⁴.',
    },
    'scope-WPS01-equal-curvature': {
        'description': 'Equal-curvature diagonal of the SymmetryFactor model.',
        'domain': 'all lam > 0 on the diagonal kr = kp = lam.',
    },
    'scope-WPS01-descriptor-axis': {
        'description': 'Sabatier descriptor-axis scope over the branch curvatures.',
        'domain': 'all (lam1, lam2, dE) in ℝ³.',
    },
    'scope-WPS01-candidate-bridge': {
        'description': 'Candidate bridge scope for a comparison whose translation is not '
                       'declared by the delivered theories.',
        'domain': 'candidate contexts only; no total delivered translation.',
    },
}

TRUE_PREMISE = {}
POS_LAM_PREMISE = {}


def premise(predicate, ids, definitions):
    return {'predicate': predicate, 'premiseIds': ids, 'definitions': definitions}


def tprem(ctx):
    return premise('fun _ : %s => True' % ctx, [], [])


def pos_lam(ctx, pid='marcus.curvaturePositive', text='The curvature is positive.'):
    return premise('fun δ : %s => 0 < δ.lam' % ctx, [pid],
                   [{'id': pid, 'predicate': 'fun δ : %s => 0 < δ.lam' % ctx,
                     'statement': text, 'loadBearing': 'Keeps the two totalized divisions '
                                                      'and the sign comparison meaningful.'}])


def endpoint(stmt_id, form, note=None):
    row = INV_BY_ID[stmt_id]
    out = {
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
    if note:
        out['endpointNote'] = note
    return out


def translation(ctx, tid='identity', term=None, requirement=None):
    if term is None:
        term = 'fun δ : %s => δ' % ctx
    return {
        'id': tid,
        'term': term,
        'requirement': requirement or 'Both statement contexts are the shared context; the '
                                     'translation is total on the declared domain.',
    }


def identity_translations(ctx):
    return {'left': translation(ctx), 'right': translation(ctx)}


def no_translations(reason):
    return {
        'left': {'id': 'none-declared', 'term': None, 'reason': reason,
                 'requirement': 'A total translation into the left statement context is '
                                'not declared by the delivered theories.'},
        'right': {'id': 'none-declared', 'term': None, 'reason': reason,
                  'requirement': 'A total translation into the right statement context is '
                                 'not declared by the delivered theories.'},
    }


def legacy_evidence(cert_id, reuse_note=None):
    cert = REG_CERTS[cert_id]
    ev = {
        'type': 'legacy-certificate',
        'certificateId': cert_id,
        'kind': cert['kind'],
        'lean': {
            'declaration': cert['lean'],
            'module': cert['module'],
            'constructor': cert['constructor'],
            'kindFunction': cert['kindFunction'],
            'kindCheck': 'example : certificateKind %s = RelationKind.%s := rfl'
                         % (cert['lean'], cert['kind']),
        },
        'source': {'path': cert['sourcePath'], 'sha256': cert['sourceSha256']},
        'axiomFootprint': cert['axiomFootprint'],
        'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'reuseAudit': {
            'declarationExistsInDeliveredSource': True,
            'sourceHashMatchesAcceptedRegistry': True,
            'axiomAuditLog': 'bounded_audit/wp-surface-01/evidence/legacy-axioms.log',
            'axiomAuditResult': 'PASS (only propext, Classical.choice, Quot.sound)',
        },
    }
    if reuse_note:
        ev['reuseAudit']['endpointNote'] = reuse_note
    return ev


def probe_evidence(decl, kind, theorems, note):
    return {
        'type': 'r2-probe-certificate',
        'certificateId': 'QP-' + decl.rsplit('.', 1)[-1],
        'kind': kind,
        'probe': {
            'path': PROBE_REL,
            'sha256': sha_file(os.path.join(ROOT, PROBE_REL)),
            'declaration': 'PhotoLean.RelationAudit.BoundedAudit.Surface.' + decl,
            'kindCheckTheorem': 'PhotoLean.RelationAudit.BoundedAudit.Surface.' + decl + '_kind',
            'buildCommand': 'proofs/scripts/lake env lean ' + PROBE_REL,
            'log': 'bounded_audit/wp-surface-01/evidence/surface-probe.log',
        },
        'underlyingTheorems': theorems,
        'axiomFootprint': ['propext', 'Classical.choice', 'Quot.sound'],
        'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'justification': note,
    }


def certified(qid, pair, title, question, rationale, src, tgt, ctx, scope, kind,
              kind_rationale, falsification, premises, evidence, channels=None,
              translations=None, provenance_extra=None):
    q = {
        'queryId': qid,
        'pairId': pair,
        'title': title,
        'chemicalQuestion': question,
        'chemicalRationale': rationale,
        'endpoints': {'source': src, 'target': tgt},
        'sharedContext': dict(CONTEXTS[ctx], id=ctx),
        'translations': translations or identity_translations(ctx),
        'premises': premises,
        'observationChannels': channels or [],
        'scope': dict(SCOPES[scope], id=scope, snapshot=SNAPSHOT_ID),
        'expectedKind': kind,
        'expectedKindRationale': kind_rationale,
        'falsificationCondition': falsification,
        'outcome': {
            'status': 'certified',
            'rationale': 'The query is answered by the checked certificate of the declared kind.',
            'evidence': evidence,
        },
        'provenance': {
            'kind': evidence['type'],
            'certificateId': evidence.get('certificateId'),
            'sourceArtifact': PROBE_REL if evidence['type'] == 'r2-probe-certificate'
                              else evidence['source']['path'],
            'locator': evidence.get('lean', {}).get('declaration')
                       or evidence.get('probe', {}).get('declaration'),
        },
    }
    if provenance_extra:
        q['provenance'].update(provenance_extra)
    return q


def unresolved(qid, pair, title, question, rationale, src, tgt, ctx, scope, kind,
               kind_rationale, falsification, premises, search_ref, candidate_summary,
               translations=None):
    return {
        'queryId': qid,
        'pairId': pair,
        'title': title,
        'chemicalQuestion': question,
        'chemicalRationale': rationale,
        'endpoints': {'source': src, 'target': tgt},
        'sharedContext': dict(CONTEXTS[ctx], id=ctx),
        'translations': translations or no_translations(
            'No delivered total translation exists for this comparison; see the search log.'),
        'premises': premises,
        'observationChannels': [],
        'scope': dict(SCOPES[scope], id=scope, snapshot=SNAPSHOT_ID),
        'expectedKind': kind,
        'expectedKindRationale': kind_rationale,
        'falsificationCondition': falsification,
        'outcome': {
            'status': 'unresolved',
            'rationale': 'A candidate bridge was identified, but no certificate of the '
                         'requested kind has been constructed or checked in this snapshot.',
            'evidence': {'type': 'scoped-search', 'searchLogRef': search_ref,
                         'candidateSummary': candidate_summary},
        },
        'provenance': {
            'kind': 'scoped-search',
            'searchLogRef': search_ref,
            'sourceArtifact': 'bounded_audit/wp-surface-01/search-log.json',
            'locator': search_ref,
        },
    }


queries = []

# ---------------------------------------------------------------- P-Marcus-Hammond
queries.append(certified(
    'Q-WPS01-MH-01', 'P-Marcus-Hammond',
    'Marcus barrier is the Hammond forward reactant gap',
    'Is the Marcus forward barrier the same physical barrier height as the Hammond forward '
    'reactant gap at the same curvature and driving force?',
    'Both theories read the crossing of the same equal-curvature two-parabola model. The '
    'definitional identity is what licenses comparing their reported activation energies '
    'directly; it is not merely a notation match, because the two definitions have independent '
    'provenance in their theory modules.',
    endpoint('marcus.barrier', 'definition'),
    endpoint('stmt-Hammond-PhotoLean-Hammond-gapReactant', 'definition'),
    'TwoParabolaCtx', 'scope-WPS01-two-parabola', 'definitionalIdentity',
    'A kernel rfl pin: the two translated real-valued terms are definitionally equal.',
    'A context (lam, x) at which the two translated barrier values differ would refute the '
    'definitional identity.',
    tprem('TwoParabolaCtx'),
    legacy_evidence('cert-D-S05-hammond-barrier-eq-gapReactant',
                    'Definitional pin over the delivered Marcus.barrier and Hammond.gapReactant.'),
    provenance_extra={'legacyQueryId': 'q-D-S05-hammond-barrier-eq-gapReactant',
                      'legacyRecordId': 'rec-D-S05-hammond-barrier-eq-gapReactant'},
))

queries.append(certified(
    'Q-WPS01-MH-02', 'P-Marcus-Hammond',
    'Negative Hammond transition-state coordinate iff Marcus inverted region',
    'Does a negative Hammond transition-state coordinate exactly mark the Marcus inverted '
    'region at the same curvature and driving force?',
    'The transition-state coordinate q‡ = (lam - x)/(2 lam) changes sign exactly when the '
    'driving force passes the reorganization energy. That is the Marcus inverted-region '
    'boundary, so the equivalence is the structural reading of the inverted region.',
    endpoint('stmt-Hammond-PhotoLean-Hammond-tsCoord', 'definition'),
    endpoint('stmt-Marcus-PhotoLean-Marcus-InvertedRegion', 'definition'),
    'TwoParabolaCtx', 'scope-WPS01-two-parabola', 'equivalence',
    'A genuine iff between the sign predicate on the structural coordinate and the Marcus '
    'inverted-region predicate.',
    'A context with 0 < lam where exactly one side holds would refute the equivalence.',
    pos_lam('TwoParabolaCtx'),
    legacy_evidence('cert-D-S02-tsCoord-lt-zero-iff-inverted'),
    provenance_extra={'legacyQueryId': 'q-D-S02-tsCoord-lt-zero-iff-inverted',
                      'legacyRecordId': 'rec-D-S02-tsCoord-lt-zero-iff-inverted'},
))

queries.append(certified(
    'Q-WPS01-MH-03', 'P-Marcus-Hammond',
    'Negative Leffler secant iff Marcus inverted region at the midpoint',
    'Is a negative Hammond Leffler secant — the Brønsted coefficient measured from barrier '
    'data over two driving forces — exactly the Marcus inverted region at the secant midpoint?',
    'The Leffler secant is an observable Brønsted slope obtained from barrier differences, '
    'while the Marcus inverted region is a statement about the driving force relative to the '
    'reorganization energy. The equivalence connects the measured slope sign to the '
    'inverted-region classification at the midpoint of the two driving forces.',
    endpoint('stmt-Hammond-PhotoLean-Hammond-lefflerSecant', 'definition'),
    endpoint('stmt-Marcus-PhotoLean-Marcus-InvertedRegion', 'definition'),
    'SecantCtx', 'scope-WPS01-secant', 'equivalence',
    'A genuine iff between the secant-sign predicate and the midpoint inverted-region '
    'predicate.',
    'A context with 0 < lam and x1 ≠ x2 where exactly one side holds would refute the '
    'equivalence.',
    premise('fun δ : SecantCtx => 0 < δ.lam ∧ δ.x1 ≠ δ.x2',
            ['marcus.curvaturePositive', 'hammond.distinctDrivingForces'],
            [
                {'id': 'marcus.curvaturePositive',
                 'predicate': 'fun δ : SecantCtx => 0 < δ.lam',
                 'statement': 'The curvature is positive.',
                 'loadBearing': 'Keeps the totalized division and the sign comparison '
                                'meaningful.'},
                {'id': 'hammond.distinctDrivingForces',
                 'predicate': 'fun δ : SecantCtx => δ.x1 ≠ δ.x2',
                 'statement': 'The two driving forces are distinct.',
                 'loadBearing': 'The secant denominator is x2 - x1; without it the observable '
                                'is not defined.'},
            ]),
    legacy_evidence('cert-D-S02-lefflerSecant-neg-iff-inverted'),
    provenance_extra={'legacyQueryId': 'q-D-S02-lefflerSecant-neg-iff-inverted',
                      'legacyRecordId': 'rec-D-S02-lefflerSecant-neg-iff-inverted'},
))

queries.append(certified(
    'Q-WPS01-MH-04', 'P-Marcus-Hammond',
    'Rational Hammond and Marcus zone classifiers agree',
    'Do the rational Hammond deep-exergonic classifier and the rational Marcus inverted-zone '
    'classifier select exactly the same instances?',
    'The two theories implement decidable zone classifiers over ℚ. The equivalence says the '
    'Hammond beyond-reactant branch is exactly the Marcus inverted zone, so the two '
    'implementations make the same chemical classification in the exact-rational fragment.',
    endpoint('stmt-Hammond-PhotoLean-Hammond-Rat-hammondZoneQ', 'definition'),
    endpoint('stmt-Marcus-PhotoLean-Marcus-Rat-zoneQ', 'definition'),
    'RatCtx', 'scope-WPS01-rational', 'equivalence',
    'A genuine iff between two decidable classifier equalities over ℚ.',
    'A rational context with 0 < lam where exactly one classifier equality holds would refute '
    'the equivalence.',
    premise('fun δ : RatCtx => 0 < δ.lam', ['marcus.curvaturePositive'],
            [{'id': 'marcus.curvaturePositive',
              'predicate': 'fun δ : RatCtx => 0 < δ.lam',
              'statement': 'The rational curvature is positive.',
              'loadBearing': 'The delivered classifier equivalence is stated under this '
                             'premise.'}]),
    legacy_evidence('cert-D-S02-hammondZoneQ-beyondReactant-iff-inverted'),
    provenance_extra={'legacyQueryId': 'q-D-S02-hammondZoneQ-beyondReactant-iff-inverted',
                      'legacyRecordId': 'rec-D-S02-hammondZoneQ-beyondReactant-iff-inverted'},
))

queries.append(certified(
    'Q-WPS01-MH-05', 'P-Marcus-Hammond',
    'Hammond structural descriptor and Marcus rate descriptor are co-extensive',
    'Are the Hammond structural descriptor and the Marcus rate descriptor — everywhere-positive '
    'rate plus the inverted-region description — co-extensive under positive rate parameters?',
    'Both descriptors characterise the positive-curvature two-parabola model, but they are not '
    'restatements: one is structural (transition-state coordinate monotonicity), the other is '
    'rate-level (positivity plus inverted-region monotonicity). The equivalence is the '
    'co-extensiveness of the two sharp characterisations.',
    endpoint('stmt-Hammond-PhotoLean-Hammond-HammondDescriptor', 'definition'),
    endpoint('stmt-Marcus-PhotoLean-Marcus-descriptor_sharp', 'theorem-lhs-predicate',
             'The certificate right predicate is the left-hand conjunctive predicate of '
             'Marcus.descriptor_sharp. Legacy statementId PhotoLean.Marcus.rateDescriptor is a '
             'synthetic alias, resolved here to the real theorem statement; see '
             'aliasResolutions[AL-WPS01-02].'),
    'HammondMarcusSharpCtx', 'scope-WPS01-sharp', 'equivalence',
    'A genuine iff under the three positivity premises: the structural descriptor holds exactly '
    'when the rate is everywhere positive and the inverted-region description holds.',
    'A context with 0 < A, 0 < kB, 0 < T where exactly one side holds would refute the '
    'equivalence.',
    premise('fun δ : HammondMarcusSharpCtx => 0 < δ.A ∧ 0 < δ.kB ∧ 0 < δ.T',
            ['hammondMarcusSharp.preExponentialPositive',
             'hammondMarcusSharp.boltzmannPositive',
             'hammondMarcusSharp.temperaturePositive'],
            [
                {'id': 'hammondMarcusSharp.preExponentialPositive',
                 'predicate': 'fun δ : HammondMarcusSharpCtx => 0 < δ.A',
                 'statement': 'The Marcus pre-exponential factor is positive.',
                 'loadBearing': 'The sharp equivalence fails on the negative-prefactor branch.'},
                {'id': 'hammondMarcusSharp.boltzmannPositive',
                 'predicate': 'fun δ : HammondMarcusSharpCtx => 0 < δ.kB',
                 'statement': 'The Boltzmann constant is positive.',
                 'loadBearing': 'The rate ordering is read through the sign of kB*T.'},
                {'id': 'hammondMarcusSharp.temperaturePositive',
                 'predicate': 'fun δ : HammondMarcusSharpCtx => 0 < δ.T',
                 'statement': 'The temperature is positive.',
                 'loadBearing': 'The rate ordering is read through the sign of kB*T.'},
            ]),
    legacy_evidence('cert-D-S06-hammond-sharp-iff-marcus-sharp',
                    'The certificate metadata names PhotoLean.Marcus.rateDescriptor; the real '
                    'declaration is Marcus.descriptor_sharp, whose LHS is the right predicate. '
                    'The alias is repaired in this screening layer only.'),
    provenance_extra={'legacyQueryId': 'q-D-S06-hammond-sharp-iff-marcus-sharp',
                      'legacyRecordId': 'rec-D-S06-hammond-sharp-iff-marcus-sharp',
                      'aliasResolutionIds': ['AL-WPS01-02']},
))

# ---------------------------------------------------------------- P-Marcus-BEP
queries.append(certified(
    'Q-WPS01-MB-01', 'P-Marcus-BEP',
    'Marcus normal region entails the BEP no-inverted-direction condition',
    'Does the Marcus normal region, together with a non-inverted reverse direction, entail the '
    'BEP no-inverted-direction condition through the Evans–Polanyi bounds?',
    'The Evans–Polanyi bounds are equivalent to the absence of an inverted direction for either '
    'the forward or the reverse step. A normal-region forward direction plus a non-inverted '
    'reverse direction therefore excludes both inverted directions; the query composes the '
    'Marcus normal-region premise with the BEP equivalence through the EP-bounds mediator.',
    endpoint('marcus.normalRegion', 'definition'),
    endpoint('bep.noInvertedDirection', 'theorem-rhs-predicate',
             'The certificate right predicate is the right-hand predicate of '
             'BEP.epBounds_iff_no_inverted_direction, the delivered theorem named by the '
             'inventory row. See aliasResolutions[AL-WPS01-03].'),
    'BarrierCtx', 'scope-WPS01-two-parabola', 'conditionalComposition',
    'A typed composition of the delivered Marcus-normal implication and the delivered '
    'EP-bounds/no-inverted-direction equivalence; the child conclusion is computed, not '
    'independently proved.',
    'A context satisfying the child premises and Marcus.NormalRegion but falsifying the '
    'no-inverted-direction predicate would refute the composition.',
    premise('fun δ : BarrierCtx => 0 < δ.lam ∧ -δ.lam ≤ δ.x',
            ['barrier.positiveCurvature', 'marcus.reverseNotInverted'],
            [
                {'id': 'barrier.positiveCurvature',
                 'predicate': 'fun δ : BarrierCtx => 0 < δ.lam',
                 'statement': 'The Marcus curvature is positive.',
                 'loadBearing': 'Consumed by both parents.'},
                {'id': 'marcus.reverseNotInverted',
                 'predicate': 'fun δ : BarrierCtx => -δ.lam ≤ δ.x',
                 'statement': 'The reverse direction is not inverted.',
                 'loadBearing': 'Consumed by the Marcus-normal parent; without it the forward '
                                'normal region alone does not exclude an inverted reverse '
                                'direction.'},
            ]),
    legacy_evidence('cert-composition'),
    provenance_extra={'legacyQueryId': 'q-composition', 'legacyRecordId': 'rec-composition',
                      'aliasResolutionIds': ['AL-WPS01-03']},
))

queries.append(certified(
    'Q-WPS01-MB-02', 'P-Marcus-BEP',
    'BEP activation barrier is the Marcus forward barrier',
    'Is the BEP activation barrier definitionally the Marcus forward barrier at the same '
    'curvature and driving force?',
    'Both theories use the same equal-curvature two-parabola crossing. The definitional pin '
    'shows that their barrier symbols denote one physical barrier, so BEP activation energies '
    'and Marcus barrier heights are directly comparable.',
    endpoint('stmt-BEP-PhotoLean-BEP-eact', 'definition'),
    endpoint('marcus.barrier', 'definition'),
    'TwoParabolaCtx', 'scope-WPS01-two-parabola', 'definitionalIdentity',
    'A kernel rfl pin: both definitions unfold to the same term.',
    'A context (lam, x) at which the two translated barriers differ would refute the '
    'definitional identity.',
    tprem('TwoParabolaCtx'),
    legacy_evidence('cert-D-S05-bep-eact-eq-marcus-barrier'),
    provenance_extra={'legacyQueryId': 'q-D-S05-bep-eact-eq-marcus-barrier',
                      'legacyRecordId': 'rec-D-S05-bep-eact-eq-marcus-barrier'},
))

queries.append(certified(
    'Q-WPS01-MB-03', 'P-Marcus-BEP',
    'Marcus rate is the BEP Arrhenius form through the activation barrier',
    'Is the Marcus rate law definitionally the BEP Arrhenius form written through the BEP '
    'activation barrier?',
    'The Marcus rate and the BEP rate expression differ only by rewriting the barrier as the '
    'BEP activation energy. The definitional identity is the rate-level content of the shared '
    'barrier, and it makes the two rate languages interchangeable without a new physical '
    'assumption.',
    endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
    endpoint('stmt-BEP-PhotoLean-BEP-rate_eq_exp_neg_eact', 'theorem-rhs-term',
             'The certificate right term is the right-hand term of the delivered theorem '
             'BEP.rate_eq_exp_neg_eact. Legacy statementId PhotoLean.BEP.rateViaEact is a '
             'synthetic alias, resolved here to the real theorem statement; see '
             'aliasResolutions[AL-WPS01-01].'),
    'RateCtx', 'scope-WPS01-rate', 'definitionalIdentity',
    'A kernel rfl pin after unfolding the Marcus rate and the BEP activation barrier.',
    'A context (A, lam, kB, T, x) at which the two translated rate terms differ would refute '
    'the definitional identity.',
    tprem('RateCtx'),
    legacy_evidence('cert-D-S05-bep-rate-eq-exp-neg-eact',
                    'The certificate right endpoint names PhotoLean.BEP.rateViaEact; the real '
                    'declaration is BEP.rate_eq_exp_neg_eact, whose RHS is the term used. The '
                    'alias is repaired in this screening layer only.'),
    provenance_extra={'legacyQueryId': 'q-D-S05-bep-rate-eq-exp-neg-eact',
                      'legacyRecordId': 'rec-D-S05-bep-rate-eq-exp-neg-eact',
                      'aliasResolutionIds': ['AL-WPS01-01']},
))

# ---------------------------------------------------------------- P-Marcus-Sabatier
queries.append(certified(
    'Q-WPS01-MS-01', 'P-Marcus-Sabatier',
    'Marcus rate shares the Sabatier activity functional of the same barrier',
    'Is the Marcus rate law exactly the Sabatier activity functional of the same two-parabola '
    'barrier, scaled by the pre-exponential factor?',
    'The two theories describe different observables — an electron-transfer rate and a catalytic '
    'turnover proxy — but both use the same Arrhenius activation form on the same two-parabola '
    'barrier. The definitional identity is the exact shared functional form behind the '
    'look-alike; it does not claim that the two optima coincide.',
    endpoint('stmt-Marcus-PhotoLean-Marcus-rate', 'definition'),
    endpoint('stmt-Sabatier-PhotoLean-Sabatier-activity', 'definition'),
    'RateActivityCtx', 'scope-WPS01-rate', 'definitionalIdentity',
    'The two rate terms unfold to the same Arrhenius body after substituting the kernel '
    'barrier; the pin carries a fresh DefEq.refl.',
    'A context (A, lam, kB, T, x) at which the two translated rate terms differ would refute '
    'the definitional identity.',
    tprem('RateActivityCtx'),
    probe_evidence('marcusRateSabatierActivityPin', 'definitionalIdentity',
                   [{'declaration': 'PhotoLean.Relations.marcus_rate_eq_activity',
                     'sourceArtifact': 'PhotoLean/Relations.lean',
                     'sourceLine': 466,
                     'role': 'delivered §9 C1 theorem consumed by the probe wrapper'}],
                   'The R1 source manifest freezes the PhotoLean/**/*.lean file set; adding a '
                   'delivered module would break validate_boundary.py. The certificate is '
                   'therefore checked as a compiled probe under bounded_audit/, and the '
                   'underlying delivered theorem is cited.'),
))

# ---------------------------------------------------------------- P-Hammond-BEP
queries.append(certified(
    'Q-WPS01-HB-01', 'P-Hammond-BEP',
    'Hammond reaction region entails the Evans–Polanyi bounds',
    'Does Hammond’s reaction region — the crossing point strictly between the two wells — '
    'entail the BEP Evans–Polanyi bounds 0 ≤ α ≤ 1?',
    'The reaction region places both the forward and the reverse direction inside the Marcus '
    'normal region, so both transfer coefficients lie in [0,1]. The one-way implication is the '
    'chemical content of “inside the Hammond window implies normal Brønsted behaviour”; the '
    'converse fails outside the window.',
    endpoint('hammond.reactionRegion', 'definition'),
    endpoint('bep.epBounds', 'definition'),
    'BarrierCtx', 'scope-WPS01-two-parabola', 'implication',
    'A one-way entailment; the converse is not claimed and is false for steps outside the '
    'window that still satisfy the bounds.',
    'A context with 0 < lam satisfying Hammond.ReactionRegion but falsifying BEP.EPBounds would '
    'refute the implication.',
    pos_lam('BarrierCtx'),
    legacy_evidence('cert-hammond-bep'),
    provenance_extra={'legacyQueryId': 'q-hammond-bep', 'legacyRecordId': 'rec-hammond-bep'},
))

queries.append(certified(
    'Q-WPS01-HB-02', 'P-Hammond-BEP',
    'BEP transfer coefficient is the Hammond transition-state coordinate',
    'Is the BEP transfer coefficient observationally the Hammond transition-state coordinate at '
    'the same driving force?',
    'The BEP transfer coefficient is the linear-response form 1/2 - x/(2 lam); the Hammond '
    'transition-state coordinate is (lam - x)/(2 lam). They agree at every driving force away '
    'from lam = 0, so the two theories’ observables are the same structural quantity, not two '
    'independent descriptors.',
    endpoint('stmt-BEP-PhotoLean-BEP-transfer', 'definition'),
    endpoint('stmt-Hammond-PhotoLean-Hammond-tsCoord', 'definition'),
    'TransferCtx', 'scope-WPS01-transfer', 'observationalEquivalence',
    'Equality of the declared transfer-coefficient channel at every driving force in its '
    'domain, under lam ≠ 0.',
    'A context lam ≠ 0 and a driving force x at which the two observed coefficients differ '
    'would refute the observational equivalence.',
    premise('fun δ : TransferCtx => δ.lam ≠ 0', ['bep.lamNeZero'],
            [{'id': 'bep.lamNeZero',
              'predicate': 'fun δ : TransferCtx => δ.lam ≠ 0',
              'statement': 'The BEP linear-response coefficient is well defined only at nonzero '
                           'curvature.',
              'loadBearing': 'At lam = 0 the two totalized-division values disagree.'}]),
    legacy_evidence('cert-D-S02-transfer-eq-tsCoord-bridge'),
    channels=[{
        'id': 'transfer-coefficient',
        'observedValueType': 'ℝ',
        'inputDomain': 'x : ℝ (driving force)',
        'domainNonempty': True,
        'leftObs': 'fun δ x => BEP.transfer δ.lam x',
        'rightObs': 'fun δ x => Hammond.tsCoord δ.lam x',
    }],
    provenance_extra={'legacyQueryId': 'q-D-S02-transfer-eq-tsCoord-bridge',
                      'legacyRecordId': 'rec-D-S02-transfer-eq-tsCoord-bridge'},
))

queries.append(certified(
    'Q-WPS01-HB-03', 'P-Hammond-BEP',
    'BEP observable window slope is the Hammond Leffler secant',
    'Is the BEP observable slope over a driving-force window observationally the Hammond '
    'Leffler secant over the same window?',
    'The BEP secant slope is a finite difference of the barrier over [x, x+h]; the Hammond '
    'Leffler secant is the finite-difference Brønsted coefficient over the same pair of driving '
    'forces. Equality of the two observables means the BEP slope measurement and the Hammond '
    'Leffler coefficient are the same experimental quantity.',
    endpoint('stmt-BEP-PhotoLean-BEP-secSlope', 'definition'),
    endpoint('stmt-Hammond-PhotoLean-Hammond-lefflerSecant', 'definition'),
    'SlopeCtx', 'scope-WPS01-slope', 'observationalEquivalence',
    'Equality of the declared window-slope channel at every window in its domain.',
    'A context lam and a window (x, h) at which the two observed slopes differ would refute '
    'the observational equivalence.',
    tprem('SlopeCtx'),
    legacy_evidence('cert-D-S02-secSlope-eq-lefflerSecant'),
    channels=[{
        'id': 'window-secant-slope',
        'observedValueType': 'ℝ',
        'inputDomain': '(x, h) : ℝ × ℝ (window origin and width)',
        'domainNonempty': True,
        'leftObs': 'fun δ p => BEP.secSlope δ.lam p.1 p.2',
        'rightObs': 'fun δ p => Hammond.lefflerSecant δ.lam p.1 (p.1 + p.2)',
    }],
    provenance_extra={'legacyQueryId': 'q-D-S02-secSlope-eq-lefflerSecant',
                      'legacyRecordId': 'rec-D-S02-secSlope-eq-lefflerSecant'},
))

queries.append(certified(
    'Q-WPS01-HB-04', 'P-Hammond-BEP',
    'BEP window conformance entails the Hammond structural descriptor',
    'Does BEP line-law conformance on a declared driving-force window entail Hammond’s '
    'structural descriptor?',
    'BEP conformance on a window carries a positive-curvature conjunct; that positivity is '
    'exactly what the structural Hammond descriptor needs. The implication is one-way and the '
    'tolerance bound itself is not consumed, so the query records the precise logical road '
    'between the two predicates rather than a deeper equivalence.',
    endpoint('stmt-BEP-PhotoLean-BEP-EPConformsOnWindow', 'definition'),
    endpoint('stmt-Hammond-PhotoLean-Hammond-HammondDescriptor', 'definition'),
    'WindowCtx', 'scope-WPS01-window', 'implication',
    'A one-way entailment through the positivity conjunct of BEP.EPConformsOnWindow; the '
    'converse is not claimed.',
    'A context (lam, tol, a, b) satisfying BEP.EPConformsOnWindow but falsifying '
    'Hammond.HammondDescriptor would refute the implication.',
    tprem('WindowCtx'),
    legacy_evidence('cert-D-S03-hammondDescriptor-of-epConformsOnWindow'),
    provenance_extra={'legacyQueryId': 'q-D-S03-hammondDescriptor-of-epConformsOnWindow',
                      'legacyRecordId': 'rec-D-S03-hammondDescriptor-of-epConformsOnWindow'},
))

# ---------------------------------------------------------------- P-Hammond-SymmetryFactor
queries.append(certified(
    'Q-WPS01-HF-01', 'P-Hammond-SymmetryFactor',
    'Equal-curvature symmetry-factor coordinate is the Hammond thermoneutral coordinate',
    'At equal force constants, is the SymmetryFactor thermoneutral transition-state coordinate '
    'observationally the Hammond transition-state coordinate at thermoneutrality?',
    'The SymmetryFactor model generalises the kernel to unequal curvatures. On the equal-'
    'curvature diagonal its closed-form thermoneutral coordinate reduces to 1/2, which is '
    'exactly the Hammond/kernel coordinate at x = 0. The bridge identifies the seventh '
    'theory’s structural coordinate with the Hammond structural reading in the kernel limit.',
    endpoint('stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero', 'definition'),
    endpoint('stmt-Hammond-PhotoLean-Hammond-tsCoord', 'definition'),
    'SymFactorHammondCtx', 'scope-WPS01-equal-curvature', 'observationalEquivalence',
    'Equality of the declared thermoneutral-coordinate channel on the equal-curvature diagonal '
    'under lam > 0.',
    'A context lam > 0 at which the two observed thermoneutral coordinates differ would refute '
    'the observational equivalence.',
    pos_lam('SymFactorHammondCtx', 'symmetryFactor.lamPositive',
            'The equal-curvature diagonal requires a positive curvature.'),
    probe_evidence('symmetryFactorHammondThermoneutralBridge', 'observationalEquivalence',
                   [
                       {'declaration':
                        'PhotoLean.SymmetryFactor.tsCoordZero_eq_kernel_thermoneutral',
                        'sourceArtifact': 'PhotoLean/SymmetryFactor/Sharp.lean',
                        'sourceLine': 112,
                        'role': 'delivered equal-curvature tie-back to the kernel coordinate'},
                       {'declaration': 'PhotoLean.Relations.kernel_tsCoord_eq_hammond',
                        'sourceArtifact': 'PhotoLean/Relations.lean',
                        'sourceLine': 119,
                        'role': 'delivered kernel/Hammond definitional pin'},
                   ],
                   'The R1 source manifest freezes the PhotoLean/**/*.lean file set; adding a '
                   'delivered module would break validate_boundary.py. The certificate is '
                   'checked as a compiled probe under bounded_audit/ and cites the delivered '
                   'tie-back theorems.'),
    channels=[{
        'id': 'thermoneutral-transition-state-coordinate',
        'observedValueType': 'ℝ',
        'inputDomain': 'Unit (the diagonal fixes both force constants to lam)',
        'domainNonempty': True,
        'leftObs': 'fun δ _ => SymmetryFactor.tsCoordZero δ.lam δ.lam',
        'rightObs': 'fun δ _ => Hammond.tsCoord δ.lam 0',
    }],
))

# ---------------------------------------------------------------- P-BEP-Sabatier
queries.append(certified(
    'Q-WPS01-BS-01', 'P-BEP-Sabatier',
    'Linear volcano is the maximum of the two BEP tangent lines',
    'Is the Sabatier linear volcano exactly the pointwise maximum of the two BEP tangent lines '
    'of the parabolic branches?',
    'Sabatier’s description layer writes the effective barrier as the maximum of two affine '
    'BEP branches. At the parameter choice alphaA = alphaB = 1/2, betaA = lam1/4, '
    'betaB = lam2/4, that maximum is exactly the BEP tangent-line construction. The identity '
    'is the exact link between the literature’s linear volcano and the repository’s BEP '
    'linear-response model.',
    endpoint('stmt-Sabatier-PhotoLean-Sabatier-volcanoBarrier', 'definition'),
    endpoint('stmt-BEP-PhotoLean-BEP-bepLine', 'definition'),
    'BepSabatierCtx', 'scope-WPS01-descriptor-axis', 'observationalEquivalence',
    'Equality of the descriptor-axis barrier channel at every descriptor value, with no '
    'premise because the delivered theorem is unconditional.',
    'A context (lam1, lam2) and a descriptor dE at which the two observed barriers differ '
    'would refute the observational equivalence.',
    tprem('BepSabatierCtx'),
    probe_evidence('bepSabatierLinearVolcanoBridge', 'observationalEquivalence',
                   [
                       {'declaration': 'PhotoLean.Sabatier.linearVolcano_eq_bepTangent',
                        'sourceArtifact': 'PhotoLean/Sabatier/Compose.lean',
                        'sourceLine': 103,
                        'role': 'delivered §8 identity consumed by the probe wrapper'},
                       {'declaration': 'PhotoLean.Relations.linearVolcano_eq_bepTangent',
                        'sourceArtifact': 'PhotoLean/Relations.lean',
                        'sourceLine': 402,
                        'role': 'delivered cross-theory re-export'},
                   ],
                   'The R1 source manifest freezes the PhotoLean/**/*.lean file set; adding a '
                   'delivered module would break validate_boundary.py. The certificate is '
                   'checked as a compiled probe under bounded_audit/ and cites the delivered '
                   'identity theorem.'),
    channels=[{
        'id': 'descriptor-axis-barrier',
        'observedValueType': 'ℝ',
        'inputDomain': 'dE : ℝ (Sabatier descriptor / binding energy)',
        'domainNonempty': True,
        'leftObs': 'fun δ dE => Sabatier.volcanoBarrier (1/2) (δ.lam1/4) (1/2) (δ.lam2/4) dE',
        'rightObs': 'fun δ dE => max (BEP.bepLine δ.lam1 (-dE)) (BEP.bepLine δ.lam2 dE)',
    }],
))

# ---------------------------------------------------------------- P-BEP-SymmetryFactor
queries.append(certified(
    'Q-WPS01-BF-01', 'P-BEP-SymmetryFactor',
    'Equal-curvature symmetry-factor coordinate is the BEP thermoneutral transfer coefficient',
    'At equal force constants, is the SymmetryFactor thermoneutral transition-state coordinate '
    'observationally the BEP transfer coefficient at thermoneutrality?',
    'On the equal-curvature diagonal the SymmetryFactor closed form reduces to the BEP '
    'linear-response coefficient at x = 0. The bridge extends the BEP transfer/structural '
    'coordinate chain to the seventh theory and identifies the shared thermoneutral value.',
    endpoint('stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero', 'definition'),
    endpoint('stmt-BEP-PhotoLean-BEP-transfer', 'definition'),
    'SymFactorBepCtx', 'scope-WPS01-equal-curvature', 'observationalEquivalence',
    'Equality of the declared thermoneutral transfer-coefficient channel on the equal-curvature '
    'diagonal under lam > 0.',
    'A context lam > 0 at which the two observed coefficients differ would refute the '
    'observational equivalence.',
    pos_lam('SymFactorBepCtx', 'symmetryFactor.lamPositive',
            'The equal-curvature diagonal requires a positive curvature.'),
    probe_evidence('symmetryFactorBepThermoneutralBridge', 'observationalEquivalence',
                   [{'declaration': 'PhotoLean.SymmetryFactor.betaHalf_eq_transfer_thermoneutral',
                     'sourceArtifact': 'PhotoLean/SymmetryFactor/Sharp.lean',
                     'sourceLine': 133,
                     'role': 'delivered equal-curvature tie-back to BEP.transfer'}],
                   'The R1 source manifest freezes the PhotoLean/**/*.lean file set; adding a '
                   'delivered module would break validate_boundary.py. The certificate is '
                   'checked as a compiled probe under bounded_audit/ and cites the delivered '
                   'tie-back theorem.'),
    channels=[{
        'id': 'thermoneutral-transfer-coefficient',
        'observedValueType': 'ℝ',
        'inputDomain': 'Unit (the diagonal fixes both force constants to lam)',
        'domainNonempty': True,
        'leftObs': 'fun δ _ => SymmetryFactor.tsCoordZero δ.lam δ.lam',
        'rightObs': 'fun δ _ => BEP.transfer δ.lam 0',
    }],
))

# ---------------------------------------------------------------- P-Hammond-Sabatier
queries.append(unresolved(
    'Q-WPS01-HS-01', 'P-Hammond-Sabatier',
    'Hammond structural descriptor versus Sabatier volcano descriptor',
    'Does Hammond’s structural descriptor entail the Sabatier volcano descriptor when the '
    'Sabatier descriptor profile is instantiated on the same two-parabola barrier?',
    'Both theories describe a single optimum on a one-dimensional energy coordinate: Hammond’s '
    'transition state sits at the crossing, while Sabatier’s volcano apex is the unique '
    'minimiser of the effective barrier. A bridge would identify the Sabatier descriptor axis '
    'with the Hammond driving force and transfer the uniqueness statement. The pair is '
    'registered as a no-edge in the legacy registry; the candidate bridge is recorded here but '
    'not certified.',
    endpoint('stmt-Hammond-PhotoLean-Hammond-HammondDescriptor', 'definition'),
    endpoint('stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor', 'definition'),
    'HammondSabatierCandidateCtx', 'scope-WPS01-candidate-bridge', 'implication',
    'A one-way implication from the structural descriptor to the volcano descriptor under a '
    'candidate instantiation.',
    'A context satisfying Hammond.HammondDescriptor but falsifying the instantiated '
    'VolcanoDescriptor would refute the implication.',
    premise('fun δ : HammondSabatierCandidateCtx => 0 < δ.lam', ['barrier.positiveCurvature'],
            [{'id': 'barrier.positiveCurvature',
              'predicate': 'fun δ : HammondSabatierCandidateCtx => 0 < δ.lam',
              'statement': 'The curvature is positive.',
              'loadBearing': 'The candidate bridge needs the positive-curvature kernel model.'}]),
    'SL-WPS01-HS-01',
    'Candidate: Sabatier.parabolicBarrier unfolds to the maximum of the two Hammond '
    'gapReactant terms; the descriptor-level implication is not certified.',
))

# ---------------------------------------------------------------- P-Sabatier-SymmetryFactor
queries.append(unresolved(
    'Q-WPS01-SF-01', 'P-Sabatier-SymmetryFactor',
    'Sabatier volcano apex versus SymmetryFactor thermoneutral coordinate',
    'Do Sabatier’s volcano apex and SymmetryFactor’s thermoneutral crossing coordinate '
    'identify the same structural optimum when the two branch curvatures are read as the two '
    'force constants?',
    'Both quantities are closed-form optima of an unequal-curvature two-parabola model, but '
    'they live on different axes: Sabatier’s apexPar is a descriptor-axis value, while '
    'SymmetryFactor’s tsCoordZero is a reaction-coordinate crossing. A candidate algebraic '
    'relation exists (apexPar = sqrt(lam1*lam2) * (2*tsCoordZero - 1)), but no delivered '
    'statement identifies the two physical coordinates.',
    endpoint('stmt-Sabatier-PhotoLean-Sabatier-apexPar', 'definition'),
    endpoint('stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero', 'definition'),
    'SabatierSymmetryCandidateCtx', 'scope-WPS01-candidate-bridge', 'equivalence',
    'An equivalence between the two optimum predicates under the candidate coordinate '
    'identification.',
    'A context where one optimum predicate holds and the other fails would refute the '
    'equivalence.',
    premise('fun δ : SabatierSymmetryCandidateCtx => 0 < δ.lam1 ∧ 0 < δ.lam2',
            ['sabatier.positiveCurvatures'],
            [{'id': 'sabatier.positiveCurvatures',
              'predicate': 'fun δ : SabatierSymmetryCandidateCtx => 0 < δ.lam1 ∧ 0 < δ.lam2',
              'statement': 'Both branch curvatures are positive.',
              'loadBearing': 'Both closed forms require positive curvatures.'}]),
    'SL-WPS01-SF-01',
    'Candidate: apexPar = sqrt(lam1*lam2) * (2*tsCoordZero - 1) is an algebraic relation; '
    'the physical coordinate identification is not certified.',
))

# ---------------------------------------------------------------- P-Kasha-Sabatier
queries.append(unresolved(
    'Q-WPS01-KS-01', 'P-Kasha-Sabatier',
    'Kasha rule versus Sabatier volcano condition on the energy-gap axis',
    'Does Kasha’s rule — no emission from upper excited states — correspond to a Sabatier '
    'optimal or volcano condition on the same energy-gap axis?',
    'Kasha’s rule is a statement about the branching ratios of a ladder of excited states; the '
    'Sabatier condition is a statement about the unique optimum of a barrier profile along a '
    'descriptor axis. A bridge would need a declared map from the ladder’s energy gap and '
    'yield ratios to the descriptor-axis barrier. The theories share the Arrhenius rate '
    'template but not a delivered statement linking the two predicates.',
    endpoint('kasha.kashaRule', 'definition'),
    endpoint('stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor', 'definition'),
    'KashaSabatierCandidateCtx', 'scope-WPS01-candidate-bridge', 'equivalence',
    'An equivalence between the Kasha-rule predicate and the instantiated volcano descriptor.',
    'A context where the Kasha rule holds and the volcano descriptor fails, or conversely, '
    'would refute the equivalence.',
    premise('fun δ : KashaSabatierCandidateCtx => 0 < δ.kB * δ.T', ['thermalEnergyPositive'],
            [{'id': 'thermalEnergyPositive',
              'predicate': 'fun δ : KashaSabatierCandidateCtx => 0 < δ.kB * δ.T',
              'statement': 'The thermal energy is positive.',
              'loadBearing': 'Both rate languages divide by kB*T.'}]),
    'SL-WPS01-KS-01',
    'Candidate: Kasha.marcusIC and Sabatier.activity share the Arrhenius template; the '
    'rule-versus-volcano predicate bridge is not certified.',
))

# ---------------------------------------------------------------- assemble pairs
PAIR_THEORIES = {
    'P-Marcus-Hammond': ['Marcus', 'Hammond'],
    'P-Marcus-BEP': ['Marcus', 'BEP'],
    'P-Marcus-Sabatier': ['Marcus', 'Sabatier'],
    'P-Hammond-BEP': ['Hammond', 'BEP'],
    'P-Hammond-Sabatier': ['Hammond', 'Sabatier'],
    'P-Hammond-SymmetryFactor': ['Hammond', 'SymmetryFactor'],
    'P-BEP-Sabatier': ['BEP', 'Sabatier'],
    'P-BEP-SymmetryFactor': ['BEP', 'SymmetryFactor'],
    'P-Kasha-Sabatier': ['Kasha', 'Sabatier'],
    'P-Sabatier-SymmetryFactor': ['Sabatier', 'SymmetryFactor'],
}

pairs = []
for pair_id in PAIRS:
    pair_queries = [q for q in queries if q['pairId'] == pair_id]
    pairs.append({
        'pairId': pair_id,
        'theories': PAIR_THEORIES[pair_id],
        'primaryCluster': QUEUE_BY_ID[pair_id]['screeningCluster'],
        'r1QueueLegacyStatus': 'covered',
        'queryIds': [q['queryId'] for q in pair_queries],
        'queries': pair_queries,
    })

status_counts = {}
kind_counts = {}
for q in queries:
    status_counts[q['outcome']['status']] = status_counts.get(q['outcome']['status'], 0) + 1
    kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1

screening = {
    'schemaVersion': '1.0.0',
    'artifactKind': 'bounded-screening-package',
    'round': 'R2',
    'generatedOn': '2026-11-04',
    'workPackage': {
        'id': 'WP-SURFACE-01',
        'title': 'Surface and free-energy relations',
        'source': 'loop/计划.md R2, step 1',
        'pairIds': PAIRS,
        'pairCount': len(PAIRS),
        'r1ClusterPlanWorkPackage': {
            'id': 'WP-surface-free-energy-01',
            'pairIds': [
                'P-Marcus-Hammond', 'P-Marcus-BEP', 'P-Marcus-Sabatier',
                'P-Marcus-SymmetryFactor', 'P-Hammond-BEP', 'P-Hammond-Sabatier',
                'P-Hammond-SymmetryFactor', 'P-BEP-Sabatier', 'P-BEP-SymmetryFactor',
                'P-Sabatier-SymmetryFactor',
            ],
            'difference': {
                'addedByR2Plan': ['P-Kasha-Sabatier'],
                'removedByR2Plan': ['P-Marcus-SymmetryFactor'],
                'note': 'The approved R2 plan names ten pairs including P-Kasha-Sabatier and '
                        'excluding P-Marcus-SymmetryFactor. The R1 cluster plan work package '
                        'has the opposite membership. This package follows the approved R2 '
                        'plan; the mismatch is recorded rather than silently reconciled. '
                        'No R1 artifact is edited.',
            },
        },
    },
    'statusVocabulary': ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope'],
    'kindVocabulary': ['definitionalIdentity', 'implication', 'equivalence',
                       'conditionalComposition', 'observationalEquivalence',
                       'distinguishability', 'refutation'],
    'allowedAxioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'snapshot': SNAPSHOT,
    'inventoryReference': {
        'path': INV_REL,
        'sha256': SNAPSHOT['inventorySha256'],
        'statementRows': len(inv['statements']),
        'screeningEligible': sum(1 for row in inv['statements'] if row['screeningEligible']),
        'schemaVersion': inv['schemaVersion'],
        'round': inv['round'],
    },
    'legacyRegistryReference': {
        'path': REGISTRY_REL,
        'sha256': SNAPSHOT['legacyRegistrySha256'],
        'expectedSha256': '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0',
        'mode': 'read-only',
    },
    'aliasResolutions': [
        {
            'id': 'AL-WPS01-01',
            'aliasClass': 'r1-legacy-dangling',
            'aliasStatementId': 'stmt-BEP-PhotoLean-BEP-rateViaEact',
            'aliasDeclaration': 'PhotoLean.BEP.rateViaEact',
            'resolvedStatementId': 'stmt-BEP-PhotoLean-BEP-rate_eq_exp_neg_eact',
            'resolvedDeclaration': 'PhotoLean.BEP.rate_eq_exp_neg_eact',
            'resolutionKind': 'theorem-rhs-term',
            'legacyQueryId': 'q-D-S05-bep-rate-eq-exp-neg-eact',
            'legacyRecordId': 'rec-D-S05-bep-rate-eq-exp-neg-eact',
            'certificateId': 'cert-D-S05-bep-rate-eq-exp-neg-eact',
            'note': 'The R1 inventory records PhotoLean.BEP.rateViaEact as dangling legacy '
                    'metadata. The real declaration is BEP.rate_eq_exp_neg_eact, whose RHS is '
                    'the term the certificate compares. The alias is repaired in this '
                    'screening layer only; the legacy registry is not edited.',
        },
        {
            'id': 'AL-WPS01-02',
            'aliasClass': 'r1-legacy-dangling',
            'aliasStatementId': 'stmt-Marcus-PhotoLean-Marcus-rateDescriptor',
            'aliasDeclaration': 'PhotoLean.Marcus.rateDescriptor',
            'resolvedStatementId': 'stmt-Marcus-PhotoLean-Marcus-descriptor_sharp',
            'resolvedDeclaration': 'PhotoLean.Marcus.descriptor_sharp',
            'resolutionKind': 'theorem-lhs-predicate',
            'legacyQueryId': 'q-D-S06-hammond-sharp-iff-marcus-sharp',
            'legacyRecordId': 'rec-D-S06-hammond-sharp-iff-marcus-sharp',
            'certificateId': 'cert-D-S06-hammond-sharp-iff-marcus-sharp',
            'note': 'The R1 inventory records PhotoLean.Marcus.rateDescriptor as dangling legacy '
                    'metadata. The real declaration is Marcus.descriptor_sharp, whose LHS is '
                    'the conjunctive rate-descriptor predicate used by the certificate. The '
                    'alias is repaired in this screening layer only.',
        },
        {
            'id': 'AL-WPS01-03',
            'aliasClass': 'certificate-internal-endpoint',
            'aliasStatementId': 'PhotoLean.BEP.noInvertedDirection',
            'aliasDeclaration': 'PhotoLean.BEP.noInvertedDirection',
            'resolvedStatementId': 'bep.noInvertedDirection',
            'resolvedDeclaration': 'PhotoLean.BEP.epBounds_iff_no_inverted_direction',
            'resolutionKind': 'theorem-rhs-predicate',
            'legacyQueryId': 'q-composition',
            'legacyRecordId': 'rec-composition',
            'certificateId': 'cert-composition',
            'note': 'The certificate-internal StatementRef string PhotoLean.BEP.'
                    'noInvertedDirection is not a delivered declaration; it names the RHS '
                    'predicate of BEP.epBounds_iff_no_inverted_direction. The inventory row '
                    'bep.noInvertedDirection is that real theorem. Recorded here so the '
                    'endpoint does not silently become a fictional declaration.',
        },
    ],
    'contextLibrary': CONTEXTS,
    'scopeLibrary': {k: dict(v, id=k, snapshot=SNAPSHOT_ID) for k, v in SCOPES.items()},
    'pairs': pairs,
    'counts': {
        'pairs': len(pairs),
        'queries': len(queries),
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
        'A certified row is a checked relation under its declared context, premises and '
        'snapshot; it is not a claim of physical universality.',
        'An unresolved row is not a negative claim and is not a refutation.',
        'No pair was forced into a relation to increase edge count.',
        'The two no-edge pairs carried over from the R1 registry (Hammond-Sabatier and '
        'Kasha-Sabatier) and the Sabatier-SymmetryFactor pair remain unresolved; the legacy '
        'no-edge registrations are not silently overturned.',
    ],
}

# ---------------------------------------------------------------- search log
SEARCHES = [
    {
        'searchId': 'SL-WPS01-HS-01',
        'queryId': 'Q-WPS01-HS-01',
        'pairId': 'P-Hammond-Sabatier',
        'status': 'unresolved',
        'scope': 'scope-WPS01-candidate-bridge',
        'snapshot': SNAPSHOT_ID,
        'searchedStatements': [
            'stmt-Hammond-PhotoLean-Hammond-HammondDescriptor',
            'stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor',
            'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
            'stmt-Sabatier-PhotoLean-Sabatier-apexPar',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'conditionalComposition', 'observationalEquivalence'],
        'contextsConsidered': [
            'HammondSabatierCandidateCtx (lam, x) with the Sabatier profile instantiated on '
            'the Hammond barrier',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean',
             'locator': '§10 no-edge registry, Sabatier ↔ Hammond',
             'finding': 'The accepted registry states there is no edge: Sabatier consumes '
                        'PhotoLean.BEP.Basic only and never the structural reading.'},
            {'artifact': 'PhotoLean/Sabatier/Basic.lean',
             'locator': 'VolcanoDescriptor, branchUp, branchDown, volcanoBarrier, activity',
             'finding': 'The Sabatier predicate is a higher-order property of a barrier '
                        'profile on a descriptor axis; it has no structural-coordinate '
                        'argument.'},
            {'artifact': 'PhotoLean/Hammond/Basic.lean',
             'locator': 'HammondDescriptor, ReactionRegion, gapReactant, tsCoord',
             'finding': 'The Hammond predicate is a property of the curvature lam only; the '
                        'structural coordinate is a function of (lam, x).'},
            {'artifact': 'PhotoLean/Sabatier/Compose.lean',
             'locator': 'parabolicBarrier, parabolaUp, parabolaDown',
             'finding': 'The two-parabola Sabatier barrier unfolds to BEP.eact at ±dE, which '
                        'is definitionally the kernel/Hammond barrier. A term-level identity '
                        'is available, but it does not by itself transfer the descriptor '
                        'predicate.'},
        ],
        'commands': [
            {'command': "grep -rn '^import' PhotoLean/Sabatier",
             'purpose': 'Measure the module dependency fact.',
             'result': 'Sabatier/Compose imports PhotoLean.BEP.Basic and '
                       'PhotoLean.Sabatier.Basic; no Hammond/Kasha/SymmetryFactor import.'},
            {'command': "grep -rn '^import' PhotoLean/Hammond",
             'purpose': 'Measure the module dependency fact.',
             'result': 'Hammond imports Marcus modules only; no Sabatier import.'},
            {'command': "grep -rn 'Sabatier' PhotoLean/Hammond PhotoLean/Kasha "
                       "PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search for a delivered cross-theory statement.',
             'result': 'No matches.'},
            {'command': "grep -rn 'Hammond\\|Kasha\\|SymmetryFactor' PhotoLean/Sabatier "
                       "--include='*.lean'",
             'purpose': 'Search for a delivered cross-theory statement from the Sabatier side.',
             'result': 'No matches.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair '
                        'P-Hammond-Sabatier',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False; "
                       "registry record rec-notestablished-P-Hammond-Sabatier status="
                       "'notEstablished', certificate=None."},
        ],
        'strategiesAttempted': [
            {'strategy': 'Search the legacy registry for a certificate between the two '
                         'predicates.',
             'outcome': 'None; the pair has only a pair-level notEstablished record.'},
            {'strategy': 'Search the delivered cross-theory modules for a theorem whose type '
                         'mentions both predicates.',
             'outcome': 'None.'},
            {'strategy': 'Instantiate Sabatier.VolcanoDescriptor on the Hammond/kernel '
                         'barrier and try to reuse a delivered monotonicity lemma.',
             'outcome': 'The candidate implication appears provable, but no delivered '
                        'statement-level bridge or typed certificate exists; building it '
                        'would require a new uniqueness proof and a declared translation of '
                        'the descriptor axis. Not attempted in this round.'},
        ],
        'candidateEvidence': [
            {'kind': 'term-level identity',
             'statement': 'Sabatier.parabolicBarrier lam1 lam2 dE = max '
                          '(Hammond.gapReactant lam1 (-dE)) (Hammond.gapReactant lam2 dE)',
             'status': 'candidate; not certified, because the query asks about the '
                       'descriptor predicate, not the barrier term.'},
        ],
        'remainingGap': 'A checked implication from Hammond.HammondDescriptor to the '
                        'instantiated Sabatier.VolcanoDescriptor, together with a declared '
                        'total translation of the descriptor axis to the Hammond driving '
                        'force, is missing.',
        'recomputeCommands': [
            'grep -rn \'^import\' PhotoLean/Sabatier',
            'grep -rn \'^import\' PhotoLean/Hammond',
            'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-Sabatier',
        ],
        'rationale': 'The pair is a registered no-edge in the legacy registry. A term-level '
                     'barrier identity exists, but the descriptor-level comparison is not '
                     'settled; recording it as unresolved avoids both a forced edge and an '
                     'unsupported negative claim.',
    },
    {
        'searchId': 'SL-WPS01-KS-01',
        'queryId': 'Q-WPS01-KS-01',
        'pairId': 'P-Kasha-Sabatier',
        'status': 'unresolved',
        'scope': 'scope-WPS01-candidate-bridge',
        'snapshot': SNAPSHOT_ID,
        'searchedStatements': [
            'kasha.kashaRule',
            'stmt-Sabatier-PhotoLean-Sabatier-VolcanoDescriptor',
            'stmt-Kasha-PhotoLean-Kasha-marcusIC',
            'stmt-Sabatier-PhotoLean-Sabatier-activity',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'conditionalComposition', 'observationalEquivalence'],
        'contextsConsidered': [
            'KashaSabatierCandidateCtx (x, A, kB, T) with the Sabatier descriptor axis read '
            'as the Kasha energy gap',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean',
             'locator': '§10 no-edge registry, Sabatier ↔ Kasha',
             'finding': 'The accepted registry states the two second-batch theories share no '
                        'module and no object: one is a descriptor-axis optimisation, the '
                        'other an excited-state cascade.'},
            {'artifact': 'PhotoLean/Kasha/Basic.lean',
             'locator': 'KashaRule, KashaWithin, upperYield, cascade',
             'finding': 'The Kasha rule is a branching-ratio predicate on a ladder of rates; '
                        'it has no descriptor-axis barrier argument.'},
            {'artifact': 'PhotoLean/Kasha/Compose.lean',
             'locator': 'marcusIC',
             'finding': 'Kasha.marcusIC is an Arrhenius rate with the Marcus barrier; it '
                        'shares the rate template with Sabatier.activity but not the '
                        'volcano predicate.'},
            {'artifact': 'PhotoLean/Sabatier/Basic.lean',
             'locator': 'VolcanoDescriptor, activity',
             'finding': 'The Sabatier activity is a functional of a barrier profile; the '
                        'volcano descriptor is a uniqueness predicate on that profile.'},
        ],
        'commands': [
            {'command': "grep -rn '^import' PhotoLean/Kasha",
             'purpose': 'Measure the module dependency fact.',
             'result': 'Kasha imports PhotoLean.Marcus.Basic in Compose; no Sabatier import.'},
            {'command': "grep -rn '^import' PhotoLean/Sabatier",
             'purpose': 'Measure the module dependency fact.',
             'result': 'Sabatier imports BEP.Basic and its own modules; no Kasha import.'},
            {'command': "grep -rn 'Sabatier' PhotoLean/Kasha --include='*.lean'",
             'purpose': 'Search for a delivered cross-theory statement.',
             'result': 'No matches.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair '
                        'P-Kasha-Sabatier',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False; "
                       "registry record rec-notestablished-P-Kasha-Sabatier status="
                       "'notEstablished', certificate=None."},
        ],
        'strategiesAttempted': [
            {'strategy': 'Search for a legacy named query or certificate linking the Kasha '
                         'rule to a Sabatier optimum.',
             'outcome': 'None; only a pair-level notEstablished record.'},
            {'strategy': 'Try the shared Arrhenius rate template (Kasha.marcusIC versus '
                         'Sabatier.activity) as a bridge.',
             'outcome': 'The rate terms share a template, but the Kasha rule is a ladder '
                        'predicate and the Sabatier descriptor is a barrier-profile '
                        'predicate; the template does not transfer either predicate.'},
            {'strategy': 'Read the Kasha window result (kashaWithin_one_marcus) as a '
                         'candidate tolerance condition and compare it with '
                         'Sabatier.NearOptimal.',
             'outcome': 'The two tolerance predicates constrain different quantities (yield '
                        'ratio versus descriptor distance); no total translation is '
                        'delivered.'},
        ],
        'candidateEvidence': [
            {'kind': 'shared Arrhenius template',
             'statement': 'Kasha.marcusIC A lam kB T x = A * Sabatier.activity '
                          '(fun y => Kernel.barrier lam y) kB T x',
             'status': 'candidate term-level identity; it does not answer the rule-versus-'
                       'volcano query.'},
        ],
        'remainingGap': 'A declared map from the ladder energy gap and yield ratios to the '
                        'Sabatier descriptor axis, plus a checked equivalence between '
                        'KashaRule and the instantiated volcano/optimality predicate, is '
                        'missing.',
        'recomputeCommands': [
            'grep -rn \'^import\' PhotoLean/Kasha',
            'grep -rn \'^import\' PhotoLean/Sabatier',
            'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-Sabatier',
        ],
        'rationale': 'The pair is a registered no-edge. The only visible bridge is the shared '
                     'Arrhenius template, which does not relate the two predicates. The '
                     'predicate-level question is left unresolved rather than forced.',
    },
    {
        'searchId': 'SL-WPS01-SF-01',
        'queryId': 'Q-WPS01-SF-01',
        'pairId': 'P-Sabatier-SymmetryFactor',
        'status': 'unresolved',
        'scope': 'scope-WPS01-candidate-bridge',
        'snapshot': SNAPSHOT_ID,
        'searchedStatements': [
            'stmt-Sabatier-PhotoLean-Sabatier-apexPar',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-Sabatier-PhotoLean-Sabatier-parabolicBarrier',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-asymReactantSurface',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-asymProductSurface',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'conditionalComposition', 'observationalEquivalence'],
        'contextsConsidered': [
            'SabatierSymmetryCandidateCtx (lam1, lam2) read both as branch curvatures and '
            'as force constants',
        ],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean',
             'locator': '§10 no-edge registry, SymmetryFactor ↔ Sabatier',
             'finding': 'The accepted registry states the curvature-pair scalar (kr, kp) '
                        'shares no object with the volcano descriptor axis; no module is '
                        'imported across the pair.'},
            {'artifact': 'PhotoLean/Sabatier/Compose.lean',
             'locator': 'apexPar, parabolicBarrier, parabolaUp, parabolaDown',
             'finding': 'The Sabatier apex is a descriptor-axis closed form '
                        '(lam2*sqrt(lam1) - lam1*sqrt(lam2))/(sqrt(lam1)+sqrt(lam2)).'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean',
             'locator': 'tsCoordZero, asymReactantSurface, asymProductSurface',
             'finding': 'The SymmetryFactor coordinate is a reaction-coordinate crossing '
                        'sqrt(kp)/(sqrt(kr)+sqrt(kp)); the two quantities are different '
                        'coordinates of the two-parabola model.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Sharp.lean',
             'locator': 'tsCoordZero_eq_kernel_thermoneutral, '
                        'betaHalf_eq_transfer_thermoneutral',
             'finding': 'The delivered tie-backs go to Kernel.tsCoord and BEP.transfer, not '
                        'to Sabatier.apexPar.'},
        ],
        'commands': [
            {'command': "grep -rn '^import' PhotoLean/SymmetryFactor",
             'purpose': 'Measure the module dependency fact.',
             'result': 'SymmetryFactor imports Kernel and BEP.Criterion; no Sabatier import.'},
            {'command': "grep -rn '^import' PhotoLean/Sabatier",
             'purpose': 'Measure the module dependency fact.',
             'result': 'Sabatier imports BEP.Basic and its own modules; no SymmetryFactor '
                       'import.'},
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/Sabatier --include='*.lean'",
             'purpose': 'Search for a delivered cross-theory statement.',
             'result': 'No matches.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair '
                        'P-Sabatier-SymmetryFactor',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label='absence' subtype='registered-absence'; candidate=False; "
                       "registry record rec-notestablished-P-Sabatier-SymmetryFactor "
                       "status='notEstablished', certificate=None."},
        ],
        'strategiesAttempted': [
            {'strategy': 'Search for a legacy or delivered statement linking the two closed '
                         'forms.',
             'outcome': 'None.'},
            {'strategy': 'Check whether the two formulas are the same expression after '
                         'substitution.',
             'outcome': 'They are not: apexPar is a descriptor-axis value and tsCoordZero is '
                        'a reaction-coordinate ratio.'},
            {'strategy': 'Look for an algebraic bridge of the form '
                         'apexPar = sqrt(lam1*lam2) * (2*tsCoordZero - 1).',
             'outcome': 'The identity is a plausible algebraic candidate, but it is not '
                        'delivered and it still does not identify the two physical '
                        'coordinates. Not attempted in this round.'},
        ],
        'candidateEvidence': [
            {'kind': 'algebraic candidate',
             'statement': 'apexPar lam1 lam2 = sqrt(lam1*lam2) * '
                          '(2*tsCoordZero lam1 lam2 - 1)',
             'status': 'candidate; not checked in Lean and not a physical coordinate '
                       'identification.'},
        ],
        'remainingGap': 'A checked algebraic relation and a declared physical '
                        'coordinate identification between the Sabatier descriptor axis and '
                        'the SymmetryFactor reaction coordinate are missing.',
        'recomputeCommands': [
            'grep -rn \'^import\' PhotoLean/SymmetryFactor',
            'grep -rn \'^import\' PhotoLean/Sabatier',
            'python3 tools/relation_audit_registry.py --explain-pair '
            'P-Sabatier-SymmetryFactor',
        ],
        'rationale': 'The pair is a registered no-edge. The two optimum formulas live on '
                     'different axes; a candidate algebraic relation is recorded, but no '
                     'physical-coordinate identification is delivered. The query remains '
                     'unresolved rather than being forced into an equivalence.',
    },
]

search_log = {
    'schemaVersion': '1.0.0',
    'artifactKind': 'bounded-search-log',
    'round': 'R2',
    'generatedOn': '2026-11-04',
    'workPackage': 'WP-SURFACE-01',
    'snapshot': SNAPSHOT_ID,
    'entries': SEARCHES,
    'counts': {
        'entries': len(SEARCHES),
        'byStatus': {s: sum(1 for e in SEARCHES if e['status'] == s)
                     for s in sorted({e['status'] for e in SEARCHES})},
    },
}

with open(os.path.join(ROOT, SCREENING_REL), 'w', encoding='utf-8') as fh:
    json.dump(screening, fh, ensure_ascii=False, indent=2)
    fh.write('\n')
with open(os.path.join(ROOT, 'bounded_audit/wp-surface-01/search-log.json'), 'w',
          encoding='utf-8') as fh:
    json.dump(search_log, fh, ensure_ascii=False, indent=2)
    fh.write('\n')

print('wrote', SCREENING_REL)
print('pairs', len(pairs), 'queries', len(queries), 'statuses', status_counts)
