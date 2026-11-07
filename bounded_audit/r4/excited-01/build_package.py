#!/usr/bin/env python3
"""Build the R4 E1 screening package JSON artifacts.

Usage (from the photolean repository root):
    python3 bounded_audit/r4/excited-01/build_package.py

The builder reads the frozen R1 inventory and pair queue, resolves every endpoint
from the inventory, and writes screening.json, search-log.json and
coverage-fragment.json next to itself. It does not write outside the package
directory and it does not touch coverage.json or any accepted artifact.
"""

import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

INV_REL = 'audit_boundary/statement-inventory.json'
QUEUE_REL = 'audit_boundary/pair-queue.json'
CLUSTER_REL = 'audit_boundary/cluster-plan.json'
BOUNDARY_REL = 'audit_boundary/BOUNDARY.md'
REGISTRY_REL = 'relation_audit/registry.json'
PROBE_REL = 'bounded_audit/r4/excited-01/probes/E1-probe.lean'

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']

PAIR_IDS = [
    'P-Hammond-Kasha',
    'P-Hammond-KashaVavilov',
    'P-Hammond-SternVolmer',
    'P-Hammond-QuantumYield',
    'P-Hammond-FluorPhos',
    'P-Hammond-EnergyGapLaw',
    'P-Hammond-StokesShift',
    'P-Hammond-ICvsISC',
    'P-Hammond-Forster',
    'P-Hammond-Einstein',
    'P-BEP-Kasha',
    'P-BEP-KashaVavilov',
    'P-BEP-SternVolmer',
    'P-BEP-QuantumYield',
    'P-BEP-FluorPhos',
    'P-BEP-EnergyGapLaw',
]


def sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


INV = load(INV_REL)
QUEUE = load(QUEUE_REL)
CLUSTER = load(CLUSTER_REL)
INV_BY_ID = {r['id']: r for r in INV['statements']}
QUEUE_BY_ID = {r['pairId']: r for r in QUEUE['pairs']}


def endpoint(stmt_id, form='definition'):
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


SNAP = {
    'id': 'snap-bounded-audit-2026-11-04',
    'date': '2026-11-04',
    'round': 'R4',
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

PROBE_SHA = sha_file(os.path.join(ROOT, PROBE_REL))
COMPILE_LOG = 'bounded_audit/r4/excited-01/probes/compile.log'
SCAN_LOG = 'bounded_audit/r4/excited-01/probes/scan.log'

CONTEXT_LIBRARY = {}
SCOPE_LIBRARY = {}


def ctx(cid, fields, reading, provenance):
    CONTEXT_LIBRARY[cid] = {
        'fields': fields,
        'physicalReading': reading,
        'provenance': provenance,
    }
    return cid


def scope(sid, description, domain):
    SCOPE_LIBRARY[sid] = {'description': description, 'domain': domain}
    return sid


def q_scope(sid):
    return {
        'id': sid,
        'description': SCOPE_LIBRARY[sid]['description'],
        'domain': SCOPE_LIBRARY[sid]['domain'],
        'snapshot': SNAP['id'],
    }


def premise(predict, ids, defs):
    return {'predicate': predict, 'premiseIds': ids, 'definitions': defs}


def defn(pid, pred, statement, load):
    return {'id': pid, 'predicate': pred, 'statement': statement, 'loadBearing': load}


def translation(tid, term, requirement, reason=None):
    out = {'id': tid, 'term': term, 'requirement': requirement}
    if tid in ('none-declared', 'candidate-not-total'):
        out['reason'] = reason
    return out


# ---------------------------------------------------------------- contexts
ctx('HammondEnergyGapCtx', ['lam : ℝ', 'x : ℝ'],
    'Equal-curvature two-parabola context: reorganization energy lam and driving force '
    'x = -ΔG°. The forward barrier is (lam - x)^2/(4 lam) and the crossing coordinate is '
    '(lam - x)/(2 lam); the barrierless point is x = lam.',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#HammondEnergyGapCtx')
ctx('BepEnergyGapCtx', ['lam : ℝ', 'x : ℝ'],
    'Equal-curvature two-parabola context shared by BEP and the energy-gap law: reorganization '
    'energy lam and driving force x = -ΔG°; the BEP coefficient is 1/2 - x/(2 lam) and the '
    'energy-gap-law inverted region is lam < x.',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#BepEnergyGapCtx')
ctx('HammondKashaCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
    'Kasha internal-conversion step read in the Marcus form: pre-exponential A, reorganization '
    'energy lam, thermal energy kB·T, and the S2→S1 gap x. The IC rate is A exp(-barrier/(kB T)); '
    'the Hammond crossing coordinate is (lam - x)/(2 lam).',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#HammondKashaCtx')
ctx('HammondICvsISCCtx', ['lam : ℝ', 'x : ℝ'],
    'Equal-curvature two-parabola barrier context for the IC channel: reorganization energy lam '
    'and gap x. Both the IC Franck–Condon barrier and the Hammond forward gap are copies of the '
    'same kernel barrier.',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#HammondICvsISCCtx')
ctx('BepKashaCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
    'BEP coefficient and Kasha Marcus-form IC rate on the same step: pre-exponential A, '
    'reorganization energy lam, thermal energy kB·T, and gap x.',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#BepKashaCtx')
ctx('HammondStokesCtx', ['lam : ℝ', 'e00 : ℝ'],
    'Displaced equal-curvature oscillator: ground surface lam q^2 and excited surface '
    'lam (q - 1)^2 + e00. The vertical absorption at q = 0 is the gap between the excited and '
    'ground surfaces.',
    'bounded_audit/r4/excited-01/probes/E1-probe.lean#HammondStokesCtx')
ctx('HammondKashaVavilovCandidateCtx',
    ['lam : ℝ', 'x : ℝ', 'rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ'],
    'Candidate juxtaposition of a Kasha–Vavilov ladder (radiative and IC rate functions over '
    'levels 0..N) and the Hammond two-parabola barrier (lam, x). No total map from a ladder '
    'level or a ladder rate to a driving force is declared.',
    'bounded_audit/r4/excited-01/screening.json#HammondKashaVavilovCandidateCtx (candidate; no Lean structure)')
ctx('BepKashaVavilovCandidateCtx',
    ['lam : ℝ', 'x : ℝ', 'rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'N : ℕ'],
    'Candidate juxtaposition of a Kasha–Vavilov ladder and the BEP activation barrier (lam, x). '
    'No total map from a ladder level or a ladder rate to a driving force is declared.',
    'bounded_audit/r4/excited-01/screening.json#BepKashaVavilovCandidateCtx (candidate; no Lean structure)')
ctx('HammondSvCandidateCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ', 'k0 : ℝ', 'kq : ℝ', 'q : ℝ'],
    'Candidate juxtaposition of a Hammond barrier (lam, x) and a Stern–Volmer concentration '
    'channel k0 + kq q. No total translation between the quencher concentration q and the '
    'driving force x is declared.',
    'bounded_audit/r4/excited-01/screening.json#HammondSvCandidateCtx (candidate; no Lean structure)')
ctx('BepSvCandidateCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ', 'k0 : ℝ', 'kq : ℝ', 'q : ℝ'],
    'Candidate juxtaposition of a BEP activation barrier (lam, x) and a Stern–Volmer '
    'concentration channel k0 + kq q. No total translation between q and x is declared.',
    'bounded_audit/r4/excited-01/screening.json#BepSvCandidateCtx (candidate; no Lean structure)')
ctx('HammondQyCandidateCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ', 'kr : ℝ'],
    'Candidate two-channel yield context: a radiative channel kr and an IC channel that would be '
    'the Arrhenius rate over the Hammond forward barrier. The yield vector is not a delivered '
    'object and no channel identification is declared.',
    'bounded_audit/r4/excited-01/screening.json#HammondQyCandidateCtx (candidate; no Lean structure)')
ctx('BepQyCandidateCtx', ['A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ', 'kr : ℝ'],
    'Candidate two-channel yield context: a radiative channel kr and an IC channel that would be '
    'the Arrhenius rate over the BEP activation barrier. No channel identification is declared.',
    'bounded_audit/r4/excited-01/screening.json#BepQyCandidateCtx (candidate; no Lean structure)')
ctx('HammondFpCandidateCtx', ['kF : ℝ', 'kISC : ℝ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
    'Candidate FluorPhos competition context: kF and kISC are free rates, and the IC channel '
    'would be the Arrhenius rate over the Hammond forward barrier. The identification of kIC '
    'with that barrier-controlled rate is not delivered.',
    'bounded_audit/r4/excited-01/screening.json#HammondFpCandidateCtx (candidate; no Lean structure)')
ctx('BepFpCandidateCtx', ['kF : ℝ', 'kISC : ℝ', 'A : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
    'Candidate FluorPhos competition context with the IC channel read as the Arrhenius rate over '
    'the BEP activation barrier. The identification is not delivered.',
    'bounded_audit/r4/excited-01/screening.json#BepFpCandidateCtx (candidate; no Lean structure)')
ctx('HammondEinsteinCandidateCtx', ['A : ℝ', 'kNR : ℝ', 'lam : ℝ', 'kB : ℝ', 'T : ℝ', 'x : ℝ'],
    'Candidate radiative-yield context: the Einstein two-channel yield A/(A + kNR) with kNR '
    'would be the Arrhenius rate over the Hammond forward barrier. No such identification is '
    'declared.',
    'bounded_audit/r4/excited-01/screening.json#HammondEinsteinCandidateCtx (candidate; no Lean structure)')
ctx('HammondForsterCandidateCtx', ['R : ℝ', 'tauD : ℝ', 'lam : ℝ', 'x : ℝ'],
    'Candidate juxtaposition of a Förster transfer geometry (donor–acceptor separation R, donor '
    'lifetime tauD) and a Hammond two-parabola barrier (lam, x). The two state spaces share no '
    'scalar and no total map between them is declared.',
    'bounded_audit/r4/excited-01/screening.json#HammondForsterCandidateCtx (candidate; no Lean structure)')

# ---------------------------------------------------------------- scopes
scope('scope-R4-E1-barrierless',
      'Barrierless-locus scope of the equal-curvature two-parabola model: lam ≠ 0 or lam > 0, '
      'all driving forces x; the compared predicates are zero-barrier and inverted-region loci.',
      'all (lam, x) in ℝ² with the declared curvature premise; no other restriction.')
scope('scope-R4-E1-rate-geometry',
      'Rate/geometry scope of the Marcus-form internal-conversion step: A > 0, kB·T > 0, lam > 0, '
      'all driving forces x; the compared predicates are a rate maximum and a crossing-coordinate '
      'boundary.',
      'all (A, lam, kB, T, x) in ℝ⁵ with the declared positivity premises.')
scope('scope-R4-E1-barrier-pin',
      'Definitional barrier-pin scope: all (lam, x) in ℝ²; the compared terms are the two barrier '
      'copies, both totalized at lam = 0.',
      'all (lam, x) in ℝ²; no premise.')
scope('scope-R4-E1-surface-observable',
      'Vertical-absorption observable scope: all (lam, e00) in ℝ²; the channel observes the '
      'absorption energy at the ground-state geometry.',
      'all (lam, e00) in ℝ²; no premise.')
scope('scope-R4-E1-candidate-bridge',
      'Scoped search for a delivered statement-level bridge between a two-parabola barrier and a '
      'partner-theory rate, ladder, or yield. No negative claim outside the named search.',
      'the named pair and the statements/kinds/contexts recorded in its search-log entry.')
scope('scope-R4-E1-jurisdiction',
      'Jurisdiction scope of a query for which no shared context and no total translation exists. '
      'This records jurisdiction, not logical absence.',
      'the named pair and the two endpoint statements; the declared translations are not total.')

NS = 'PhotoLean.RelationAudit.BoundedAudit.R4Excited01.'
PROBE_EVIDENCE = {
    'hammondEnergyGapBarrierZeroEquiv': {
        'kind': 'equivalence',
        'declaration': NS + 'hammondEnergyGapBarrierZeroEquiv',
        'kindTheorem': NS + 'hammondEnergyGapBarrierZeroEquiv_kind',
        'underlying': [
            {'declaration': 'PhotoLean.Relations.eg_boundary_eq_tsCoord_zero',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 920,
             'role': 'delivered §15 boundary row consumed by the proof'},
            {'declaration': 'PhotoLean.EnergyGapLaw.cert_nrBarrier',
             'sourceArtifact': 'PhotoLean/EnergyGapLaw/Basic.lean', 'sourceLine': 67,
             'role': 'delivered kernel pin of the energy-gap-law barrier'},
        ],
        'justification': 'The probe proves the barrier-zero equivalence and pins it as an '
                         'equivalence certificate; the delivered boundary row supplies the '
                         'coordinate half and the kernel pin supplies the barrier identity.',
    },
    'bepEnergyGapInvertedEquiv': {
        'kind': 'equivalence',
        'declaration': NS + 'bepEnergyGapInvertedEquiv',
        'kindTheorem': NS + 'bepEnergyGapInvertedEquiv_kind',
        'underlying': [
            {'declaration': 'PhotoLean.Relations.transfer_eq_tsCoord_bridge',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 144,
             'role': 'delivered §2 BEP/Hammond coefficient bridge consumed by the proof'},
            {'declaration': 'PhotoLean.Relations.tsCoord_lt_zero_iff_inverted',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 164,
             'role': 'delivered §2 inverted-region sign row consumed by the proof'},
        ],
        'justification': 'The probe composes the delivered transfer/coordinate bridge with the '
                         'delivered inverted-region sign row; the certificate is an equivalence '
                         'of the two regime predicates.',
    },
    'hammondKashaICMaxEquiv': {
        'kind': 'equivalence',
        'declaration': NS + 'hammondKashaICMaxEquiv',
        'kindTheorem': NS + 'hammondKashaICMaxEquiv_kind',
        'underlying': [
            {'declaration': 'PhotoLean.Relations.kernel_marcusIC',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 339,
             'role': 'delivered §7 kernel identity of the Kasha IC rate consumed by the proof'},
            {'declaration': 'PhotoLean.Relations.kernel_barrier_eq_hammond',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 105,
             'role': 'delivered §1 kernel/Hammond barrier pin used by the chemical reading'},
        ],
        'justification': 'The probe rewrites the Kasha rate through the delivered kernel identity '
                         'and proves the rate-maximum/coordinate-boundary equivalence.',
    },
    'hammondICvsISCBarrierPin': {
        'kind': 'definitionalIdentity',
        'declaration': NS + 'hammondICvsISCBarrierPin',
        'kindTheorem': NS + 'hammondICvsISCBarrierPin_kind',
        'underlying': [
            {'declaration': 'PhotoLean.ICvsISC.cert_fcBarrier',
             'sourceArtifact': 'PhotoLean/ICvsISC/Basic.lean', 'sourceLine': 67,
             'role': 'delivered pin of the IC barrier to the kernel barrier'},
            {'declaration': 'PhotoLean.Relations.kernel_barrier_eq_hammond',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 105,
             'role': 'delivered pin of the kernel barrier to the Hammond forward gap'},
        ],
        'justification': 'The IC barrier and the Hammond forward gap are both copies of the kernel '
                         'barrier; the probe records a fresh rfl-only DefEq pin over the two '
                         'delivered declarations.',
    },
    'bepKashaTransferZeroEquiv': {
        'kind': 'equivalence',
        'declaration': NS + 'bepKashaTransferZeroEquiv',
        'kindTheorem': NS + 'bepKashaTransferZeroEquiv_kind',
        'underlying': [
            {'declaration': 'PhotoLean.Relations.transfer_eq_tsCoord_bridge',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 144,
             'role': 'delivered §2 coefficient/coordinate bridge consumed by the proof'},
            {'declaration': 'PhotoLean.Relations.kernel_marcusIC',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 339,
             'role': 'delivered §7 kernel identity used by the shared §3 pin'},
        ],
        'justification': 'The probe composes the delivered coefficient bridge with the §3 '
                         'rate/coordinate pin to obtain the coefficient-zero/rate-maximum '
                         'equivalence.',
    },
    'hammondStokesAbsorptionBridge': {
        'kind': 'observationalEquivalence',
        'declaration': NS + 'hammondStokesAbsorptionBridge',
        'kindTheorem': NS + 'hammondStokesAbsorptionBridge_kind',
        'underlying': [
            {'declaration': 'PhotoLean.StokesShift.absEnergy_eq',
             'sourceArtifact': 'PhotoLean/StokesShift/Criterion.lean', 'sourceLine': 48,
             'role': 'delivered §4 absorption-energy law consumed by the proof'},
            {'declaration': 'PhotoLean.Relations.kernel_productSurface_eq_hammond',
             'sourceArtifact': 'PhotoLean/Relations.lean', 'sourceLine': 134,
             'role': 'delivered §1 kernel/Hammond product-surface pin used by the chemical reading'},
        ],
        'justification': 'The probe proves equality of the declared absorption-energy channel on '
                         'its whole domain and pins the certificate as an observational '
                         'equivalence.',
    },
}


def certified_evidence(qid, key):
    pe = PROBE_EVIDENCE[key]
    return {
        'type': 'r4-probe-certificate',
        'certificateId': qid,
        'kind': pe['kind'],
        'probe': {
            'path': PROBE_REL,
            'sha256': PROBE_SHA,
            'declaration': pe['declaration'],
            'kindCheckTheorem': pe['kindTheorem'],
            'buildCommand': 'proofs/scripts/lake env lean ' + PROBE_REL,
            'log': COMPILE_LOG,
        },
        'underlyingTheorems': pe['underlying'],
        'axiomFootprint': ALLOWED_AXIOMS,
        'allowedAxioms': ALLOWED_AXIOMS,
        'justification': pe['justification'],
    }


def scoped_evidence(qid, search_id, summary):
    return {
        'type': 'scoped-search',
        'searchLogRef': search_id,
        'candidateSummary': summary,
    }


QUERIES = []
SEARCHES = []


def add_query(pair, qid, source, target, title, question, rationale, context,
              left_tr, right_tr, premises, scope_id, kind, kind_rationale,
              falsification, status, evidence, prov_kind, prov_locator,
              channels=None, extra=None):
    q = {
        'queryId': qid,
        'pairId': pair,
        'title': title,
        'chemicalQuestion': question,
        'chemicalRationale': rationale,
        'endpoints': {
            'source': endpoint(source),
            'target': endpoint(target, 'theorem' if INV_BY_ID[target]['declarationKind'] == 'theorem' else 'definition'),
        },
        'sharedContext': {
            'id': context,
            'fields': CONTEXT_LIBRARY[context]['fields'],
            'physicalReading': CONTEXT_LIBRARY[context]['physicalReading'],
            'provenance': CONTEXT_LIBRARY[context]['provenance'],
        },
        'translations': {'left': left_tr, 'right': right_tr},
        'premises': premises,
        'observationChannels': channels or [],
        'scope': q_scope(scope_id),
        'expectedKind': kind,
        'expectedKindRationale': kind_rationale,
        'falsificationCondition': falsification,
        'outcome': {
            'status': status,
            'rationale': '',
            'evidence': evidence,
        },
        'provenance': {
            'kind': prov_kind,
            'sourceArtifact': PROBE_REL if prov_kind == 'r4-probe-certificate'
                              else ('bounded_audit/r4/excited-01/search-log.json'
                                    if prov_kind == 'scoped-search'
                                    else 'bounded_audit/r4/excited-01/search-log.json'),
            'locator': prov_locator,
        },
    }
    if extra:
        q.update(extra)
    QUERIES.append(q)
    return q


P_TRUE = lambda c: 'fun _ : %s => True' % c
ID = lambda c: translation('identity', 'fun δ : %s => δ' % c,
                           'Both statement contexts are the shared context; the translation is total on the declared domain.')

# ---------------------------------------------------------------- certified queries
add_query(
    'P-Hammond-EnergyGapLaw',
    'Q-R4-E1-HEG-01',
    'stmt-Hammond-PhotoLean-Hammond-tsCoord',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-nrBarrier',
    'The energy-gap-law barrier vanishes exactly at the Hammond barrierless geometry',
    'At the same reorganization energy and driving force, does the energy-gap-law nonradiative '
    'barrier vanish exactly when the Hammond transition-state coordinate reaches the reactant well?',
    'Both theories read the same equal-curvature two-parabola crossing. The energy-gap law reports '
    'the nonradiative barrier as nrBarrier = (lam - x)^2/(4 lam); Hammond reports the crossing '
    'coordinate as tsCoord = (lam - x)/(2 lam) and its forward barrier as gapReactant. The '
    'nonradiative barrier is zero exactly at x = lam, which is exactly where the Hammond '
    'transition state reaches the reactant geometry. The delivered §15 boundary row already '
    'identifies the kernel coordinate zero with lam = x; this query asks whether the '
    'energy-gap-law barrier zero and the Hammond coordinate zero are the same physical locus. '
    'That is a statement about where a nonradiative channel becomes barrierless, not a notation '
    'match.',
    'HammondEnergyGapCtx', ID('HammondEnergyGapCtx'), ID('HammondEnergyGapCtx'),
    premise('fun δ : HammondEnergyGapCtx => δ.lam ≠ 0', ['hammondEnergyGap.lamNeZero'],
            [defn('hammondEnergyGap.lamNeZero', 'fun δ : HammondEnergyGapCtx => δ.lam ≠ 0',
                  'lam ≠ 0: the reorganization energy is nonzero, so both barrier presentations '
                  'are well defined.', 'Consumed by the division clearing in the checked certificate.')]),
    'scope-R4-E1-barrierless', 'equivalence',
    'Both sides are propositions on the same (lam, x) context; the certificate is an iff under '
    'the declared nonzero-curvature premise.',
    'A context with lam ≠ 0 at which nrBarrier lam x = 0 but Hammond.tsCoord lam x ≠ 0 (or '
    'conversely) would refute the equivalence.',
    'certified', certified_evidence('Q-R4-E1-HEG-01', 'hammondEnergyGapBarrierZeroEquiv'),
    'r4-probe-certificate', NS + 'hammondEnergyGapBarrierZeroEquiv')
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the nonradiative barrier zero is equivalent to the '
    'Hammond crossing-coordinate zero under lam ≠ 0. The proof consumes the delivered §15 '
    'boundary row and the energy-gap-law kernel pin.')

add_query(
    'P-BEP-EnergyGapLaw',
    'Q-R4-E1-BEG-01',
    'stmt-BEP-PhotoLean-BEP-transfer',
    'stmt-EnergyGapLaw-PhotoLean-EnergyGapLaw-InvertedGap',
    'The energy-gap inverted region is exactly the negative BEP transfer-coefficient region',
    'At positive reorganization energy, is the energy-gap-law inverted region (driving force '
    'beyond lam) exactly the driving-force range where the BEP/Brønsted transfer coefficient '
    'becomes negative?',
    'The energy-gap law calls the gap inverted when lam < x. The BEP coefficient is '
    'transfer = 1/2 - x/(2 lam), the linear-response slope of the same two-parabola barrier. The '
    'delivered bridge identifies transfer with the Hammond transition-state coordinate, and the '
    'delivered §2 row identifies a negative coordinate with the Marcus inverted region. The query '
    'asks whether the two theories place the regime boundary at the same driving force: the point '
    'where the barrier starts to fall as the driving force grows is the point where the '
    'energy-gap law calls the gap inverted. That is a statement about the sign of the free-energy '
    'dependence, not a shape similarity.',
    'BepEnergyGapCtx', ID('BepEnergyGapCtx'), ID('BepEnergyGapCtx'),
    premise('fun δ : BepEnergyGapCtx => 0 < δ.lam', ['bepEnergyGap.lamPositive'],
            [defn('bepEnergyGap.lamPositive', 'fun δ : BepEnergyGapCtx => 0 < δ.lam',
                  '0 < lam: the curvature is positive, so the inverted region has the physical '
                  'orientation lam < x.', 'Consumed by the delivered sign row and the proof.')]),
    'scope-R4-E1-barrierless', 'equivalence',
    'Both sides are propositions on the same (lam, x) context; the certificate is an iff under '
    'positive curvature.',
    'A context with lam > 0 at which exactly one of InvertedGap and transfer < 0 holds would '
    'refute the equivalence.',
    'certified', certified_evidence('Q-R4-E1-BEG-01', 'bepEnergyGapInvertedEquiv'),
    'r4-probe-certificate', NS + 'bepEnergyGapInvertedEquiv')
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the energy-gap-law inverted region and the negative BEP '
    'coefficient region coincide under positive curvature. The proof consumes the delivered '
    'transfer/coordinate bridge and the delivered inverted-region sign row.')

add_query(
    'P-Hammond-Kasha',
    'Q-R4-E1-HK-01',
    'stmt-Hammond-PhotoLean-Hammond-tsCoord',
    'stmt-Kasha-PhotoLean-Kasha-marcusIC',
    'Kasha internal conversion is at its pre-exponential exactly at the Hammond barrierless geometry',
    'Under the declared Marcus form of the Kasha S2→S1 internal-conversion rate, does that rate '
    'reach its pre-exponential factor A exactly when the Hammond transition-state coordinate '
    'reaches the reactant well?',
    'Kasha\'s ladder model makes the S2→S1 internal-conversion channel a Marcus-form rate '
    'marcusIC = A exp(-barrier/(kB T)); Hammond reports the same equal-curvature forward barrier '
    'and its crossing coordinate tsCoord. The rate is maximal, equal to A, exactly when the '
    'barrier vanishes, which is exactly when tsCoord = 0. The query connects a Kasha rate '
    'observable to a Hammond geometric observable: internal conversion is activationless exactly '
    'at the reactant-geometry crossing. The Marcus-form identification of the IC channel is a '
    'declared modelling premise of the Kasha module; the query does not assert that all internal '
    'conversion is a Marcus process.',
    'HammondKashaCtx', ID('HammondKashaCtx'), ID('HammondKashaCtx'),
    premise('fun δ : HammondKashaCtx => ∀ p ∈ hammondKashaPremises, p.predicate δ',
            ['kasha.preExponentialPositive', 'thermal.energyPositive', 'hammond.curvaturePositive'],
            [defn('kasha.preExponentialPositive', 'fun δ : HammondKashaCtx => 0 < δ.A',
                  '0 < A: the pre-exponential factor is positive.', 'Consumed to cancel A.'),
             defn('thermal.energyPositive', 'fun δ : HammondKashaCtx => 0 < δ.kB * δ.T',
                  '0 < kB·T: the thermal energy is positive.', 'Consumed to clear the exponential argument.'),
             defn('hammond.curvaturePositive', 'fun δ : HammondKashaCtx => 0 < δ.lam',
                  '0 < lam: the reorganization energy is positive.', 'Consumed by the barrier algebra.')]),
    'scope-R4-E1-rate-geometry', 'equivalence',
    'Both sides are propositions on the same (A, lam, kB, T, x) context; the certificate is an '
    'iff under the declared positivity premises.',
    'A context satisfying the positivity premises at which marcusIC = A but tsCoord ≠ 0 (or '
    'conversely) would refute the equivalence.',
    'certified', certified_evidence('Q-R4-E1-HK-01', 'hammondKashaICMaxEquiv'),
    'r4-probe-certificate', NS + 'hammondKashaICMaxEquiv')
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the Kasha IC rate equals its pre-exponential exactly at '
    'the Hammond coordinate zero under the positivity premises. The proof consumes the delivered '
    'kernel identity of the Kasha IC rate.')

add_query(
    'P-Hammond-ICvsISC',
    'Q-R4-E1-HIC-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-ICvsISC-PhotoLean-ICvsISC-fcBarrier',
    'The IC Franck–Condon barrier is the Hammond forward reactant gap',
    'At the same reorganization energy and gap, is the Franck–Condon barrier of the '
    'internal-conversion channel the same equal-curvature forward barrier that Hammond reports as '
    'its reactant gap?',
    'The ICvsISC theory computes its Franck–Condon barrier as fcBarrier = (lam - x)^2/(4 lam), a '
    'channel-specific copy of the shared kernel barrier. Hammond computes the forward barrier '
    'gapReactant from the crossing of the same two harmonic surfaces. Both are the same physical '
    'barrier of the equal-curvature displaced-oscillator model, with independent definitions and '
    'independent provenance. The query asks for the definitional identity of the two barrier '
    'copies. It is a model-level statement: it does not assert that the microscopic IC barrier is '
    'a chemical reaction barrier in every system.',
    'HammondICvsISCCtx', ID('HammondICvsISCCtx'), ID('HammondICvsISCCtx'),
    premise(P_TRUE('HammondICvsISCCtx'), [], []),
    'scope-R4-E1-barrier-pin', 'definitionalIdentity',
    'The two endpoints are real-valued barrier definitions with identical bodies; the certificate '
    'is a fresh rfl-only DefEq pin.',
    'A context at which fcBarrier and gapReactant take different values would refute the '
    'definitional identity.',
    'certified', certified_evidence('Q-R4-E1-HIC-01', 'hammondICvsISCBarrierPin'),
    'r4-probe-certificate', NS + 'hammondICvsISCBarrierPin')
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the two barrier copies are definitionally equal. The '
    'delivered pins identify both with the shared kernel barrier, and the probe carries the fresh '
    'rfl-only DefEq pin.')

add_query(
    'P-BEP-Kasha',
    'Q-R4-E1-BK-01',
    'stmt-BEP-PhotoLean-BEP-transfer',
    'stmt-Kasha-PhotoLean-Kasha-marcusIC',
    'The BEP coefficient vanishes exactly at the Kasha IC-rate maximum',
    'Does the BEP/Brønsted transfer coefficient vanish exactly where the Kasha Marcus-form '
    'internal-conversion rate reaches its pre-exponential value?',
    'The BEP transfer coefficient is the linear-response slope of the same two-parabola barrier; '
    'the delivered bridge identifies it with the Hammond transition-state coordinate. The Kasha '
    'IC rate is A exp(-barrier/(kB T)), maximal at zero barrier. The query asks whether the BEP '
    'coefficient zero and the Kasha IC rate maximum are the same driving-force point: the point '
    'where the barrier has no first-order free-energy dependence is the point where the '
    'nonradiative channel is activationless. The statement is about the two observables, not a '
    'restatement of either definition.',
    'BepKashaCtx', ID('BepKashaCtx'), ID('BepKashaCtx'),
    premise('fun δ : BepKashaCtx => ∀ p ∈ bepKashaPremises, p.predicate δ',
            ['kasha.preExponentialPositive', 'thermal.energyPositive', 'bep.curvaturePositive'],
            [defn('kasha.preExponentialPositive', 'fun δ : BepKashaCtx => 0 < δ.A',
                  '0 < A: the pre-exponential factor is positive.', 'Consumed to cancel A.'),
             defn('thermal.energyPositive', 'fun δ : BepKashaCtx => 0 < δ.kB * δ.T',
                  '0 < kB·T: the thermal energy is positive.', 'Consumed to clear the exponential argument.'),
             defn('bep.curvaturePositive', 'fun δ : BepKashaCtx => 0 < δ.lam',
                  '0 < lam: the reorganization energy is positive.', 'Consumed by the coefficient algebra.')]),
    'scope-R4-E1-rate-geometry', 'equivalence',
    'Both sides are propositions on the same (A, lam, kB, T, x) context; the certificate is an '
    'iff under the declared positivity premises.',
    'A context satisfying the positivity premises at which transfer = 0 but marcusIC ≠ A (or '
    'conversely) would refute the equivalence.',
    'certified', certified_evidence('Q-R4-E1-BK-01', 'bepKashaTransferZeroEquiv'),
    'r4-probe-certificate', NS + 'bepKashaTransferZeroEquiv')
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the BEP coefficient zero is equivalent to the Kasha '
    'IC-rate maximum under the positivity premises. The proof consumes the delivered '
    'coefficient/coordinate bridge and the shared §3 pin.')

add_query(
    'P-Hammond-StokesShift',
    'Q-R4-E1-HSS-01',
    'stmt-Hammond-PhotoLean-Hammond-productSurface',
    'stmt-StokesShift-PhotoLean-StokesShift-absEnergy',
    'The Stokes absorption maximum is the Hammond vertical surface gap',
    'Is the Stokes vertical absorption energy the same physical gap as the Hammond product-surface '
    'energy at the ground-state geometry minus the Hammond reactant-surface energy there?',
    'StokesShift defines the absorption maximum as the vertical transition at the ground-state '
    'minimum, absEnergy = s1Surface(0) - s0Surface(0). Hammond\'s two surfaces are the displaced '
    'ground and excited surfaces of the same equal-curvature oscillator: productSurface at q = 0 '
    'minus reactantSurface at q = 0 is exactly the vertical gap. The query identifies the '
    'spectroscopic band maximum with the surface gap; it is an observable-level statement, and it '
    'does not claim that every measured Stokes shift is a two-parabola reorganization energy.',
    'HammondStokesCtx', ID('HammondStokesCtx'), ID('HammondStokesCtx'),
    premise(P_TRUE('HammondStokesCtx'), [], []),
    'scope-R4-E1-surface-observable', 'observationalEquivalence',
    'Both readings are real-valued absorption energies on the same (lam, e00) context; the '
    'certificate is equality of every declared channel observation.',
    'A context at which the Stokes absorption energy differs from the Hammond vertical surface '
    'gap would refute the equivalence.',
    'certified', certified_evidence('Q-R4-E1-HSS-01', 'hammondStokesAbsorptionBridge'),
    'r4-probe-certificate', NS + 'hammondStokesAbsorptionBridge',
    channels=[{
        'id': 'absorptionEnergy',
        'observedValueType': 'ℝ',
        'inputDomain': 'Unit (the single vertical-absorption configuration)',
        'domainNonempty': True,
        'leftObs': 'fun δ _ => StokesShift.absEnergy δ.lam δ.e00',
        'rightObs': ('fun δ _ => Hammond.productSurface δ.lam δ.e00 0 '
                     '- Hammond.reactantSurface δ.lam 0'),
    }])
QUERIES[-1]['outcome']['rationale'] = (
    'The probe certificate is checked: the declared absorption-energy channel is equal on its '
    'whole domain. The proof consumes the delivered absorption-energy law and the Hammond '
    'surface definitions.')

# ---------------------------------------------------------------- non-certified queries
PARTNER = {
    'KashaVavilov': {
        'imports': 'Mathlib; PhotoLean.Kasha.Basic; PhotoLean.Kasha.Criterion; '
                   'PhotoLean.KashaVavilov.Basic; PhotoLean.KashaVavilov.Criterion',
        'refs': 'PhotoLean/KashaVavilov/Basic.lean:39 (a fidelity-script path inside a comment); '
                'no delivered declaration references Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 939,
        'noedge_text': 'KashaVavilov ↔ Marcus / Hammond / BEP — no edge: the D2 layer is about '
                       'branching laws of the ladder, not barriers or coordinates; its only contact '
                       'with the two-parabola family runs through Kasha §7 (Kasha.marcusIC).',
        'key_def': 'PhotoLean/KashaVavilov/Basic.lean#SpecSame',
    },
    'SternVolmer': {
        'imports': 'Mathlib; PhotoLean.SternVolmer.Basic; PhotoLean.SternVolmer.Criterion; '
                   'PhotoLean.SternVolmer.RatModel',
        'refs': 'PhotoLean/SternVolmer/RatModel.lean:37, Basic.lean:33, Instances.lean:30 '
                '(fidelity-script paths inside comments); no delivered declaration references '
                'Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 945,
        'noedge_text': 'SternVolmer ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / '
                       'SymmetryFactor — no edge: the SV model has no energy surface, no '
                       'descriptor axis, no geometry; its contacts run through QuantumYield.',
        'key_def': 'PhotoLean/SternVolmer/Basic.lean#dynDecay',
    },
    'QuantumYield': {
        'imports': 'Mathlib; PhotoLean.QuantumYield.Basic; PhotoLean.QuantumYield.RatModel',
        'refs': 'PhotoLean/QuantumYield/Basic.lean:24, Instances.lean:30 (fidelity-script paths '
                'inside comments); no delivered declaration references Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 948,
        'noedge_text': 'QuantumYield ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / '
                       'SymmetryFactor — no edge: the parallel-channel calculus is purely '
                       'algebraic; the energy-side theories enter only through the specific rates '
                       'that fill its channels.',
        'key_def': 'PhotoLean/QuantumYield/Basic.lean#yieldOf',
    },
    'FluorPhos': {
        'imports': 'Mathlib; PhotoLean.FluorPhos.Basic; PhotoLean.FluorPhos.Criterion; '
                   'PhotoLean.FluorPhos.RatModel',
        'refs': 'PhotoLean/FluorPhos/RatModel.lean:24, Criterion.lean:51, Instances.lean:30, '
                'Basic.lean:22 (fidelity-script paths inside comments); no delivered declaration '
                'references Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 952,
        'noedge_text': 'FluorPhos ↔ Marcus / Hammond / BEP / Sabatier / Goldschmidt / '
                       'SymmetryFactor / StokesShift / EnergyGapLaw / Forster / Einstein — no edge '
                       'except through QuantumYield; its objects are branch probabilities.',
        'key_def': 'PhotoLean/FluorPhos/Basic.lean#phiF',
    },
    'Forster': {
        'imports': 'Mathlib; PhotoLean.Forster.Basic; PhotoLean.Forster.Criterion; '
                   'PhotoLean.Forster.RatModel',
        'refs': 'PhotoLean/Forster/RatModel.lean:27, Instances.lean:23, Basic.lean:35 '
                '(fidelity-script paths inside comments); no delivered declaration references '
                'Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 964,
        'noedge_text': 'Forster ↔ Marcus / Hammond / BEP / Kasha / KashaVavilov / Sabatier / '
                       'SymmetryFactor / StokesShift / EnergyGapLaw / ICvsISC — no edge: the '
                       'transfer geometry shares no scalar with the energy-surface family.',
        'key_def': 'PhotoLean/Forster/Basic.lean#fretEff6',
    },
    'Einstein': {
        'imports': 'Mathlib; PhotoLean.Einstein.Basic; PhotoLean.Einstein.Criterion; '
                   'PhotoLean.Einstein.RatModel',
        'refs': 'PhotoLean/Einstein/Basic.lean:26 (a fidelity-script path inside a comment); no '
                'delivered declaration references Hammond or BEP',
        'barrier': 'No matches (grep exit 1).',
        'noedge_line': 969,
        'noedge_text': 'Einstein ↔ Marcus / Hammond / BEP / Kasha / KashaVavilov / Sabatier / '
                       'Goldschmidt / SymmetryFactor / StokesShift / Forster — no edge: the '
                       'radiative conversions reach the batch only through the QuantumYield anchor.',
        'key_def': 'PhotoLean/Einstein/Basic.lean#aOfB',
    },
}


def partner_deps(partner):
    p = PARTNER[partner]
    return [
        {'artifact': 'PhotoLean/Relations.lean',
         'locator': '§16 extended no-edge register, line %d' % p['noedge_line'],
         'finding': p['noedge_text']},
        {'artifact': 'PhotoLean/%s/Basic.lean' % partner,
         'locator': p['key_def'],
         'finding': 'The partner object is a free rate/predicate parameter; the module imports '
                    'only Mathlib plus its own theory modules (KashaVavilov additionally '
                    'imports Kasha).'},
        {'artifact': 'PhotoLean/Relations.lean',
         'locator': '§16 workspace dependency note (lines 1025-1029)',
         'finding': 'The photophysics modules import only Mathlib plus their own theory modules '
                    '(plus Kernel/Marcus for the group-B theories); Relations.lean is the only '
                    'cross-theory module.'},
        {'artifact': 'relation_audit/registry.json',
         'locator': 'rec-notestablished-%s' % 'PAIR_PLACEHOLDER',
         'finding': 'The legacy record is a pair-level notEstablished anchor, not a named '
                    'chemical query; it carries no certificate.'},
        {'artifact': 'audit_boundary/statement-inventory.json',
         'locator': 'endpoint rows for this query',
         'finding': 'Both endpoint statements are screening-eligible inventory declarations with '
                    'resolved source artifacts and signature hashes.'},
    ]


def partner_commands(partner, pair, barrier_theory):
    p = PARTNER[partner]
    return [
        {'command': "grep -rn 'Hammond\\|BEP' PhotoLean/%s --include='*.lean'" % partner,
         'purpose': 'Search the partner modules for a delivered Hammond/BEP statement.',
         'result': p['refs'] + '.'},
        {'command': "grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/%s "
                    "--include='*.lean'" % partner,
         'purpose': 'Search the partner modules for any barrier or coordinate declaration.',
         'result': p['barrier']},
        {'command': "grep -h '^import' PhotoLean/%s/*.lean | sort -u" % partner,
         'purpose': 'Measure the partner module dependencies.',
         'result': p['imports'] + '.'},
        {'command': "grep -rn '%s' PhotoLean/%s --include='*.lean'" % (partner, barrier_theory),
         'purpose': 'Search the barrier-theory modules for a reference to the partner theory.',
         'result': 'No matches (grep exit 1).'},
        {'command': 'python3 tools/relation_audit_registry.py --explain-pair %s' % pair,
         'purpose': 'Recompute the accepted legacy disposition for the pair.',
         'result': "label='absence' subtype='registered-absence'; registry record "
                   "'rec-notestablished-%s' status='notEstablished' kind=None certificate=None." % pair},
        {'command': "grep -n '%s' PhotoLean/Relations.lean" % partner,
         'purpose': 'Locate the delivered no-edge registration for the pair.',
         'result': 'First match line %d: %s' % (p['noedge_line'], p['noedge_text'])},
    ]


def add_search(sid, qid, pair, status, scope_id, searched, kinds, contexts, partner,
               barrier_theory, strategies, candidate, gap, rationale, recompute):
    deps = partner_deps(partner)
    deps[3]['locator'] = 'rec-notestablished-%s' % pair
    entry = {
        'searchId': sid,
        'queryId': qid,
        'pairId': pair,
        'status': status,
        'scope': scope_id,
        'snapshot': SNAP['id'],
        'searchedStatements': searched,
        'searchedKinds': kinds,
        'contextsConsidered': contexts,
        'dependenciesConsulted': deps,
        'commands': partner_commands(partner, pair, barrier_theory),
        'strategiesAttempted': strategies,
        'candidateEvidence': candidate,
        'remainingGap': gap,
        'recomputeCommands': recompute,
        'rationale': rationale,
    }
    SEARCHES.append(entry)


def noncert(pair, qid, sid, source, target, title, question, rationale, context,
            left_tr, right_tr, premises, scope_id, kind, kind_rationale, falsification,
            status, candidate_summary, extra_evidence=None):
    ev = scoped_evidence(qid, sid, candidate_summary)
    if extra_evidence:
        ev.update(extra_evidence)
    q = add_query(pair, qid, source, target, title, question, rationale, context,
                  left_tr, right_tr, premises, scope_id, kind, kind_rationale,
                  falsification, status, ev, 'scoped-search', sid)
    return q


CAND_TOTAL = lambda c: translation('candidate-not-total', '',
                                   'No total translation is declared; the candidate context is a '
                                   'juxtaposition of the two state spaces.',
                                   'The delivered corpus contains no total map between the two '
                                   'coordinate systems named in the context.')

# ---- KashaVavilov × Hammond
noncert(
    'P-Hammond-KashaVavilov', 'Q-R4-E1-HKV-01', 'SL-R4-E1-HKV-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'Does the Kasha–Vavilov ladder inherit a barrier window from the Hammond model?',
    'If the S2→S1 internal-conversion loss of a Kasha–Vavilov ladder is the Marcus-form rate at '
    'the Hammond forward barrier, does the Vavilov spectral-agreement predicate become a '
    'statement about a driving-force window around the reorganization energy?',
    'KashaVavilov\'s SpecSame compares normalized spectra across excitation levels; its ladder '
    'rates are free functions. The only contact with the two-parabola family registered in the '
    'delivered corpus runs through Kasha\'s marcusIC, which carries the Hammond/kernel barrier. A '
    'conditional composition would identify the ladder ic with marcusIC and then use the Kasha '
    'window criterion; the query asks whether that composition is delivered. It is a genuine '
    'chemical question because Vavilov behaviour is often discussed as a gap-dependent loss, but '
    'the delivered theory does not identify the ladder rates with a barrier.',
    'HammondKashaVavilovCandidateCtx', CAND_TOTAL('HammondKashaVavilovCandidateCtx'),
    CAND_TOTAL('HammondKashaVavilovCandidateCtx'),
    premise(P_TRUE('HammondKashaVavilovCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'conditionalComposition',
    'The candidate is a typed composition of the ladder rates with the Kasha Marcus-form rate '
    'and the Kasha window criterion; no such delivered composition exists.',
    'A context at which the ladder is Vavilov-conforming but the composed barrier window fails '
    '(or conversely) would refute the candidate composition.',
    'unresolved',
    'Candidate: identify the ladder S2→S1 ic with Kasha.marcusIC at the Hammond barrier and '
    'compose the Kasha window criterion; the delivered corpus has no such conditional '
    'composition.')
QUERIES[-1]['outcome']['rationale'] = (
    'No delivered statement-level composition connects KashaVavilov\'s SpecSame predicate to a '
    'Hammond barrier window; the ladder rates are free functions. The legacy register records no '
    'edge and names Kasha\'s §7 composition as the only contact, so the honest status is '
    'unresolved rather than refuted or a forced edge.')
add_search(
    'SL-R4-E1-HKV-01', 'Q-R4-E1-HKV-01', 'P-Hammond-KashaVavilov', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant', 'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
     'stmt-Kasha-PhotoLean-Kasha-marcusIC', 'kasha.kashaWithin'],
    ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition'],
    ['HammondKashaVavilovCandidateCtx (lam, x, rad, ic, N); no total map from a ladder level or '
     'rate to a driving force'],
    'KashaVavilov', 'Hammond',
    [{'strategy': 'Search the KashaVavilov modules for a delivered theorem mentioning a barrier, '
                  'tsCoord, gapReactant, or eact.',
      'outcome': 'No matches; the module contains no barrier symbol.'},
     {'strategy': 'Try the Kasha §7 composition: identify ic with Kasha.marcusIC at the Hammond '
                  'barrier and carry the Kasha window criterion to SpecSame.',
      'outcome': 'The first step is a modelling premise, and no delivered theorem connects '
                 'SpecSame to KashaWithin; the composition is not delivered.'},
     {'strategy': 'Search the legacy registry for a named query or certificate for the pair.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'KashaVavilov.SpecSame rad ic M N plus ic = Kasha.marcusIC A lam kB T x would '
                   'make spectral agreement a statement about the Hammond barrier window.',
      'status': 'candidate only; no delivered conditional composition.'}],
    'A delivered conditional composition that (i) identifies the ladder S2→S1 ic with '
    'Kasha.marcusIC at the Hammond barrier and (ii) carries the Kasha window criterion to '
    'SpecSame is missing; KashaVavilov\'s ladder rates are free functions.',
    'The legacy register records no edge and names Kasha §7 as the only contact. A candidate '
    'composition remains, so the honest status is unresolved, not refuted and not a forced edge.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/KashaVavilov --include='*.lean'",
     "grep -h '^import' PhotoLean/KashaVavilov/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-KashaVavilov'])

# ---- KashaVavilov × BEP
noncert(
    'P-BEP-KashaVavilov', 'Q-R4-E1-BKV-01', 'SL-R4-E1-BKV-01',
    'stmt-BEP-PhotoLean-BEP-eact',
    'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
    'Does the Kasha–Vavilov ladder inherit a barrier window from the BEP activation energy?',
    'If the S2→S1 internal-conversion loss of a Kasha–Vavilov ladder is an Arrhenius rate over the '
    'BEP activation energy, does the Vavilov spectral-agreement predicate become a statement about '
    'the BEP driving-force window?',
    'KashaVavilov\'s SpecSame compares normalized spectra across excitation levels; its ladder '
    'rates are free functions. BEP supplies an activation barrier eact of the equal-curvature '
    'two-parabola step. A conditional composition would identify the ladder ic with an Arrhenius '
    'rate over eact and carry the Vavilov predicate to a barrier statement; the delivered corpus '
    'has no such composition. The query is chemically meaningful because Vavilov behaviour is '
    'often read as a gap-dependent loss, but the delivered theory leaves the ladder rates free.',
    'BepKashaVavilovCandidateCtx', CAND_TOTAL('BepKashaVavilovCandidateCtx'),
    CAND_TOTAL('BepKashaVavilovCandidateCtx'),
    premise(P_TRUE('BepKashaVavilovCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'conditionalComposition',
    'The candidate is a typed composition of the ladder rates with a BEP-barrier Arrhenius rate; '
    'no such delivered composition exists.',
    'A context at which the ladder is Vavilov-conforming but the composed BEP barrier window '
    'fails (or conversely) would refute the candidate composition.',
    'unresolved',
    'Candidate: identify the ladder S2→S1 ic with an Arrhenius rate over BEP.eact and compose the '
    'Vavilov predicate; the delivered corpus has no such conditional composition.')
QUERIES[-1]['outcome']['rationale'] = (
    'No delivered statement-level composition connects KashaVavilov\'s SpecSame predicate to the '
    'BEP activation barrier; the ladder rates are free functions. The legacy register records no '
    'edge, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-BKV-01', 'Q-R4-E1-BKV-01', 'P-BEP-KashaVavilov', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-BEP-PhotoLean-BEP-eact', 'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
     'stmt-Kasha-PhotoLean-Kasha-marcusIC', 'kasha.kashaWithin'],
    ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition'],
    ['BepKashaVavilovCandidateCtx (lam, x, rad, ic, N); no total map from a ladder level or rate '
     'to a driving force'],
    'KashaVavilov', 'BEP',
    [{'strategy': 'Search the KashaVavilov modules for a delivered BEP activation-energy '
                  'statement.',
      'outcome': 'No matches; the module contains no barrier or eact symbol.'},
     {'strategy': 'Try a conditional composition: identify ic with an Arrhenius rate over '
                  'BEP.eact, then carry the Vavilov predicate.',
      'outcome': 'The identification is a modelling premise and no delivered theorem connects '
                 'SpecSame to a BEP window; the composition is not delivered.'},
     {'strategy': 'Search the legacy registry for a named query or certificate for the pair.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'KashaVavilov.SpecSame rad ic M N plus ic = A exp(-BEP.eact lam x/(kB T)) '
                   'would make spectral agreement a statement about the BEP barrier.',
      'status': 'candidate only; no delivered conditional composition.'}],
    'A delivered conditional composition that (i) identifies the ladder S2→S1 ic with an '
    'Arrhenius rate over BEP.eact and (ii) carries the Vavilov predicate is missing; the ladder '
    'rates are free functions.',
    'The legacy register records no edge. A candidate composition remains, so the honest status '
    'is unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/KashaVavilov --include='*.lean'",
     "grep -h '^import' PhotoLean/KashaVavilov/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-BEP-KashaVavilov'])

# ---- SternVolmer × Hammond
noncert(
    'P-Hammond-SternVolmer', 'Q-R4-E1-HSV-01', 'SL-R4-E1-HSV-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
    'Is the Stern–Volmer added quenching channel a barrier-controlled rate at the Hammond step?',
    'Is the Stern–Volmer added decay channel kq·[Q] the same physical rate as an Arrhenius rate '
    'over the Hammond forward barrier at a quencher-dependent driving force?',
    'SternVolmer models the quencher-dependent decay as k0 + kq q, with kq a free bimolecular '
    'rate; Hammond supplies a barrier for an elementary step. If collisional quenching is an '
    'activated transfer step, kq should be a barrier-controlled rate. A statement-level bridge '
    'would identify the added channel with exp(-Hammond.gapReactant/(kB T)) at a driving force '
    'tied to the quencher. The query asks for that bridge; the missing piece is a translation '
    'between quencher concentration and the driving force.',
    'HammondSvCandidateCtx', CAND_TOTAL('HammondSvCandidateCtx'), CAND_TOTAL('HammondSvCandidateCtx'),
    premise(P_TRUE('HammondSvCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from a barrier-controlled channel to the SV added '
    'channel; no such delivered statement exists.',
    'A context at which the SV added channel differs from the barrier-controlled rate at the same '
    'quencher loading would refute the candidate implication.',
    'unresolved',
    'Candidate: the SV added channel kq·q is an Arrhenius rate over the Hammond barrier at a '
    'quencher-dependent driving force; no delivered identification exists.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered identification of the SV added channel kq·q with an Arrhenius rate over the '
    'Hammond barrier, plus a total translation from quencher concentration to the driving force, '
    'is missing. The legacy register records no edge and routes SV contacts through QuantumYield, '
    'so the honest status is unresolved.')
add_search(
    'SL-R4-E1-HSV-01', 'Q-R4-E1-HSV-01', 'P-Hammond-SternVolmer', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant', 'stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
     'sternvolmer.intensityDyn'],
    ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence'],
    ['HammondSvCandidateCtx (A, lam, kB, T, x, k0, kq, q); no total translation q ↔ x'],
    'SternVolmer', 'Hammond',
    [{'strategy': 'Search the SternVolmer modules for a delivered theorem mentioning a barrier or '
                  'a driving force.',
      'outcome': 'No matches; the module contains no energy-surface symbol.'},
     {'strategy': 'Read the SV added channel kq·q as an Arrhenius rate over the Hammond barrier '
                  'at a quencher-dependent driving force.',
      'outcome': 'The structural analogy is clear, but no translation [Q] → x and no delivered '
                 'theorem exist.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'rate-law analogy',
      'statement': 'SternVolmer.dynDecay k0 kq q = k0 + kq q versus an Arrhenius rate '
                   'A exp(-Hammond.gapReactant lam x/(kB T)).',
      'status': 'candidate only; no statement-level identification is delivered.'}],
    'A delivered identification of the SV added channel kq·q with an Arrhenius rate over the '
    'Hammond barrier, plus a total translation between quencher concentration and the driving '
    'force, is missing.',
    'The legacy register records no edge and routes SV contacts through QuantumYield. A rate-law '
    'analogy remains, so the honest status is unresolved, not refuted and not a forced edge.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/SternVolmer --include='*.lean'",
     "grep -h '^import' PhotoLean/SternVolmer/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-SternVolmer'])

# ---- SternVolmer × BEP
noncert(
    'P-BEP-SternVolmer', 'Q-R4-E1-BSV-01', 'SL-R4-E1-BSV-01',
    'stmt-BEP-PhotoLean-BEP-eact',
    'stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
    'Is the Stern–Volmer added quenching channel a barrier-controlled rate at the BEP step?',
    'Is the Stern–Volmer added decay channel kq·[Q] the same physical rate as an Arrhenius rate '
    'over the BEP activation energy at a quencher-dependent driving force?',
    'SternVolmer models the quencher-dependent decay as k0 + kq q, with kq a free bimolecular '
    'rate; BEP supplies an activation barrier eact for an elementary step. If collisional '
    'quenching is an activated transfer step, kq should be a barrier-controlled rate. A '
    'statement-level bridge would identify the added channel with exp(-BEP.eact/(kB T)) at a '
    'driving force tied to the quencher. The query asks for that bridge; the missing piece is a '
    'translation between quencher concentration and the driving force.',
    'BepSvCandidateCtx', CAND_TOTAL('BepSvCandidateCtx'), CAND_TOTAL('BepSvCandidateCtx'),
    premise(P_TRUE('BepSvCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from a BEP-barrier rate to the SV added channel; no '
    'such delivered statement exists.',
    'A context at which the SV added channel differs from the BEP-barrier rate at the same '
    'quencher loading would refute the candidate implication.',
    'unresolved',
    'Candidate: the SV added channel kq·q is an Arrhenius rate over BEP.eact at a '
    'quencher-dependent driving force; no delivered identification exists.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered identification of the SV added channel kq·q with an Arrhenius rate over BEP.eact, '
    'plus a total translation from quencher concentration to the driving force, is missing. The '
    'legacy register records no edge, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-BSV-01', 'Q-R4-E1-BSV-01', 'P-BEP-SternVolmer', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-BEP-PhotoLean-BEP-eact', 'stmt-SternVolmer-PhotoLean-SternVolmer-dynDecay',
     'sternvolmer.intensityDyn'],
    ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence'],
    ['BepSvCandidateCtx (A, lam, kB, T, x, k0, kq, q); no total translation q ↔ x'],
    'SternVolmer', 'BEP',
    [{'strategy': 'Search the SternVolmer modules for a delivered theorem mentioning a BEP '
                  'activation energy.',
      'outcome': 'No matches; the module contains no energy-surface symbol.'},
     {'strategy': 'Read the SV added channel kq·q as an Arrhenius rate over eact.',
      'outcome': 'The structural analogy is clear, but no translation [Q] → x and no delivered '
                 'theorem exist.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'rate-law analogy',
      'statement': 'SternVolmer.dynDecay k0 kq q = k0 + kq q versus an Arrhenius rate '
                   'A exp(-BEP.eact lam x/(kB T)).',
      'status': 'candidate only; no statement-level identification is delivered.'}],
    'A delivered identification of the SV added channel kq·q with an Arrhenius rate over '
    'BEP.eact, plus a total translation between quencher concentration and the driving force, is '
    'missing.',
    'The legacy register records no edge. A rate-law analogy remains, so the honest status is '
    'unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/SternVolmer --include='*.lean'",
     "grep -h '^import' PhotoLean/SternVolmer/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-BEP-SternVolmer'])

# ---- QuantumYield × Hammond
noncert(
    'P-Hammond-QuantumYield', 'Q-R4-E1-HQY-01', 'SL-R4-E1-HQY-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
    'Does a Hammond-barrier nonradiative channel control the parallel-channel quantum yield?',
    'In a two-channel quantum-yield model whose nonradiative channel is an Arrhenius rate over the '
    'Hammond forward barrier, is the radiative yield a monotone function of that barrier?',
    'QuantumYield defines yieldOf as k_i / Σ k, with every channel rate free. Hammond supplies the '
    'barrier. A bridge would set the nonradiative channel to A exp(-gapReactant/(kB T)) and prove '
    'the yield comparison; the delivered corpus has no theorem identifying a yield channel with a '
    'barrier-controlled rate. The query asks for that composition. It is chemically meaningful '
    'because the fluorescence quantum yield is the standard observable of competition between '
    'radiative decay and activated nonradiative loss.',
    'HammondQyCandidateCtx', CAND_TOTAL('HammondQyCandidateCtx'), CAND_TOTAL('HammondQyCandidateCtx'),
    premise(P_TRUE('HammondQyCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from a barrier-controlled channel to a yield '
    'monotonicity; no such delivered statement exists.',
    'A context at which the yield does not move monotonically with the barrier-controlled channel '
    'would refute the candidate implication.',
    'unresolved',
    'Candidate: a two-channel yield with the nonradiative channel A exp(-Hammond.gapReactant/(kB '
    'T)); no delivered theorem identifies a yield channel with the barrier rate.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered two-channel yield theorem whose nonradiative channel is an Arrhenius rate over '
    'the Hammond barrier is missing; QuantumYield leaves every channel rate free. The legacy '
    'register records no edge, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-HQY-01', 'Q-R4-E1-HQY-01', 'P-Hammond-QuantumYield', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant', 'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
     'stmt-QuantumYield-PhotoLean-QuantumYield-totalRate'],
    ['definitionalIdentity', 'implication', 'equivalence'],
    ['HammondQyCandidateCtx (A, lam, kB, T, x, kr); no delivered channel vector'],
    'QuantumYield', 'Hammond',
    [{'strategy': 'Search the QuantumYield modules for a delivered theorem mentioning a barrier or '
                  'a rate law.',
      'outcome': 'No matches; the module is purely algebraic and imports no energy-side module.'},
     {'strategy': 'Instantiate yieldOf on a two-channel vector whose second channel is the '
                  'Hammond-barrier rate.',
      'outcome': 'The instantiation is possible in principle, but no delivered theorem relates '
                 'the resulting yield to the barrier; the bridge is missing.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'QuantumYield.yieldOf ![kr, A exp(-Hammond.gapReactant lam x/(kB T))] 0 is the '
                   'fluorescence yield of a barrier-controlled two-channel model.',
      'status': 'candidate only; no delivered theorem.'}],
    'A delivered two-channel yield theorem whose nonradiative channel is A '
    'exp(-Hammond.gapReactant/(kB T)) is missing; QuantumYield leaves every channel rate free.',
    'The legacy register records no edge and says the energy-side theories enter only through the '
    'specific rates that fill the channels. A candidate composition remains, so the honest status '
    'is unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/QuantumYield --include='*.lean'",
     "grep -h '^import' PhotoLean/QuantumYield/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-QuantumYield'])

# ---- QuantumYield × BEP
noncert(
    'P-BEP-QuantumYield', 'Q-R4-E1-BQY-01', 'SL-R4-E1-BQY-01',
    'stmt-BEP-PhotoLean-BEP-eact',
    'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
    'Does a BEP-barrier nonradiative channel control the parallel-channel quantum yield?',
    'In a two-channel quantum-yield model whose nonradiative channel is an Arrhenius rate over the '
    'BEP activation energy, is the radiative yield a monotone function of that barrier?',
    'QuantumYield defines yieldOf as k_i / Σ k, with every channel rate free. BEP supplies an '
    'activation barrier eact. A bridge would set the nonradiative channel to A exp(-eact/(kB T)) '
    'and prove the yield comparison; the delivered corpus has no theorem identifying a yield '
    'channel with a barrier-controlled rate. The query asks for that composition. It is '
    'chemically meaningful because the fluorescence quantum yield is the standard observable of '
    'competition between radiative decay and activated nonradiative loss.',
    'BepQyCandidateCtx', CAND_TOTAL('BepQyCandidateCtx'), CAND_TOTAL('BepQyCandidateCtx'),
    premise(P_TRUE('BepQyCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from a BEP-barrier rate to a yield monotonicity; no '
    'such delivered statement exists.',
    'A context at which the yield does not move monotonically with the BEP-barrier channel would '
    'refute the candidate implication.',
    'unresolved',
    'Candidate: a two-channel yield with the nonradiative channel A exp(-BEP.eact/(kB T)); no '
    'delivered theorem identifies a yield channel with the barrier rate.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered two-channel yield theorem whose nonradiative channel is an Arrhenius rate over '
    'BEP.eact is missing; QuantumYield leaves every channel rate free. The legacy register '
    'records no edge, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-BQY-01', 'Q-R4-E1-BQY-01', 'P-BEP-QuantumYield', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-BEP-PhotoLean-BEP-eact', 'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
     'stmt-QuantumYield-PhotoLean-QuantumYield-totalRate'],
    ['definitionalIdentity', 'implication', 'equivalence'],
    ['BepQyCandidateCtx (A, lam, kB, T, x, kr); no delivered channel vector'],
    'QuantumYield', 'BEP',
    [{'strategy': 'Search the QuantumYield modules for a delivered theorem mentioning a barrier.',
      'outcome': 'No matches; the module is purely algebraic.'},
     {'strategy': 'Instantiate yieldOf on a two-channel vector whose second channel is the '
                  'BEP-barrier rate.',
      'outcome': 'The instantiation is possible in principle, but no delivered theorem relates '
                 'the resulting yield to the barrier; the bridge is missing.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'QuantumYield.yieldOf ![kr, A exp(-BEP.eact lam x/(kB T))] 0 is the '
                   'fluorescence yield of a BEP-barrier-controlled two-channel model.',
      'status': 'candidate only; no delivered theorem.'}],
    'A delivered two-channel yield theorem whose nonradiative channel is A exp(-BEP.eact/(kB T)) '
    'is missing; QuantumYield leaves every channel rate free.',
    'The legacy register records no edge. A candidate composition remains, so the honest status is '
    'unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/QuantumYield --include='*.lean'",
     "grep -h '^import' PhotoLean/QuantumYield/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-BEP-QuantumYield'])

# ---- FluorPhos × Hammond
noncert(
    'P-Hammond-FluorPhos', 'Q-R4-E1-HFP-01', 'SL-R4-E1-HFP-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'Does the Hammond barrier control the S1 fluorescence/phosphorescence competition?',
    'If the S1 internal-conversion rate in the FluorPhos competition model is an Arrhenius rate '
    'over the Hammond forward barrier, does the fluorescence yield phiF decrease as that barrier '
    'decreases?',
    'FluorPhos writes phiF = kF/(kF + kISC + kIC), with kIC a free rate; Hammond supplies the '
    'barrier. A bridge would replace kIC by the barrier-controlled rate and derive the '
    'monotonicity. The delivered corpus has no such theorem. The query is chemically meaningful '
    'because internal conversion is the nonradiative channel that competes with fluorescence and '
    'intersystem crossing in the S1 decay.',
    'HammondFpCandidateCtx', CAND_TOTAL('HammondFpCandidateCtx'), CAND_TOTAL('HammondFpCandidateCtx'),
    premise(P_TRUE('HammondFpCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from the barrier-controlled IC rate to a fluorescence-'
    'yield monotonicity; no such delivered statement exists.',
    'A context at which phiF does not move monotonically with the barrier-controlled kIC would '
    'refute the candidate implication.',
    'unresolved',
    'Candidate: identify kIC with A exp(-Hammond.gapReactant/(kB T)) inside the FluorPhos '
    'competition; no delivered identification exists.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered identification kIC = A exp(-Hammond.gapReactant/(kB T)) inside the FluorPhos '
    'competition is missing; kIC is a free rate. The legacy register records no edge except '
    'through QuantumYield, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-HFP-01', 'Q-R4-E1-HFP-01', 'P-Hammond-FluorPhos', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant', 'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
     'stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay'],
    ['definitionalIdentity', 'implication', 'equivalence'],
    ['HammondFpCandidateCtx (kF, kISC, A, lam, kB, T, x); no delivered kIC identification'],
    'FluorPhos', 'Hammond',
    [{'strategy': 'Search the FluorPhos modules for a delivered theorem mentioning a barrier or an '
                  'activation energy.',
      'outcome': 'No matches; the module is a branch-probability layer with free rates.'},
     {'strategy': 'Replace kIC by the Hammond-barrier Arrhenius rate and differentiate phiF.',
      'outcome': 'The monotonicity argument is informal; no delivered theorem identifies kIC with '
                 'the barrier rate.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'FluorPhos.phiF kF kISC (A exp(-Hammond.gapReactant lam x/(kB T))) is a '
                   'barrier-controlled fluorescence yield.',
      'status': 'candidate only; no delivered theorem.'}],
    'A delivered identification kIC = A exp(-Hammond.gapReactant/(kB T)) inside the FluorPhos '
    'competition is missing; kIC is a free rate and the module imports no energy-side module.',
    'The legacy register records no edge except through QuantumYield. A candidate composition '
    'remains, so the honest status is unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/FluorPhos --include='*.lean'",
     "grep -h '^import' PhotoLean/FluorPhos/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-FluorPhos'])

# ---- FluorPhos × BEP
noncert(
    'P-BEP-FluorPhos', 'Q-R4-E1-BFP-01', 'SL-R4-E1-BFP-01',
    'stmt-BEP-PhotoLean-BEP-eact',
    'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
    'Does the BEP barrier control the S1 fluorescence/phosphorescence competition?',
    'If the S1 internal-conversion rate in the FluorPhos competition model is an Arrhenius rate '
    'over the BEP activation energy, does the fluorescence yield phiF decrease as that barrier '
    'decreases?',
    'FluorPhos writes phiF = kF/(kF + kISC + kIC), with kIC a free rate; BEP supplies an '
    'activation barrier eact. A bridge would replace kIC by the BEP-barrier rate and derive the '
    'monotonicity. The delivered corpus has no such theorem. The query is chemically meaningful '
    'because internal conversion is the nonradiative channel that competes with fluorescence and '
    'intersystem crossing in the S1 decay.',
    'BepFpCandidateCtx', CAND_TOTAL('BepFpCandidateCtx'), CAND_TOTAL('BepFpCandidateCtx'),
    premise(P_TRUE('BepFpCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from the BEP-barrier rate to a fluorescence-yield '
    'monotonicity; no such delivered statement exists.',
    'A context at which phiF does not move monotonically with the BEP-barrier-controlled kIC '
    'would refute the candidate implication.',
    'unresolved',
    'Candidate: identify kIC with A exp(-BEP.eact/(kB T)) inside the FluorPhos competition; no '
    'delivered identification exists.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered identification kIC = A exp(-BEP.eact/(kB T)) inside the FluorPhos competition is '
    'missing; kIC is a free rate. The legacy register records no edge except through QuantumYield, '
    'so the honest status is unresolved.')
add_search(
    'SL-R4-E1-BFP-01', 'Q-R4-E1-BFP-01', 'P-BEP-FluorPhos', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-BEP-PhotoLean-BEP-eact', 'stmt-FluorPhos-PhotoLean-FluorPhos-phiF',
     'stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay'],
    ['definitionalIdentity', 'implication', 'equivalence'],
    ['BepFpCandidateCtx (kF, kISC, A, lam, kB, T, x); no delivered kIC identification'],
    'FluorPhos', 'BEP',
    [{'strategy': 'Search the FluorPhos modules for a delivered theorem mentioning a BEP barrier.',
      'outcome': 'No matches; the module is a branch-probability layer with free rates.'},
     {'strategy': 'Replace kIC by the BEP-barrier Arrhenius rate and differentiate phiF.',
      'outcome': 'The monotonicity argument is informal; no delivered theorem identifies kIC with '
                 'the barrier rate.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'FluorPhos.phiF kF kISC (A exp(-BEP.eact lam x/(kB T))) is a '
                   'BEP-barrier-controlled fluorescence yield.',
      'status': 'candidate only; no delivered theorem.'}],
    'A delivered identification kIC = A exp(-BEP.eact/(kB T)) inside the FluorPhos competition is '
    'missing; kIC is a free rate.',
    'The legacy register records no edge except through QuantumYield. A candidate composition '
    'remains, so the honest status is unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/FluorPhos --include='*.lean'",
     "grep -h '^import' PhotoLean/FluorPhos/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-BEP-FluorPhos'])

# ---- Einstein × Hammond
noncert(
    'P-Hammond-Einstein', 'Q-R4-E1-HEIN-01', 'SL-R4-E1-HEIN-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-Einstein-PhotoLean-Einstein-yield_radiative',
    'Does a Hammond-barrier nonradiative channel control the Einstein radiative yield?',
    'In the two-channel radiative-yield model yield_radiative = A/(A + kNR), is the yield '
    'controlled by the Hammond forward barrier when kNR is the barrier-controlled nonradiative '
    'rate?',
    'Einstein\'s yield_radiative is the radiative branching ratio of a two-channel decay, with kNR '
    'free; Hammond supplies the barrier. A bridge would identify kNR with an Arrhenius rate over '
    'gapReactant and prove the monotonicity. The delivered corpus has no such theorem. The query '
    'is chemically meaningful because the radiative quantum yield is the standard competition '
    'observable, but the identification of kNR with a specific reaction barrier is a modelling '
    'premise.',
    'HammondEinsteinCandidateCtx', CAND_TOTAL('HammondEinsteinCandidateCtx'),
    CAND_TOTAL('HammondEinsteinCandidateCtx'),
    premise(P_TRUE('HammondEinsteinCandidateCtx'), [], []),
    'scope-R4-E1-candidate-bridge', 'implication',
    'The candidate is a typed implication from the barrier-controlled kNR to the radiative-yield '
    'monotonicity; no such delivered statement exists.',
    'A context at which the radiative yield does not move monotonically with the barrier-'
    'controlled kNR would refute the candidate implication.',
    'unresolved',
    'Candidate: identify kNR with A exp(-Hammond.gapReactant/(kB T)) in yield_radiative; no '
    'delivered identification exists.')
QUERIES[-1]['outcome']['rationale'] = (
    'A delivered identification kNR = A exp(-Hammond.gapReactant/(kB T)) in yield_radiative is '
    'missing; kNR is a free rate. The legacy register records no edge and routes the radiative '
    'conversions only through the QuantumYield anchor, so the honest status is unresolved.')
add_search(
    'SL-R4-E1-HEIN-01', 'Q-R4-E1-HEIN-01', 'P-Hammond-Einstein', 'unresolved',
    'scope-R4-E1-candidate-bridge',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant',
     'stmt-Einstein-PhotoLean-Einstein-yield_radiative',
     'stmt-Einstein-PhotoLean-Einstein-tauR'],
    ['definitionalIdentity', 'implication', 'equivalence'],
    ['HammondEinsteinCandidateCtx (A, kNR, lam, kB, T, x); no delivered kNR identification'],
    'Einstein', 'Hammond',
    [{'strategy': 'Search the Einstein modules for a delivered theorem mentioning a barrier or a '
                  'driving force.',
      'outcome': 'No matches; the module is a two-level radiative-conversion layer.'},
     {'strategy': 'Identify kNR with the Hammond-barrier Arrhenius rate and read yield_radiative '
                  'as a barrier-controlled yield.',
      'outcome': 'The identification is a modelling premise; no delivered theorem connects the '
                 'two.'},
     {'strategy': 'Search the legacy registry for a named query or certificate.',
      'outcome': 'Only a pair-level notEstablished anchor; no named proposition-level query.'}],
    [{'kind': 'candidate composition',
      'statement': 'Einstein.yield_radiative A (A exp(-Hammond.gapReactant lam x/(kB T))) is a '
                   'barrier-controlled radiative yield.',
      'status': 'candidate only; no delivered theorem.'}],
    'A delivered identification kNR = A exp(-Hammond.gapReactant/(kB T)) in yield_radiative is '
    'missing; kNR is a free rate.',
    'The legacy register records no edge and routes the radiative conversions only through the '
    'QuantumYield anchor. A candidate composition remains, so the honest status is unresolved.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/Einstein --include='*.lean'",
     "grep -h '^import' PhotoLean/Einstein/*.lean | sort -u",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-Einstein'])

# ---- Forster × Hammond (outOfScope)
add_query(
    'P-Hammond-Forster', 'Q-R4-E1-HFO-01',
    'stmt-Hammond-PhotoLean-Hammond-gapReactant',
    'stmt-Forster-PhotoLean-Forster-fretEff6',
    'Is there a shared scalar between the Förster transfer geometry and the Hammond barrier?',
    'Can the Förster transfer efficiency at donor–acceptor separation R be expressed as a function '
    'of the Hammond two-parabola barrier at the same driving force?',
    'Forster\'s transfer efficiency is R0^6/(R0^6 + R^6), a function of the donor–acceptor '
    'separation and the spectral/orientation parameters; Hammond\'s barrier is a function of '
    'reorganization energy and driving force. The delivered Förster statements contain no '
    'potential-energy surface, no reorganization energy, and no driving force; the Hammond '
    'statements contain no donor–acceptor separation and no spectral overlap. The delivered §16 '
    'extended no-edge register states that the transfer geometry shares no scalar with the '
    'energy-surface family. The query asks whether a shared scalar exists; the audit finds no '
    'declared context or translation, so the query is outside the declared jurisdiction rather '
    'than logically false.',
    'HammondForsterCandidateCtx',
    translation('none-declared', '',
                'No total translation is declared from the Förster geometry to the Hammond '
                'coordinates.',
                'The Förster statements have no reorganization energy or driving force, so there '
                'is no coordinate to map into the Hammond context.'),
    translation('none-declared', '',
                'No total translation is declared from the Hammond coordinates to the Förster '
                'geometry.',
                'The Hammond statements have no donor–acceptor separation or spectral overlap, so '
                'there is no coordinate to map into the Förster context.'),
    premise(P_TRUE('HammondForsterCandidateCtx'), [], []),
    'scope-R4-E1-jurisdiction', 'implication',
    'The candidate would be an implication from the surface barrier to the transfer efficiency; '
    'the audit finds no shared scalar on which to state it.',
    'A context in which a total translation from R (and the spectral parameters) to (lam, x) is '
    'declared would move the query into scope; the current record claims no counterexample.',
    'outOfScope',
    {'type': 'jurisdiction',
     'jurisdictionRationale': 'The two endpoint statements have no shared scalar and no declared '
                              'total translation: Förster quantifies over (R, tauD, r0six, '
                              'kappaSq, J) and Hammond over (lam, x). The delivered §16 register '
                              'records the same jurisdiction finding. This is not a claim that no '
                              'relation could ever be written.',
     'searchLogRef': 'SL-R4-E1-HFO-01'},
    'jurisdiction', 'SL-R4-E1-HFO-01')
QUERIES[-1]['provenance']['kind'] = 'jurisdiction'
QUERIES[-1]['outcome']['rationale'] = (
    'The query is outside the declared audit jurisdiction: there is no shared context and no '
    'total translation between the Förster transfer geometry and the Hammond two-parabola '
    'coordinates. The finding is statement-level and cited to the delivered §16 register; it is '
    'not logical absence.')
add_search(
    'SL-R4-E1-HFO-01', 'Q-R4-E1-HFO-01', 'P-Hammond-Forster', 'outOfScope',
    'scope-R4-E1-jurisdiction',
    ['stmt-Hammond-PhotoLean-Hammond-gapReactant',
     'stmt-Forster-PhotoLean-Forster-fretEff6',
     'stmt-Forster-PhotoLean-Forster-fretEff',
     'stmt-Forster-PhotoLean-Forster-kappaSq'],
    ['definitionalIdentity', 'implication', 'equivalence', 'observationalEquivalence'],
    ['HammondForsterCandidateCtx (R, tauD, lam, x); no total map between the transfer geometry and '
     'the two-parabola coordinates'],
    'Forster', 'Hammond',
    [{'strategy': 'Search the Förster modules for a delivered theorem mentioning a barrier, a '
                  'driving force, or a reorganization energy.',
      'outcome': 'No matches; the module contains only the transfer geometry and spectral '
                 'parameters.'},
     {'strategy': 'Search the Hammond modules for a delivered theorem mentioning a distance, a '
                  'spectral overlap, or an orientation factor.',
      'outcome': 'No matches; the module contains only the two-parabola surface geometry.'},
     {'strategy': 'Search the legacy registry and the §16 register for a candidate bridge.',
      'outcome': 'The register records no edge and states that the transfer geometry shares no '
                 'scalar with the energy-surface family.'}],
    [{'kind': 'jurisdiction',
      'statement': 'No shared scalar exists between Förster fretEff6 and Hammond gapReactant; the '
                   'two statements live on disjoint coordinate sets.',
      'status': 'jurisdiction finding, not logical absence.'}],
    'No shared context or total translation: Förster statements quantify over (R, tauD, r0six, '
    'kappaSq, J) and Hammond statements over (lam, x); the §16 register states the transfer '
    'geometry shares no scalar with the energy-surface family. This is a jurisdiction finding, '
    'not logical absence.',
    'The delivered §16 register records the jurisdiction finding. No counterexample is claimed '
    'and no forced edge is created; the query is outOfScope by statement-level reason.',
    ["grep -rn 'barrier\\|tsCoord\\|gapReactant\\|eact' PhotoLean/Forster --include='*.lean'",
     "grep -rn 'tauD\\|kappaSq\\|r0six\\|fretEff' PhotoLean/Hammond --include='*.lean'",
     'python3 tools/relation_audit_registry.py --explain-pair P-Hammond-Forster'])


# ---------------------------------------------------------------- assemble
PAIRS = []
for pid in PAIR_IDS:
    qids = [q['queryId'] for q in QUERIES if q['pairId'] == pid]
    PAIRS.append({
        'pairId': pid,
        'theories': QUEUE_BY_ID[pid]['theories'],
        'primaryCluster': QUEUE_BY_ID[pid]['screeningCluster'],
        'r1QueueLegacyStatus': QUEUE_BY_ID[pid]['legacyCoverage']['census']['label'],
        'screeningRequirement': 'namedQueryOrStatementLevelOutOfScope',
        'queryIds': qids,
        'queries': [q for q in QUERIES if q['pairId'] == pid],
    })

STATUS_COUNTS = {}
KIND_COUNTS = {}
for q in QUERIES:
    STATUS_COUNTS[q['outcome']['status']] = STATUS_COUNTS.get(q['outcome']['status'], 0) + 1
    KIND_COUNTS[q['expectedKind']] = KIND_COUNTS.get(q['expectedKind'], 0) + 1

COUNTS = {
    'pairs': len(PAIRS),
    'queries': len(QUERIES),
    'byStatus': STATUS_COUNTS,
    'byExpectedKind': KIND_COUNTS,
    'certified': STATUS_COUNTS.get('certified', 0),
    'refuted': STATUS_COUNTS.get('refuted', 0),
    'unresolved': STATUS_COUNTS.get('unresolved', 0),
    'notEstablished': STATUS_COUNTS.get('notEstablished', 0),
    'outOfScope': STATUS_COUNTS.get('outOfScope', 0),
    'searchEntries': len(SEARCHES),
}

R1_WP = None
for cl in CLUSTER['clusters']:
    for wp in cl.get('workPackages', []):
        if wp['id'] == 'WP-excited-state-kinetics-01':
            R1_WP = wp
assert R1_WP is not None
assert R1_WP['pairIds'] == PAIR_IDS, (R1_WP['pairIds'], PAIR_IDS)

SEARCH_LOG = {
    'schemaVersion': '1.0.0',
    'artifactKind': 'bounded-search-log',
    'round': 'R4',
    'generatedOn': '2026-11-04',
    'workPackage': {
        'id': 'R4-E1-EXCITED-01',
        'r1WorkPackage': 'WP-excited-state-kinetics-01',
        'pairIds': PAIR_IDS,
        'pairCount': len(PAIR_IDS),
    },
    'snapshot': SNAP['id'],
    'entries': SEARCHES,
    'counts': {'entries': len(SEARCHES), 'byStatus': {
        s: sum(1 for e in SEARCHES if e['status'] == s)
        for s in sorted({e['status'] for e in SEARCHES})}},
    'nonClaims': [
        'A search entry records a scoped, machine-recomputable search; it is not a negative claim '
        'outside the named statements, kinds, and contexts.',
        'The outOfScope entry records jurisdiction, not logical absence.',
        'No failed proof attempt is relabelled as a refutation.',
    ],
}

SEARCH_PATH = 'bounded_audit/r4/excited-01/search-log.json'
with open(os.path.join(HERE, 'search-log.json'), 'w', encoding='utf-8') as fh:
    json.dump(SEARCH_LOG, fh, indent=2, ensure_ascii=False)
    fh.write('\n')
SEARCH_SHA = sha_file(os.path.join(HERE, 'search-log.json'))

SCREENING = {
    'schemaVersion': '1.0.0',
    'artifactKind': 'bounded-screening-package',
    'round': 'R4',
    'generatedOn': '2026-11-04',
    'workPackage': {
        'id': 'R4-E1-EXCITED-01',
        'title': 'Excited-state kinetics, E1 batch',
        'source': 'loop/计划.md R4, Package E1',
        'r1WorkPackage': 'WP-excited-state-kinetics-01',
        'pairIds': PAIR_IDS,
        'pairCount': len(PAIR_IDS),
        'r1ClusterPlanWorkPackage': {
            'id': R1_WP['id'],
            'pairIds': R1_WP['pairIds'],
            'difference': {
                'addedByR4Plan': [],
                'removedByR4Plan': [],
                'note': 'The R4 E1 pair list is exactly the R1 work-package list; no R2/R3 pair '
                        'is rescreened.',
            },
        },
    },
    'statusVocabulary': STATUSES,
    'kindVocabulary': KINDS,
    'allowedAxioms': ALLOWED_AXIOMS,
    'snapshot': SNAP,
    'inventoryReference': {
        'path': INV_REL,
        'sha256': SNAP['inventorySha256'],
        'statementRows': INV['counts']['totalStatements'],
        'screeningEligible': INV['counts']['screeningEligible'],
        'schemaVersion': INV['schemaVersion'],
        'round': INV['round'],
    },
    'legacyRegistryReference': {
        'path': REGISTRY_REL,
        'sha256': SNAP['legacyRegistrySha256'],
        'expectedSha256': '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0',
        'mode': 'read-only',
    },
    'searchLogReference': {
        'path': SEARCH_PATH,
        'sha256': SEARCH_SHA,
        'entryCount': len(SEARCHES),
    },
    'probeReference': {
        'path': PROBE_REL,
        'sha256': PROBE_SHA,
        'compileLog': COMPILE_LOG,
        'scanLog': SCAN_LOG,
        'buildCommand': 'proofs/scripts/lake env lean ' + PROBE_REL,
        'axiomAuditCommand': 'proofs/scripts/lake env lean ' + PROBE_REL,
        'allowedAxioms': ALLOWED_AXIOMS,
    },
    'coverageFragment': {
        'path': 'bounded_audit/r4/excited-01/coverage-fragment.json',
        'note': 'The fragment carries this package counting only; it does not write the mutable R4 '
                'cumulative coverage ledger.',
    },
    'aliasResolutions': [],
    'contextLibrary': CONTEXT_LIBRARY,
    'scopeLibrary': SCOPE_LIBRARY,
    'pairs': PAIRS,
    'counts': COUNTS,
    'nonClaims': [
        'A certified record is a checked statement-level relation under its declared context and '
        'premises; it is not a claim of physical universality.',
        'A definitional identity is a kernel rfl pin over the declared translations; it is not '
        'propositional equality of the two physical vocabularies.',
        'An unresolved record is a candidate registration; it is not a negative claim.',
        'The outOfScope record is a jurisdiction finding, not logical absence.',
        'No accepted R2/R3 pair is rescreened, and this package does not write the mutable R4 '
        'cumulative coverage ledger.',
        'The r1QueueLegacyStatus field is a legacy census label, not an audit verdict.',
        'The package makes no pair-count or edge-count target claim.',
    ],
}

with open(os.path.join(HERE, 'screening.json'), 'w', encoding='utf-8') as fh:
    json.dump(SCREENING, fh, indent=2, ensure_ascii=False)
    fh.write('\n')
SCREENING_SHA = sha_file(os.path.join(HERE, 'screening.json'))

FRAGMENT = {
    'schemaVersion': '1.0.0',
    'artifactKind': 'bounded-coverage-fragment',
    'round': 'R4',
    'generatedOn': '2026-11-04',
    'package': {
        'id': 'R4-E1-EXCITED-01',
        'workPackage': 'WP-excited-state-kinetics-01',
        'status': 'submitted-R4-pending-review',
        'pairCount': len(PAIR_IDS),
        'queryCount': len(QUERIES),
    },
    'snapshot': {
        'id': SNAP['id'],
        'date': SNAP['date'],
        'inventorySha256': SNAP['inventorySha256'],
        'pairQueueSha256': SNAP['pairQueueSha256'],
        'clusterPlanSha256': SNAP['clusterPlanSha256'],
        'boundarySha256': SNAP['boundarySha256'],
        'legacyRegistrySha256': SNAP['legacyRegistrySha256'],
    },
    'counts': COUNTS,
    'pairs': [{
        'pairId': p['pairId'],
        'theories': p['theories'],
        'primaryCluster': p['primaryCluster'],
        'queryIds': p['queryIds'],
        'outcomes': [{
            'queryId': q['queryId'],
            'status': q['outcome']['status'],
            'expectedKind': q['expectedKind'],
            'evidenceType': q['outcome']['evidence']['type'],
            'certificateId': q['outcome']['evidence'].get('certificateId'),
        } for q in p['queries']],
        'screeningRequirement': 'namedQueryOrStatementLevelOutOfScope',
    } for p in PAIRS],
    'packageArtifacts': {
        'screening': {'path': 'bounded_audit/r4/excited-01/screening.json', 'sha256': SCREENING_SHA},
        'searchLog': {'path': SEARCH_PATH, 'sha256': SEARCH_SHA},
        'probe': {'path': PROBE_REL, 'sha256': PROBE_SHA},
    },
    'nonClaims': [
        'This fragment carries the sixteen E1 pairs only; it does not write or replace the mutable '
        'R4 cumulative coverage ledger.',
        'The submitted status is not an acceptance; independent K3 review is required.',
    ],
}

with open(os.path.join(HERE, 'coverage-fragment.json'), 'w', encoding='utf-8') as fh:
    json.dump(FRAGMENT, fh, indent=2, ensure_ascii=False)
    fh.write('\n')

print('pairs:', len(PAIRS))
print('queries:', len(QUERIES))
print('byStatus:', STATUS_COUNTS)
print('byExpectedKind:', KIND_COUNTS)
print('searchEntries:', len(SEARCHES))
print('probeSha256:', PROBE_SHA)
print('screeningSha256:', SCREENING_SHA)
print('searchLogSha256:', SEARCH_SHA)
print('fragmentSha256:', sha_file(os.path.join(HERE, 'coverage-fragment.json')))
