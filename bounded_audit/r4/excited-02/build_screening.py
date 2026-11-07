#!/usr/bin/env python3
"""Build the E2 bounded-screening package artifacts deterministically.

This is a reproducibility helper, not an accepted artifact itself. It writes
screening.json, search-log.json, and coverage-fragment.json and prints the
hashes of the generated files. It never edits the frozen R1/R2/R3 artifacts.
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
R2_REL = 'bounded_audit/wp-surface-01/screening.json'
R3_REL = 'bounded_audit/r3/screening.json'
PROBE_REL = 'bounded_audit/r4/excited-02/probes/E2-probe.lean'
PROBE_LOG_REL = 'bounded_audit/r4/excited-02/probes/compile.log'
SEARCH_REL = 'bounded_audit/r4/excited-02/search-log.json'
SCREENING_REL = 'bounded_audit/r4/excited-02/screening.json'
FRAGMENT_REL = 'bounded_audit/r4/excited-02/coverage-fragment.json'
SNAP_ID = 'snap-bounded-audit-2026-11-04-r4e2'
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']

E2_PAIRS = [
    'P-BEP-StokesShift', 'P-BEP-ICvsISC', 'P-BEP-Forster', 'P-BEP-Einstein',
    'P-Kasha-SymmetryFactor', 'P-SymmetryFactor-KashaVavilov',
    'P-SymmetryFactor-SternVolmer', 'P-SymmetryFactor-QuantumYield',
    'P-SymmetryFactor-FluorPhos', 'P-SymmetryFactor-EnergyGapLaw',
    'P-SymmetryFactor-StokesShift', 'P-SymmetryFactor-ICvsISC',
    'P-SymmetryFactor-Forster', 'P-SymmetryFactor-Einstein',
]


def sha_file(rel):
    h = hashlib.sha256()
    with open(os.path.join(ROOT, rel), 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return json.load(fh)


def dump(rel, obj):
    with open(os.path.join(ROOT, rel), 'w', encoding='utf-8') as fh:
        json.dump(obj, fh, indent=2, ensure_ascii=False)
        fh.write('\n')


INV = load(INV_REL)
QUEUE = load(QUEUE_REL)
QUEUE_BY_ID = {row['pairId']: row for row in QUEUE['pairs']}
INV_BY_DECL = {row['declaration']: row for row in INV['statements']}


def ep(decl):
    row = INV_BY_DECL[decl]
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


def ctx(cid, fields, reading, provenance):
    return {'id': cid, 'fields': fields, 'physicalReading': reading, 'provenance': provenance}


def ident(term='fun δ => δ'):
    return {'id': 'identity', 'term': term,
            'requirement': 'Both statement contexts are the shared context; the translation is total.'}


def coord(term, requirement):
    return {'id': 'coordinate-map', 'term': term, 'requirement': requirement}


def none_decl(reason):
    return {'id': 'none-declared', 'requirement': 'none-declared', 'reason': reason, 'term': ''}


def true_premises(ctx_id, predicate, note=None):
    out = {'predicate': 'fun _ : %s => True' % ctx_id, 'premiseIds': [], 'definitions': []}
    if note:
        out['note'] = note
    return out


def pos_premises(ctx_id, prem_name, pid, predicate, statement, load_bearing):
    return {
        'predicate': 'fun δ : %s => ∀ p ∈ %s, p.predicate δ' % (ctx_id, prem_name),
        'premiseIds': [pid],
        'definitions': [{'id': pid, 'predicate': predicate, 'statement': statement,
                         'loadBearing': load_bearing}],
    }


def scope_ref(sid):
    return {'id': sid}


CONTEXTS = {
    'BepStokesCtx': ctx(
        'BepStokesCtx', ['lam : ℝ', 'e00 : ℝ'],
        'Equal-curvature two-parabola step read both kinetically (BEP barrier at x = 0) and '
        'optically (vertical absorption minus vertical emission). lam is the reorganization '
        'energy shared by both readings; e00 is the 0-0 energy that cancels from the Stokes shift.',
        'bounded_audit/r4/excited-02/probes/E2-probe.lean#BepStokesCtx'),
    'BepICCtx': ctx(
        'BepICCtx', ['lam : ℝ', 'x : ℝ'],
        'Equal-curvature two-parabola crossing at reorganization energy lam and driving-force gap x. '
        'ICvsISC reads the same crossing as the nonradiative-channel Franck-Condon barrier; BEP '
        'reads it as the forward activation barrier of the elementary step.',
        'bounded_audit/r4/excited-02/probes/E2-probe.lean#BepICCtx'),
    'ScStokesCtx': ctx(
        'ScStokesCtx', ['lam : ℝ', 'e00 : ℝ', 'q : ℝ'],
        'Equal-curvature displaced parabolas: ground surface at q = 0 and excited surface at q = 1 '
        'with 0-0 offset e00. SymmetryFactor reads the same surface pair with reactant/product '
        'curvature parameters kr = kp = lam.',
        'bounded_audit/r4/excited-02/probes/E2-probe.lean#ScStokesCtx'),
    'ScEgCtx': ctx(
        'ScEgCtx', ['lam : ℝ'],
        'Thermoneutral equal-curvature two-parabola step: reorganization energy lam, driving force '
        'x = 0, and crossing coordinate fixed at the SymmetryFactor beta = 1/2 point.',
        'bounded_audit/r4/excited-02/probes/E2-probe.lean#ScEgCtx'),
    'ScICCtx': ctx(
        'ScICCtx', ['lam : ℝ'],
        'Thermoneutral equal-curvature two-parabola channel: reorganization energy lam, gap x = 0, '
        'and crossing coordinate fixed at the SymmetryFactor beta = 1/2 point.',
        'bounded_audit/r4/excited-02/probes/E2-probe.lean#ScICCtx'),
    'BepForsterDisjointCtx': ctx(
        'BepForsterDisjointCtx', ['lam : ℝ', 'x : ℝ', 'tauD : ℝ', 'r6 : ℝ', 'R : ℝ'],
        'Disjoint descriptor sets: BEP has a reaction coordinate and an activation barrier; Förster '
        'has a donor lifetime and a donor-acceptor separation with an R^-6 rate law. No shared '
        'physical coordinate or declared translation exists.',
        'bounded_audit/r4/excited-02/screening.json#BepForsterDisjointCtx (candidate context; no Lean structure)'),
    'BepEinsteinDisjointCtx': ctx(
        'BepEinsteinDisjointCtx', ['lam : ℝ', 'x : ℝ', 'h : ℝ', 'c : ℝ', 'nu : ℝ'],
        'Disjoint descriptor sets: BEP has a reaction coordinate and an activation barrier; the '
        'Einstein A/B coefficients are radiative transition quantities with a radiation-density '
        'factor. No shared physical coordinate or declared translation exists.',
        'bounded_audit/r4/excited-02/screening.json#BepEinsteinDisjointCtx (candidate context; no Lean structure)'),
    'KashaScCandidateCtx': ctx(
        'KashaScCandidateCtx', ['rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'kr : ℝ', 'kp : ℝ'],
        'Candidate shared context: a two-level ladder whose upper-to-lower internal-conversion rate '
        'would be a crossing-controlled step with SymmetryFactor curvatures. The ladder leaves ic '
        'as an arbitrary rate function and no delivered translation relates it to (kr, kp).',
        'bounded_audit/r4/excited-02/screening.json#KashaScCandidateCtx (candidate context; no Lean structure)'),
    'ScKvDisjointCtx': ctx(
        'ScKvDisjointCtx', ['kr : ℝ', 'kp : ℝ', 'rad : ℕ → ℝ', 'ic : ℕ → ℝ', 'M : ℕ', 'N : ℕ'],
        'Disjoint observable sets: SymmetryFactor compares a curvature pair and a crossing '
        'coordinate; KashaVavilov compares normalized spectra of a ladder at two excitation levels. '
        'No shared scalar or channel exists.',
        'bounded_audit/r4/excited-02/screening.json#ScKvDisjointCtx (candidate context; no Lean structure)'),
    'ScSvCandidateCtx': ctx(
        'ScSvCandidateCtx', ['kr : ℝ', 'kp : ℝ', 'k0 : ℝ', 'kq : ℝ', 'q : ℝ'],
        'Candidate shared context: a crossing-controlled quenching channel with SymmetryFactor '
        'curvatures alongside a Stern-Volmer intrinsic decay k0 and concentration channel kq*q. '
        'No total translation from [Q] to a driving force is declared.',
        'bounded_audit/r4/excited-02/screening.json#ScSvCandidateCtx (candidate context; no Lean structure)'),
    'ScQyCandidateCtx': ctx(
        'ScQyCandidateCtx', ['kr : ℝ', 'kp : ℝ', 'k : Fin n → ℝ', 'i : Fin n'],
        'Candidate shared context: one parallel decay channel of the QuantumYield calculus would be '
        'a crossing-controlled nonradiative rate with SymmetryFactor curvatures. No delivered '
        'instance fills a channel with such a rate.',
        'bounded_audit/r4/excited-02/screening.json#ScQyCandidateCtx (candidate context; no Lean structure)'),
    'ScFpCandidateCtx': ctx(
        'ScFpCandidateCtx', ['kr : ℝ', 'kp : ℝ', 'kF : ℝ', 'kISC : ℝ', 'kIC : ℝ'],
        'Candidate shared context: the FluorPhos S1 intersystem-crossing/internal-conversion '
        'channels would be crossing-controlled processes with SymmetryFactor curvatures. No '
        'delivered rate law relates the two parameter sets.',
        'bounded_audit/r4/excited-02/screening.json#ScFpCandidateCtx (candidate context; no Lean structure)'),
    'ScForsterDisjointCtx': ctx(
        'ScForsterDisjointCtx', ['kr : ℝ', 'kp : ℝ', 'thetaD : ℝ', 'thetaA : ℝ', 'phi : ℝ'],
        'Disjoint geometric sets: the SymmetryFactor crossing coordinate is a two-parabola '
        'reaction-coordinate geometry; the Förster orientation factor is a donor-acceptor dipole '
        'geometry. Both are geometric, but they share no scalar.',
        'bounded_audit/r4/excited-02/screening.json#ScForsterDisjointCtx (candidate context; no Lean structure)'),
    'ScEinsteinDisjointCtx': ctx(
        'ScEinsteinDisjointCtx', ['kr : ℝ', 'kp : ℝ', 'h : ℝ', 'c : ℝ', 'nu : ℝ'],
        'Disjoint descriptor sets: the SymmetryFactor crossing coordinate is a structural '
        'surface-crossing geometry; the Einstein A/B coefficients are radiative transition '
        'quantities. No shared scalar or declared translation exists.',
        'bounded_audit/r4/excited-02/screening.json#ScEinsteinDisjointCtx (candidate context; no Lean structure)'),
}

SCOPES = {
    'scope-E2-bep-stokes-thermoneutral': {
        'id': 'scope-E2-bep-stokes-thermoneutral',
        'description': 'Thermoneutral equal-curvature two-parabola step read by BEP and StokesShift.',
        'domain': 'all (lam, e00) in ℝ²; the totalized lam = 0 corner is included.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-bep-ic-barrier': {
        'id': 'scope-E2-bep-ic-barrier',
        'description': 'Equal-curvature crossing barrier compared between BEP and the ICvsISC channel.',
        'domain': 'all (lam, x) in ℝ²; no positivity premise is needed for the definitional pin.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-sc-stokes-surfaces': {
        'id': 'scope-E2-sc-stokes-surfaces',
        'description': 'Equal-curvature surface pair shared by StokesShift and SymmetryFactor.',
        'domain': 'all (lam, e00, q) in ℝ³; the paired ground and excited surfaces are compared.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-sc-egl-thermoneutral': {
        'id': 'scope-E2-sc-egl-thermoneutral',
        'description': 'Thermoneutral equal-curvature barrier height in EnergyGapLaw and SymmetryFactor.',
        'domain': 'all lam > 0; driving force fixed at x = 0 and crossing coordinate at beta = 1/2.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-sc-ic-thermoneutral': {
        'id': 'scope-E2-sc-ic-thermoneutral',
        'description': 'Thermoneutral equal-curvature barrier height in ICvsISC and SymmetryFactor.',
        'domain': 'all lam > 0; gap fixed at x = 0 and crossing coordinate at beta = 1/2.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-candidate-bridge': {
        'id': 'scope-E2-candidate-bridge',
        'description': 'Scoped search for a delivered statement-level bridge; no negative claim outside the named search.',
        'domain': 'the four named unresolved pairs and the statements/kinds/contexts recorded in their search-log entries.',
        'snapshot': SNAP_ID,
    },
    'scope-E2-jurisdiction': {
        'id': 'scope-E2-jurisdiction',
        'description': 'Jurisdiction record for pairs with no shared context or declared translation.',
        'domain': 'the five named outOfScope pairs and the statements/kinds/contexts recorded in their search-log entries.',
        'snapshot': SNAP_ID,
    },
}


def obs_channel(cid, name, left, right):
    return {
        'id': cid,
        'name': name,
        'observedValueType': 'ℝ',
        'inputDomain': 'Unit (the single declared configuration)',
        'domainNonempty': True,
        'leftObs': left,
        'rightObs': right,
    }


def underlying(decl, artifact, line, role):
    return {'declaration': decl, 'sourceArtifact': artifact, 'sourceLine': line, 'role': role}


def cert_evidence(cert_id, decl, kind_thm, kind, under, justification, probe_sha):
    return {
        'type': 'e2-probe-certificate',
        'certificateId': cert_id,
        'kind': kind,
        'probe': {
            'path': PROBE_REL,
            'sha256': probe_sha,
            'declaration': decl,
            'kindCheckTheorem': kind_thm,
            'buildCommand': 'proofs/scripts/lake env lean %s' % PROBE_REL,
            'log': PROBE_LOG_REL,
        },
        'underlyingTheorems': under,
        'axiomFootprint': list(ALLOWED_AXIOMS),
        'allowedAxioms': list(ALLOWED_AXIOMS),
        'justification': justification,
    }


def search_evidence(search_id, summary):
    return {'type': 'scoped-search', 'searchLogRef': search_id, 'candidateSummary': summary}


def jurisdiction_evidence(search_id, rationale):
    return {'type': 'jurisdiction', 'searchLogRef': search_id,
            'jurisdictionRationale': rationale}


LEGACY_NOTE = ('The legacy record for this pair is a pair-level notEstablished anchor; it is '
               'coverage history, not an audit verdict, and is not cited as evidence.')


def build_queries(probe_sha):
    qs = []

    # ---------------------------------------------------------------- certified
    qs.append({
        'queryId': 'Q-E2-BS-01',
        'pairId': 'P-BEP-StokesShift',
        'title': 'BEP thermoneutral barrier is one eighth of the Stokes shift',
        'chemicalQuestion': (
            'In the shared equal-curvature two-parabola model, is the BEP activation barrier at '
            'thermoneutrality one eighth of the optical Stokes shift computed from the same '
            'reorganization energy?'),
        'chemicalRationale': (
            'BEP reads the model kinetically: the barrier at x = 0 is the reactant surface at the '
            'two-parabola crossing. StokesShift reads the same displaced parabolas optically: '
            'vertical absorption minus vertical emission is 2*lam. The thermoneutral barrier is '
            'lam/4, so the two theory-owned descriptors are linked by the factor 1/8. The query '
            'asks whether the kinetic and optical readings report the same reorganization energy, '
            'not whether two notations look alike.'),
        'endpoints': {'source': ep('PhotoLean.BEP.eact'),
                      'target': ep('PhotoLean.StokesShift.stokesShift')},
        'sharedContext': {
            'id': 'BepStokesCtx', 'fields': ['lam : ℝ', 'e00 : ℝ'],
            'physicalReading': CONTEXTS['BepStokesCtx']['physicalReading'],
            'provenance': CONTEXTS['BepStokesCtx']['provenance']},
        'translations': {'left': ident(), 'right': ident()},
        'premises': true_premises(
            'BepStokesCtx', 'fun _ : BepStokesCtx => True',
            'The identity holds for every lam, including the totalized lam = 0 corner; no '
            'positivity premise is load-bearing, so none is declared.'),
        'observationChannels': [obs_channel(
            'thermoneutralBarrierVsEighthStokesShift',
            'thermoneutralBarrierVsEighthStokesShift',
            'fun δ _ => PhotoLean.BEP.eact δ.lam 0',
            'fun δ _ => PhotoLean.StokesShift.stokesShift δ.lam δ.e00 / 8')],
        'scope': {**SCOPES['scope-E2-bep-stokes-thermoneutral']},
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': (
            'Both readings are real-valued observables on the shared context; the certificate is '
            'equality of the declared barrier-height channel against the band-separation channel.'),
        'falsificationCondition': (
            'A context (lam, e00) at which BEP.eact lam 0 differs from '
            'StokesShift.stokesShift lam e00 / 8 would refute the equality; the totalized lam = 0 '
            'corner is included.'),
        'outcome': {
            'status': 'certified',
            'rationale': (
                'The probe theorem bepStokesThermoneutral and the observational channel '
                'certificate bepStokesBridge are checked; the equality holds for every lam and '
                'e00 including lam = 0.'),
            'evidence': cert_evidence(
                'EB2-BS-01',
                'PhotoLean.RelationAudit.BoundedAudit.E2.bepStokesBridge',
                'PhotoLean.RelationAudit.BoundedAudit.E2.bepStokesBridge_kind',
                'observationalEquivalence',
                [underlying('PhotoLean.BEP.eact_at_zero', 'PhotoLean/BEP/Basic.lean', 137,
                            'delivered thermoneutral evaluation row eact lam 0 = lam/4'),
                 underlying('PhotoLean.StokesShift.stokesShift_eq_two_lam',
                            'PhotoLean/StokesShift/Criterion.lean', 60,
                            'delivered Stokes-shift law stokesShift lam e00 = 2*lam')],
                'The probe re-derives both delivered evaluation rows so the lam = 0 totalized '
                'corner is covered in one statement; the two delivered rows are cited as source '
                'coherence. The legacy registry has no certificate for this pair.',
                probe_sha)},
        'provenance': {
            'kind': 'e2-probe-certificate', 'certificateId': 'EB2-BS-01',
            'sourceArtifact': PROBE_REL,
            'locator': 'PhotoLean.RelationAudit.BoundedAudit.E2.bepStokesBridge',
            'legacyDisposition': LEGACY_NOTE},
    })

    qs.append({
        'queryId': 'Q-E2-BI-01',
        'pairId': 'P-BEP-ICvsISC',
        'title': 'The IC channel Franck-Condon barrier is the BEP activation barrier',
        'chemicalQuestion': (
            'Is the controlling Franck-Condon barrier of the ICvsISC internal-conversion channel '
            'the same equal-curvature crossing barrier that BEP reports as its activation energy '
            'at the same reorganization energy and gap?'),
        'chemicalRationale': (
            'Both theories are built on the same equal-curvature two-parabola crossing. ICvsISC '
            'copies the kernel barrier as fcBarrier to control the IC channel Arrhenius rate; BEP '
            'reports the forward activation barrier eact of the elementary step. The query asks '
            'whether the two theory-owned barrier descriptors are the same object, which is the '
            'statement-level bridge between the nonradiative-channel reading and the '
            'linear-free-energy reading.'),
        'endpoints': {'source': ep('PhotoLean.BEP.eact'),
                      'target': ep('PhotoLean.ICvsISC.fcBarrier')},
        'sharedContext': {
            'id': 'BepICCtx', 'fields': ['lam : ℝ', 'x : ℝ'],
            'physicalReading': CONTEXTS['BepICCtx']['physicalReading'],
            'provenance': CONTEXTS['BepICCtx']['provenance']},
        'translations': {'left': ident(), 'right': ident()},
        'premises': true_premises(
            'BepICCtx', 'fun _ : BepICCtx => True',
            'The two terms are definitionally the same total function of (lam, x); no premise is '
            'load-bearing.'),
        'observationChannels': [],
        'scope': {**SCOPES['scope-E2-bep-ic-barrier']},
        'expectedKind': 'definitionalIdentity',
        'expectedKindRationale': (
            'The obligation is a fresh kernel rfl check after the identity translations, not a '
            'propositional equality or a physical-identity claim.'),
        'falsificationCondition': (
            'A context (lam, x) at which BEP.eact lam x differs from ICvsISC.fcBarrier lam x would '
            'refute the definitional identity.'),
        'outcome': {
            'status': 'certified',
            'rationale': (
                'The probe constructs a DefinitionalPin whose two translated terms elaborate by '
                'rfl; the pin is wrapped as a typed definitionalIdentity certificate.'),
            'evidence': cert_evidence(
                'EB2-BI-01',
                'PhotoLean.RelationAudit.BoundedAudit.E2.bepICBridge',
                'PhotoLean.RelationAudit.BoundedAudit.E2.bepICBridge_kind',
                'definitionalIdentity',
                [underlying('PhotoLean.Relations.bep_eact_eq_marcus_barrier',
                            'PhotoLean/Relations.lean', 245,
                            'delivered BEP activation barrier / Marcus barrier pin'),
                 underlying('PhotoLean.Relations.icvscic_barrier_eq_kernel',
                            'PhotoLean/Relations.lean', 693,
                            'delivered IC Franck-Condon barrier / kernel barrier pin')],
                'Both theory copies are pinned to the delivered kernel barrier; the probe performs '
                'the fresh rfl check of the two theory-owned terms. It is not a wrapper around a '
                'certified count: the identity is the barrier-level bridge between the two '
                'readings.',
                probe_sha)},
        'provenance': {
            'kind': 'e2-probe-certificate', 'certificateId': 'EB2-BI-01',
            'sourceArtifact': PROBE_REL,
            'locator': 'PhotoLean.RelationAudit.BoundedAudit.E2.bepICBridge',
            'legacyDisposition': LEGACY_NOTE},
    })

    qs.append({
        'queryId': 'Q-E2-SS-01',
        'pairId': 'P-SymmetryFactor-StokesShift',
        'title': 'Stokes-shift surfaces are the SymmetryFactor parabolas at equal curvature',
        'chemicalQuestion': (
            'Are the ground- and excited-state surfaces of the Stokes-shift model the same two '
            'displaced parabolas whose unequal-curvature generalization SymmetryFactor adjudicates, '
            'specialized to equal curvature?'),
        'chemicalRationale': (
            'StokesShift carries its own copies of the kernel reactant and product surfaces to '
            'compute vertical band positions; SymmetryFactor carries the unequal-curvature '
            'surfaces asymReactantSurface/asymProductSurface whose equal-curvature specialization '
            'is the kernel surface. The query asks whether the optical surfaces are the structural '
            'surfaces at kr = kp = lam with dG = e00. That is the model-level bridge between the '
            'band-position reading and the crossing-coordinate reading.'),
        'endpoints': {'source': ep('PhotoLean.StokesShift.s0Surface'),
                      'target': ep('PhotoLean.SymmetryFactor.asymReactantSurface')},
        'sharedContext': {
            'id': 'ScStokesCtx', 'fields': ['lam : ℝ', 'e00 : ℝ', 'q : ℝ'],
            'physicalReading': CONTEXTS['ScStokesCtx']['physicalReading'],
            'provenance': CONTEXTS['ScStokesCtx']['provenance']},
        'translations': {'left': ident(), 'right': ident()},
        'premises': true_premises(
            'ScStokesCtx', 'fun _ : ScStokesCtx => True',
            'The paired surface identity holds definitionally for every (lam, e00, q); no premise '
            'is load-bearing.'),
        'observationChannels': [],
        'scope': {**SCOPES['scope-E2-sc-stokes-surfaces']},
        'expectedKind': 'definitionalIdentity',
        'expectedKindRationale': (
            'The certificate pins the paired translated surface terms by a fresh rfl check; the '
            'excited pair s1Surface/asymProductSurface is included in the same pin.'),
        'falsificationCondition': (
            'A context (lam, e00, q) at which either the ground or the excited surface pair differs '
            'would refute the identity.'),
        'outcome': {
            'status': 'certified',
            'rationale': (
                'The probe DefinitionalPin pairs (s0Surface, s1Surface) with '
                '(asymReactantSurface, asymProductSurface) and elaborates by rfl.'),
            'evidence': cert_evidence(
                'EB2-SS-01',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scStokesBridge',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scStokesBridge_kind',
                'definitionalIdentity',
                [underlying('PhotoLean.Relations.ss_s0Surface_eq_kernel',
                            'PhotoLean/Relations.lean', 683,
                            'delivered Stokes ground surface / kernel reactant surface pin'),
                 underlying('PhotoLean.Relations.ss_s1Surface_eq_kernel',
                            'PhotoLean/Relations.lean', 688,
                            'delivered Stokes excited surface / kernel product surface pin')],
                'The delivered kernel pins give each surface pair the same normal form; the probe '
                'pins both pairs in one fresh rfl check. The legacy registry registers this pair '
                'as an absence anchor, not as a named query.',
                probe_sha)},
        'provenance': {
            'kind': 'e2-probe-certificate', 'certificateId': 'EB2-SS-01',
            'sourceArtifact': PROBE_REL,
            'locator': 'PhotoLean.RelationAudit.BoundedAudit.E2.scStokesBridge',
            'legacyDisposition': LEGACY_NOTE},
    })

    qs.append({
        'queryId': 'Q-E2-SE-01',
        'pairId': 'P-SymmetryFactor-EnergyGapLaw',
        'title': 'EGL thermoneutral barrier is the SymmetryFactor surface height at beta = 1/2',
        'chemicalQuestion': (
            'At thermoneutral equal curvature, is the energy-gap law nonradiative barrier the '
            'SymmetryFactor reactant-surface height at its beta = 1/2 crossing coordinate?'),
        'chemicalRationale': (
            'EnergyGapLaw copies the kernel barrier as the nonradiative barrier of an electronic '
            'relaxation; SymmetryFactor computes the thermoneutral crossing coordinate of the '
            'two-parabola model and its surface height. At equal curvature the crossing coordinate '
            'is 1/2 and the reactant-surface height there is lam/4, which is the EGL barrier at '
            'x = 0. The query asks whether the barrier that controls the nonradiative rate and the '
            'crossing height that fixes the structural transfer coefficient are the same '
            'observable.'),
        'endpoints': {'source': ep('PhotoLean.EnergyGapLaw.nrBarrier'),
                      'target': ep('PhotoLean.SymmetryFactor.asymReactantSurface')},
        'sharedContext': {
            'id': 'ScEgCtx', 'fields': ['lam : ℝ'],
            'physicalReading': CONTEXTS['ScEgCtx']['physicalReading'],
            'provenance': CONTEXTS['ScEgCtx']['provenance']},
        'translations': {
            'left': ident(),
            'right': coord(
                'fun δ : ScEgCtx => (δ.lam, δ.lam, PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)',
                'The right context sets kr = kp = lam and q = tsCoordZero lam lam; the map is total.')},
        'premises': pos_premises(
            'ScEgCtx', 'scEgPremises', 'scEg.lamPositive',
            'fun δ : ScEgCtx => 0 < δ.lam',
            '0 < lam: the reorganization energy is positive (load-bearing for the division by '
            '4*lam and for betaHalf_holds_in_kernel).',
            'Consumed by the probe proof (field_simp and betaHalf_holds_in_kernel).'),
        'observationChannels': [obs_channel(
            'thermoneutralBarrierHeight',
            'thermoneutralBarrierHeight',
            'fun δ _ => PhotoLean.EnergyGapLaw.nrBarrier δ.lam 0',
            'fun δ _ => PhotoLean.SymmetryFactor.asymReactantSurface δ.lam '
            '(PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)')],
        'scope': {**SCOPES['scope-E2-sc-egl-thermoneutral']},
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': (
            'The two readings are real-valued barrier-height observables on the same shared '
            'context; the certificate is equality of the declared channel.'),
        'falsificationCondition': (
            'A context lam > 0 at which EnergyGapLaw.nrBarrier lam 0 differs from the '
            'SymmetryFactor reactant-surface height at tsCoordZero lam lam would refute the '
            'equality.'),
        'outcome': {
            'status': 'certified',
            'rationale': (
                'The probe checks egThermoneutralSurface under 0 < lam and wraps it in the '
                'thermoneutralBarrierHeight observational certificate.'),
            'evidence': cert_evidence(
                'EB2-SE-01',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scEgBridge',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scEgBridge_kind',
                'observationalEquivalence',
                [underlying('PhotoLean.Relations.eg_barrier_eq_kernel',
                            'PhotoLean/Relations.lean', 669,
                            'delivered EGL barrier / kernel barrier pin'),
                 underlying('PhotoLean.SymmetryFactor.betaHalf_holds_in_kernel',
                            'PhotoLean/SymmetryFactor/Sharp.lean', 128,
                            'delivered equal-curvature beta = 1/2 reading')],
                'The probe extends the delivered section 11 tie-back to the EGL kernel copy. The '
                'channel is the barrier height, not the bare predicate, so the row is an '
                'observational equivalence rather than a shape note.',
                probe_sha)},
        'provenance': {
            'kind': 'e2-probe-certificate', 'certificateId': 'EB2-SE-01',
            'sourceArtifact': PROBE_REL,
            'locator': 'PhotoLean.RelationAudit.BoundedAudit.E2.scEgBridge',
            'legacyDisposition': LEGACY_NOTE},
    })

    qs.append({
        'queryId': 'Q-E2-SI-01',
        'pairId': 'P-SymmetryFactor-ICvsISC',
        'title': 'ICvsISC thermoneutral barrier is the SymmetryFactor surface height at beta = 1/2',
        'chemicalQuestion': (
            'At thermoneutral equal curvature, is the IC channel Franck-Condon barrier the '
            'SymmetryFactor reactant-surface height at its beta = 1/2 crossing coordinate?'),
        'chemicalRationale': (
            'ICvsISC fcBarrier controls the internal-conversion rate; SymmetryFactor computes the '
            'thermoneutral crossing coordinate and its surface height. At equal curvature the '
            'crossing is at 1/2 and the reactant-surface height is lam/4, which is the IC barrier '
            'at x = 0. The query asks whether the barrier that controls the IC channel is the same '
            'crossing height that the symmetry-factor theory reports, which is a genuine '
            'statement-level comparison of the two theory-owned barrier descriptors.'),
        'endpoints': {'source': ep('PhotoLean.ICvsISC.fcBarrier'),
                      'target': ep('PhotoLean.SymmetryFactor.asymReactantSurface')},
        'sharedContext': {
            'id': 'ScICCtx', 'fields': ['lam : ℝ'],
            'physicalReading': CONTEXTS['ScICCtx']['physicalReading'],
            'provenance': CONTEXTS['ScICCtx']['provenance']},
        'translations': {
            'left': ident(),
            'right': coord(
                'fun δ : ScICCtx => (δ.lam, δ.lam, PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)',
                'The right context sets kr = kp = lam and q = tsCoordZero lam lam; the map is total.')},
        'premises': pos_premises(
            'ScICCtx', 'scICPremises', 'scIC.lamPositive',
            'fun δ : ScICCtx => 0 < δ.lam',
            '0 < lam: the reorganization energy is positive (load-bearing for the division by '
            '4*lam and for betaHalf_holds_in_kernel).',
            'Consumed by the probe proof (field_simp and betaHalf_holds_in_kernel).'),
        'observationChannels': [obs_channel(
            'thermoneutralBarrierHeight',
            'thermoneutralBarrierHeight',
            'fun δ _ => PhotoLean.ICvsISC.fcBarrier δ.lam 0',
            'fun δ _ => PhotoLean.SymmetryFactor.asymReactantSurface δ.lam '
            '(PhotoLean.SymmetryFactor.tsCoordZero δ.lam δ.lam)')],
        'scope': {**SCOPES['scope-E2-sc-ic-thermoneutral']},
        'expectedKind': 'observationalEquivalence',
        'expectedKindRationale': (
            'The two readings are real-valued barrier-height observables on the same shared '
            'context; the certificate is equality of the declared channel.'),
        'falsificationCondition': (
            'A context lam > 0 at which ICvsISC.fcBarrier lam 0 differs from the SymmetryFactor '
            'reactant-surface height at tsCoordZero lam lam would refute the equality.'),
        'outcome': {
            'status': 'certified',
            'rationale': (
                'The probe checks icThermoneutralSurface under 0 < lam and wraps it in the '
                'thermoneutralBarrierHeight observational certificate.'),
            'evidence': cert_evidence(
                'EB2-SI-01',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scICBridge',
                'PhotoLean.RelationAudit.BoundedAudit.E2.scICBridge_kind',
                'observationalEquivalence',
                [underlying('PhotoLean.Relations.icvscic_barrier_eq_kernel',
                            'PhotoLean/Relations.lean', 693,
                            'delivered IC barrier / kernel barrier pin'),
                 underlying('PhotoLean.SymmetryFactor.betaHalf_holds_in_kernel',
                            'PhotoLean/SymmetryFactor/Sharp.lean', 128,
                            'delivered equal-curvature beta = 1/2 reading')],
                'The probe extends the delivered section 11 tie-back to the ICvsISC kernel copy. '
                'The channel is the barrier height, so the row is an observational equivalence '
                'rather than a shape note.',
                probe_sha)},
        'provenance': {
            'kind': 'e2-probe-certificate', 'certificateId': 'EB2-SI-01',
            'sourceArtifact': PROBE_REL,
            'locator': 'PhotoLean.RelationAudit.BoundedAudit.E2.scICBridge',
            'legacyDisposition': LEGACY_NOTE},
    })

    # ---------------------------------------------------------------- unresolved
    def unresolved(qid, pid, title, question, rationale, ctx_id, src, tgt, scope,
                   search_id, summary, falsification, kind_rationale,
                   left_reason=None, right_reason=None):
        return {
            'queryId': qid, 'pairId': pid, 'title': title,
            'chemicalQuestion': question, 'chemicalRationale': rationale,
            'endpoints': {'source': ep(src), 'target': ep(tgt)},
            'sharedContext': {
                'id': ctx_id, 'fields': CONTEXTS[ctx_id]['fields'],
                'physicalReading': CONTEXTS[ctx_id]['physicalReading'],
                'provenance': CONTEXTS[ctx_id]['provenance']},
            'translations': {
                'left': none_decl(left_reason or
                                  'No total translation from the SymmetryFactor curvature pair to '
                                  'the partner parameter space is declared in the delivered corpus.'),
                'right': none_decl(right_reason or
                                   'No total translation from the partner parameter space to the '
                                   'SymmetryFactor curvature pair is declared in the delivered corpus.')},
            'premises': true_premises(ctx_id, 'fun _ : %s => True' % ctx_id,
                                      'No certificate is claimed; the candidate premises are not '
                                      'load-bearing for a disposition.'),
            'observationChannels': [],
            'scope': {**SCOPES[scope]},
            'expectedKind': 'implication',
            'expectedKindRationale': kind_rationale,
            'falsificationCondition': falsification,
            'outcome': {
                'status': 'unresolved',
                'rationale': summary,
                'evidence': search_evidence(search_id, summary)},
            'provenance': {
                'kind': 'scoped-search', 'sourceArtifact': SEARCH_REL, 'locator': search_id,
                'legacyDisposition': LEGACY_NOTE},
        }

    qs.append(unresolved(
        'Q-E2-KS-01', 'P-Kasha-SymmetryFactor',
        'Is the Kasha funnel ratio controlled by the SymmetryFactor crossing coordinate?',
        'Can the Kasha ladder internal-conversion/radiative funnel ratio be read as a '
        'crossing-controlled rate whose barrier is fixed by the SymmetryFactor thermoneutral '
        'crossing coordinate?',
        'Kasha funnelRatio is rad 0 * ic 1 / (rad 1 * decay 0); the ladder leaves ic as an '
        'arbitrary rate function, so a physical reading of the funnel needs a rate law. '
        'SymmetryFactor supplies a crossing coordinate and surfaces but no rate. If IC were a '
        'crossing-controlled process, the two theories would share a barrier descriptor; the '
        'query asks for that bridge. The candidate is chemically motivated but not delivered.',
        'KashaScCandidateCtx',
        'PhotoLean.Kasha.funnelRatio', 'PhotoLean.SymmetryFactor.tsCoordZero',
        'scope-E2-candidate-bridge', 'SL-E2-KS-01',
        'A delivered identification of the ladder internal-conversion rate ic 1 with a '
        'crossing-controlled rate whose barrier is the SymmetryFactor thermoneutral crossing '
        'height is missing; Kasha.ic is an arbitrary rate function and SymmetryFactor has no rate '
        'coordinate.',
        'A ladder and a curvature pair at which the funnel ratio is not controlled by the '
        'crossing height would refute the candidate implication; no such statement is delivered.',
        'The candidate is a rate-versus-structure bridge; the weakest composable form is an '
        'implication from a crossing-height premise to a funnel-ratio premise.',
        left_reason='No total translation from the Kasha ladder rate functions to the SymmetryFactor '
                    'curvature pair is declared; the ladder index is not a reaction coordinate.',
        right_reason='No total translation from the SymmetryFactor curvature pair to the Kasha '
                     'ladder rate functions is declared; the crossing coordinate is not a ladder index.'))

    qs.append(unresolved(
        'Q-E2-SV-01', 'P-SymmetryFactor-SternVolmer',
        'Is the Stern-Volmer bimolecular rate a crossing-controlled rate with the SymmetryFactor coefficient?',
        'Is the Stern-Volmer added quenching channel kq*[Q] an activated crossing-controlled '
        'channel whose barrier geometry is the SymmetryFactor two-parabola crossing?',
        'SternVolmer is a rate-parameter model over a concentration variable; SymmetryFactor is a '
        'structural crossing-coordinate theory. If the quencher acts by electron transfer, kq '
        'could be an activated rate whose barrier is a Marcus-type two-parabola crossing, and the '
        'symmetry factor supplies the thermoneutral crossing coordinate. The candidate bridge '
        'needs a rate law and a translation from [Q] to a driving force. Neither is delivered.',
        'ScSvCandidateCtx',
        'PhotoLean.SymmetryFactor.tsCoordZero', 'PhotoLean.SternVolmer.KSV',
        'scope-E2-candidate-bridge', 'SL-E2-SV-01',
        'A delivered identification of the Stern-Volmer constant KSV = kq/k0 with a '
        'crossing-controlled rate at the SymmetryFactor barrier, plus a total translation from '
        'quencher concentration to the driving force, is missing.',
        'A context at which the SV quenching rate is not a crossing-controlled rate would refute '
        'the candidate implication; no such statement is delivered.',
        'The candidate is a rate-versus-structure bridge; the weakest composable form is an '
        'implication from a crossing-controlled rate premise to the SV ratio premise.'))

    qs.append(unresolved(
        'Q-E2-SQ-01', 'P-SymmetryFactor-QuantumYield',
        'Is a quantum-yield channel controlled by the SymmetryFactor crossing height?',
        'Can one parallel decay channel of the QuantumYield calculus be read as a '
        'crossing-controlled nonradiative channel whose barrier is the SymmetryFactor '
        'thermoneutral crossing height?',
        'QuantumYield is an algebraic rate-share calculus; SymmetryFactor gives surfaces and a '
        'crossing coordinate. A bridge would fill a QuantumYield channel with a crossing-controlled '
        'rate and read its share through the symmetry-factor barrier. No delivered instance fills '
        'a channel with such a rate, and the QY calculus leaves the rate vector arbitrary.',
        'ScQyCandidateCtx',
        'PhotoLean.SymmetryFactor.tsCoordZero', 'PhotoLean.QuantumYield.yieldOf',
        'scope-E2-candidate-bridge', 'SL-E2-SQ-01',
        'A delivered instance that fills a QuantumYield channel with a crossing-controlled rate '
        'whose barrier is the SymmetryFactor thermoneutral crossing height is missing; the QY '
        'calculus is purely algebraic.',
        'A quantum-yield channel whose rate is not crossing-controlled would refute the candidate '
        'implication; no such statement is delivered.',
        'The candidate is a rate-versus-share bridge; the weakest composable form is an implication '
        'from a crossing-controlled channel premise to the yield-share premise.'))

    qs.append(unresolved(
        'Q-E2-SF-01', 'P-SymmetryFactor-FluorPhos',
        'Are the FluorPhos ISC and IC channels crossing-controlled with the SymmetryFactor barrier?',
        'Can the FluorPhos S1 nonradiative channels kISC and kIC be read as crossing-controlled '
        'processes whose barriers are the SymmetryFactor thermoneutral crossing height?',
        'FluorPhos treats the S1 intersystem-crossing and internal-conversion channels as rate '
        'parameters; SymmetryFactor gives a crossing geometry. A bridge would identify kIC or '
        'kISC with an activated crossing rate whose barrier is the symmetry-factor surface height. '
        'The FluorPhos model has no energy surface and SymmetryFactor has no spin-orbit or rate '
        'object, so the candidate is chemically plausible but not delivered.',
        'ScFpCandidateCtx',
        'PhotoLean.SymmetryFactor.tsCoordZero', 'PhotoLean.FluorPhos.iscBranch',
        'scope-E2-candidate-bridge', 'SL-E2-SF-01',
        'A delivered rate law identifying the FluorPhos iscBranch or internal-conversion channel '
        'with a crossing-controlled rate at the SymmetryFactor barrier is missing.',
        'A FluorPhos channel whose rate is not crossing-controlled would refute the candidate '
        'implication; no such statement is delivered.',
        'The candidate is a rate-versus-branch bridge; the weakest composable form is an '
        'implication from a crossing-controlled channel premise to the ISC branch premise.'))

    # ---------------------------------------------------------------- outOfScope
    def out_of_scope(qid, pid, title, question, rationale, ctx_id, src, tgt, search_id,
                     jurisdiction, falsification, kind_rationale,
                     left_reason=None, right_reason=None):
        return {
            'queryId': qid, 'pairId': pid, 'title': title,
            'chemicalQuestion': question, 'chemicalRationale': rationale,
            'endpoints': {'source': ep(src), 'target': ep(tgt)},
            'sharedContext': {
                'id': ctx_id, 'fields': CONTEXTS[ctx_id]['fields'],
                'physicalReading': CONTEXTS[ctx_id]['physicalReading'],
                'provenance': CONTEXTS[ctx_id]['provenance']},
            'translations': {
                'left': none_decl(left_reason or
                                  'No total translation from this descriptor set to the partner '
                                  'descriptor set is declared; the two physical contexts are disjoint.'),
                'right': none_decl(right_reason or
                                   'No total translation from the partner descriptor set to this '
                                   'descriptor set is declared; the two physical contexts are disjoint.')},
            'premises': true_premises(ctx_id, 'fun _ : %s => True' % ctx_id,
                                      'No certificate is claimed; the jurisdiction record does not '
                                      'consume a premise.'),
            'observationChannels': [],
            'scope': {**SCOPES['scope-E2-jurisdiction']},
            'expectedKind': 'implication',
            'expectedKindRationale': kind_rationale,
            'falsificationCondition': falsification,
            'outcome': {
                'status': 'outOfScope',
                'rationale': jurisdiction,
                'evidence': jurisdiction_evidence(search_id, jurisdiction)},
            'provenance': {
                'kind': 'jurisdiction', 'sourceArtifact': SEARCH_REL, 'locator': search_id,
                'jurisdictionStatement': jurisdiction,
                'legacyDisposition': LEGACY_NOTE},
        }

    qs.append(out_of_scope(
        'Q-E2-BF-01', 'P-BEP-Forster',
        'Is the Förster transfer rate an activated BEP process?',
        'Is the Förster resonance energy-transfer rate an activated elementary-step rate whose '
        'barrier is the BEP activation barrier at the same driving force?',
        'Förster transfer is a through-space dipolar process with an R^-6 distance law and no '
        'reaction coordinate; BEP is an activated crossing with a reorganization energy and a '
        'driving force. The two models share no energy coordinate, and a translation from '
        '(tauD, r6, R) to (lam, x) is not a coordinate change of the declared model. The question '
        'is outside the declared jurisdiction, not logically false.',
        'BepForsterDisjointCtx',
        'PhotoLean.BEP.eact', 'PhotoLean.Forster.fretRate',
        'SL-E2-BF-01',
        'No shared context or declared translation exists: BEP has a reaction coordinate and a '
        'barrier, Förster has a donor lifetime and a donor-acceptor separation with an R^-6 rate '
        'law. The absence is jurisdictional, not a refutation or a logical non-existence claim.',
        'A delivered statement identifying the Förster R^-6 rate with a BEP barrier would refute '
        'the outOfScope boundary; none exists.',
        'The would-be form is an implication from a BEP barrier premise to a Förster rate premise; '
        'the jurisdiction record denies the shared translation.',
        left_reason='No total translation from the BEP (lam, x) barrier descriptor to the Förster '
                    '(tauD, r6, R) transfer descriptor is declared; the two coordinate sets are disjoint.',
        right_reason='No total translation from the Förster (tauD, r6, R) transfer descriptor to the '
                     'BEP (lam, x) barrier descriptor is declared; the two coordinate sets are disjoint.'))

    qs.append(out_of_scope(
        'Q-E2-BE-01', 'P-BEP-Einstein',
        'Are the Einstein A/B coefficients an activated BEP barrier?',
        'Do the Einstein radiative coefficients constrain or imply the BEP activation barrier of '
        'the same transition?',
        'Einstein A/B are radiative transition coefficients with a radiation-density factor; BEP '
        'is a ground-state reaction barrier with a reaction coordinate and a reorganization '
        'energy. The coefficient pair does not contain a barrier and the barrier does not contain '
        'a radiative rate; no shared scalar or declared translation exists. The question is '
        'outside the declared jurisdiction.',
        'BepEinsteinDisjointCtx',
        'PhotoLean.BEP.eact', 'PhotoLean.Einstein.radFactor',
        'SL-E2-BE-01',
        'No shared context or declared translation exists: the BEP barrier is an activated '
        'crossing energy, while the Einstein coefficients are radiative transition quantities. '
        'The absence is jurisdictional, not a refutation.',
        'A delivered statement identifying an Einstein coefficient with a BEP barrier would refute '
        'the outOfScope boundary; none exists.',
        'The would-be form is an implication from a BEP barrier premise to a radiative-coefficient '
        'premise; the jurisdiction record denies the shared translation.',
        left_reason='No total translation from the BEP (lam, x) barrier descriptor to the Einstein '
                    '(h, c, nu) radiative-coefficient descriptor is declared; the two coordinate sets are disjoint.',
        right_reason='No total translation from the Einstein (h, c, nu) radiative-coefficient '
                     'descriptor to the BEP (lam, x) barrier descriptor is declared; the two coordinate sets are disjoint.'))

    qs.append(out_of_scope(
        'Q-E2-SK-01', 'P-SymmetryFactor-KashaVavilov',
        'Does the SymmetryFactor crossing coordinate constrain Kasha-Vavilov spectral invariance?',
        'Does the SymmetryFactor beta = 1/2 crossing coordinate constrain the Kasha-Vavilov '
        'predicate that normalized spectra are excitation-independent?',
        'SymmetryFactor is a structural crossing-coordinate theory over a curvature pair; '
        'KashaVavilov.SpecSame is a normalized-spectrum predicate over a ladder at two excitation '
        'levels. A crossing coordinate does not enter a normalized spectrum and a spectrum does '
        'not enter a surface geometry. No shared observable or declared translation exists, so the '
        'question is outside the declared jurisdiction.',
        'ScKvDisjointCtx',
        'PhotoLean.SymmetryFactor.BetaHalfReading', 'PhotoLean.KashaVavilov.SpecSame',
        'SL-E2-SK-01',
        'No shared context or declared translation exists: the curvature pair and crossing '
        'coordinate share no scalar with the ladder rates and normalized spectra. The absence is '
        'jurisdictional, not a refutation.',
        'A delivered statement relating the crossing coordinate to a normalized-spectrum '
        'predicate would refute the outOfScope boundary; none exists.',
        'The would-be form is an implication from a crossing-coordinate premise to a '
        'spectral-invariance premise; the jurisdiction record denies the shared translation.'))

    qs.append(out_of_scope(
        'Q-E2-SFo-01', 'P-SymmetryFactor-Forster',
        'Does the SymmetryFactor crossing geometry constrain the Förster orientation factor?',
        'Does the SymmetryFactor thermoneutral crossing coordinate constrain the Förster '
        'orientation factor kappa^2 or the R^-6 transfer rate?',
        'The Förster orientation factor is a donor-acceptor dipole geometry of two distinct '
        'chromophores; the symmetry factor is a two-parabola crossing coordinate of a reaction '
        'step. Both are geometric, but they are different geometries with no shared scalar or '
        'declared translation. The question is outside the declared jurisdiction.',
        'ScForsterDisjointCtx',
        'PhotoLean.SymmetryFactor.tsCoordZero', 'PhotoLean.Forster.kappaSq',
        'SL-E2-SFo-01',
        'No shared context or declared translation exists: the crossing coordinate of a '
        'two-parabola reaction step shares no scalar with the orientation/distance geometry of a '
        'donor-acceptor pair. The absence is jurisdictional, not a refutation.',
        'A delivered statement relating the crossing coordinate to the orientation factor would '
        'refute the outOfScope boundary; none exists.',
        'The would-be form is an implication from a crossing-coordinate premise to an '
        'orientation-factor premise; the jurisdiction record denies the shared translation.'))

    qs.append(out_of_scope(
        'Q-E2-SEIn-01', 'P-SymmetryFactor-Einstein',
        'Does the SymmetryFactor crossing coordinate constrain Einstein radiative coefficients?',
        'Does the SymmetryFactor thermoneutral crossing coordinate constrain the Einstein A/B '
        'coefficients or the radiative lifetime of the same transition?',
        'The Einstein coefficients are radiative transition quantities with a radiation-density '
        'factor; the symmetry factor is a structural ground/excited crossing geometry. The '
        'radiative coefficients contain no crossing coordinate and the crossing geometry contains '
        'no radiative rate. No shared scalar or declared translation exists; the question is '
        'outside the declared jurisdiction.',
        'ScEinsteinDisjointCtx',
        'PhotoLean.SymmetryFactor.tsCoordZero', 'PhotoLean.Einstein.radFactor',
        'SL-E2-SEIn-01',
        'No shared context or declared translation exists: the crossing coordinate of a '
        'two-parabola step shares no scalar with the radiative A/B coefficients. The absence is '
        'jurisdictional, not a refutation.',
        'A delivered statement relating the crossing coordinate to an Einstein coefficient would '
        'refute the outOfScope boundary; none exists.',
        'The would-be form is an implication from a crossing-coordinate premise to a '
        'radiative-coefficient premise; the jurisdiction record denies the shared translation.'))

    return qs


def build_pairs(queries):
    by_pair = {}
    for q in queries:
        by_pair.setdefault(q['pairId'], []).append(q)
    pairs = []
    for pid in E2_PAIRS:
        row = QUEUE_BY_ID[pid]
        qs = by_pair[pid]
        pairs.append({
            'pairId': pid,
            'theories': row['theories'],
            'primaryCluster': row['screeningCluster'],
            'queryIds': [q['queryId'] for q in qs],
            'queries': qs,
        })
    return pairs


def main():
    probe_sha = sha_file(PROBE_REL)
    queries = build_queries(probe_sha)
    pairs = build_pairs(queries)

    # ---------------------------------------------------------------- search log
    search_entries = SEARCH_ENTRIES
    search_log = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-search-log',
        'round': 'R4',
        'generatedOn': '2026-11-04',
        'workPackage': 'WP-excited-state-kinetics-02',
        'snapshot': SNAP_ID,
        'entries': search_entries,
        'counts': {'entries': len(search_entries)},
        'nonClaims': [
            'A scoped search records what the named statements and contexts did not supply; it is not a completeness claim.',
            'An outOfScope entry records jurisdiction, not logical non-existence.',
            'An unresolved entry records a remaining candidate bridge, not a refutation.',
            'No failed proof attempt is recorded as refuted evidence.',
        ],
    }
    dump(SEARCH_REL, search_log)
    search_sha = sha_file(SEARCH_REL)

    # ---------------------------------------------------------------- screening
    status_counts = {}
    kind_counts = {}
    for q in queries:
        status_counts[q['outcome']['status']] = status_counts.get(q['outcome']['status'], 0) + 1
        kind_counts[q['expectedKind']] = kind_counts.get(q['expectedKind'], 0) + 1
    counts = {
        'pairs': len(pairs), 'queries': len(queries),
        'byStatus': status_counts, 'byExpectedKind': kind_counts,
        'certified': status_counts.get('certified', 0),
        'refuted': status_counts.get('refuted', 0),
        'unresolved': status_counts.get('unresolved', 0),
        'notEstablished': status_counts.get('notEstablished', 0),
        'outOfScope': status_counts.get('outOfScope', 0),
    }
    screening = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-screening-package',
        'round': 'R4',
        'generatedOn': '2026-11-04',
        'workPackage': {
            'id': 'WP-excited-state-kinetics-02',
            'title': 'Excited-state kinetics, second half: BEP and SymmetryFactor bridge screening',
            'source': 'R4 plan file, Package E2',
            'pairIds': list(E2_PAIRS),
            'pairCount': len(E2_PAIRS),
            'note': 'Exactly the fourteen pairs assigned to Package E2. No accepted R2/R3 pair is rescreened.',
        },
        'statusVocabulary': STATUSES,
        'kindVocabulary': KINDS,
        'allowedAxioms': ALLOWED_AXIOMS,
        'snapshot': {
            'id': SNAP_ID,
            'date': '2026-11-04',
            'round': 'R4',
            'inventory': INV_REL, 'inventorySha256': sha_file(INV_REL),
            'pairQueue': QUEUE_REL, 'pairQueueSha256': sha_file(QUEUE_REL),
            'clusterPlan': CLUSTER_REL, 'clusterPlanSha256': sha_file(CLUSTER_REL),
            'boundary': BOUNDARY_REL, 'boundarySha256': sha_file(BOUNDARY_REL),
            'legacyRegistry': REGISTRY_REL, 'legacyRegistrySha256': sha_file(REGISTRY_REL),
            'acceptedR2Package': R2_REL, 'acceptedR2Sha256': sha_file(R2_REL),
            'acceptedR3Package': R3_REL, 'acceptedR3Sha256': sha_file(R3_REL),
            'leanToolchain': 'leanprover/lean4:v4.17.0',
            'deliveredLeanFileCount': 102,
            'note': 'The mutable R4 cumulative coverage ledger is deliberately not pinned by this package.',
        },
        'inventoryReference': {
            'path': INV_REL, 'sha256': sha_file(INV_REL),
            'statementRows': len(INV['statements']),
            'screeningEligibleRows': sum(1 for s in INV['statements'] if s['screeningEligible']),
        },
        'legacyRegistryReference': {
            'path': REGISTRY_REL, 'sha256': sha_file(REGISTRY_REL),
            'certificateCount': len(load(REGISTRY_REL)['certificates']),
            'queryCount': len(load(REGISTRY_REL)['queries']),
            'recordCount': len(load(REGISTRY_REL)['records']),
        },
        'acceptedCoverageReference': {
            'acceptedPairs': 21,
            'sources': [R2_REL, R3_REL],
            'note': 'The accepted R2/R3 packages are pinned by hash; the R4 cumulative ledger is not.',
        },
        'searchLogReference': {
            'path': SEARCH_REL, 'sha256': search_sha, 'entryCount': len(search_entries)},
        'probeReference': {
            'path': PROBE_REL, 'sha256': probe_sha,
            'declarationCount': 5, 'log': PROBE_LOG_REL},
        'contextLibrary': CONTEXTS,
        'scopeLibrary': SCOPES,
        'pairs': pairs,
        'counts': counts,
        'nonClaims': [
            'This package is not a completeness claim about any pair.',
            'A certified row is a checked relation under its declared context, premises and snapshot; it is not a claim of physical universality.',
            'An unresolved row is not a negative claim and is not a refutation.',
            'An outOfScope row records jurisdiction, not logical absence.',
            'No pair was forced into a relation to increase edge or certification counts.',
            'The legacy registry is read-only in R4; its pair-level absence anchors are coverage history, not audit verdicts.',
            'The 14/136 count is a bounded-audit coverage count, not the cumulative R4 ledger.',
        ],
    }
    dump(SCREENING_REL, screening)
    screening_sha = sha_file(SCREENING_REL)

    # ---------------------------------------------------------------- fragment
    fragment = {
        'schemaVersion': '1.0.0',
        'artifactKind': 'bounded-coverage-fragment',
        'round': 'R4',
        'generatedOn': '2026-11-04',
        'workPackage': 'WP-excited-state-kinetics-02',
        'packagePath': SCREENING_REL,
        'screeningSha256': screening_sha,
        'pairCount': len(pairs),
        'queryCount': len(queries),
        'byStatus': status_counts,
        'byExpectedKind': kind_counts,
        'primaryCluster': 'excited-state-kinetics',
        'screenedPairs': [
            {'pairId': p['pairId'], 'theories': p['theories'],
             'primaryCluster': p['primaryCluster'], 'queryCount': len(p['queries']),
             'byStatus': {st: sum(1 for x in p['queries'] if x['outcome']['status'] == st)
                          for st in sorted({x['outcome']['status'] for x in p['queries']})}}
            for p in pairs
        ],
        'acceptance': 'submitted-R4-pending-review',
        'nonClaims': [
            'This fragment contributes fourteen pairs to the R4 cumulative ledger; it does not itself edit the ledger.',
            'Screened is not the same as certified.',
            'The fragment records the package status as submitted-R4-pending-review until independent K3 review.',
        ],
    }
    dump(FRAGMENT_REL, fragment)

    print('probe       ', probe_sha, PROBE_REL)
    print('search-log  ', search_sha, SEARCH_REL)
    print('screening   ', screening_sha, SCREENING_REL)
    print('fragment    ', sha_file(FRAGMENT_REL), FRAGMENT_REL)
    print('counts      ', json.dumps(counts, ensure_ascii=False))


# The search entries are defined below the builder so the command lists stay readable.
SEARCH_ENTRIES = [
    # ---------------------------------------------------------------- Kasha / SymmetryFactor
    {
        'searchId': 'SL-E2-KS-01',
        'queryId': 'Q-E2-KS-01',
        'pairId': 'P-Kasha-SymmetryFactor',
        'status': 'unresolved',
        'scope': 'scope-E2-candidate-bridge',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-Kasha-PhotoLean-Kasha-funnelRatio',
            'stmt-Kasha-PhotoLean-Kasha-decay',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-asymReactantSurface',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'KashaScCandidateCtx (rad, ic, kr, kp): a ladder rate function and a curvature pair with '
            'no declared translation'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 603: SymmetryFactor vs Kasha no edge',
             'finding': 'The legacy register states that the curvature-pair scalar shares no object with the ladder branching rates.'},
            {'artifact': 'PhotoLean/Kasha/Basic.lean', 'locator': 'funnelRatio, decay, radBranch',
             'finding': 'The ladder leaves ic as an arbitrary rate function; there is no energy surface or barrier.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'asymReactantSurface, tsCoordZero',
             'finding': 'SymmetryFactor exposes surfaces and a crossing coordinate, not a rate law.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-Kasha-SymmetryFactor',
             'finding': 'The legacy record is a pair-level notEstablished anchor, not a named query.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/Kasha --include='*.lean'",
             'purpose': 'Search the Kasha modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Kasha' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered Kasha statement.',
             'result': 'One match, a docstring reference to Kasha K4b; no import or declaration.'},
            {'command': "grep -h '^import' PhotoLean/Kasha/*.lean | sort -u",
             'purpose': 'Measure the Kasha module dependencies.',
             'result': 'Mathlib plus Kasha submodules and PhotoLean.Marcus.Basic; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no Kasha import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-SymmetryFactor',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': "label=absence subtype=registered-absence; rec-notestablished-P-Kasha-SymmetryFactor status=notEstablished certificate=None; candidate=False."},
        ],
        'strategiesAttempted': [
            {'strategy': 'Read the ladder ic rate as a crossing-controlled rate at the SymmetryFactor barrier.',
             'outcome': 'No delivered rate law relates ic to a two-parabola surface.'},
            {'strategy': 'Search for a composition row from Kasha funnelRatio to SymmetryFactor tsCoordZero.',
             'outcome': 'No typed parent chain or delivered theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'rate-versus-structure candidate',
             'statement': 'Kasha.funnelRatio = rad 0 * ic 1 / (rad 1 * decay 0) versus '
                          'SymmetryFactor.tsCoordZero kr kp; a crossing-controlled IC rate would be the bridge.',
             'status': 'candidate only; no statement-level identification is delivered.'},
        ],
        'remainingGap': 'A delivered identification of the ladder internal-conversion rate with a crossing-controlled rate at the SymmetryFactor barrier, plus a translation from the ladder rates to the curvature pair, is missing.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/Kasha --include='*.lean'",
            "grep -rn 'Kasha' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-Kasha-SymmetryFactor',
        ],
        'rationale': 'The legacy register says no edge and no shared scalar. A kinetic candidate remains, so the honest status is unresolved, not refuted and not a forced edge.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / SternVolmer
    {
        'searchId': 'SL-E2-SV-01',
        'queryId': 'Q-E2-SV-01',
        'pairId': 'P-SymmetryFactor-SternVolmer',
        'status': 'unresolved',
        'scope': 'scope-E2-candidate-bridge',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-SternVolmer-PhotoLean-SternVolmer-KSV',
            'sternvolmer.intensityDyn',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScSvCandidateCtx (kr, kp, k0, kq, q): a crossing-controlled quench channel with no '
            'declared translation from [Q] to a driving force'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 945: SternVolmer vs SymmetryFactor no edge',
             'finding': 'The SV model has no energy surface and no geometry; its contacts run through QuantumYield.'},
            {'artifact': 'PhotoLean/SternVolmer/Basic.lean', 'locator': 'dynDecay, KSV, svRatioDyn',
             'finding': 'kq is a free concentration-channel parameter; no driving force or barrier is defined.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'tsCoordZero',
             'finding': 'The symmetry factor is a crossing coordinate, not a rate or a concentration response.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-SternVolmer',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/SternVolmer --include='*.lean'",
             'purpose': 'Search the SV modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'SternVolmer' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered SV statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/SternVolmer/*.lean | sort -u",
             'purpose': 'Measure the SV module dependencies.',
             'result': 'Mathlib plus SternVolmer submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no SternVolmer import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-SternVolmer',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-SternVolmer status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Read kq as an activated crossing rate at the SymmetryFactor barrier.',
             'outcome': 'No rate law and no translation [Q] -> driving force are delivered.'},
            {'strategy': 'Search for a composition row through QuantumYield.',
             'outcome': 'SV reaches the batch through QuantumYield only; no row reaches SymmetryFactor.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'rate-versus-structure candidate',
             'statement': 'SternVolmer.KSV = kq / k0 versus SymmetryFactor.tsCoordZero; an electron-transfer '
                          'quenching step would need a Marcus-type barrier and a crossing coordinate.',
             'status': 'candidate only; no statement-level identification is delivered.'},
        ],
        'remainingGap': 'A delivered rate law for the SV quenching channel as a crossing-controlled process, plus a total translation from quencher concentration to the driving force, is missing.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/SternVolmer --include='*.lean'",
            "grep -rn 'SternVolmer' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-SternVolmer',
        ],
        'rationale': 'The candidate bridge is chemically motivated but not delivered; the honest status is unresolved, not refuted and not a forced edge.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / QuantumYield
    {
        'searchId': 'SL-E2-SQ-01',
        'queryId': 'Q-E2-SQ-01',
        'pairId': 'P-SymmetryFactor-QuantumYield',
        'status': 'unresolved',
        'scope': 'scope-E2-candidate-bridge',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-QuantumYield-PhotoLean-QuantumYield-yieldOf',
            'stmt-QuantumYield-PhotoLean-QuantumYield-totalRate',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScQyCandidateCtx (kr, kp, k, i): one algebraic channel share with no delivered '
            'crossing-controlled rate instance'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 948: QuantumYield vs SymmetryFactor no edge',
             'finding': 'The parallel-channel calculus is purely algebraic; the energy-side theories enter only through specific rates.'},
            {'artifact': 'PhotoLean/QuantumYield/Basic.lean', 'locator': 'yieldOf, totalRate, QYData',
             'finding': 'The rate vector is arbitrary; no rate law or surface is defined.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'tsCoordZero',
             'finding': 'The symmetry factor is a crossing coordinate, not a channel rate.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-QuantumYield',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/QuantumYield --include='*.lean'",
             'purpose': 'Search the QY modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'QuantumYield' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered QY statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/QuantumYield/*.lean | sort -u",
             'purpose': 'Measure the QY module dependencies.',
             'result': 'Mathlib plus QuantumYield submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no QuantumYield import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-QuantumYield',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-QuantumYield status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Fill one QY channel with a crossing-controlled rate at the SymmetryFactor barrier.',
             'outcome': 'No delivered instance fills an arbitrary channel with such a rate.'},
            {'strategy': 'Search the delivered composition rows for a SymmetryFactor channel.',
             'outcome': 'The composition rows use Kasha, SV, FP, Einstein, Forster and RACI rates; none uses a SymmetryFactor surface.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'rate-versus-share candidate',
             'statement': 'QuantumYield.yieldOf = k i / totalRate versus SymmetryFactor.tsCoordZero; '
                          'a crossing-controlled channel would carry the two-parabola barrier.',
             'status': 'candidate only; no statement-level instance is delivered.'},
        ],
        'remainingGap': 'A delivered instance that fills a QuantumYield channel with a crossing-controlled rate whose barrier is the SymmetryFactor thermoneutral crossing height is missing.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/QuantumYield --include='*.lean'",
            "grep -rn 'QuantumYield' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-QuantumYield',
        ],
        'rationale': 'The QY calculus is algebraic and the symmetry factor is structural; a candidate bridge remains but is not delivered. Unresolved, not refuted.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / FluorPhos
    {
        'searchId': 'SL-E2-SF-01',
        'queryId': 'Q-E2-SF-01',
        'pairId': 'P-SymmetryFactor-FluorPhos',
        'status': 'unresolved',
        'scope': 'scope-E2-candidate-bridge',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-FluorPhos-PhotoLean-FluorPhos-iscBranch',
            'stmt-FluorPhos-PhotoLean-FluorPhos-s1Decay',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScFpCandidateCtx (kr, kp, kF, kISC, kIC): rate parameters with no delivered '
            'crossing-controlled rate law'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 952-953: FluorPhos vs SymmetryFactor no edge',
             'finding': 'The competition layer has branch probabilities and no energy surface; its contacts run through QuantumYield.'},
            {'artifact': 'PhotoLean/FluorPhos/Basic.lean', 'locator': 'iscBranch, s1Decay, phiF',
             'finding': 'kISC and kIC are free rate parameters; no barrier or surface is defined.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'tsCoordZero',
             'finding': 'The symmetry factor is a crossing coordinate, not a spin-orbit or rate object.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-FluorPhos',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/FluorPhos --include='*.lean'",
             'purpose': 'Search the FluorPhos modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'FluorPhos' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered FluorPhos statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/FluorPhos/*.lean | sort -u",
             'purpose': 'Measure the FluorPhos module dependencies.',
             'result': 'Mathlib plus FluorPhos submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no FluorPhos import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-FluorPhos',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-FluorPhos status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Read kISC or kIC as a crossing-controlled rate at the SymmetryFactor barrier.',
             'outcome': 'No delivered rate law or spin-orbit bridge exists.'},
            {'strategy': 'Search the delivered FluorPhos rows for a surface or barrier.',
             'outcome': 'The model is a two-state rate-parameter competition with no surface.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'rate-versus-branch candidate',
             'statement': 'FluorPhos.iscBranch = kISC / s1Decay versus SymmetryFactor.tsCoordZero; '
                          'a crossing-controlled ISC/IC channel would be the bridge.',
             'status': 'candidate only; no statement-level identification is delivered.'},
        ],
        'remainingGap': 'A delivered rate law identifying the FluorPhos ISC or IC channel with a crossing-controlled rate at the SymmetryFactor barrier is missing.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/FluorPhos --include='*.lean'",
            "grep -rn 'FluorPhos' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-FluorPhos',
        ],
        'rationale': 'The candidate bridge is chemically plausible but not delivered; the honest status is unresolved, not refuted and not a forced edge.',
    },
    # ---------------------------------------------------------------- BEP / Forster
    {
        'searchId': 'SL-E2-BF-01',
        'queryId': 'Q-E2-BF-01',
        'pairId': 'P-BEP-Forster',
        'status': 'outOfScope',
        'scope': 'scope-E2-jurisdiction',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-BEP-PhotoLean-BEP-eact',
            'stmt-Forster-PhotoLean-Forster-fretRate',
            'stmt-Forster-PhotoLean-Forster-r0six',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'BepForsterDisjointCtx (lam, x, tauD, r6, R): a barrier coordinate and a donor-acceptor '
            'distance law with no shared scalar'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 964-965: Forster vs BEP no edge',
             'finding': 'The transfer geometry shares no scalar with the energy-surface family.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'fretRate, r0six',
             'finding': 'The FRET rate is (1/tauD)*(r6/R^6); there is no activation barrier or driving force.'},
            {'artifact': 'PhotoLean/BEP/Basic.lean', 'locator': 'eact',
             'finding': 'eact requires a scalar reaction coordinate and reorganization energy; there is no distance law.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-BEP-Forster',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'Forster' PhotoLean/BEP --include='*.lean'",
             'purpose': 'Search the BEP modules for a delivered Forster statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'BEP' PhotoLean/Forster --include='*.lean'",
             'purpose': 'Search the Forster modules for a delivered BEP statement.',
             'result': 'Three matches, all docstring references to the fidelity script path theories/BEP/probes/bep-fidelity.py; no import or declaration.'},
            {'command': "grep -h '^import' PhotoLean/BEP/*.lean | sort -u",
             'purpose': 'Measure the BEP module dependencies.',
             'result': 'Mathlib plus BEP submodules, Hammond.Basic and Marcus.Basic; no Forster import.'},
            {'command': "grep -h '^import' PhotoLean/Forster/*.lean | sort -u",
             'purpose': 'Measure the Forster module dependencies.',
             'result': 'Mathlib plus Forster submodules; no BEP import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-BEP-Forster',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-BEP-Forster status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Read the FRET R^-6 rate as an activated BEP rate at a fixed distance.',
             'outcome': 'The FRET rate has no barrier or driving force; the analogy is not a translation.'},
            {'strategy': 'Search for a delivered theorem mentioning both BEP.eact and Forster.fretRate.',
             'outcome': 'No such theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'no shared descriptor',
             'statement': 'BEP.eact is a function of (lam, x); Forster.fretRate is a function of '
                          '(tauD, r6, R). No total map between the two parameter spaces is declared.',
             'status': 'outside jurisdiction; not a logical absence claim.'},
        ],
        'remainingGap': 'Jurisdiction boundary: the two models share no scalar and no declared translation. This is not a claim that no physical relation exists, only that the frozen statement universe gives no context in which the question is well formed.',
        'jurisdictionReason': 'No shared context or declared translation exists between the activated two-parabola barrier and the R^-6 donor-acceptor transfer rate.',
        'recomputeCommands': [
            "grep -rn 'Forster' PhotoLean/BEP --include='*.lean'",
            "grep -rn 'BEP' PhotoLean/Forster --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-BEP-Forster',
        ],
        'rationale': 'The pair is outside the declared audit jurisdiction because the two statement contexts share no physical coordinate; the record does not assert logical non-existence.',
    },
    # ---------------------------------------------------------------- BEP / Einstein
    {
        'searchId': 'SL-E2-BE-01',
        'queryId': 'Q-E2-BE-01',
        'pairId': 'P-BEP-Einstein',
        'status': 'outOfScope',
        'scope': 'scope-E2-jurisdiction',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-BEP-PhotoLean-BEP-eact',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'BepEinsteinDisjointCtx (lam, x, h, c, nu): a reaction barrier and a radiative '
            'transition coefficient with no shared scalar'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 969-970: Einstein vs BEP no edge',
             'finding': 'The radiative conversions have no reaction coordinate; their only machine contact is the QuantumYield anchor.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'radFactor, aOfB, tauR',
             'finding': 'The A/B coefficients are radiative transition quantities with a radiation-density factor; no barrier is defined.'},
            {'artifact': 'PhotoLean/BEP/Basic.lean', 'locator': 'eact',
             'finding': 'eact is an activated crossing energy; there is no radiative coefficient.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-BEP-Einstein',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'Einstein' PhotoLean/BEP --include='*.lean'",
             'purpose': 'Search the BEP modules for a delivered Einstein statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'BEP' PhotoLean/Einstein --include='*.lean'",
             'purpose': 'Search the Einstein modules for a delivered BEP statement.',
             'result': 'One match, a docstring reference to the fidelity script path theories/BEP/probes/bep-fidelity.py; no import or declaration.'},
            {'command': "grep -h '^import' PhotoLean/BEP/*.lean | sort -u",
             'purpose': 'Measure the BEP module dependencies.',
             'result': 'Mathlib plus BEP submodules, Hammond.Basic and Marcus.Basic; no Einstein import.'},
            {'command': "grep -h '^import' PhotoLean/Einstein/*.lean | sort -u",
             'purpose': 'Measure the Einstein module dependencies.',
             'result': 'Mathlib plus Einstein submodules; no BEP import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-BEP-Einstein',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-BEP-Einstein status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Read the BEP barrier as an Einstein coefficient constraint.',
             'outcome': 'The coefficient pair contains no barrier and the barrier contains no radiative rate.'},
            {'strategy': 'Search for a delivered theorem mentioning both BEP.eact and Einstein.radFactor.',
             'outcome': 'No such theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'no shared descriptor',
             'statement': 'BEP.eact is a function of (lam, x); Einstein.radFactor is a function of '
                          '(h, c, nu). No total map between the two parameter spaces is declared.',
             'status': 'outside jurisdiction; not a logical absence claim.'},
        ],
        'remainingGap': 'Jurisdiction boundary: the activated barrier and the radiative A/B coefficients share no scalar and no declared translation.',
        'jurisdictionReason': 'No shared context or declared translation exists between the activated two-parabola barrier and the radiative transition coefficients.',
        'recomputeCommands': [
            "grep -rn 'Einstein' PhotoLean/BEP --include='*.lean'",
            "grep -rn 'BEP' PhotoLean/Einstein --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-BEP-Einstein',
        ],
        'rationale': 'The pair is outside the declared audit jurisdiction because the two statement contexts share no physical coordinate; the record does not assert logical non-existence.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / KashaVavilov
    {
        'searchId': 'SL-E2-SK-01',
        'queryId': 'Q-E2-SK-01',
        'pairId': 'P-SymmetryFactor-KashaVavilov',
        'status': 'outOfScope',
        'scope': 'scope-E2-jurisdiction',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'symmetry.betaHalfReading',
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-KashaVavilov-PhotoLean-KashaVavilov-SpecSame',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScKvDisjointCtx (kr, kp, rad, ic, M, N): a curvature pair and a normalized-spectrum '
            'predicate with no shared scalar'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'line 942: KashaVavilov vs SymmetryFactor no edge',
             'finding': 'No shared scalar: the D2 predicates speak about yields and ladders; the curvature pair shares none of them.'},
            {'artifact': 'PhotoLean/KashaVavilov/Basic.lean', 'locator': 'SpecSame',
             'finding': 'SpecSame compares normalized spectra at two excitation levels; no surface or curvature enters.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'BetaHalfReading, tsCoordZero',
             'finding': 'The symmetry-factor reading is a crossing-coordinate proposition; no spectrum enters.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-KashaVavilov',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/KashaVavilov --include='*.lean'",
             'purpose': 'Search the KashaVavilov modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'KashaVavilov' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered KashaVavilov statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/KashaVavilov/*.lean | sort -u",
             'purpose': 'Measure the KashaVavilov module dependencies.',
             'result': 'Mathlib plus Kasha and KashaVavilov submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no KashaVavilov import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-KashaVavilov',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-KashaVavilov status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Relate the crossing coordinate to the spectral-invariance predicate.',
             'outcome': 'No shared observable; a crossing coordinate does not enter a normalized spectrum.'},
            {'strategy': 'Search for a delivered theorem mentioning both the curvature pair and SpecSame.',
             'outcome': 'No such theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'no shared observable',
             'statement': 'SymmetryFactor.BetaHalfReading is a proposition about (kr, kp); '
                          'KashaVavilov.SpecSame is a proposition about (rad, ic, M, N). No translation is declared.',
             'status': 'outside jurisdiction; not a logical absence claim.'},
        ],
        'remainingGap': 'Jurisdiction boundary: the structural crossing coordinate and the normalized-spectrum predicate share no observable and no declared translation.',
        'jurisdictionReason': 'No shared context or declared translation exists between a two-parabola crossing coordinate and a normalized-spectrum predicate.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/KashaVavilov --include='*.lean'",
            "grep -rn 'KashaVavilov' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-KashaVavilov',
        ],
        'rationale': 'The pair is outside the declared audit jurisdiction because the two statement contexts share no observable; the record does not assert logical non-existence.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / Forster
    {
        'searchId': 'SL-E2-SFo-01',
        'queryId': 'Q-E2-SFo-01',
        'pairId': 'P-SymmetryFactor-Forster',
        'status': 'outOfScope',
        'scope': 'scope-E2-jurisdiction',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-Forster-PhotoLean-Forster-kappaSq',
            'stmt-Forster-PhotoLean-Forster-fretRate',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScForsterDisjointCtx (kr, kp, thetaD, thetaA, phi): a reaction-coordinate geometry '
            'and a donor-acceptor dipole geometry with no shared scalar'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 964-965: Forster vs SymmetryFactor no edge',
             'finding': 'The transfer geometry shares no scalar with the energy-surface family.'},
            {'artifact': 'PhotoLean/Forster/Basic.lean', 'locator': 'kappaSq, fretRate',
             'finding': 'kappa^2 is an orientation factor and fretRate an R^-6 distance law; no crossing coordinate.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'tsCoordZero',
             'finding': 'The symmetry factor is a reaction-coordinate crossing coordinate; no dipole geometry.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-Forster',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/Forster --include='*.lean'",
             'purpose': 'Search the Forster modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Forster' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered Forster statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/Forster/*.lean | sort -u",
             'purpose': 'Measure the Forster module dependencies.',
             'result': 'Mathlib plus Forster submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no Forster import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-Forster',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-Forster status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Relate the crossing coordinate to the orientation factor.',
             'outcome': 'Both are geometric but the geometries are different; no shared scalar.'},
            {'strategy': 'Search for a delivered theorem mentioning both tsCoordZero and kappaSq.',
             'outcome': 'No such theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'no shared scalar',
             'statement': 'SymmetryFactor.tsCoordZero depends on (kr, kp); Forster.kappaSq depends on '
                          '(thetaD, thetaA, phi). No total map between the geometries is declared.',
             'status': 'outside jurisdiction; not a logical absence claim.'},
        ],
        'remainingGap': 'Jurisdiction boundary: the two-parabola crossing geometry and the donor-acceptor orientation geometry share no scalar and no declared translation.',
        'jurisdictionReason': 'No shared context or declared translation exists between a reaction-coordinate crossing coordinate and a dipole orientation factor.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/Forster --include='*.lean'",
            "grep -rn 'Forster' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-Forster',
        ],
        'rationale': 'The pair is outside the declared audit jurisdiction because the two statement contexts share no scalar; the record does not assert logical non-existence.',
    },
    # ---------------------------------------------------------------- SymmetryFactor / Einstein
    {
        'searchId': 'SL-E2-SEIn-01',
        'queryId': 'Q-E2-SEIn-01',
        'pairId': 'P-SymmetryFactor-Einstein',
        'status': 'outOfScope',
        'scope': 'scope-E2-jurisdiction',
        'snapshot': SNAP_ID,
        'searchedStatements': [
            'stmt-SymmetryFactor-PhotoLean-SymmetryFactor-tsCoordZero',
            'stmt-Einstein-PhotoLean-Einstein-radFactor',
            'stmt-Einstein-PhotoLean-Einstein-tauR',
        ],
        'searchedKinds': ['definitionalIdentity', 'implication', 'equivalence',
                          'observationalEquivalence', 'conditionalComposition'],
        'contextsConsidered': [
            'ScEinsteinDisjointCtx (kr, kp, h, c, nu): a crossing coordinate and a radiative '
            'coefficient with no shared scalar'],
        'dependenciesConsulted': [
            {'artifact': 'PhotoLean/Relations.lean', 'locator': 'lines 969-970: Einstein vs SymmetryFactor no edge',
             'finding': 'The radiative conversions have no reaction coordinate; their only machine contact is the QuantumYield anchor.'},
            {'artifact': 'PhotoLean/Einstein/Basic.lean', 'locator': 'radFactor, tauR',
             'finding': 'The A/B coefficients and the radiative lifetime are radiative transition quantities; no crossing coordinate.'},
            {'artifact': 'PhotoLean/SymmetryFactor/Basic.lean', 'locator': 'tsCoordZero',
             'finding': 'The symmetry factor is a structural crossing coordinate; no radiative rate.'},
            {'artifact': 'relation_audit/registry.json', 'locator': 'rec-notestablished-P-SymmetryFactor-Einstein',
             'finding': 'The legacy record is a pair-level notEstablished anchor.'},
        ],
        'commands': [
            {'command': "grep -rn 'SymmetryFactor' PhotoLean/Einstein --include='*.lean'",
             'purpose': 'Search the Einstein modules for a delivered SymmetryFactor statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -rn 'Einstein' PhotoLean/SymmetryFactor --include='*.lean'",
             'purpose': 'Search the SymmetryFactor modules for a delivered Einstein statement.',
             'result': 'No matches (grep exit 1).'},
            {'command': "grep -h '^import' PhotoLean/Einstein/*.lean | sort -u",
             'purpose': 'Measure the Einstein module dependencies.',
             'result': 'Mathlib plus Einstein submodules; no SymmetryFactor import.'},
            {'command': "grep -h '^import' PhotoLean/SymmetryFactor/*.lean | sort -u",
             'purpose': 'Measure the SymmetryFactor module dependencies.',
             'result': 'Mathlib plus Kernel and BEP.Criterion; no Einstein import.'},
            {'command': 'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-Einstein',
             'purpose': 'Recompute the accepted legacy disposition.',
             'result': 'label=absence subtype=registered-absence; rec-notestablished-P-SymmetryFactor-Einstein status=notEstablished certificate=None.'},
        ],
        'strategiesAttempted': [
            {'strategy': 'Relate the crossing coordinate to the radiative A/B coefficients.',
             'outcome': 'No shared scalar; the radiative coefficients contain no crossing coordinate.'},
            {'strategy': 'Search for a delivered theorem mentioning both tsCoordZero and radFactor.',
             'outcome': 'No such theorem exists.'},
            {'strategy': 'Check the legacy registry for a named query or certificate.',
             'outcome': 'Only a pair-level notEstablished anchor.'},
        ],
        'candidateEvidence': [
            {'kind': 'no shared scalar',
             'statement': 'SymmetryFactor.tsCoordZero depends on (kr, kp); Einstein.radFactor depends on '
                          '(h, c, nu). No total map between the parameter spaces is declared.',
             'status': 'outside jurisdiction; not a logical absence claim.'},
        ],
        'remainingGap': 'Jurisdiction boundary: the crossing coordinate and the radiative A/B coefficients share no scalar and no declared translation.',
        'jurisdictionReason': 'No shared context or declared translation exists between a two-parabola crossing coordinate and the radiative transition coefficients.',
        'recomputeCommands': [
            "grep -rn 'SymmetryFactor' PhotoLean/Einstein --include='*.lean'",
            "grep -rn 'Einstein' PhotoLean/SymmetryFactor --include='*.lean'",
            'python3 tools/relation_audit_registry.py --explain-pair P-SymmetryFactor-Einstein',
        ],
        'rationale': 'The pair is outside the declared audit jurisdiction because the two statement contexts share no scalar; the record does not assert logical non-existence.',
    },
]


if __name__ == '__main__':
    main()
