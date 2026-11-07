#!/usr/bin/env python3
"""Deterministic fail-closed validator for the R5 Package RAD1 screening package.

Usage:
    python3 bounded_audit/r5/radiative-01/validate.py \
        [--screening PATH] [--fragment PATH] [--search-log PATH] [--probe PATH]

The validator re-derives its facts from the frozen R1 inventory, the frozen pair queue, the
frozen cluster plan, the accepted legacy registry, the five accepted screening packages (R2, R3,
R4 E1, R4 E2, R4 CI), the package search log, the package probe and the package coverage
fragment. It does not trust the package's own counts or prose.

It deliberately does NOT read or pin ``bounded_audit/coverage.json``: that ledger is the mutable
R5 cumulative ledger owned by the integration step. Prior coverage is derived by reading the five
accepted ``screening.json`` packages directly, which is what makes the check fail-closed while the
ledger is in flux.

Exit codes: 0 = PASS, 1 = FAIL.
"""

import argparse
import hashlib
import json
import os
import re
import sys
import traceback

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
SNAP_ID = 'snap-bounded-audit-2026-11-04-r5rad1'
WORK_PACKAGE = 'WP-radiative-energy-transfer-01'
PRIMARY_CLUSTER = 'radiative-energy-transfer'

STATUSES = ['certified', 'refuted', 'unresolved', 'notEstablished', 'outOfScope']
KINDS = ['definitionalIdentity', 'implication', 'equivalence', 'conditionalComposition',
         'observationalEquivalence', 'distinguishability', 'refutation']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ENDPOINT_FORMS = {'definition', 'theorem', 'theorem-lhs-predicate',
                  'theorem-rhs-predicate', 'theorem-rhs-term'}
TRANSLATION_IDS = {'identity', 'rfl-pin', 'coordinate-map', 'rat-to-real',
                   'surface-to-barrier', 'descriptor-endpoint', 'energy-window',
                   'observational-setup', 'candidate-not-total', 'none-declared'}
PROBE_NS = 'PhotoLean.RelationAudit.BoundedAudit.RAD1.'

EXPECTED_PAIRS = [
    'P-Marcus-KashaVavilov', 'P-Marcus-EnergyGapLaw', 'P-Marcus-StokesShift',
    'P-Marcus-ICvsISC', 'P-Marcus-Forster', 'P-Marcus-Einstein',
    'P-Kasha-KashaVavilov', 'P-Kasha-EnergyGapLaw', 'P-Kasha-StokesShift',
    'P-Kasha-ICvsISC', 'P-Kasha-Forster', 'P-Kasha-Einstein',
    'P-KashaVavilov-SternVolmer', 'P-KashaVavilov-QuantumYield',
    'P-KashaVavilov-FluorPhos', 'P-KashaVavilov-EnergyGapLaw',
]
ACCEPTED_SOURCES = [R2_REL, R3_REL, R4_E1_REL, R4_E2_REL, R4_CI_REL]
EXPECTED_ACCEPTED_PAIRS = 67
EXPECTED_UNIVERSE_PAIRS = 136
EXPECTED_REGISTRY_SHA = '25d38791ce86f9030598eb68b6894a886513164ddb9165e0fff371883c1ecbf0'
EXPECTED_LEAN_FILES = 102
CANDIDATE_SCOPE = 'scope-RAD1-candidate-bridge'
JURISDICTION_SCOPE = 'scope-RAD1-jurisdiction'

# --------------------------------------------------------------------------- semantic pins
# These are the repaired R6 prose values. The comparison is exact so the two metadata fields
# cannot silently drift back to the reversed normal/inverted reading (Q-RAD1-MSS-01), and the
# kind rationale cannot silently reattach a Vavilov yield-independence claim to SpecSame
# (Q-RAD1-KKV-01). The delivered-source checks below tie each pin to the certified direction.

MSS_QUERY = 'Q-RAD1-MSS-01'
KKV_QUERY = 'Q-RAD1-KKV-01'
MKVV_QUERY = 'Q-RAD1-MKVV-01'
MKV_CMP_LEFT_DECL = 'PhotoLean.Marcus.barrier'

EXPECTED_MSS_QUESTION = (
    'Does the Stokes emission energy become positive (`0 < emEnergy`) — a vertical photon above '
    'the 0-0 energy — exactly in the Marcus inverted region (`InvertedRegion`, lam < e00), '
    'and is it negative or zero outside that region (normal region e00 < lam, and the '
    'zero-photon corner e00 = lam)?')

EXPECTED_MSS_FALSIFICATION = (
    'A pair (lam, e00) at which exactly one of `0 < emEnergy lam e00` and '
    '`InvertedRegion lam e00` holds — e.g. positive emission energy on the normal side, or '
    'negative emission energy in the inverted region — would refute the equivalence; the corner '
    'e00 = lam gives emEnergy = 0 on both sides, so it is not a counterexample.')

EXPECTED_KKV_RATIONALE = (
    'The certificate is the one-way implication `KashaRule → SpecSame`: the exact Kasha rule '
    'entails equality of the normalized spectral shapes, and the converse is not claimed. '
    '`SpecSame` is a statement about spectral shape only; it does not assert that the '
    'fluorescence yield is constant across excitation levels, and no VavilovAt/VavilovUpTo '
    'yield-independence claim is attached to it.')

INDEPENDENCE_LEAK = re.compile(
    r'pointwise independent|independent in both directions|converse fails|lossless corner')

# --------------------------------------------------------------------- §4 probe comment pin
# R7 repaired the last reversed Marcus/StokesShift sentence: the old §4 block had the
# inverted-region sign backwards, the opposite of the delivered `emEnergy_pos_iff_inverted`.
# The pin freezes the whole corrected block (whitespace-normalised, so only wording is pinned)
# and names the three regimes explicitly: `emEnergy = e00 - lam` is positive in `lam < e00`,
# negative in `e00 < lam`, and zero at `e00 = lam`. The equality is exact, so any reinstated
# reversed wording fails closed.

EXPECTED_SS_PROBE_COMMENT = (
    '/-! ## §4 — Marcus / StokesShift: the emission energy is positive exactly in the inverted '
    'region The Stokes emission energy is `emEnergy = e00 - lam`. It is positive exactly in the '
    'Marcus inverted region (`lam < e00`), negative in the normal region (`e00 < lam`), and '
    'zero at `e00 = lam`. The delivered row SS-C9 is re-used here as the certificate\'s '
    'entailment. -/')

REVERSED_SS_PROBE = re.compile(
    r'turns negative|inverted-emission corner|emission maximum moves below|'
    r'negative[^.]{0,80}exactly in the Marcus inverted|'
    r'positive[^.]{0,80}exactly (?:on|in) the Marcus normal')



def sha_path(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha_rel(rel):
    return sha_path(os.path.join(ROOT, rel))


def load_path(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def load_rel(rel):
    return load_path(os.path.join(ROOT, rel))


def read_rel(rel):
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        return fh.read()


def signature_sha(kind, declaration, signature):
    text = kind + ' ' + declaration + ' ' + signature
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


class Checker:
    def __init__(self):
        self.failures = []

    def check(self, cond, code, message):
        if not cond:
            self.failures.append((code, message))

    def nonempty(self, value, code, message):
        self.check(isinstance(value, str) and value.strip() != '', code, message)

    def summary(self):
        print('R5 RAD1 bounded screening validation')
        print('  root: %s' % ROOT)
        print('  checks failed: %d' % len(self.failures))
        if self.failures:
            for code, message in self.failures:
                print('FAIL [%s] %s' % (code, message))
            print('RESULT: FAIL (%d failed checks)' % len(self.failures))
            return 1
        print('RESULT: PASS (all RAD1 bounded-screening checks passed)')
        return 0


def parse_probe_axioms(text):
    """Parse `#print axioms` output, tolerating Lean's line wrapping."""
    blocks = {}
    joined = re.sub(r'\s*\n\s*', ' ', text)
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", joined):
        axioms = {a.strip() for a in m.group(2).split(',') if a.strip()}
        blocks[m.group(1)] = axioms
    return blocks


def short_name(decl):
    return decl.rsplit('.', 1)[-1]


def status_counts(queries):
    out = {}
    for q in queries:
        status = q.get('outcome', {}).get('status')
        out[status] = out.get(status, 0) + 1
    return out


def kind_counts(queries):
    out = {}
    for q in queries:
        kind = q.get('expectedKind')
        out[kind] = out.get(kind, 0) + 1
    return out


def normalise_space(text):
    return re.sub(r'\s+', ' ', text)


def check_probe_section4_comment(c, probe_text):
    """Pin the corrected §4 comment and reject the old reversed emission-energy wording."""
    marker = re.search(r'/-!\s*##\s*§4\b.*?-/', probe_text, re.S)
    c.check(marker is not None, 'pin.ssProbeComment.missing',
            'cannot locate the §4 block comment in the probe')
    flat = normalise_space(marker.group(0)) if marker is not None else ''
    expected = normalise_space(EXPECTED_SS_PROBE_COMMENT)
    c.check(flat == expected, 'pin.ssProbeComment.text',
            'probe §4 comment is not the pinned three-regime emission-energy reading')
    c.check('`emEnergy = e00 - lam`' in flat, 'pin.ssProbeComment.equation',
            'probe §4 comment does not state emEnergy = e00 - lam')
    c.check('positive exactly in the Marcus inverted region (`lam < e00`)' in flat,
            'pin.ssProbeComment.inverted',
            'probe §4 comment does not state positivity exactly in the inverted region lam < e00')
    c.check('negative in the normal region (`e00 < lam`)' in flat,
            'pin.ssProbeComment.normal',
            'probe §4 comment does not state negativity in the normal region e00 < lam')
    c.check('zero at `e00 = lam`' in flat, 'pin.ssProbeComment.corner',
            'probe §4 comment does not state the zero at e00 = lam')
    c.check(REVERSED_SS_PROBE.search(flat) is None, 'pin.ssProbeComment.reversed',
            'probe §4 comment still carries reversed inverted/normal emission wording')
    c.check(REVERSED_SS_PROBE.search(normalise_space(probe_text)) is None,
            'pin.ssProbe.reversed', 'the probe still carries a reversed emission-energy phrase')
    criterion = normalise_space(read_rel('PhotoLean/StokesShift/Criterion.lean'))
    c.check('theorem emEnergy_eq (lam e00 : ℝ) : emEnergy lam e00 = e00 - lam' in criterion,
            'pin.ssProbeComment.certifiedEquation',
            'delivered emEnergy_eq no longer gives emEnergy = e00 - lam')
    c.check('theorem inverted_corner {lam e00 : ℝ} (h : e00 < lam) : emEnergy lam e00 < 0'
            in criterion, 'pin.ssProbeComment.certifiedNormal',
            'delivered inverted_corner no longer makes the normal region emissive-negative')
    c.check('theorem emission_window_closes (lam : ℝ) : emEnergy lam lam = 0' in criterion,
            'pin.ssProbeComment.certifiedCorner',
            'delivered emission_window_closes no longer gives zero at e00 = lam')


def check_semantic_pins(c, query_by_id, probe_text):
    """Fail closed unless the repaired RAD1 prose is pinned to the delivered mathematics."""
    check_probe_section4_comment(c, probe_text)
    mss = query_by_id.get(MSS_QUERY)
    kkv = query_by_id.get(KKV_QUERY)
    c.check(mss is not None, 'pin.mss.missing', 'query %s is missing' % MSS_QUERY)
    c.check(kkv is not None, 'pin.kkv.missing', 'query %s is missing' % KKV_QUERY)

    if mss is not None:
        question = mss.get('chemicalQuestion', '')
        falsification = mss.get('falsificationCondition', '')
        c.check(question == EXPECTED_MSS_QUESTION, 'pin.mss.chemicalQuestion',
                'Q-RAD1-MSS-01 chemicalQuestion is not the pinned inverted-region reading')
        c.check(falsification == EXPECTED_MSS_FALSIFICATION, 'pin.mss.falsificationCondition',
                'Q-RAD1-MSS-01 falsificationCondition is not the pinned one-side-mismatch test')
        c.check('0 < emEnergy' in question and 'InvertedRegion' in question,
                'pin.mss.predicateTokens',
                'Q-RAD1-MSS-01 chemicalQuestion does not name both certified predicates')
        c.check('lam < e00' in question, 'pin.mss.directionTokens',
                'Q-RAD1-MSS-01 chemicalQuestion does not state the inverted-region direction')
        c.check('normal region e00 < lam' in question and 'e00 = lam' in question,
                'pin.mss.outsideRegion',
                'Q-RAD1-MSS-01 chemicalQuestion does not state the normal/zero-photon outside')
        c.check('exactly one' in falsification, 'pin.mss.exactlyOne',
                'Q-RAD1-MSS-01 falsificationCondition is not an exactly-one mismatch test')
        c.check('`0 < emEnergy lam e00`' in falsification and
                '`InvertedRegion lam e00`' in falsification, 'pin.mss.falsifyPredicates',
                'Q-RAD1-MSS-01 falsificationCondition does not name the two compared predicates')
        c.check('e00 = lam' in falsification and 'counterexample' in falsification,
                'pin.mss.corner',
                'Q-RAD1-MSS-01 falsificationCondition does not identify the zero-photon corner')
        underlying = [t.get('declaration') for t in
                      mss.get('outcome', {}).get('evidence', {}).get('underlyingTheorems', [])]
        c.check('PhotoLean.StokesShift.emEnergy_pos_iff_inverted' in underlying,
                'pin.mss.underlying',
                'Q-RAD1-MSS-01 does not cite the delivered sign equivalence')
        criterion = normalise_space(read_rel('PhotoLean/StokesShift/Criterion.lean'))
        c.check('0 < emEnergy lam e00 ↔ PhotoLean.Marcus.InvertedRegion lam e00' in criterion,
                'pin.mss.certifiedDirection',
                'delivered emEnergy_pos_iff_inverted no longer has the pinned direction')
        marcus = normalise_space(read_rel('PhotoLean/Marcus/Basic.lean'))
        c.check('def InvertedRegion (lam x : ℝ) : Prop := lam < x' in marcus,
                'pin.mss.invertedRegionBody',
                'delivered InvertedRegion no longer means lam < x')

    if kkv is not None:
        rationale = kkv.get('expectedKindRationale', '')
        c.check(rationale == EXPECTED_KKV_RATIONALE, 'pin.kkv.expectedKindRationale',
                'Q-RAD1-KKV-01 expectedKindRationale is not the pinned one-way SpecSame reading')
        c.check(kkv.get('expectedKind') == 'implication', 'pin.kkv.kind',
                'Q-RAD1-KKV-01 expectedKind is not implication')
        c.check('KashaRule → SpecSame' in rationale and 'one-way' in rationale,
                'pin.kkv.direction',
                'Q-RAD1-KKV-01 rationale does not state the one-way KashaRule → SpecSame claim')
        c.check('converse is not claimed' in rationale, 'pin.kkv.converse',
                'Q-RAD1-KKV-01 rationale does not disown the converse')
        c.check('spectral shape' in rationale and 'fluorescence yield' in rationale and
                'constant' in rationale, 'pin.kkv.shapeVsYield',
                'Q-RAD1-KKV-01 rationale does not distinguish spectral shape from yield')
        c.check('VavilovAt/VavilovUpTo' in rationale and
                'no ' in rationale and 'attached to it' in rationale,
                'pin.kkv.independenceDisavowal',
                'Q-RAD1-KKV-01 rationale does not disavow the Vavilov yield-independence claim')
        c.check(INDEPENDENCE_LEAK.search(rationale) is None, 'pin.kkv.independenceLeak',
                'Q-RAD1-KKV-01 rationale still attaches a Vavilov independence claim to SpecSame')
        underlying = [t.get('declaration') for t in
                      kkv.get('outcome', {}).get('evidence', {}).get('underlyingTheorems', [])]
        c.check('PhotoLean.KashaVavilov.specSame_of_kashaRule' in underlying,
                'pin.kkv.underlying',
                'Q-RAD1-KKV-01 does not cite the delivered KV-B7 implication')
        kasha_vav = normalise_space(read_rel('PhotoLean/KashaVavilov/Basic.lean'))
        c.check('(hK : Kasha.KashaRule rad ic N) : ∀ M, M ≤ N → SpecSame rad ic M N' in kasha_vav,
                'pin.kkv.certifiedDirection',
                'delivered specSame_of_kashaRule no longer has the pinned one-way direction')
        specsame = re.search(r'def\s+SpecSame\b.*?(?=\n\n)', read_rel(
            'PhotoLean/KashaVavilov/Basic.lean'), re.S)
        c.check(specsame is not None, 'pin.kkv.specSameDefinition',
                'cannot locate PhotoLean.KashaVavilov.SpecSame in its delivered source')
        if specsame is not None:
            body = specsame.group(0)
            c.check('specFrac' in body and 'fluoYield' not in body,
                    'pin.kkv.specSameShapeOnly',
                    'delivered SpecSame is not a spectral-shape predicate')

    match = re.search(r'def\s+mkvCmp\b.*?(?=\n(def|theorem)\s)', probe_text, re.S)
    c.check(match is not None, 'pin.mkvCmp.missing', 'cannot locate def mkvCmp in the probe')
    if match is not None:
        block = match.group(0)
        c.check(('mkRef "PhotoLean.Marcus" "%s"' % MKV_CMP_LEFT_DECL) in block,
                'pin.mkvCmp.statementRef',
                'mkvCmp left StatementRef is not %s' % MKV_CMP_LEFT_DECL)
        c.check('"PhotoLean.Kasha.marcusIC"' not in block, 'pin.mkvCmp.legacyRef',
                'mkvCmp left StatementRef still names PhotoLean.Kasha.marcusIC')
        c.check('PhotoLean/Marcus/Basic.lean#barrier' in block, 'pin.mkvCmp.provenance',
                'mkvCmp left StatementRef provenance is not the Marcus barrier source')
        mkvv = query_by_id.get(MKVV_QUERY)
        c.check(mkvv is not None and
                mkvv.get('endpoints', {}).get('source', {}).get('declaration') ==
                MKV_CMP_LEFT_DECL, 'pin.mkvCmp.endpoint',
                'mkvCmp left StatementRef does not agree with the MKVV query endpoint')


def main():
    parser = argparse.ArgumentParser(description='R5 RAD1 package validator')
    parser.add_argument('--screening', default=os.path.join(ROOT, SCREENING_REL))
    parser.add_argument('--fragment', default=os.path.join(ROOT, FRAGMENT_REL))
    parser.add_argument('--search-log', default=os.path.join(ROOT, SEARCH_REL))
    parser.add_argument('--probe', default=os.path.join(ROOT, PROBE_REL))
    args = parser.parse_args()

    c = Checker()

    required = [INV_REL, QUEUE_REL, CLUSTER_REL, BOUNDARY_REL, REGISTRY_REL,
                PROBE_LOG_REL] + ACCEPTED_SOURCES
    for rel in required:
        if not os.path.exists(os.path.join(ROOT, rel)):
            print('FAIL [file.missing] required artifact not found: %s' % rel)
            print('RESULT: FAIL')
            return 1
    for path, rel in [(args.screening, SCREENING_REL), (args.search_log, SEARCH_REL),
                      (args.fragment, FRAGMENT_REL), (args.probe, PROBE_REL)]:
        if not os.path.exists(path):
            print('FAIL [file.missing] required artifact not found: %s' % rel)
            print('RESULT: FAIL')
            return 1

    screening = load_path(args.screening)
    inv = load_rel(INV_REL)
    queue = load_rel(QUEUE_REL)
    cluster = load_rel(CLUSTER_REL)
    registry = load_rel(REGISTRY_REL)
    accepted_packages = [load_rel(rel) for rel in ACCEPTED_SOURCES]
    search_log = load_path(args.search_log)
    fragment = load_path(args.fragment)
    probe_text = open(args.probe, encoding='utf-8').read()
    probe_log = read_rel(PROBE_LOG_REL)

    inv_by_id = {row['id']: row for row in inv['statements']}
    dangling_ids = {d['id'] for d in inv.get('legacyDanglingStatements', [])}
    queue_by_id = {row['pairId']: row for row in queue['pairs']}
    probe_axioms = parse_probe_axioms(probe_log)

    # ---------------------------------------------------------------- vocabulary
    c.check(screening.get('schemaVersion') == '1.0.0', 'schema.version',
            'unexpected schemaVersion')
    c.check(screening.get('artifactKind') == 'bounded-screening-package',
            'schema.kind', 'unexpected artifactKind')
    c.check(screening.get('round') == 'R5', 'schema.round', 'unexpected round')
    c.check(screening.get('statusVocabulary') == STATUSES, 'schema.statusVocabulary',
            'status vocabulary drift')
    c.check(screening.get('kindVocabulary') == KINDS, 'schema.kindVocabulary',
            'kind vocabulary drift')
    c.check(set(screening.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
            'schema.allowedAxioms', 'allowed-axiom list drift')
    c.check('acceptance' not in screening or screening.get('acceptance') not in
            ('accepted', 'accepted-R5'), 'schema.selfAcceptance',
            'package self-declares acceptance; R5 packages stay submitted until review')

    # ---------------------------------------------------------------- snapshot
    snap = screening.get('snapshot', {})
    c.check(snap.get('id') == SNAP_ID, 'snapshot.id', 'snapshot id drift')
    c.check(snap.get('round') == 'R5', 'snapshot.round', 'snapshot round drift')
    for rel, key in [(INV_REL, 'inventorySha256'), (QUEUE_REL, 'pairQueueSha256'),
                     (CLUSTER_REL, 'clusterPlanSha256'),
                     (BOUNDARY_REL, 'boundarySha256'),
                     (REGISTRY_REL, 'legacyRegistrySha256'),
                     (R2_REL, 'acceptedR2Sha256'), (R3_REL, 'acceptedR3Sha256'),
                     (R4_E1_REL, 'acceptedR4E1Sha256'), (R4_E2_REL, 'acceptedR4E2Sha256'),
                     (R4_CI_REL, 'acceptedR4CISha256')]:
        actual = sha_rel(rel)
        c.check(snap.get(key) == actual, 'snapshot.%s' % key,
                '%s hash drift: %s != %s' % (rel, snap.get(key), actual))
    c.check(snap.get('legacyRegistrySha256') == EXPECTED_REGISTRY_SHA,
            'snapshot.registryPinned', 'legacy registry hash is not the accepted hash')
    c.check('coverageLedgerSha256' not in snap and
            'coverage.json' not in json.dumps(snap), 'snapshot.mutableLedger',
            'snapshot pins the mutable R5 cumulative coverage ledger')
    c.check('coverage.json' not in json.dumps(screening.get('acceptedCoverageReference', {})),
            'acceptedCoverageReference.mutableLedger',
            'prior-coverage reference names the mutable ledger instead of accepted packages')
    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(os.path.join(ROOT, 'PhotoLean')):
        for name in filenames:
            if name.endswith('.lean'):
                lean_files.append(os.path.join(dirpath, name))
    c.check(len(lean_files) == EXPECTED_LEAN_FILES, 'snapshot.leanFileCount',
            'delivered Lean tree has %d files, expected %d'
            % (len(lean_files), EXPECTED_LEAN_FILES))
    c.check(snap.get('deliveredLeanFileCount') == EXPECTED_LEAN_FILES,
            'snapshot.leanFileCountField', 'delivered Lean file count field drift')

    # ---------------------------------------------------------------- references
    inv_ref = screening.get('inventoryReference', {})
    c.check(inv_ref.get('path') == INV_REL, 'inventoryReference.path',
            'inventory reference path drift')
    c.check(inv_ref.get('sha256') == sha_rel(INV_REL), 'inventoryReference.sha256',
            'inventory reference hash drift')
    c.check(inv_ref.get('statementRows') == len(inv['statements']),
            'inventoryReference.rows', 'inventory row count drift')
    c.check(inv_ref.get('screeningEligibleRows') ==
            sum(1 for s in inv['statements'] if s['screeningEligible']),
            'inventoryReference.eligible', 'eligible row count drift')
    reg_ref = screening.get('legacyRegistryReference', {})
    c.check(reg_ref.get('sha256') == sha_rel(REGISTRY_REL),
            'legacyRegistryReference.sha256', 'registry reference hash drift')
    c.check(reg_ref.get('certificateCount') == len(registry['certificates']),
            'legacyRegistryReference.certs', 'registry certificate count drift')
    c.check(reg_ref.get('queryCount') == len(registry['queries']),
            'legacyRegistryReference.queries', 'registry query count drift')
    c.check(reg_ref.get('recordCount') == len(registry['records']),
            'legacyRegistryReference.records', 'registry record count drift')
    search_ref = screening.get('searchLogReference', {})
    c.check(search_ref.get('path') == SEARCH_REL, 'searchLogReference.path',
            'search-log reference path drift')
    c.check(search_ref.get('sha256') == sha_path(args.search_log),
            'searchLogReference.sha256', 'search-log hash drift')
    probe_ref = screening.get('probeReference', {})
    c.check(probe_ref.get('path') == PROBE_REL, 'probeReference.path',
            'probe reference path drift')
    c.check(probe_ref.get('sha256') == sha_path(args.probe), 'probeReference.sha256',
            'probe hash drift')
    c.check(probe_ref.get('log') == PROBE_LOG_REL, 'probeReference.log',
            'probe log path drift')

    # ---------------------------------------------------------------- pair universe
    accepted_pairs = []
    for rel, pkg in zip(ACCEPTED_SOURCES, accepted_packages):
        rows = pkg.get('pairs', [])
        c.check(len(rows) >= 1, 'accepted.empty', 'accepted package %s has no pair rows' % rel)
        accepted_pairs.extend(row['pairId'] for row in rows)
    c.check(len(accepted_pairs) == EXPECTED_ACCEPTED_PAIRS, 'accepted.count',
            'accepted prior-coverage pair count is %d, expected %d'
            % (len(accepted_pairs), EXPECTED_ACCEPTED_PAIRS))
    c.check(len(set(accepted_pairs)) == len(accepted_pairs), 'accepted.duplicate',
            'accepted prior-coverage list has a duplicate pair')
    universe = [row['pairId'] for row in queue['pairs']]
    c.check(len(universe) == EXPECTED_UNIVERSE_PAIRS, 'universe.count',
            'R1 queue pair count is %d, expected %d'
            % (len(universe), EXPECTED_UNIVERSE_PAIRS))
    c.check(set(accepted_pairs) <= set(universe), 'accepted.unknownPair',
            'an accepted pair is outside the R1 queue')
    rad1_set = set(EXPECTED_PAIRS)
    c.check(not (rad1_set & set(accepted_pairs)), 'universe.acceptedOverlap',
            'RAD1 pair set overlaps the accepted prior-coverage pairs')
    c.check(rad1_set <= set(universe), 'universe.unknownPair',
            'a RAD1 pair is not in the R1 queue')
    remaining = [pid for pid in universe if pid not in set(accepted_pairs)]
    c.check(len(remaining) == EXPECTED_UNIVERSE_PAIRS - EXPECTED_ACCEPTED_PAIRS,
            'universe.remaining', 'remaining pair count after prior coverage is %d'
            % len(remaining))
    c.check(rad1_set <= set(remaining), 'universe.notRemaining',
            'a RAD1 pair is not in the remaining (unaccepted) set')
    c.check('P-Kasha-Sabatier' in accepted_pairs, 'universe.kashaSabatier',
            'the early P-Kasha-Sabatier pair is not part of the accepted prior coverage')

    # ---------------------------------------------------------------- work package
    r1_wp = None
    for cl in cluster.get('clusters', []):
        for cand in cl.get('workPackages', []):
            if cand.get('id') == WORK_PACKAGE:
                r1_wp = (cl.get('id'), cand)
    c.check(r1_wp is not None, 'workPackage.r1Missing',
            'R1 cluster plan has no %s' % WORK_PACKAGE)
    if r1_wp is not None:
        c.check(r1_wp[0] == PRIMARY_CLUSTER, 'workPackage.cluster',
                'R1 work package sits in cluster %r' % (r1_wp[0],))
        c.check(r1_wp[1].get('pairIds') == EXPECTED_PAIRS, 'workPackage.r1Drift',
                'R1 work-package pair list differs from the approved sixteen')
        c.check(r1_wp[1].get('pairCount') == len(EXPECTED_PAIRS),
                'workPackage.r1Count', 'R1 work-package pair count drift')
    wp = screening.get('workPackage', {})
    c.check(wp.get('id') == WORK_PACKAGE, 'workPackage.id', 'work package id drift')
    c.check(wp.get('pairIds') == EXPECTED_PAIRS, 'workPackage.pairIds',
            'work package pair list is not the approved sixteen')
    c.check(wp.get('pairCount') == len(EXPECTED_PAIRS), 'workPackage.pairCount',
            'work package pair count drift')

    pairs = screening.get('pairs', [])
    pair_ids = [p.get('pairId') for p in pairs]
    c.check(len(pair_ids) == len(set(pair_ids)), 'pairs.duplicate',
            'duplicate pair id in screening package')
    c.check(len(pair_ids) == len(EXPECTED_PAIRS), 'pairs.count',
            'screening pair count is %d, expected %d' % (len(pair_ids), len(EXPECTED_PAIRS)))
    c.check(set(pair_ids) == rad1_set, 'pairs.coverage',
            'screening pair set is not exactly the approved sixteen')

    all_query_ids = []
    query_by_id = {}
    for pair in pairs:
        pid = pair.get('pairId')
        c.nonempty(pid, 'pair.id', 'pair row without pairId')
        qrow = queue_by_id.get(pid)
        c.check(qrow is not None, 'pair.queueMissing',
                'pair %r is not in the R1 pair queue' % pid)
        if qrow is not None:
            c.check(pair.get('theories') == qrow['theories'], 'pair.theories',
                    'pair %r theories do not match the R1 queue' % pid)
            c.check(pair.get('primaryCluster') == qrow['screeningCluster'],
                    'pair.cluster', 'pair %r primary cluster does not match the R1 queue' % pid)
            c.check(pair.get('primaryCluster') == PRIMARY_CLUSTER, 'pair.clusterValue',
                    'pair %r is not in the radiative-energy-transfer cluster' % pid)
        qids = pair.get('queryIds', [])
        c.check(isinstance(qids, list) and len(qids) >= 1, 'pair.noQuery',
                'pair %r has no named query or outOfScope record' % pid)
        c.check(qids == [q.get('queryId') for q in pair.get('queries', [])],
                'pair.queryIds', 'pair %r queryIds do not match its query rows' % pid)
        c.check(len(qids) == len(set(qids)), 'pair.queryDuplicate',
                'pair %r has duplicate query ids' % pid)
        c.check(len(pair.get('queries', [])) >= 1, 'pair.noQueryRow',
                'pair %r has no query row' % pid)
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            all_query_ids.append(qid)
            query_by_id[qid] = q
            c.check(q.get('pairId') == pid, 'query.pairId',
                    'query %r pairId does not match its pair row' % qid)

    c.check(len(all_query_ids) == len(set(all_query_ids)), 'queries.duplicate',
            'duplicate query id in screening package')
    c.check(len(all_query_ids) >= len(EXPECTED_PAIRS), 'queries.count',
            'there are fewer queries than assigned pairs')

    # ---------------------------------------------------------------- contexts / scopes
    ctx_lib = screening.get('contextLibrary', {})
    scope_lib = screening.get('scopeLibrary', {})
    c.check(isinstance(ctx_lib, dict) and len(ctx_lib) >= 1, 'contextLibrary.missing',
            'screening package has no context library')
    c.check(isinstance(scope_lib, dict) and len(scope_lib) >= 1, 'scopeLibrary.missing',
            'screening package has no scope library')
    for cid, ctx in ctx_lib.items():
        c.check(ctx.get('id') == cid, 'contextLibrary.id',
                'context library key %r does not match its id field' % cid)
        c.check(isinstance(ctx.get('fields'), list) and len(ctx.get('fields')) >= 1,
                'contextLibrary.fields', 'context %r has no fields' % cid)
        c.nonempty(ctx.get('physicalReading'), 'contextLibrary.reading',
                   'context %r has no physical reading' % cid)
        c.nonempty(ctx.get('provenance'), 'contextLibrary.provenance',
                   'context %r has no provenance' % cid)
    for sid, scope in scope_lib.items():
        c.check(scope.get('id') == sid, 'scopeLibrary.id',
                'scope library key %r does not match its id field' % sid)
        c.nonempty(scope.get('description'), 'scopeLibrary.description',
                   'scope %r has no description' % sid)
        c.nonempty(scope.get('domain'), 'scopeLibrary.domain',
                   'scope %r has no domain' % sid)
        c.check(scope.get('snapshot') == snap.get('id'), 'scopeLibrary.snapshot',
                'scope %r snapshot drift' % sid)

    # ---------------------------------------------------------------- per-query checks
    non_certified = []
    certified_decls = set()
    search_required = set()
    for pair in pairs:
        for q in pair.get('queries', []):
            qid = q.get('queryId')
            c.nonempty(qid, 'query.id', 'query row without queryId')
            for field in ['title', 'chemicalQuestion', 'chemicalRationale',
                          'expectedKindRationale', 'falsificationCondition']:
                c.nonempty(q.get(field), 'query.%s' % field,
                           'query %r missing %s' % (qid, field))

            kind = q.get('expectedKind')
            c.check(kind in KINDS, 'query.kind',
                    'query %r expectedKind %r is not a seven-kind value' % (qid, kind))
            c.check(kind != 'refuted', 'query.kindRefuted',
                    'query %r uses the status refuted as an evidence kind' % qid)

            # endpoints
            endpoints = q.get('endpoints', {})
            for side in ['source', 'target']:
                ep = endpoints.get(side, {})
                stmt = ep.get('statementId')
                c.check(stmt in inv_by_id, 'endpoint.missing',
                        'query %r %s endpoint %r is not an inventory statement'
                        % (qid, side, stmt))
                if stmt not in inv_by_id:
                    continue
                row = inv_by_id[stmt]
                for key in ['theory', 'declaration', 'declarationKind', 'sourceArtifact',
                            'sourceLine', 'version', 'signatureSha256',
                            'sourceArtifactSha256']:
                    c.check(ep.get(key) == row[key], 'endpoint.%s' % key,
                            'query %r %s endpoint field %s drifts from the inventory'
                            % (qid, side, key))
                src_path = os.path.join(ROOT, row['sourceArtifact'])
                c.check(os.path.exists(src_path), 'endpoint.sourceMissing',
                        'query %r %s source artifact is missing' % (qid, side))
                if os.path.exists(src_path):
                    c.check(sha_path(src_path) == row['sourceArtifactSha256'],
                            'endpoint.sourceHash',
                            'query %r %s source artifact hash drift' % (qid, side))
                    lines = open(src_path, encoding='utf-8').read().splitlines()
                    line = row['sourceLine']
                    c.check(isinstance(line, int) and 1 <= line <= len(lines),
                            'endpoint.lineRange',
                            'query %r %s source line is outside its artifact' % (qid, side))
                    if isinstance(line, int) and 1 <= line <= len(lines):
                        c.check(short_name(row['declaration']) in lines[line - 1],
                                'endpoint.lineMatch',
                                'query %r %s declaration is not at its source line'
                                % (qid, side))
                    prefix = (row['declarationKind'] + ' ' +
                              row['declaration'].rsplit('.', 1)[-1] + ' ')
                    sig = (row['sourceSignature'][len(prefix):]
                           if row['sourceSignature'].startswith(prefix) else None)
                    c.check(sig is not None, 'endpoint.signaturePrefix',
                            'query %r %s sourceSignature does not carry its kind/name prefix'
                            % (qid, side))
                    if sig is not None:
                        expected = signature_sha(row['declarationKind'],
                                                 row['declaration'], sig)
                        c.check(expected == row['signatureSha256'],
                                'endpoint.signatureHash',
                                'query %r %s signatureSha256 does not recompute'
                                % (qid, side))
                c.check(ep.get('endpointForm') in ENDPOINT_FORMS, 'endpoint.form',
                        'query %r %s has unknown endpointForm' % (qid, side))
                c.check(stmt not in dangling_ids, 'endpoint.danglingAlias',
                        'query %r %s cites a dangling legacy alias as an endpoint'
                        % (qid, side))
            src_theory = endpoints.get('source', {}).get('theory')
            tgt_theory = endpoints.get('target', {}).get('theory')
            c.check(src_theory != tgt_theory, 'endpoint.sameTheory',
                    'query %r endpoints are not cross-theory' % qid)
            c.check({src_theory, tgt_theory} == set(pair.get('theories', [])),
                    'endpoint.pairTheories',
                    'query %r endpoints do not belong to the pair theories' % qid)

            # shared context and translations
            ctx = q.get('sharedContext', {})
            ctx_id = ctx.get('id')
            c.check(ctx_id in ctx_lib, 'context.missing',
                    'query %r shared context %r is not in the context library'
                    % (qid, ctx_id))
            c.check(isinstance(ctx.get('fields'), list) and len(ctx.get('fields')) >= 1,
                    'context.fields', 'query %r shared context has no fields' % qid)
            c.nonempty(ctx.get('physicalReading'), 'context.reading',
                       'query %r shared context has no physical reading' % qid)
            c.nonempty(ctx.get('provenance'), 'context.provenance',
                       'query %r shared context has no provenance' % qid)
            trans = q.get('translations', {})
            for side in ['left', 'right']:
                tr = trans.get(side, {})
                tid = tr.get('id')
                c.check(tid in TRANSLATION_IDS, 'translation.id',
                        'query %r %s translation id %r is not admissible'
                        % (qid, side, tid))
                if tid in {'none-declared', 'candidate-not-total'}:
                    c.nonempty(tr.get('reason'), 'translation.reason',
                               'query %r %s translation %r has no reason'
                               % (qid, side, tid))
                else:
                    c.nonempty(tr.get('term'), 'translation.term',
                               'query %r %s translation has no term' % (qid, side))
                c.nonempty(tr.get('requirement'), 'translation.requirement',
                           'query %r %s translation has no requirement note' % (qid, side))

            # premises
            prem = q.get('premises', {})
            c.nonempty(prem.get('predicate'), 'premise.predicate',
                       'query %r has no premise predicate' % qid)
            pids = prem.get('premiseIds')
            defs = prem.get('definitions')
            c.check(isinstance(pids, list), 'premise.ids',
                    'query %r premiseIds is not a list' % qid)
            c.check(isinstance(defs, list), 'premise.defs',
                    'query %r premise definitions is not a list' % qid)
            def_ids = []
            for d in defs or []:
                def_ids.append(d.get('id'))
                c.nonempty(d.get('predicate'), 'premise.defPredicate',
                           'query %r premise definition has no predicate' % qid)
                c.nonempty(d.get('statement'), 'premise.defStatement',
                           'query %r premise definition has no statement' % qid)
                c.nonempty(d.get('loadBearing'), 'premise.defLoadBearing',
                           'query %r premise definition has no load-bearing note' % qid)
            c.check(sorted(def_ids) == sorted(pids or []), 'premise.defIds',
                    'query %r premiseIds and definitions do not match' % qid)
            if not pids:
                c.check('True' in (prem.get('predicate') or ''), 'premise.emptyPredicate',
                        'query %r has no premise ids but its predicate is not True' % qid)

            # scope and snapshot
            scope = q.get('scope', {})
            sid = scope.get('id')
            c.check(sid in scope_lib, 'scope.missing',
                    'query %r scope %r is not in the scope library' % (qid, sid))
            c.nonempty(scope.get('description'), 'scope.description',
                       'query %r scope has no description' % qid)
            c.nonempty(scope.get('domain'), 'scope.domain',
                       'query %r scope has no domain' % qid)
            c.check(scope.get('snapshot') == snap.get('id'), 'scope.snapshot',
                    'query %r scope snapshot does not match the package snapshot' % qid)

            # observation channels
            channels = q.get('observationChannels', [])
            c.check(isinstance(channels, list), 'channel.list',
                    'query %r observationChannels is not a list' % qid)
            if kind in {'observationalEquivalence', 'distinguishability'}:
                c.check(len(channels) >= 1, 'channel.required',
                        'query %r has kind %s but no observation channel' % (qid, kind))
            for ch in channels or []:
                c.nonempty(ch.get('id'), 'channel.id',
                           'query %r has a channel without id' % qid)
                c.nonempty(ch.get('observedValueType'), 'channel.valueType',
                           'query %r channel has no observed-value type' % qid)
                c.nonempty(ch.get('inputDomain'), 'channel.inputDomain',
                           'query %r channel has no input domain' % qid)
                c.check(ch.get('domainNonempty') is True, 'channel.domainNonempty',
                        'query %r channel domain is not declared nonempty' % qid)
                c.nonempty(ch.get('leftObs'), 'channel.leftObs',
                           'query %r channel has no left observation' % qid)
                c.nonempty(ch.get('rightObs'), 'channel.rightObs',
                           'query %r channel has no right observation' % qid)

            # outcome
            outcome = q.get('outcome', {})
            status = outcome.get('status')
            c.check(status in STATUSES, 'outcome.status',
                    'query %r outcome status %r is not one of the five' % (qid, status))
            c.nonempty(outcome.get('rationale'), 'outcome.rationale',
                       'query %r outcome has no rationale' % qid)
            evidence = outcome.get('evidence', {})
            c.check(isinstance(evidence, dict), 'outcome.evidence',
                    'query %r outcome evidence is not an object' % qid)

            if status == 'certified':
                c.check(q.get('scope', {}).get('id') not in {CANDIDATE_SCOPE, JURISDICTION_SCOPE},
                        'outcome.certifiedScope',
                        'certified query %r uses a non-certified scope' % qid)
                etype = evidence.get('type')
                c.check(etype == 'rad1-probe-certificate', 'evidence.type',
                        'query %r certified evidence has unsupported type %r' % (qid, etype))
                c.check(evidence.get('kind') == kind, 'evidence.kindMatch',
                        'query %r evidence kind %r does not match expectedKind %r'
                        % (qid, evidence.get('kind'), kind))
                c.check(evidence.get('kind') in KINDS, 'evidence.kind',
                        'query %r evidence kind is not a seven-kind value' % qid)
                footprint = set(evidence.get('axiomFootprint', []))
                c.check(footprint <= ALLOWED_AXIOMS, 'evidence.axioms',
                        'query %r evidence footprint contains disallowed axioms: %s'
                        % (qid, sorted(footprint - ALLOWED_AXIOMS)))
                c.check(set(evidence.get('allowedAxioms', [])) == ALLOWED_AXIOMS,
                        'evidence.allowedAxioms',
                        'query %r evidence allowed-axiom list drift' % qid)
                probe = evidence.get('probe', {})
                c.check(probe.get('path') == PROBE_REL, 'evidence.probePath',
                        'query %r probe path drift' % qid)
                c.check(probe.get('sha256') == sha_path(args.probe),
                        'evidence.probeHash', 'query %r probe source hash drift' % qid)
                decl = probe.get('declaration', '')
                certified_decls.add(decl)
                c.check(decl.startswith(PROBE_NS), 'evidence.probeDecl',
                        'query %r probe declaration is outside the expected namespace' % qid)
                short = short_name(decl)
                c.check(re.search(r'\bdef\s+%s\b' % re.escape(short), probe_text)
                        is not None, 'evidence.probeDeclMissing',
                        'query %r probe declaration is not in the probe source' % qid)
                kind_thm = probe.get('kindCheckTheorem', '')
                c.check(re.search(r'\btheorem\s+%s\b' % re.escape(short_name(kind_thm)),
                                  probe_text) is not None,
                        'evidence.probeKindMissing',
                        'query %r probe kind-check theorem is missing' % qid)
                c.check(probe.get('buildCommand', '').startswith(
                    'proofs/scripts/lake env lean '), 'evidence.probeBuild',
                    'query %r probe build command drift' % qid)
                c.check(probe.get('log') == PROBE_LOG_REL, 'evidence.probeLog',
                        'query %r probe log path drift' % qid)
                axioms = probe_axioms.get(decl)
                c.check(axioms is not None, 'evidence.probeAxiomLog',
                        'query %r probe declaration has no axiom print-out' % qid)
                if axioms is not None:
                    c.check(axioms == footprint, 'evidence.probeAxiomMatch',
                            'query %r probe axiom print-out %r does not match the declared '
                            'footprint %r' % (qid, sorted(axioms), sorted(footprint)))
                    c.check(axioms <= ALLOWED_AXIOMS, 'evidence.probeAxiomDisallowed',
                            'query %r probe certificate has disallowed axioms: %s'
                            % (qid, sorted(axioms - ALLOWED_AXIOMS)))
                theorems = evidence.get('underlyingTheorems', [])
                c.check(isinstance(theorems, list) and len(theorems) >= 1,
                        'evidence.underlying',
                        'query %r probe evidence cites no underlying theorem' % qid)
                for thm in theorems or []:
                    d = thm.get('declaration', '')
                    rel = thm.get('sourceArtifact', '')
                    line = thm.get('sourceLine')
                    c.nonempty(d, 'evidence.underlyingDecl',
                               'query %r underlying theorem has no declaration' % qid)
                    path = os.path.join(ROOT, rel)
                    c.check(os.path.exists(path), 'evidence.underlyingSource',
                            'query %r underlying theorem source is missing' % qid)
                    c.check(isinstance(line, int) and line >= 1,
                            'evidence.underlyingLine',
                            'query %r underlying theorem has no positive source line' % qid)
                    if os.path.exists(path) and isinstance(line, int):
                        text = open(path, encoding='utf-8').read().splitlines()
                        c.check(line <= len(text), 'evidence.underlyingLineRange',
                                'query %r underlying theorem line is outside its source' % qid)
                        if line <= len(text):
                            c.check(short_name(d) in text[line - 1],
                                    'evidence.underlyingLineMatch',
                                    'query %r underlying theorem is not at its declared '
                                    'source line' % qid)
            elif status in {'unresolved', 'notEstablished'}:
                c.check(q.get('scope', {}).get('id') == CANDIDATE_SCOPE,
                        'outcome.searchScope',
                        'query %r status %s does not use the candidate-bridge scope'
                        % (qid, status))
                non_certified.append((qid, status, evidence))
                search_required.add(qid)
                c.check(evidence.get('type') == 'scoped-search', 'evidence.searchType',
                        'query %r status %s requires a scoped-search evidence record'
                        % (qid, status))
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r status %s has no search-log reference' % (qid, status))
                c.nonempty(evidence.get('candidateSummary'), 'evidence.candidateSummary',
                           'query %r status %s has no candidate metadata summary'
                           % (qid, status))
            elif status == 'outOfScope':
                c.check(q.get('scope', {}).get('id') == JURISDICTION_SCOPE,
                        'outcome.jurisdictionScope',
                        'query %r outOfScope does not use the jurisdiction scope' % qid)
                non_certified.append((qid, status, evidence))
                search_required.add(qid)
                c.check(evidence.get('type') == 'jurisdiction', 'evidence.jurisdictionType',
                        'query %r outOfScope requires a jurisdiction evidence record' % qid)
                c.nonempty(evidence.get('searchLogRef'), 'evidence.searchRef',
                           'query %r outOfScope has no search-log reference' % qid)
                c.nonempty(evidence.get('jurisdictionRationale'),
                           'evidence.jurisdictionRationale',
                           'query %r outOfScope has no statement-level rationale' % qid)
                c.check('PhotoLean.' in (evidence.get('jurisdictionRationale') or ''),
                        'evidence.jurisdictionStatementLevel',
                        'query %r outOfScope rationale does not name delivered statements' % qid)
            elif status == 'refuted':
                c.check(evidence.get('type') == 'refutation-certificate',
                        'evidence.refutationType',
                        'query %r refuted requires a refutation certificate' % qid)
                c.check(evidence.get('kind') == 'refutation', 'evidence.refutationKind',
                        'query %r refuted evidence kind is not refutation' % qid)
                c.nonempty(evidence.get('counterexampleWitness'),
                           'evidence.counterexample',
                           'query %r refuted has no explicit counterexample witness' % qid)

    # ---------------------------------------------------------------- semantic pins
    check_semantic_pins(c, query_by_id, probe_text)

    c.check(certified_decls == set(probe_axioms), 'probe.declarationCoverage',
            'probe axiom declarations %r do not match the certified query declarations %r'
            % (sorted(set(probe_axioms)), sorted(certified_decls)))
    c.check(probe_ref.get('declarationCount') == len(probe_axioms),
            'probe.declarationCount', 'probe reference declaration count drift')
    c.check(len(certified_decls) >= 1, 'probe.noCertificate',
            'package certifies no relation at all')

    # ---------------------------------------------------------------- search log
    entries = search_log.get('entries', [])
    c.check(search_log.get('artifactKind') == 'bounded-search-log', 'search.kind',
            'search-log artifactKind drift')
    c.check(search_log.get('round') == 'R5', 'search.round', 'search-log round drift')
    c.check(search_log.get('snapshot') == snap.get('id'), 'search.snapshot',
            'search-log snapshot drift')
    c.check(search_log.get('workPackage') == wp.get('id'), 'search.workPackage',
            'search-log work package drift')
    entry_ids = [e.get('searchId') for e in entries]
    c.check(len(entry_ids) == len(set(entry_ids)), 'search.duplicate',
            'duplicate search id')
    entry_by_id = {e.get('searchId'): e for e in entries}
    for e in entries:
        sid = e.get('searchId')
        qid = e.get('queryId')
        c.check(qid in query_by_id, 'search.queryMissing',
                'search entry %r points to unknown query %r' % (sid, qid))
        q = query_by_id.get(qid)
        if q is not None:
            c.check(e.get('pairId') == q.get('pairId'), 'search.pairId',
                    'search entry %r pairId drift' % sid)
            c.check(e.get('status') == q.get('outcome', {}).get('status'),
                    'search.status', 'search entry %r status does not match its query' % sid)
            c.check(q.get('outcome', {}).get('evidence', {}).get('searchLogRef') == sid,
                    'search.backref',
                    'query %r does not point back to search entry %r' % (qid, sid))
        c.check(e.get('scope') in scope_lib, 'search.scope',
                'search entry %r has unknown scope' % sid)
        if e.get('status') in {'unresolved', 'notEstablished'}:
            c.check(e.get('scope') == CANDIDATE_SCOPE, 'search.scopeKind',
                    'search entry %r for status %s does not use the candidate-bridge scope'
                    % (sid, e.get('status')))
        if e.get('status') == 'outOfScope':
            c.check(e.get('scope') == JURISDICTION_SCOPE, 'search.scopeKind',
                    'search entry %r for outOfScope does not use the jurisdiction scope' % sid)
        c.check(e.get('snapshot') == snap.get('id'), 'search.entrySnapshot',
                'search entry %r snapshot drift' % sid)
        stmts = e.get('searchedStatements')
        c.check(isinstance(stmts, list) and len(stmts) >= 1, 'search.searchedStatements',
                'search entry %r has no searched statements' % sid)
        for st in stmts or []:
            c.check(st in inv_by_id, 'search.searchedStatementMissing',
                    'search entry %r cites unknown inventory statement %r' % (sid, st))
        kinds = e.get('searchedKinds')
        c.check(isinstance(kinds, list) and len(kinds) >= 1, 'search.searchedKinds',
                'search entry %r has no searched kinds' % sid)
        c.check(set(kinds or []) <= set(KINDS), 'search.kindVocabulary',
                'search entry %r searches an unknown kind' % sid)
        ctxs = e.get('contextsConsidered')
        c.check(isinstance(ctxs, list) and len(ctxs) >= 1, 'search.contexts',
                'search entry %r has no considered context' % sid)
        deps = e.get('dependenciesConsulted')
        c.check(isinstance(deps, list) and len(deps) >= 1, 'search.dependencies',
                'search entry %r has no consulted dependencies' % sid)
        for dep in deps or []:
            c.nonempty(dep.get('artifact'), 'search.depArtifact',
                       'search entry %r dependency has no artifact' % sid)
            c.nonempty(dep.get('locator'), 'search.depLocator',
                       'search entry %r dependency has no locator' % sid)
            c.nonempty(dep.get('finding'), 'search.depFinding',
                       'search entry %r dependency has no finding' % sid)
            art = dep.get('artifact', '')
            if art.startswith(('PhotoLean/', 'tools/', 'bounded_audit/', 'audit_boundary/',
                               'relation_audit/')):
                c.check(os.path.exists(os.path.join(ROOT, art)), 'search.depMissing',
                        'search entry %r dependency artifact is missing: %s' % (sid, art))
        cmds = e.get('commands')
        c.check(isinstance(cmds, list) and len(cmds) >= 1, 'search.commands',
                'search entry %r has no recorded commands' % sid)
        for cmd in cmds or []:
            c.nonempty(cmd.get('command'), 'search.command',
                       'search entry %r command is empty' % sid)
            c.nonempty(cmd.get('purpose'), 'search.commandPurpose',
                       'search entry %r command has no purpose' % sid)
            c.nonempty(cmd.get('result'), 'search.commandResult',
                       'search entry %r command has no result' % sid)
        strategies = e.get('strategiesAttempted')
        c.check(isinstance(strategies, list) and len(strategies) >= 1,
                'search.strategies', 'search entry %r has no attempted strategies' % sid)
        for st in strategies or []:
            c.nonempty(st.get('strategy'), 'search.strategy',
                       'search entry %r strategy is empty' % sid)
            c.nonempty(st.get('outcome'), 'search.strategyOutcome',
                       'search entry %r strategy has no outcome' % sid)
        candidates = e.get('candidateEvidence')
        c.check(isinstance(candidates, list) and len(candidates) >= 1,
                'search.candidates', 'search entry %r has no candidate evidence' % sid)
        c.nonempty(e.get('remainingGap'), 'search.remainingGap',
                   'search entry %r has no remaining gap or jurisdiction boundary' % sid)
        if e.get('status') == 'outOfScope':
            c.nonempty(e.get('jurisdictionReason'), 'search.jurisdictionReason',
                       'outOfScope search entry %r has no jurisdiction reason' % sid)
        rec = e.get('recomputeCommands')
        c.check(isinstance(rec, list) and len(rec) >= 1, 'search.recompute',
                'search entry %r has no recompute command' % sid)
        c.nonempty(e.get('rationale'), 'search.rationale',
                   'search entry %r has no rationale' % sid)

    for qid, status, evidence in non_certified:
        sid = evidence.get('searchLogRef')
        c.check(sid in entry_by_id, 'search.missing',
                'query %r status %s has no search-log entry %r' % (qid, status, sid))
        if sid in entry_by_id:
            c.check(entry_by_id[sid].get('queryId') == qid, 'search.mismatch',
                    'search entry %r queryId does not match %r' % (sid, qid))
    for e in entries:
        q = query_by_id.get(e.get('queryId'))
        if q is not None:
            c.check(q.get('outcome', {}).get('status') != 'certified',
                    'search.certifiedEntry',
                    'certified query %r has a search-log entry' % e.get('queryId'))
    c.check(len(entries) == len(search_required), 'search.entryCount',
            'search-log entry count %d does not match the %d non-certified queries'
            % (len(entries), len(search_required)))

    # ---------------------------------------------------------------- counts
    declared = screening.get('counts', {})
    sc = status_counts([q for p in pairs for q in p.get('queries', [])])
    kc = kind_counts([q for p in pairs for q in p.get('queries', [])])
    c.check(declared.get('pairs') == len(pairs), 'counts.pairs', 'pair count drift')
    c.check(declared.get('queries') == len(all_query_ids), 'counts.queries',
            'query count drift')
    c.check(declared.get('byStatus') == sc, 'counts.byStatus',
            'status counts drift: %r != %r' % (declared.get('byStatus'), sc))
    c.check(declared.get('byExpectedKind') == kc, 'counts.byExpectedKind',
            'kind counts drift: %r != %r' % (declared.get('byExpectedKind'), kc))
    for status in STATUSES:
        c.check(declared.get(status) == sc.get(status, 0),
                'counts.%s' % status, 'declared %s count drift' % status)
    c.check(search_log.get('counts', {}).get('entries') == len(entries),
            'counts.searchEntries', 'search-log entry count drift')
    c.check(search_ref.get('entryCount') == len(entries),
            'searchLogReference.entryCount', 'search-log reference entry count drift')

    # ---------------------------------------------------------------- coverage fragment
    c.check(fragment.get('schemaVersion') == '1.0.0', 'fragment.version',
            'coverage fragment schemaVersion drift')
    c.check(fragment.get('artifactKind') == 'bounded-coverage-fragment',
            'fragment.kind', 'coverage fragment artifactKind drift')
    c.check(fragment.get('round') == 'R5', 'fragment.round',
            'coverage fragment round drift')
    c.check(fragment.get('workPackage') == wp.get('id'), 'fragment.workPackage',
            'coverage fragment work package drift')
    c.check(fragment.get('packagePath') == SCREENING_REL, 'fragment.packagePath',
            'coverage fragment package path drift')
    c.check(fragment.get('screeningSha256') == sha_path(args.screening),
            'fragment.screeningSha', 'coverage fragment screening hash drift')
    c.check(fragment.get('pairCount') == len(EXPECTED_PAIRS), 'fragment.pairCount',
            'coverage fragment pair count drift')
    c.check(fragment.get('queryCount') == len(all_query_ids), 'fragment.queryCount',
            'coverage fragment query count drift')
    c.check(fragment.get('byStatus') == sc, 'fragment.byStatus',
            'coverage fragment status counts drift')
    c.check(fragment.get('byExpectedKind') == kc, 'fragment.byExpectedKind',
            'coverage fragment kind counts drift')
    c.check(fragment.get('primaryCluster') == PRIMARY_CLUSTER,
            'fragment.cluster', 'coverage fragment primary cluster drift')
    c.check(fragment.get('acceptance') == 'submitted-R5-pending-review',
            'fragment.acceptance', 'coverage fragment acceptance status drift')
    c.check('cumulative' not in fragment and
            'remainingPairCount' not in json.dumps(fragment), 'fragment.cumulative',
            'coverage fragment claims a cumulative ledger count')
    frag_pairs = fragment.get('screenedPairs', [])
    frag_ids = [e.get('pairId') for e in frag_pairs]
    c.check(len(frag_ids) == len(EXPECTED_PAIRS), 'fragment.pairRows',
            'coverage fragment screenedPairs count drift')
    c.check(len(frag_ids) == len(set(frag_ids)), 'fragment.duplicate',
            'coverage fragment has a duplicate screened pair')
    c.check(set(frag_ids) == rad1_set, 'fragment.pairSet',
            'coverage fragment pair set is not exactly the approved sixteen')
    pkg_by_id = {p['pairId']: p for p in pairs}
    for e in frag_pairs:
        pid = e.get('pairId')
        p = pkg_by_id.get(pid)
        c.check(p is not None, 'fragment.unknownPair',
                'coverage fragment names unknown pair %r' % pid)
        if p is not None:
            c.check(e.get('queryCount') == len(p.get('queries', [])),
                    'fragment.queryCountPair',
                    'coverage fragment query count for %r drift' % pid)
            c.check(e.get('byStatus') == status_counts(p.get('queries', [])),
                    'fragment.byStatusPair',
                    'coverage fragment byStatus for %r drift' % pid)
            c.check(e.get('theories') == p.get('theories'), 'fragment.theories',
                    'coverage fragment theories for %r drift' % pid)
            c.check(e.get('primaryCluster') == p.get('primaryCluster'),
                    'fragment.pairCluster',
                    'coverage fragment cluster for %r drift' % pid)
    c.check(isinstance(fragment.get('nonClaims'), list) and
            len(fragment.get('nonClaims')) >= 1, 'fragment.nonClaims',
            'coverage fragment has no non-claims statement')

    # ---------------------------------------------------------------- forbidden tokens
    forbidden = re.compile(r'sorry|admit|^[ \t]*(private[ \t]+|protected[ \t]+)?'
                           r'(axiom|constant)([ \t]|$)', re.M)
    c.check(forbidden.search(probe_text) is None, 'probe.forbiddenToken',
            'probe source contains a forbidden token')
    c.check('[exit=0]' in probe_log, 'probe.logExit',
            'probe compile log does not record a zero exit')
    c.check('depends on axioms' in probe_log, 'probe.logAxioms',
            'probe compile log carries no axiom print-outs')

    # ---------------------------------------------------------------- non-claims
    c.check(isinstance(screening.get('nonClaims'), list)
            and len(screening.get('nonClaims')) >= 1, 'nonClaims.missing',
            'screening package has no non-claims statement')
    c.check(isinstance(search_log.get('nonClaims'), list)
            and len(search_log.get('nonClaims')) >= 1, 'nonClaims.search',
            'search log has no non-claims statement')
    joined = ' '.join(screening.get('nonClaims', []))
    c.check('not the same as certified' in joined, 'nonClaims.screenedVsCertified',
            'screening non-claims do not separate screened from certified')
    c.check('outside the frozen bounded query protocol' in joined or
            'outside the frozen bounded query protocol' in
            ' '.join(fragment.get('nonClaims', [])), 'nonClaims.nonExhaustive',
            'package does not state the non-exhaustiveness claim')

    return c.summary()


if __name__ == '__main__':
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Exception:
        print('FAIL [validator.exception] uncaught exception:')
        traceback.print_exc()
        print('RESULT: FAIL (fail-closed on validator exception)')
        sys.exit(1)
