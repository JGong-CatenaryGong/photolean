#!/usr/bin/env python3
"""Machine-recomputable statement-level vocabulary scan for the R5 XD2 package.

Usage:
    python3 bounded_audit/r5/cross-domain-02/evidence/signature_scan.py <PartnerTheory>

The scan reads the frozen R1 statement inventory, takes the *declaration signatures*
(`sourceSignature`, the authoritative statement text), and reports, for the Goldschmidt
authority and the named partner authority:

  * the number of statement rows on each side;
  * which Goldschmidt identifiers occur in partner signatures;
  * which partner identifiers occur in Goldschmidt signatures.

A declaration signature is statement-level evidence: a delivered statement that mentioned an
observable of the other theory would show up here even if it lived in another module. Prose
matches in comments are reported separately by the search log (`grep`) and are not statements.

Exit code 0 when both intersections are empty, 1 otherwise. The package validator re-derives
the same scan independently; this script exists so the search-log commands can be re-run.
"""

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))))

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


def signatures(inv, theory):
    return [(row['id'], row['sourceSignature'])
            for row in inv['statements'] if row['theory'] == theory]


def hits(tokens, rows):
    found = []
    for token in tokens:
        pattern = re.compile(r'\b' + re.escape(token) + r'\b')
        matched = [rid for rid, sig in rows if pattern.search(sig)]
        if matched:
            found.append((token, matched))
    return found


def main(argv):
    if len(argv) != 2 or argv[1] not in PARTNER_TOKENS:
        print('usage: signature_scan.py <%s>' % '|'.join(sorted(PARTNER_TOKENS)))
        return 2
    partner = argv[1]
    inventory_path = os.path.join(ROOT, 'audit_boundary/statement-inventory.json')
    inv = json.load(open(inventory_path, encoding='utf-8'))
    gs = signatures(inv, 'Goldschmidt')
    pt = signatures(inv, partner)
    gs_in_pt = hits(GOLDSCHMIDT_TOKENS, pt)
    pt_in_gs = hits(PARTNER_TOKENS[partner], gs)
    print('signature scan: Goldschmidt x %s' % partner)
    print('  signature source: audit_boundary/statement-inventory.json (sourceSignature column)')
    print('  Goldschmidt statement rows: %d' % len(gs))
    print('  %s statement rows: %d' % (partner, len(pt)))
    print('  Goldschmidt identifiers in %s signatures: %d %s'
          % (partner, len(gs_in_pt), [t for t, _ in gs_in_pt]))
    print('  %s identifiers in Goldschmidt signatures: %d %s'
          % (partner, len(pt_in_gs), [t for t, _ in pt_in_gs]))
    ok = not gs_in_pt and not pt_in_gs
    print('RESULT: %s' % ('PASS (no shared statement-level identifier)' if ok else 'FAIL'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
