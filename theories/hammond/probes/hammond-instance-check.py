#!/usr/bin/env python3
"""Independent numerical cross-check of the Hammond instance verdicts (lead-owned).

The instance layer (H5b) delivers kernel-checked *exact rational* verdicts. This script
recomputes the same quantities from the definitions with exact fractions, so the verifier has
an evidence chain that does not go through the delivered Lean theorems.

Definitions (driving force x = -dG):
    q(x)      = (lam - x) / (2*lam)                  transition-state coordinate
    gapR(x)   = (lam - x)^2 / (4*lam)                forward barrier
    gapP(x)   = (lam + x)^2 / (4*lam)                reverse barrier
    secant    = -(gapR(x2) - gapR(x1)) / (x2 - x1)   measured Leffler/Bronsted coefficient
    conforms  = 0 < lam and -lam < x < lam           point-level Hammond verdict
"""
from fractions import Fraction as F

CASES = [
    # label, lam, x  (eV; x = -dG; the MCC / reaction-centre values are the ones verified in
    # theories/Marcus/LITERATURE.md and restated in theories/hammond/plan.md section 8.2)
    ("I1 thermoneutral",            F(1),    F(0)),
    ("I2 exergonic textbook",       F(1),    F(3, 4)),
    ("I3 endergonic textbook",      F(1),    F(-1, 2)),
    ("I4 barrierless forward",      F(1),    F(1)),
    ("I5 MCC normal",               F(6, 5), F(1, 20)),
    ("I6 MCC inverted",             F(6, 5), F(12, 5)),
    ("I7 reaction centre inverted", F(1, 4), F(11, 10)),
]

SECANTS = [
    ("I6 MCC pair 3/5 -> 12/5", F(6, 5), F(3, 5), F(12, 5)),
    ("I9 MCC pair 3/5 -> 12/5 (Hammond direction)", F(6, 5), F(3, 5), F(12, 5)),
]


def q(lam, x):
    return (lam - x) / (2 * lam)


def gapR(lam, x):
    return (lam - x) ** 2 / (4 * lam)


def gapP(lam, x):
    return (lam + x) ** 2 / (4 * lam)


def secant(lam, x1, x2):
    return -(gapR(lam, x2) - gapR(lam, x1)) / (x2 - x1)


def zone(lam, x):
    if x == lam:
        return "atReactant"
    if x == -lam:
        return "atProduct"
    if x < -lam:
        return "beyondProduct"
    if lam < x:
        return "beyondReactant"
    if x == 0:
        return "half"
    if 0 < x:
        return "early"
    return "late"


def main():
    print(f"{'instance':32s} {'lam':>6s} {'x':>7s} {'q(x)':>10s} {'conforms':>9s}  zone")
    for label, lam, x in CASES:
        conforms = "YES" if (0 < lam and -lam < x < lam) else "NO"
        print(f"{label:32s} {str(lam):>6s} {str(x):>7s} {str(q(lam, x)):>10s} {conforms:>9s}  {zone(lam, x)}")
    print()
    for label, lam, x1, x2 in SECANTS:
        print(f"{label}: secant = {secant(lam, x1, x2)}  (midpoint q = {q(lam, (x1 + x2) / 2)})")
    print()
    print("reverse-barrier identity gapP - gapR = x:", all(gapP(l, x) - gapR(l, x) == x for _, l, x in CASES))
    print("non-physical branches (no lam > 0):")
    for lam in (F(0), F(-1, 2)):
        print(f"  lam = {lam}: no x with -lam < x < lam exists -> no conforming instance")
    print()
    print("structural monotonicity on the MCC pair: q(12/5) < q(3/5) ->",
          q(F(6, 5), F(12, 5)) < q(F(6, 5), F(3, 5)))


if __name__ == "__main__":
    main()
