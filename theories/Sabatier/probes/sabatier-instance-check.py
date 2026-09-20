#!/usr/bin/env python3
"""Kernel-independent cross-check of the Sabatier theory's instance rows (S5b).

Exact rational arithmetic (`fractions.Fraction`) re-derives every number the instance rows assert:
the apexes, the pass heights, the effective barriers, the zone verdicts and the tolerance verdicts
of `PhotoLean/Sabatier/Instances.lean` (plan §8.2). This script is *evidence*, not a substitute for
the kernel: it validates the STATEMENTS (that the asserted numbers are the ones the model produces)
while the Lean proofs establish them inside the kernel.

Usage: python3 theories/Sabatier/probes/sabatier-instance-check.py
Exit code 0 = every row reproduced; 1 = a mismatch (printed).
"""
from fractions import Fraction as F

FAIL = []


def check(label, got, want):
    ok = got == want
    print(f"{'ok  ' if ok else 'FAIL'} {label}: got {got} want {want}")
    if not ok:
        FAIL.append(label)


def branch_up(aA, bA, dE):
    return aA * dE + bA


def branch_down(aB, bB, dE):
    return bB - aB * dE


def barrier(aA, bA, aB, bB, dE):
    return max(branch_up(aA, bA, dE), branch_down(aB, bB, dE))


def apex(aA, bA, aB, bB):
    return F(bB - bA, 1) / F(aA + aB, 1)


def apex_barrier(aA, bA, aB, bB):
    return barrier(aA, bA, aB, bB, apex(aA, bA, aB, bB))


def zone(apexD, dE):
    if dE == apexD:
        return "optimal"
    return "tooStrong" if dE < apexD else "tooWeak"


print("== I1  symmetric thermoneutral series (1/2, 1/2, 1/2, 1/2) ==")
check("I1 apex", apex(F(1, 2), F(1, 2), F(1, 2), F(1, 2)), F(0))
check("I1 apexBarrier", apex_barrier(F(1, 2), F(1, 2), F(1, 2), F(1, 2)), F(1, 2))
check("I1 zone(0)", zone(F(0), F(0)), "optimal")
check("I1 zone(-1/2)", zone(F(0), F(-1, 2)), "tooStrong")
check("I1 barrier(-1/2)", barrier(F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(-1, 2)), F(3, 4))

print("== I2/I3  asymmetric series (1/2, 0, 1, 1) ==")
check("I2 apex", apex(F(1, 2), F(0), F(1), F(1)), F(2, 3))
check("I2 zone(0)", zone(F(2, 3), F(0)), "tooStrong")
check("I2 barrier(0)", barrier(F(1, 2), F(0), F(1), F(1), F(0)), F(1))
check("I2 zone(1)", zone(F(2, 3), F(1)), "tooWeak")
check("I2 barrier(1)", barrier(F(1, 2), F(0), F(1), F(1), F(1)), F(1, 2))
check("I3 barrier(-1/3)", barrier(F(1, 2), F(0), F(1), F(1), F(-1, 3)), F(4, 3))
check("I3 zone(-1/3)", zone(F(2, 3), F(-1, 3)), "tooStrong")

print("== I4  zero-slope series (0, 1, 1, 1): plateau, no pointed apex ==")
check("I4 conforms", F(0) > 0 and F(1) > 0, False)
check("I4 apex", apex(F(0), F(1), F(1), F(1)), F(0))
check("I4 barrier(1)", barrier(F(0), F(1), F(1), F(1), F(1)), barrier(F(0), F(1), F(1), F(1), F(0)))
check("I4 barrier(1/2)", barrier(F(0), F(1), F(1), F(1), F(1, 2)),
      barrier(F(0), F(1), F(1), F(1), F(0)))
# the minimizer is NOT unique: the barrier equals its apex value on the whole half-line dE >= 0
ties = [d for d in (F(0), F(1, 4), F(1), F(10)) if barrier(F(0), F(1), F(1), F(1), d)
        == barrier(F(0), F(1), F(1), F(1), F(0))]
check("I4 plateau ties (>=2 distinct)", len(set(ties)) >= 2, True)

print("== I5  mixed-slope series (1, 0, -1, 1): strictly monotone, no interior optimum ==")
check("I5 conforms", F(1) > 0 and F(-1) > 0, False)
xs = [F(-3), F(-1), F(0), F(1), F(3)]
vals = [barrier(F(1), F(0), F(-1), F(1), x) for x in xs]
check("I5 strictly increasing", all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)), True)

print("== I6  tolerance rows on the I2 series ==")
check("I6 |1/2 - apex| <= 1/2", abs(F(1, 2) - F(2, 3)) <= F(1, 2), True)
check("I6 penalty", barrier(F(1, 2), F(0), F(1), F(1), F(1, 2)) - apex_barrier(F(1, 2), F(0), F(1), F(1)),
      F(1, 6))

print("== I7  two-parabola cross-check lam1 = 1, lam2 = 4 ==")
# apexPar = (lam2*sqrt(lam1) - lam1*sqrt(lam2)) / (sqrt(lam1) + sqrt(lam2)) with sqrt exact here
check("I7 apexPar", (F(4) * 1 - F(1) * 2) / (1 + 2), F(2, 3))
d = F(2, 3)
check("I7 crossing", (1 + d) ** 2 / (4 * 1) == (4 - d) ** 2 / (4 * 4), True)
check("I7 apexBarrier", (1 + d) ** 2 / (4 * 1), F(25, 36))
check("I7 linear below", max(d / 2 + F(1, 4), F(1) - d / 2) < F(25, 36), True)
check("I7 linear value", max(d / 2 + F(1, 4), F(1) - d / 2), F(2, 3))

print("== I9/I10/I11  literature rows on the I1 reference volcano (apex 0) ==")
ref = (F(1, 2), F(1, 2), F(1, 2), F(1, 2))
for metal, xe in (("Pt", F(-9, 100)), ("Au", F(45, 100)), ("W", F(-43, 100))):
    print(f"   {metal}: DeltaG_H* = {float(xe):+.2f} eV -> zone {zone(F(0), xe)}, "
          f"barrier {barrier(*ref, xe)}")
check("I9 barrier(Pt)", barrier(*ref, F(-9, 100)), F(109, 200))
check("I9 zone(Pt)", zone(F(0), F(-9, 100)), "tooStrong")
check("I9 nearOptimal(Pt, 1/10)", abs(F(-9, 100)) <= F(1, 10), True)
check("I10 barrier(Au)", barrier(*ref, F(45, 100)), F(29, 40))
check("I10 zone(Au)", zone(F(0), F(45, 100)), "tooWeak")
check("I10 not nearOptimal(Au, 1/10)", abs(F(45, 100)) <= F(1, 10), False)
check("I11 zone(W)", zone(F(0), F(-43, 100)), "tooStrong")
check("I11 nearOptimal(W, 1/2)", abs(F(-43, 100)) <= F(1, 2), True)

print("== I12  OER volcano (Man et al. 2011, Eq. 4.16-4.18): max(x, 3.20 - x) ==")
check("I12 apex", apex(F(1), F(0), F(1), F(16, 5)), F(8, 5))
check("I12 apexBarrier", apex_barrier(F(1), F(0), F(1), F(16, 5)), F(8, 5))
check("I12 conforms", F(1) > 0 and F(1) > 0, True)
check("I12 overpotential", apex_barrier(F(1), F(0), F(1), F(16, 5)) - F(123, 100), F(37, 100))
# the two OER branches cross exactly at 8/5: 8/5 = 16/5 - 8/5
check("I12 branches cross at apex", F(8, 5) == F(16, 5) - F(8, 5), True)

print("== sharp condition spot checks (the plan's headline) ==")
for (aA, aB), want in (((F(1, 2), F(1, 2)), True), ((F(0), F(1)), False),
                       ((F(1), F(-1)), False), ((F(-1), F(-1)), True)):
    check(f"descriptor present for (aA,aB)=({aA},{aB})", aA * aB > 0, want)

print()
if FAIL:
    print(f"FAIL: {len(FAIL)} mismatched row(s): {FAIL}")
    raise SystemExit(1)
print("all instance rows reproduced exactly (rational arithmetic)")
