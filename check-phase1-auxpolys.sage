# check-phase1-auxpolys.sage --- E048 Phase 1, gate for padic/auxpolys.py.
#
# The plan's Phase 1 gate has two halves:
#   (a) on hyperelliptic input, the genus and the dimension of H^1 agree with
#       what Sage says independently;
#   (b) for C_4 the cohomology basis has size 2g = 6.
# This script is the auxpolys half: it checks every quantity Section 2 of
# Tuitman I defines, on three calibration curves and on C_4, and it checks the
# dimension count that Theorem 3.6 predicts for H^1_rig(U) against the
# topological value 2g + #D - 1, where D is the divisor removed.
#
# Run: sage check-phase1-auxpolys.sage

import sys
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()

CURVES = [
    ("hyperelliptic y^2 = x^5-1  (g=2)", y**2 - (x**5 - 1), 2),
    ("hyperelliptic y^2 = x^7-1  (g=3)", y**2 - (x**7 - 1), 3),
    ("hyperelliptic y^2 = x^6-x-1 (g=2)", y**2 - (x**6 - x - 1), 2),
    ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)", y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 3),
]


def removed_points(C):
    """#D, the number of geometric points of X outside U = X \\ D.

    U = Spec Z_q[x,1/r,y]/(Q), so D consists of the points over the roots of r
    together with the points over x = infinity -- which is exactly the support
    of the divisor of r seen as a function on X: its zeros are the points over
    the roots of r, its poles are the points over infinity.  Counting geometric
    points means summing the residue degrees.
    """
    D = C.L(C.r).divisor()
    return sum(pl.degree() for pl in D.support())


def report(label, Qxy, expected_genus):
    print("=" * 72)
    C = TuitmanCurve(Qxy, name=label)
    print(C.summary())
    ok = True

    if C.genus != expected_genus:
        print("  *** genus %d, expected %d ***" % (C.genus, expected_genus))
        ok = False
    if not C.W0_is_identity:
        print("  NOTE: W0 is not the identity, so Assumption 2 fails for this model")

    # Theorem 3.6 dimension count
    Eb = C.E_bounds()
    Bb = C.B_bounds()
    dimE = sum(b + 1 for b in Eb if b >= 0)
    dimB = sum(b + 1 for b in Bb if b >= 0)
    # d kills exactly the constants inside B
    dimdB = dimB - 1
    dimH1U = dimE - dimdB
    nD = removed_points(C)
    predicted = 2 * C.genus + nD - 1
    print("  dim E_0 cap E_inf = %d, dim B_0 cap B_inf = %d, dim d(B) = %d"
          % (dimE, dimB, dimdB))
    print("  ==> dim H^1_rig(U) = %d" % dimH1U)
    print("      #D = %d, so 2g + #D - 1 = %d" % (nD, predicted))
    if dimH1U != predicted:
        print("  *** MISMATCH: the degree bounds or the count are wrong ***")
        ok = False
    else:
        print("      match")
    sys.stdout.flush()
    return ok, C


def main():
    print("=== check-phase1-auxpolys.sage --- Phase 1 gate, Section 2 data ===")
    print("")
    allok = True
    for label, Qxy, g in CURVES:
        ok, C = report(label, Qxy, g)
        allok = allok and ok
        print("")
    print("=" * 72)
    print("VERDICT: %s" % ("all checks passed" if allok else "*** FAILURES ***"))
    sys.stdout.flush()


main()
