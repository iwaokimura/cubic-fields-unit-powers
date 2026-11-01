# check-phase1-coho.sage --- E048 Phase 1 GATE.
#
# The gate, as the plan states it: on hyperelliptic input the genus and dim H^1
# agree with Sage, and for C_4 the cohomology basis has size 2g = 6.
#
# What is checked here, per curve:
#   (1) dim H^1_rig(U) from Theorem 3.6 equals 2g + #D - 1;
#   (2) exact forms have zero residues (a bug in d or in the residue map shows
#       up here first);
#   (3) dim H^1_rig(X) = 2g -- the gate proper;
#   (4) CALIBRATION of the ported half: the kernel of Proposition 3.12 (finite
#       residues, Tuitman's own criterion) equals the kernel of Sage's residues
#       at the finite places.  These are two independent computations of the
#       same subspace of E.
#
# Run: sage check-phase1-coho.sage

import sys
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()

CURVES = [
    ("hyperelliptic y^2 = x^5-1  (g=2)", y**2 - (x**5 - 1), 2),
    ("hyperelliptic y^2 = x^7-1  (g=3)", y**2 - (x**7 - 1), 3),
    ("hyperelliptic y^2 = x^6-x-1 (g=2)", y**2 - (x**6 - x - 1), 2),
    ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)", y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 3),
]


def one(label, Qxy, g):
    print("=" * 72)
    print(label)
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    ok = True
    print("  genus %d, d_x = %d, deg r = %d, dim E = %d, dim B = %d"
          % (C.genus, C.dx, C.degr, H.dim_E, H.dim_B))
    sys.stdout.flush()

    # (1)
    dU, im = H.H1U()
    nD = sum(pl.degree() for pl in C.L(C.r).divisor().support())
    pred = 2 * C.genus + nD - 1
    print("  dim H^1_rig(U) = %d, predicted 2g + #D - 1 = %d + %d - 1 = %d  %s"
          % (dU, 2 * C.genus, nD, pred, "ok" if dU == pred else "*** MISMATCH ***"))
    ok = ok and (dU == pred)
    sys.stdout.flush()

    # (2) and (3)
    dX, rk, places = H.H1X()
    print("  residue map rank %d (at most #D - 1 = %d)" % (rk, nD - 1))
    print("  dim H^1_rig(X) = %d, 2g = %d  %s"
          % (dX, 2 * C.genus, "ok" if dX == 2 * C.genus else "*** GATE FAILS ***"))
    ok = ok and (dX == 2 * C.genus)
    sys.stdout.flush()

    # (4) calibration of Proposition 3.12 against Sage's finite residues
    # NB: L.places_infinite() returns the EMPTY list for these fields, so
    # filtering with "pl not in L.places_infinite()" keeps the place over
    # x = infinity and silently compares the wrong two subspaces.  The
    # predicate that works is is_infinite_place().
    finite_places = [pl for pl in places if not pl.is_infinite_place()]
    Mfin, _ = H.residue_matrix_sage(places=finite_places)
    ker_sage = Mfin.right_kernel()
    ker_tuitman = H.finite_residue_kernel_tuitman()
    same = (ker_sage == ker_tuitman)
    print("  Prop 3.12 kernel dim %d, Sage finite-residue kernel dim %d, equal: %s %s"
          % (ker_tuitman.dimension(), ker_sage.dimension(), same,
             "" if same else "*** CALIBRATION FAILS ***"))
    ok = ok and same
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase1-coho.sage --- E048 Phase 1 gate ===")
    print("")
    allok = True
    for label, Qxy, g in CURVES:
        try:
            allok = one(label, Qxy, g) and allok
        except Exception as e:
            print("  *** EXCEPTION: %s: %s" % (type(e).__name__, e))
            allok = False
        print("")
        sys.stdout.flush()
    print("=" * 72)
    print("PHASE 1 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
