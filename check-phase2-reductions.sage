# check-phase2-reductions.sage --- E057 (E048 Phase 2) GATE, part 1.
#
# What is checked here, per curve:
#   (1) Proposition 3.4 is an IDENTITY, not an approximation: for each test
#       1-form, (sum (w_i - u_i) b^inf_i)/r equals the derivative of
#       sum v_i b^inf_i, exactly, in the function field; and the reduction
#       terminates with ord_inf(u) > -deg(r), which is the hypothesis of
#       Proposition 3.13.
#   (2) Remark 3.5: sum v_i b^inf_i has poles only over x = infinity, i.e. the
#       infinite reduction does not disturb the finite side.
#   (3) Proposition 2.10 / proof of 3.13: the eigenvalues of Ginf_{-1} are
#       rational, lie in [0,1), and the matrix is diagonalisable.
#   (4) CALIBRATION: the kernel of Proposition 3.13 on E equals the kernel of
#       Sage's residues at the infinite places.  Two independent computations.
#   (5) dim H^1_rig(X) computed with BOTH residue maps in Tuitman's terms
#       reproduces E056's table (4, 6, 4, 6).
#
# E056's lesson applies: the three hyperelliptic curves have a single place over
# x = infinity and cannot separate the two subspaces in (4).  C_4, with four
# conjugate points at infinity, is the only curve here that can fail.
#
# Run: sage check-phase2-reductions.sage

import sys
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.reductions import InfiniteReduction, ord_infinity_vector

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()

CURVES = [
    ("hyperelliptic y^2 = x^5-1  (g=2)", y**2 - (x**5 - 1), 2, 4),
    ("hyperelliptic y^2 = x^7-1  (g=3)", y**2 - (x**7 - 1), 3, 6),
    ("hyperelliptic y^2 = x^6-x-1 (g=2)", y**2 - (x**6 - x - 1), 2, 4),
    ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
     y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 3, 6),
]


def bexp(C, coeffs):
    """sum_i coeffs_i b^inf_i as an element of the function field L."""
    L = C.L
    bas = [sum(C.Winf[i, j] * C.y**i for i in range(C.dx)) for j in range(C.dx)]
    return sum(L(coeffs[j]) * bas[j] for j in range(C.dx))


def identity_holds(C, w, u, v):
    """Proposition 3.4 as an exact identity in the function field."""
    lhs = bexp(C, [w[i] - u[i] for i in range(C.dx)]) / C.L(C.r)
    rhs = bexp(C, list(v)).derivative()
    return lhs == rhs


def finite_pole_count(C, v):
    """Number of finite places where sum v_i b^inf_i has a pole (Remark 3.5
    says there are none while the reduction stays in its range)."""
    f = bexp(C, list(v))
    if f == 0:
        return 0
    return sum(1 for pl, e in f.divisor().list()
               if e < 0 and not pl.is_infinite_place())


def test_forms(C):
    """Test vectors w in the b^inf basis, including some with a high pole order
    at infinity so that several reduction steps actually run."""
    K = C.K
    xg = K.gen()
    T = C.Winf.inverse()
    out = []
    # the E-basis elements x^d y^i, in the b^inf basis
    for (i, d) in [(0, 0), (1, 0), (C.dx - 1, 1)]:
        out.append(("x^%d y^%d" % (d, i),
                    vector(K, [T[j, i] * xg**d for j in range(C.dx)])))
    # deliberately unreduced: high powers of x
    for d in [C.degr, C.degr + 3]:
        out.append(("x^%d y^0 (unreduced)" % d,
                    vector(K, [T[j, 0] * xg**d for j in range(C.dx)])))
    # a mixed one
    out.append(("mixed", vector(K, [T[j, 0] * xg**(C.degr + 1)
                                    + T[j, C.dx - 1] * xg**2
                                    for j in range(C.dx)])))
    return out


def one(label, Qxy, g, dimH1X):
    print("=" * 72)
    print(label)
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    red = InfiniteReduction(C)
    ok = True
    print("  genus %d, d_x = %d, deg r = %d, ord_0(Winf) = %s, dim E = %d"
          % (C.genus, C.dx, C.degr, C.ord0_Winf, H.dim_E))
    sys.stdout.flush()

    # (3) Proposition 2.10 on Ginf_{-1}
    rep = red.eigenvalue_report()
    good = rep["all_rational"] and rep["in_[0,1)"] and rep["diagonalisable"]
    print("  Ginf_{-1}: eigenvalues %s, rational %s, in [0,1) %s, diagonalisable %s  %s"
          % ([str(l) for l, _ in rep["eigenvalues"]], rep["all_rational"],
             rep["in_[0,1)"], rep["diagonalisable"],
             "ok" if good else "*** PROP 2.10 FAILS ***"))
    ok = ok and good
    sys.stdout.flush()

    # (1) and (2).  Two targets, because they are genuinely different:
    #   mmin = m_min_remark35  ->  E_infinity of Theorem 3.6, every step inside
    #                              Remark 3.5, so the exact form is in B_0;
    #   mmin = 1               ->  the hypothesis of Proposition 3.13, reached
    #                              by steps BELOW Remark 3.5's range, where the
    #                              exact form may acquire a pole at x = 0.
    mmin35 = red.m_min_remark35()
    thrE = C.ord0_Winf - C.degr + 1
    print("  Remark 3.5 holds for m >= %d; Prop 3.13 needs the schedule down to m = 1"
          % mmin35)
    nfail = 0
    forms = test_forms(C)
    for name, w in forms:
        uE, vE, _ = red.reduce(w, mmin=mmin35)
        oE = ord_infinity_vector(uE)
        inE = (oE is Infinity) or (oE > thrE)
        exE = identity_holds(C, w, uE, vE)
        polesE = finite_pole_count(C, vE)

        u1, v1, _ = red.reduce(w, mmin=1)
        o1 = ord_infinity_vector(u1)
        hyp13 = (o1 is Infinity) or (o1 > -C.degr)
        ex1 = identity_holds(C, w, u1, v1)
        poles1 = finite_pole_count(C, v1)

        good = exE and inE and polesE == 0 and ex1 and hyp13
        if not good:
            nfail += 1
        print("    %-24s E_inf: ord %-5s in E_inf %s id %s Rmk3.5 %s | "
              "3.13: ord %-5s hyp %s id %s (finite poles %d)  %s"
              % (name, oE, inE, exE, polesE == 0, o1, hyp13, ex1, poles1,
                 "" if good else "*** FAILS ***"))
        sys.stdout.flush()
    print("  Proposition 3.4: %d/%d test forms ok" % (len(forms) - nfail, len(forms)))
    ok = ok and (nfail == 0)

    # (4) calibration of Proposition 3.13 against Sage's residues at infinity
    places = C.L(C.r).divisor().support()
    inf_places = [pl for pl in places if pl.is_infinite_place()]
    Minf, _ = H.residue_matrix_sage(places=inf_places)
    ker_sage = Minf.right_kernel()
    ker_tuitman, Mt = H.infinite_residue_kernel_tuitman(red=red)
    same = (ker_sage == ker_tuitman)
    print("  Prop 3.13 kernel dim %d, Sage infinite-residue kernel dim %d, equal: %s %s"
          % (ker_tuitman.dimension(), ker_sage.dimension(), same,
             "" if same else "*** CALIBRATION FAILS ***"))
    print("    (%d place(s) at infinity, of degree(s) %s)"
          % (len(inf_places), [pl.degree() for pl in inf_places]))
    ok = ok and same
    sys.stdout.flush()

    # (5) dim H^1_rig(X), both residues ported
    dX, rk, dfin, dinf = H.H1X_tuitman()
    print("  ported res kernels: finite %d, infinite %d, joint %d"
          % (dfin, dinf, H.dim_E - rk))
    print("  dim H^1_rig(X) = %d, 2g = %d, E056 gave %d  %s"
          % (dX, 2 * C.genus, dimH1X,
             "ok" if dX == 2 * C.genus == dimH1X else "*** GATE FAILS ***"))
    ok = ok and (dX == 2 * C.genus == dimH1X)
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase2-reductions.sage --- E057 gate (Prop 3.4, 3.13) ===")
    print("")
    allok = True
    for label, Qxy, g, d in CURVES:
        try:
            allok = one(label, Qxy, g, d) and allok
        except Exception as e:
            print("  *** EXCEPTION: %s: %s" % (type(e).__name__, e))
            allok = False
        print("")
        sys.stdout.flush()
    print("=" * 72)
    print("E057 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
