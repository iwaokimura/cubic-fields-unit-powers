# check-phase3-tiny.sage --- E060 (E048 Phase 3) GATE, part 1.
#
# Tiny integrals (Balakrishnan-Tuitman Algorithm 3.4) at good finite points.
# Four checks, in increasing order of what they can catch:
#
#   (1) The local expansion solves the curve: Q(x(t), y(t)) = 0 to working
#       precision, and the point rebuilt at t = p lies on the curve.
#   (2) FUNDAMENTAL THEOREM OF CALCULUS (Theorem 3.1(4)): for f a monomial of
#       B_0 cap B_inf, int_P^Q df = f(Q) - f(P).  The E-coordinates of df are a
#       column of the matrix of d from E056, so this needs no external data and
#       it tests the expansion, the form-to-series conversion and the
#       integration together.
#   (3) ADDITIVITY (Theorem 3.1(2)): int_P^Q + int_Q^R = int_P^R inside a disk.
#   (4) AGREEMENT WITH SAGE on hyperelliptic curves: our monomial x^d y dx/r is
#       x^d dx/y = 2 (x^d dx/(2y)), so it must equal twice Sage's
#       tiny_integrals_on_basis.  Tiny integrals do not use Frobenius (BT
#       Remark 3.5), so this route shares nothing with E059 -- neither the
#       matrix, nor the sign convention that E059 got wrong, nor the basis.
#
# Run: sage check-phase3-tiny.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.radic import RAdicRing
from padic.points import CurvePoint
from padic.integrals import TinyIntegrals, tprec_for

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def form_from_Ecoords(RR, H, vec):
    """E-coordinates -> the u_i with omega = (sum_i u_i(x) y^i) dx/r."""
    out = [RR.Rx.zero()] * RR.dx
    for c, (i, d) in zip(vec, H.E_basis):
        if c != 0:
            out[i] += RR._coerce_QQ(c) * RR.Rx.gen()**d
    return out


def eval_monomial(P, i, d):
    """The value of x^d y^i at a point."""
    return P.x**d * P.y**i


def check_curve(label, Qxy, p, N, x0, ysel=0, sage_f=None):
    print("-" * 72)
    print("%s   p = %d, N = %d" % (label, p, N))
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    K = Qp(p, prec=N, type='floating-point')
    RR = RAdicRing(C, p, N, base=K)
    TI = TinyIntegrals(RR)
    ok = True

    # a good point: the first x in the search list carrying a Q_p-rational y.
    # A case with no such point is a FAILURE of the gate's setup, not a pass:
    # skipping quietly would let a case disappear from the calibration set.
    Ry = PolynomialRing(K, 'Y')
    Yv = Ry.gen()
    P = None
    for cand in [x0] + list(range(-6, 12)):
        q0 = Ry.zero()
        for (ex, ey), c in Qxy.dict().items():
            q0 += RR._coerce_QQ(c) * K(cand)**ZZ(ex) * Yv**ZZ(ey)
        roots = [r for r, _ in q0.roots()]
        if not roots:
            continue
        cp = CurvePoint(RR, K(cand), y=roots[ysel % len(roots)])
        if cp.is_good() and cp.on_curve():
            P = cp
            break
    if P is None:
        print("   *** no good Q_p-rational point found: gate setup FAILS")
        return False
    print("   P = %s;  good: %s, on curve: %s" % (P, P.is_good(), P.on_curve()))
    if not (P.is_good() and P.on_curve()):
        return False

    # (1) the expansion
    exp = TI.expansion_at(P)
    res = exp.residual()
    Q = exp.point_at(K(p))
    Rp = exp.point_at(K(p)**2)
    good1 = (res >= N) and Q.on_curve() and Rp.on_curve() and P.same_disk(Q)
    print("   (1) t-prec %d, residual of Q(x(t),y(t)) = %s (>= N = %d): %s; "
          "rebuilt points on curve: %s, %s"
          % (TI.tprec, res, N, res >= N, Q.on_curve(), Rp.on_curve()))
    ok = ok and good1

    # (2) fundamental theorem of calculus on the B-basis
    dM = H.d_matrix()
    nfail, ntest = 0, 0
    for col, (i, d) in enumerate(H.B_basis):
        vec = dM.column(col)
        coeffs = form_from_Ecoords(RR, H, vec)
        lhs = TI.tiny_integral(coeffs, P, Q)
        rhs = eval_monomial(Q, i, d) - eval_monomial(P, i, d)
        ntest += 1
        if not RR._coeff_is_zero(lhs - rhs):
            nfail += 1
    print("   (2) int d(x^d y^i) = f(Q) - f(P): %d/%d ok" % (ntest - nfail, ntest))
    ok = ok and (nfail == 0)

    # (3) additivity inside the disk
    forms = []
    for dd in range(2 * C.genus):
        u = [RR.Rx.zero()] * C.dx
        u[min(1, C.dx - 1)] = RR.Rx.gen()**dd
        forms.append(u)
    a = TI.tiny_integrals_on_basis(forms, P, Q)
    b = TI.tiny_integrals_on_basis(forms, Q, Rp)
    c = TI.tiny_integrals_on_basis(forms, P, Rp)
    add_ok = all(RR._coeff_is_zero(a[k] + b[k] - c[k]) for k in range(len(a)))
    print("   (3) additivity int_P^Q + int_Q^R = int_P^R: %s" % add_ok)
    ok = ok and add_ok

    # (4) Sage, hyperelliptic only
    if sage_f is not None:
        HCp = HyperellipticCurve(sage_f).change_ring(Qp(p, N))
        P_s = HCp(Qp(p, N)(P.x), Qp(p, N)(P.y))
        Q_s = HCp(Qp(p, N)(Q.x), Qp(p, N)(Q.y))
        sv = HCp.tiny_integrals_on_basis(P_s, Q_s)
        m = all(K(K(2 * sv[k]) - a[k]).valuation() >= N - 1
                for k in range(len(sv)))
        print("   (4) vs Sage tiny_integrals_on_basis (x2): %s" % m)
        ok = ok and m
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase3-tiny.sage --- E060 gate (BT Algorithm 3.4) ===")
    Rx = PolynomialRing(QQ, 'X')
    X = Rx.gen()
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 11, 8, 2, 0, X**5 - 1),
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 13, 6, 3, 0, X**5 - 1),
        ("y^2 = x^7-1", y**2 - (x**7 - 1), 11, 6, 4, 0, X**7 - 1),
        ("y^2 = x^6-x-1", y**2 - (x**6 - x - 1), 7, 6, 3, 0, X**6 - X - 1),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 11, 8, 1, 0, None),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 13, 6, -2, 0, None),
    ]
    for (label, Qxy, p, N, x0, ysel, f) in cases:
        t0 = time.time()
        try:
            r = check_curve(label, Qxy, p, N, x0, ysel, f)
        except Exception as e:
            print("   *** EXCEPTION: %s: %s" % (type(e).__name__, e))
            r = False
        print("   %s  (%.1f s)" % ("ok" if r else "*** FAILS ***",
                                   time.time() - t0))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E060 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
