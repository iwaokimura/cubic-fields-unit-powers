# check-phase3-bad.sage --- E062 (E048 Phase 3) GATE, part 3.
#
# Local coordinates and tiny integrals at VERY BAD points -- the points where
# r(x) = 0, which E060 and E061 refused -- both over Q_p and over the totally
# ramified extension K = Q_p(p^{1/e}) that Balakrishnan-Tuitman Remark 4.4
# forces on us.  Eight checks:
#
#   over Q_p, at the very bad point itself:
#   (1) The local expansion solves the curve, and e_P is read off it rather
#       than assumed: e_P = ord_t(x(t) - x(P)).  Proposition 3.2's two cases
#       are both exercised by the case list below (e_P = 1 and e_P = 2).
#   (2) FUNDAMENTAL THEOREM OF CALCULUS (Theorem 3.1(4)) in the bad disk.
#   (3) ADDITIVITY (Theorem 3.1(2)) in the bad disk.
#   (4) NO RESIDUE: the coefficient of t^{-1} in each basis form vanishes.
#       This is what makes the form "of the second kind", the hypothesis
#       Algorithm 3.4 rests on, and at a very bad point the series really does
#       have a pole -- so unlike at a good point, the check has content.
#   (5) AGREEMENT WITH SAGE at a Weierstrass point (hyperelliptic only).
#       NOTE ON WHAT THIS CALIBRATES: Sage's Coleman integrals from a
#       Weierstrass point use the odd-differential shortcut
#       int_W^P = (1/2) int_{iota P}^P, which returns the same value for every
#       Weierstrass point W; that route could not detect a confusion between
#       two very bad points.  The TINY integrals compared here are computed by
#       Sage from its own local coordinates at W, so they do depend on W.
#
#   over K = Q_p(p^{1/e}), e = p e_P + 1:
#   (6) The expansion still solves the curve, the pushed-out point P' lies on
#       it, and -- the point of the whole exercise -- P' satisfies Proposition
#       4.3's convergence condition ord_p(r(x)) < 1/p, which the very bad point
#       itself fails.  That is what licenses Algorithm 3.12.
#   (6b) NEGATIVE CONTROL: at t = pi^2 the condition fails (Remark 4.4's bound
#       is sharp enough to bite), so the guard in radic.evaluate must fire.
#   (7) FUNDAMENTAL THEOREM OF CALCULUS from P to P', across the extension.
#   (8) ADDITIVITY from P to P' to P''.
#
# Agreement is required to Proposition 4.1's certified precision, printed in
# every case, never to an invented tolerance.
#
# Run: sage check-phase3-bad.sage

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


def vp(a, e):
    """p-adic valuation over a ring with ramification index e."""
    if a == 0:
        return infinity
    return QQ(a.valuation()) / e


def check_bad(label, Qxy, p, N, x0, y0, sage_f=None):
    print("-" * 72)
    print("%s   p = %d, N = %d,  very bad point (x,y) = (%s, %s)"
          % (label, p, N, x0, y0))
    sys.stdout.flush()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    Kp = Qp(p, prec=N, type='floating-point')
    RR = RAdicRing(C, p, N, base=Kp)
    basis = H.H1X_basis()[0]
    forms = [form_from_Ecoords(RR, H, v) for v in basis]
    ok = True

    P = CurvePoint(RR, Kp(x0), y=Kp(y0))
    if not (P.on_curve() and P.is_very_bad()):
        print("   *** (%s,%s) is not a very bad point of the curve: gate "
              "setup FAILS (on curve: %s, very bad: %s)"
              % (x0, y0, P.on_curve(), P.is_very_bad()))
        return False

    # ------------------------------------------------------------ over Q_p
    TI = TinyIntegrals(RR)
    exp = TI.expansion_at(P)
    eP = ZZ(1) if exp.x_is_coordinate else ZZ((exp.xt - exp.xt[0]).valuation())
    res = exp.residual()
    Q1 = exp.point_at(Kp(p))
    Q2 = exp.point_at(Kp(p)**2)
    good1 = (res >= N) and Q1.on_curve() and Q2.on_curve() \
        and P.same_disk(Q1) and P.same_disk(Q2)
    print("   (1) t-prec %d, local coord %s, e_P = %d, residual = %s (>= %d): "
          "%s;  rebuilt points on curve: %s, %s"
          % (TI.tprec, "x - x(P)" if exp.x_is_coordinate else "y - y(P)",
             eP, res, N, res >= N, Q1.on_curve(), Q2.on_curve()))
    ok = ok and good1
    sys.stdout.flush()

    dM = H.d_matrix()
    nfail, ntest = 0, 0
    for col, (i, d) in enumerate(H.B_basis):
        coeffs = form_from_Ecoords(RR, H, dM.column(col))
        lhs = TI.tiny_integral(coeffs, P, Q1)
        rhs = Q1.x**d * Q1.y**i - P.x**d * P.y**i
        ntest += 1
        if not RR._coeff_is_zero(lhs - rhs):
            nfail += 1
    print("   (2) int d(x^d y^i) = f(Q) - f(P) in the bad disk: %d/%d ok"
          % (ntest - nfail, ntest))
    ok = ok and (nfail == 0)

    a = TI.tiny_integrals_on_basis(forms, P, Q1)
    b = TI.tiny_integrals_on_basis(forms, Q1, Q2, at=P)
    c = TI.tiny_integrals_on_basis(forms, P, Q2)
    add_ok = all(RR._coeff_is_zero(a[k] + b[k] - c[k]) for k in range(len(a)))
    print("   (3) additivity in the bad disk: %s   [Prop 4.1 precision p^%s]"
          % (add_ok, TI.last_precision))
    ok = ok and add_ok

    poles, dpoles, res_ok = [], [], True
    census = [(forms, poles)]
    census.append(([form_from_Ecoords(RR, H, dM.column(c))
                    for c in range(len(H.B_basis))], dpoles))
    for cfs, acc in census:
        for cf in cfs:
            g = exp.series_of_form(cf)
            acc.append(-min(0, g.valuation()))
            if g[-1] != 0 and vp(g[-1], 1) < N - 1:
                res_ok = False
    print("   (4) pole orders k: basis of H^1 %s, exact forms d(x^d y^i) %s;  "
          "residues all zero: %s" % (poles, dpoles, res_ok))
    ok = ok and res_ok
    sys.stdout.flush()

    if sage_f is not None:
        HCp = HyperellipticCurve(sage_f).change_ring(Qp(p, N))
        Ws = HCp(Qp(p, N)(P.x), Qp(p, N)(P.y))
        Qs = HCp(Qp(p, N)(Q1.x), Qp(p, N)(Q1.y))
        sv = HCp.tiny_integrals_on_basis(Ws, Qs)
        vals = []
        for k in range(len(sv)):
            d = Kp(2 * sv[k]) - a[k]
            vals.append(d.valuation() if d != 0 else N)
        m = min(vals) >= N - 1
        print("   (5) vs Sage tiny_integrals_on_basis from W (x2): agree to "
              "p^%s (need p^%s) %s   [Sage's own local coordinates at W, so "
              "this check does depend on W]" % (min(vals), N - 1,
                                                "ok" if m else "*** NO ***"))
        ok = ok and m
    else:
        print("   (5) no Sage comparison: %s"
              % ("non-hyperelliptic: no implementation anywhere but this one"))
    sys.stdout.flush()

    # -------------------------------------------------- over K = Q_p(p^{1/e})
    e = ZZ(p) * eP + 1
    K0 = Qp(p, N)
    Rz = PolynomialRing(K0, 'z')
    z = Rz.gen()
    K = K0.ext(z**e - p, names='pi')
    pi = K.gen()
    TIK = TinyIntegrals(RR, ring=K)
    t0 = time.time()
    expK = TIK.expansion_at(P.change_ring(K))
    resK = expK.residual()
    P1 = expK.point_at(pi)
    P2 = expK.point_at(pi**2)
    conv = vp(P1.rval, e) < QQ(1) / p
    good6 = (resK >= N) and P1.on_curve() and P2.on_curve() and conv
    print("   (6) K = Q_p(p^{1/%d}) (e > p e_P = %d), t-prec %d, residual = %s;"
          " P' on curve: %s;  ord_p r(x(P')) = %s < 1/p = %s: %s   (%.1f s)"
          % (e, p * eP, TIK.tprec, resK, P1.on_curve(), vp(P1.rval, e),
             QQ(1) / p, conv, time.time() - t0))
    if not conv:
        print("       *** P' is NOT far enough out: Remark 4.4 violated")
    ok = ok and good6
    sys.stdout.flush()

    # (6b) NEGATIVE CONTROL.  P'' = point at t = pi^2 is deeper in the disk,
    # and Remark 4.4's bound is sharp enough that it fails the convergence
    # condition.  The guard in radic.evaluate must therefore FIRE there: a
    # check that our refusals refuse, not only that our computations compute.
    # (Prop 4.1 needs no such condition, which is why P'' is still a legitimate
    # endpoint for the tiny integrals of check (8) below.)
    conv2 = vp(P2.rval, e) < QQ(1) / p
    guard = None
    try:
        RR.evaluate(RR.normalize({1: RR.Ry.one()}), P2.x, P2.y, ring=K)
        guard = False
    except ArithmeticError:
        guard = True
    good6b = (guard != conv2)
    print("   (6b) at t = pi^2: ord_p r(x) = %s, f_i converge: %s; "
          "evaluate() refuses: %s -- guard and criterion agree: %s"
          % (vp(P2.rval, e), conv2, guard, good6b))
    ok = ok and good6b
    sys.stdout.flush()

    nfail, ntest = 0, 0
    for col, (i, d) in enumerate(H.B_basis):
        coeffs = form_from_Ecoords(RR, H, dM.column(col))
        lhs = TIK.tiny_integral(coeffs, P.change_ring(K), P1)
        rhs = P1.x**d * P1.y**i - K(P.x)**d * K(P.y)**i
        ntest += 1
        if vp(lhs - rhs, e) < TIK.last_precision:
            nfail += 1
    print("   (7) int d(x^d y^i) = f(P') - f(P) over K: %d/%d ok"
          % (ntest - nfail, ntest))
    ok = ok and (nfail == 0)
    sys.stdout.flush()

    aK = TIK.tiny_integrals_on_basis(forms, P.change_ring(K), P1)
    bK = TIK.tiny_integrals_on_basis(forms, P1, P2, at=P.change_ring(K))
    cK = TIK.tiny_integrals_on_basis(forms, P.change_ring(K), P2)
    prec = TIK.last_precision
    vals = [vp(aK[k] + bK[k] - cK[k], e) for k in range(len(aK))]
    add_ok = min(vals) >= prec
    print("   (8) additivity over K: agrees to p^%s (Prop 4.1 gives p^%s) %s"
          % (min(vals), prec, "ok" if add_ok else "*** NO ***"))
    ok = ok and add_ok
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase3-bad.sage --- E062 gate "
          "(BT Prop 3.2, Alg 3.4, Rmk 4.4) ===")
    Rx = PolynomialRing(QQ, 'x')       # name it 'x': Sage's own frobenius
    X = Rx.gen()                       # builds x^p in a ring it names itself
    allok = True
    cases = [
        # (label, Q, p, N, x0, y0, sage model)
        # e_P = 2: a Weierstrass point of a hyperelliptic curve
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 11, 8, 1, 0, X**5 - 1),
        ("y^2 = x^7-1", y**2 - (x**7 - 1), 11, 6, 1, 0, X**7 - 1),
        # e_P = 1 at a very bad point: C_4 over t = 0 has the two points
        # (0, +- sqrt 6) besides (0,0), and 6 is a square in Q_5
        ("C_4 at (0, sqrt 6), e_P = 1",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 5, 6, 0, None, None),
        # e_P = 2, the point the whole port is for
        ("C_4 at (0,0)", y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 7, 6, 0, 0, None),
        ("C_4 at (0,0)", y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 11, 6, 0, 0, None),
    ]
    for (label, Qxy, p, N, x0, y0, f) in cases:
        if y0 is None:                 # the sqrt(6) case, resolved in Q_p
            y0 = Qp(p, N)(6).sqrt()
        t0 = time.time()
        try:
            r = check_bad(label, Qxy, p, N, x0, y0, f)
        except Exception as ex:
            print("   *** EXCEPTION: %s: %s" % (type(ex).__name__, ex))
            r = False
        print("   %s  (%.1f s)" % ("ok" if r else "*** FAILS ***",
                                   time.time() - t0))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E062 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
