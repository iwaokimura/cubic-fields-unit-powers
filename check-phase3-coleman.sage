# check-phase3-coleman.sage --- E060 (E048 Phase 3) GATE, part 2.
#
# Coleman integrals between good points, Balakrishnan-Tuitman Algorithm 3.7,
# using the functions f_i of Definition 2.17 that E059's reduction now returns.
#
#   (1) Phi - I is invertible (Remark 3.8).
#   (2) THE CONSISTENCY CHECK BT THEMSELVES POINT AT (Remark 3.5): for P and Q
#       in the SAME residue disk, Algorithm 3.7 must reproduce the tiny
#       integral -- and tiny integrals use no Frobenius, no f_i, no Phi.  So
#       this tests f_i and Phi against a route that shares none of them.
#   (3) ADDITIVITY ACROSS DISKS (Theorem 3.1(2)): int_P^Q + int_Q^R = int_P^R
#       with the three points in three different residue disks.  Each of the
#       three integrals runs the whole algorithm separately.
#   (4) AGREEMENT WITH SAGE on hyperelliptic curves, across disks: ours must be
#       twice Sage's coleman_integrals_on_basis, our x^d y dx/r being
#       x^d dx/y = 2 (x^d dx/(2y)).
#
# The required agreement is the precision to which Phi itself is certified by
# Propositions 3.7 and 3.8 (E059), not an invented tolerance; the observed
# agreement is printed in every case.
#
# Run: sage check-phase3-coleman.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.points import CurvePoint
from padic.integrals import TinyIntegrals, ColemanIntegrals
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def good_points(FM, Qxy, how_many, avoid=None):
    """Good Q_p-rational points in distinct residue disks."""
    K = FM.base
    Ry = PolynomialRing(K, 'Y')
    Yv = Ry.gen()
    out, seen = [], []
    for c in list(range(-8, 40)):
        q0 = Ry.zero()
        for (ex, ey), cc in Qxy.dict().items():
            q0 += FM.RR._coerce_QQ(cc) * K(c)**ZZ(ex) * Yv**ZZ(ey)
        for r, _ in q0.roots():
            P = CurvePoint(FM.RR, K(c), y=r)
            if not (P.is_good() and P.on_curve()):
                continue
            if any(P.same_disk(S) for S in out):
                continue
            out.append(P)
            break
        if len(out) >= how_many:
            break
    return out


def one(label, Qxy, p, N, sage_f=None, no_sage_reason=None):
    print("-" * 72)
    print("%s   p = %d, N = %d" % (label, p, N))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    FM = FrobeniusMatrix(C, H, p, N)
    FM.compute(primitives=True)
    cert = FM.certified_precision()[0]
    ok = True

    # (1)
    CI = ColemanIntegrals(FM)      # raises if Phi - I is singular
    print("   (1) Phi - I invertible: True; chi certified to p^%s" % cert)
    print("       f_i r-adic supports: %s" % [FM.RR.J_range(f) for f in FM.f])
    sys.stdout.flush()

    pts = good_points(FM, Qxy, 3)
    if len(pts) < 3:
        print("   *** fewer than 3 good points found: gate setup FAILS")
        return False
    P, Q, S = pts[0], pts[1], pts[2]
    print("   points: %s | %s | %s" % (P, Q, S))
    sys.stdout.flush()

    # (2) same-disk consistency against the Frobenius-free tiny integral
    TI = CI.tiny
    exp = TI.expansion_at(P)
    Pd = exp.point_at(FM.base(p))
    cole = CI.coleman_integrals_on_basis(P, Pd)
    tinyv = TI.tiny_integrals_on_basis(CI.forms, P, Pd)
    vals = [(cole[i] - tinyv[i]).valuation() if cole[i] != tinyv[i] else N
            for i in range(len(cole))]
    m2 = min(vals) >= cert
    print("   (2) Algorithm 3.7 vs tiny integral in one disk: agree to p^%s "
          "(need p^%s) %s" % (min(vals), cert, "ok" if m2 else "*** NO ***"))
    ok = ok and m2
    sys.stdout.flush()

    # (3) additivity across three disks
    a = CI.coleman_integrals_on_basis(P, Q)
    b = CI.coleman_integrals_on_basis(Q, S)
    c = CI.coleman_integrals_on_basis(P, S)
    vals = [(a[i] + b[i] - c[i]).valuation() if a[i] + b[i] != c[i] else N
            for i in range(len(a))]
    m3 = min(vals) >= cert
    print("   (3) additivity across disks: agrees to p^%s (need p^%s) %s"
          % (min(vals), cert, "ok" if m3 else "*** NO ***"))
    ok = ok and m3
    sys.stdout.flush()

    # (4) Sage
    if sage_f is not None:
        HCp = HyperellipticCurve(sage_f).change_ring(Qp(p, N))
        Ps = HCp([Qp(p, N)(P.x), Qp(p, N)(P.y), Qp(p, N)(1)])
        Qs = HCp([Qp(p, N)(Q.x), Qp(p, N)(Q.y), Qp(p, N)(1)])
        sv = HCp.coleman_integrals_on_basis(Ps, Qs)
        vals = []
        for i in range(len(sv)):
            d = FM.base(2 * sv[i]) - a[i]
            vals.append(d.valuation() if d != 0 else N)
        m4 = min(vals) >= cert
        print("   (4) vs Sage coleman_integrals_on_basis (x2): agree to p^%s "
              "(need p^%s) %s" % (min(vals), cert, "ok" if m4 else "*** NO ***"))
        ok = ok and m4
    else:
        print("   (4) no Sage comparison: %s"
              % (no_sage_reason or "no hyperelliptic model"))
    print("   %s  (%.1f s)" % ("ok" if ok else "*** FAILS ***", time.time() - t0))
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase3-coleman.sage --- E060 gate (BT Algorithm 3.7) ===")
    Rx = PolynomialRing(QQ, 'x')
    X = Rx.gen()
    allok = True
    # Sage's coleman_integrals_on_basis works on ODD degree models only: on
    # y^2 = x^6-x-1 it raises inside Sage itself.  That is a limitation of the
    # comparison, not a result about this port -- which computes the integrals
    # on that curve perfectly well, as checks (2) and (3) show.  It is declared
    # here rather than caught, so that no case can fail quietly.
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 11, 8, X**5 - 1, None),
        ("y^2 = x^7-1", y**2 - (x**7 - 1), 11, 8, X**7 - 1, None),
        ("y^2 = x^6-x-1", y**2 - (x**6 - x - 1), 7, 8, None,
         "Sage's Coleman integration requires an odd-degree model"),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 11, 8, None,
         "non-hyperelliptic: no implementation anywhere but this one"),
    ]
    for (label, Qxy, p, N, f, why) in cases:
        try:
            r = one(label, Qxy, p, N, f, why)
        except Exception as e:
            print("   *** EXCEPTION: %s: %s" % (type(e).__name__, e))
            r = False
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E061 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
