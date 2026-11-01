# check-phase3-general.sage --- E062 (E048 Phase 3) GATE, part 4.
#
# Balakrishnan-Tuitman Algorithm 3.12: Coleman integrals with an endpoint in a
# BAD residue disk, via replacement points over Q_p(p^{1/e}), e > p e_P.  This
# is the last piece Phase 3 was missing, and the only one C_4's rational point
# (0,0) needs.
#
#   (1) THE CHECK THAT CANNOT FAIL THE SAME WAY -- the one that matters.
#       Inside the bad disk of the very bad point B, take two points P', Q'
#       over K = Q_p(p^{1/e}) at t = pi and t = 2 pi, and a point R of the disk
#       over Q_p.  Then
#           int_B^{P'} + int_{P'}^{Q'} + int_{Q'}^R   must equal   int_B^R,
#       where the middle term runs ALGORITHM 3.7 -- Frobenius, the f_i, the
#       linear system, all of it over the ramified extension -- while the right
#       hand side is a single tiny integral, Algorithm 3.4, which uses none of
#       those (BT Remark 3.5).  The outer tiny corrections do not cancel here,
#       because P' and Q' are DIFFERENT points; that is the whole design.
#       (E061's lesson, applied: additivity among integrals computed the same
#       way is not evidence.  Check (4) below is of that weaker kind and is
#       reported as such.)
#   (2) AGREEMENT WITH SAGE from a Weierstrass point (hyperelliptic only).
#       Sage reaches int_W^P by the odd-differential shortcut
#       int_W^P = (1/2) int_{iota P}^P and never builds a ramified extension,
#       so it shares no step with Algorithm 3.12.  Its blind spot: that
#       shortcut returns the same value for every Weierstrass point W, so it
#       could not detect a confusion between two very bad points.  (1) could.
#  (2b) THE ANSWER MUST BE A Q_p NUMBER.  Both endpoints are Q_p-rational, so
#       int_B^P lies in Q_p -- although Algorithm 3.12 reaches it only through
#       a degree e ramified extension.  The components along pi,...,pi^{e-1}
#       must therefore vanish.  On C_4 this is the ONLY independent check there
#       is, Sage having no Coleman integration for non-hyperelliptic curves.
#   (3) THE PRECISION MODEL, TESTED AS A PREDICTION.  Proposition 4.6 says the
#       computed f_i(P') are correct only to min_k{pi(k) - k eps} with
#       eps = ord_p r(x(P')) = e_P/e.  With e = p e_P + 1 -- the smallest
#       Remark 4.4 allows -- eps is as large as possible and the loss is
#       largest.  So we run the SAME integral at a larger e and require the
#       agreement with Sage to improve, and to track the predicted bound in
#       both runs.  A precision model that is merely asserted is worth nothing;
#       this one has to forecast the second run from the first.
#   (4) additivity across disks, int_B^P + int_P^Q = int_B^Q: reported, but it
#       is the WEAK check -- the tiny corrections at B are identical in the two
#       Algorithm 3.12 runs and cancel, so it reduces to additivity of
#       Algorithm 3.7, which E061 already established.
#
# Run: sage check-phase3-general.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.points import CurvePoint
from padic.integrals import TinyIntegrals, ColemanIntegrals, prop46_precision
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def vp(a, e):
    if a == 0:
        return infinity
    return QQ(a.valuation()) / e


def qp_parts(a, e):
    """An element of K = Q_p(p^{1/e}) split as (its Q_p part, the valuation of
    everything else).

    Both endpoints of the integrals below are Q_p-rational, so the Coleman
    integral between them IS a Q_p number -- even though Algorithm 3.12 reaches
    it through a degree e ramified extension.  The components along
    pi, ..., pi^{e-1} therefore have to vanish, and how far they do is a check
    on the whole route that needs no external implementation at all.  It is the
    only independent check available on C_4, where Sage has nothing to compare.
    """
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    off = infinity
    for i in range(1, len(c)):
        if c[i] != 0:
            # THE WEIGHT MATTERS: the coefficient c_i sits on pi^i, so its
            # contribution to the size of the off-Q_p part is
            # ord_p(c_i) + i/e, not ord_p(c_i).  Dropping the i/e reads a
            # perfectly small tail as a large one -- which is how this check
            # first went red while the Sage comparison beside it passed.
            off = min(off, QQ(c[i].valuation()) + QQ(i) / e)
    return (c[0] if c else 0), off


def good_points(FM, Qxy, how_many, prefer=()):
    """Good Q_p-rational points in distinct residue disks."""
    K = FM.base
    Ry = PolynomialRing(K, 'Y')
    Yv = Ry.gen()
    out = []
    for c in list(prefer) + list(range(-8, 40)):
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


def one(label, Qxy, p, N, x0, y0, sage_f=None, prefer=()):
    print("-" * 72)
    print("%s   p = %d, N = %d,  bad endpoint (%s, %s)" % (label, p, N, x0, y0))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    FM = FrobeniusMatrix(C, H, p, N)
    FM.compute(primitives=True)
    cert = FM.certified_precision()[0]
    CI = ColemanIntegrals(FM)
    RR = FM.RR
    ok = True

    B = CurvePoint(RR, FM.base(x0), y=FM.base(y0))
    if not (B.on_curve() and B.is_very_bad()):
        print("   *** (%s,%s) is not a very bad point: gate setup FAILS" % (x0, y0))
        return False
    pts = good_points(FM, Qxy, 2, prefer=prefer)
    if len(pts) < 2:
        print("   *** fewer than 2 good points found: gate setup FAILS")
        return False
    P, Q = pts[0], pts[1]
    eP = CI.ramification_at(B)
    print("   B = %s   (very bad, e_P = %d)" % (B, eP))
    print("   P = %s\n   Q = %s" % (P, Q))
    sys.stdout.flush()

    # ---- (1) inside the bad disk: Algorithm 3.7 over K against Algorithm 3.4
    t1 = time.time()
    e = ZZ(p) * eP + 1
    K = CI.extension(e)
    pi = K.gen()
    tinyQp = TinyIntegrals(RR)
    tinyK = TinyIntegrals(RR, ring=K)
    expQp = tinyQp.expansion_at(B)
    Rq = expQp.point_at(FM.base(p))              # a Q_p point of the bad disk
    expK = tinyK.expansion_at(B.change_ring(K))
    P1 = expK.point_at(pi)
    P2 = expK.point_at(2 * pi)
    BK, RK = B.change_ring(K), Rq.change_ring(K)
    lhs = tinyK.tiny_integrals_on_basis(CI.forms, BK, P1)
    mid = CI.coleman_integrals_on_basis(P1, P2, at_P=BK, at_Q=BK)
    bound = CI.certified_precision(P1, P2)
    lhs2 = tinyK.tiny_integrals_on_basis(CI.forms, P2, RK, at=BK)
    rhs = tinyK.tiny_integrals_on_basis(CI.forms, BK, RK)
    vals = [vp(lhs[i] + mid[i] + lhs2[i] - rhs[i], e) for i in range(len(rhs))]
    m1 = min(vals) >= bound
    print("   (1) Alg 3.12 route vs the single tiny integral, inside the bad "
          "disk: agree to p^%s (need p^%s) %s   (%.1f s)"
          % (min(vals), bound, "ok" if m1 else "*** NO ***", time.time() - t1))
    print("       bound = min(chi %s, Prop 4.1 %s, Prop 4.6 %s at eps = %s)"
          % (cert, CI.last_tiny.last_precision, CI.value_precision_at(P1),
             P1.vp(P1.rval)))
    ok = ok and m1
    sys.stdout.flush()

    # ---- (2),(3) Sage, at two different e, as a test of the precision model
    t1 = time.time()
    BP = CI.coleman_integrals_general(B, P)
    tBP = time.time() - t1
    predicted = [CI.certified_precision(*CI.last_eval_points)]
    observed = []
    if sage_f is not None:
        HCp = HyperellipticCurve(sage_f).change_ring(Qp(p, N))
        Ws = HCp(Qp(p, N)(B.x), Qp(p, N)(B.y))
        Ps = HCp(Qp(p, N)(P.x), Qp(p, N)(P.y))
        sv = HCp.coleman_integrals_on_basis(Ws, Ps)
        observed.append(min(vp(K(2 * sv[i]) - BP[i], e) for i in range(len(sv))))
        m2 = observed[0] >= predicted[0]
        print("   (2) vs Sage coleman_integrals_on_basis from W (x2), "
              "e = %d: agrees to p^%s (Prop 4.5/4.6 + 4.1 + chi give p^%s) %s"
              % (e, observed[0], predicted[0], "ok" if m2 else "*** NO ***"))
        ok = ok and m2

    else:
        print("   (2) no Sage comparison: non-hyperelliptic, and Sage has no "
              "Coleman integration there at all")

    # (2b) the answer is a Q_p number, computed through a ramified extension
    qp1 = [qp_parts(BP[i], e) for i in range(len(BP))]
    off1 = min(v for _, v in qp1)
    m2b = off1 >= predicted[0]
    print("   (2b) B and P are Q_p-rational, so int_B^P must lie in Q_p: the "
          "components along pi,...,pi^%d vanish to p^%s (need p^%s) %s"
          % (e - 1, off1, predicted[0], "ok" if m2b else "*** NO ***"))
    ok = ok and m2b

    # (3) the same integral at a larger e, compared inside Q_p (there is no
    # conversion between two different ramified extensions, and none is needed:
    # the answer lives in Q_p by (2b))
    e2 = 2 * ZZ(p) * eP
    BP2 = CI.coleman_integrals_general(B, P, e=e2)
    predicted.append(CI.certified_precision(*CI.last_eval_points))
    qp2 = [qp_parts(BP2[i], e2) for i in range(len(BP2))]
    agree = min((qp1[i][0] - qp2[i][0]).valuation()
                if qp1[i][0] != qp2[i][0] else infinity
                for i in range(len(qp1)))
    off2 = min(v for _, v in qp2)
    m3 = (agree >= predicted[0]) and (predicted[1] > predicted[0]) \
        and (off2 >= predicted[1])
    print("   (3) the same integral at e = %d: Q_p parts agree to p^%s (the "
          "weaker of the two bounds is p^%s); predicted precision p^%s -> p^%s;"
          " off-Q_p part now p^%s: %s"
          % (e2, agree, predicted[0], predicted[0], predicted[1], off2,
             "ok" if m3 else "*** NO ***"))
    ok = ok and m3
    sys.stdout.flush()

    # ---- (4) the weak check, reported for completeness
    BQ = CI.coleman_integrals_general(B, Q)
    PQ = CI.coleman_integrals_on_basis(P, Q)
    vals = [vp(BP[i] + K(PQ[i]) - BQ[i], e) for i in range(len(BP))]
    m4 = min(vals) >= predicted[0]
    print("   (4) [weak: the corrections at B cancel] int_B^P + int_P^Q = "
          "int_B^Q: agrees to p^%s %s" % (min(vals), "ok" if m4 else "*** NO ***"))
    ok = ok and m4

    print("   (5) cost: e = %d (t-prec %d), int_B^P %.1f s, case total %.1f s"
          % (e, tinyK.tprec, tBP, time.time() - t0))
    return ok


def main():
    print("=== check-phase3-general.sage --- E062 gate "
          "(BT Algorithm 3.12) ===")
    Rx = PolynomialRing(QQ, 'x')       # name it 'x': Sage's own frobenius
    X = Rx.gen()                       # builds x^p in a ring it names itself
    C4 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 11, 8, 1, 0, X**5 - 1, ()),
        ("y^2 = x^7-1", y**2 - (x**7 - 1), 11, 6, 1, 0, X**7 - 1, ()),
        # C_4 at its rational point (0,0), against the rational points t = 1
        # and t = -2 -- the points Phase 5's gate is about
        # N = 8, not 6: at N = 6 Proposition 4.6's bound for C_4 comes out
        # NEGATIVE (-1/5 at p = 7, -6/23 at p = 11) -- the theory certifies
        # nothing there, and a gate whose threshold is vacuous tests nothing.
        ("C_4 at (0,0) vs t = 1, -2", C4, 7, 8, 0, 0, None, (1, -2)),
        ("C_4 at (0,0) vs t = 1, -2", C4, 11, 8, 0, 0, None, (1, -2)),
    ]
    for (label, Qxy, p, N, x0, y0, f, prefer) in cases:
        t0 = time.time()
        try:
            r = one(label, Qxy, p, N, x0, y0, f, prefer)
        except Exception as ex:
            print("   *** EXCEPTION: %s: %s" % (type(ex).__name__, ex))
            r = False
        print("   %s  (%.1f s)" % ("ok" if r else "*** FAILS ***",
                                   time.time() - t0))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E063 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
