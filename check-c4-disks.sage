# check-c4-disks.sage --- E080: the bad residue disks of C_4 at p = 13.
#
# Phase 4 reproduced [BDM+19] on X_s(13) without ever meeting a bad residue
# disk: r mod 17 has the single root x = 1, and every disk of U_1 turned out to
# be good.  C_4 will not be so kind -- (0,0) is a rational point and r(0) = 0 --
# so before Phase 5 is planned we measure exactly how unkind it is.  This gate
# is a MEASUREMENT: no new mathematics is implemented, and every number below
# is meant to be read as an input to the plan.
#
# SOURCES, transcribed.
#   [Tui16] Def. 2.10, Rmk 2.12.  A point is "very bad" if r(x) = 0 or x = inf;
#           a residue disk, and every point of it, is "bad" if it contains a
#           very bad point.
#   [BT17]  Prop. 3.2.  At a good or very bad point the local coordinate is
#           t = x - x(P) when e_P = 1, and t = b^0_i - b^0_i(P) otherwise.
#   [BDM+19] (Annals 189) Section 5.5, "A
#           trick for dealing with leftover residue disks":
#             "The process described above gives a way of computing a finite
#              set containing X(Q) cap ]U[.  This leaves the residue disks
#              where the Frobenius lift is not defined, or where the basis
#              differentials have poles.  To deal with those residue disks, we
#              could pass to a different choice of basis and Frobenius lift
#              until the whole of X is covered.  An alternative approach ... is
#              to change the base point."
#           Lemma 5.7 then computes the Frobenius structure at a new base point
#           b' -- ASSUMING b' "lies in a residue disk where none of our basis
#           differentials have poles" -- out of beta_phi(b,b) and the single
#           integrals int_b^{b'} omega.  Section 6.5 is the first route (a
#           second chart) and Section 6.6 the second (Lemma 5.7), used there for
#           the single leftover disk of (1:1:1).
#
# WHAT IS MEASURED, AND WHAT WOULD FALSIFY THE PLAN.
#   (1) SETUP.  The chart-1 data, and the one fact that makes the census below
#       legitimate: the affine plane model of C_4 is SMOOTH (over Q, hence over
#       F_p for every p not dividing the resultant), so affine F_p-points of
#       the model and finite degree-1 places of the reduction are the same
#       thing and can be counted by brute force.
#   (2) [T] THE BAD DISK CANNOT BE AVOIDED BY CHOOSING p.  (0,0) is a rational
#       point of C_4 and r(0) = 0, so for EVERY prime the residue disk of (0,0)
#       is bad.  There is no lucky prime; the leftover-disk step of Section 5.5
#       is part of Phase 5 whatever else is decided.  Checked here as an
#       identity over Q, and then in the table over primes.
#   (3) THE CENSUS AT p = 13, BY TWO ROUTES that share no code: Sage's places
#       of degree 1 of the reduction, and brute force on the plane model plus
#       the degree-1 factors of (1/x) at infinity.  Cross-checked against
#       E059's chi_13 for C_4, whose T-coefficient gives #X(F_13).
#   (4) THE CLASSIFICATION AT p = 13.  How many disks are bad, which, and with
#       what local structure (deg, e_P, and which of Prop. 3.2's two cases).
#   (5) THE KNOWN RATIONAL POINTS.  All nine affine ones, their disks, and
#       which of them are bad.  If two of them shared a disk the T_i matrix of
#       Section 6.4.1 would be built from fewer independent points than Phase 5
#       assumes, so this is a check and not a display.
#   (6) LEMMA 5.7'S HYPOTHESIS, MEASURED.  The pole divisor of the six phase-4
#       basis differentials.  If any of them had a pole in the disk of (0,0),
#       Section 6.6's route would be closed and only a second chart would
#       remain.  THIS IS THE FALSIFIABLE ONE.
#   (7) A SECOND CHART EXISTS.  3*Q_1(y/3, x) is monic of degree 4 in y, of
#       genus 3, and its r does not vanish at the image of (0,0).  So the first
#       route of Section 5.5 is available too, as an independent cross-check on
#       whatever the second route computes.
#   (8) NEGATIVE CONTROLS.  The port must REFUSE the bad disk where it cannot
#       act: teichmuller_point at (0,0), and a local expansion at a bad but not
#       very bad point.  And the classifier must not be answering "1 bad disk"
#       by accident: at p = 5, 11, 17, 19, 23 it must return more.
#   (9) THE TABLE over the small primes, as the planning output.
#  (10) TIER 2: the one input Lemma 5.7 needs that nothing else in the port has
#       had to compute -- int_b^{b'} omega from b = (1,3) to b' = (0,0) -- run
#       at two ramification degrees, with E063's Q_p-rationality check.  Set
#       E080_SKIP_INTEGRAL=1 to skip it (the census is unaffected).
#
# Run: sage check-c4-disks.sage

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.points import CurvePoint, LocalExpansion, teichmuller_point
from padic.integrals import TinyIntegrals, ColemanIntegrals
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()

Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)          # chart 1: (x,y) = (t,w)
Q2 = y**4 - 2*(y-3)**2*x**2 + 3*x**4 - 108*y         # chart 2: (x,y) = (w,3t)

P_GATE = 13

# E059(b), for C_4: chi(T) = 1 + 7T + 27T^2 + 74T^3 + 351T^4 + 1183T^5 + 2197T^6
E059_CHI13 = [1, 7, 27, 74, 351, 1183, 2197]

# The known rational points of C_4, as (t, w).  E040/E045/E065: the four
# t-values -2, -1, -1/11, 1 each carry two rational w, and (0,0) is fixed by
# w |-> -w.  The four points at infinity are the roots of w^4-6w^2+27, which is
# irreducible over Q, so the list below is all of the known C_4(Q).
KNOWN = [(1, 3), (1, -3), (-1, 3), (-1, -3), (-2, 6), (-2, -6),
         (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11), (0, 0)]

FAIL = []


def check(cond, msg):
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def info(msg):
    print("        %s" % msg)
    sys.stdout.flush()


# --------------------------------------------------------------- reductions

def reduction(p, Qxy=Q1):
    """The function field of the reduction mod p, or None if it degenerates."""
    Fp = GF(p)
    Kf = FunctionField(Fp, 'x')
    xx = Kf.gen()
    RY = PolynomialRing(Kf, 'y')
    Y = RY.gen()
    Qff = sum(Kf(c) * xx**ZZ(e0) * Y**ZZ(e1) for (e0, e1), c in Qxy.dict().items())
    if not Qff.is_irreducible():
        return None
    L = Kf.extension(Qff, 'y')
    return L


def affine_points(p, Qxy=Q1):
    """The F_p-points of the affine plane model, by brute force.

    Legitimate as a count of finite degree-1 places because check (1) verifies
    that the affine model is smooth.
    """
    Fp = GF(p)
    Ry = PolynomialRing(Fp, 'Y')
    Yv = Ry.gen()
    out = []
    for a in Fp:
        f = Ry.zero()
        for (e0, e1), c in Qxy.dict().items():
            f += Fp(QQ(c)) * a**ZZ(e0) * Yv**ZZ(e1)
        for b, _ in f.roots():
            out.append((a, b))
    return out


def infinite_places(L):
    xx = L(L.base_field().gen())
    return [I.place() for I, _ in L.maximal_order_infinite().ideal(1/xx).factor()]


def census(p, Qxy=Q1, rpoly=None):
    """(disks, bad, detail) at p, by the fast route.

    A disk is a degree-1 place of the reduction; it is bad iff it lies over a
    root of r mod p or over x = infinity (Rmk 2.12).
    """
    L = reduction(p, Qxy)
    if L is None or L.genus() != 3:
        return None
    Fp = GF(p)
    rp = rpoly.change_ring(Fp)
    pts = affine_points(p, Qxy)
    ninf = len([P for P in infinite_places(L) if P.degree() == 1])
    bad = [pt for pt in pts if rp(pt[0]) == 0]
    return len(pts) + ninf, len(bad) + ninf, (pts, bad, ninf)


# ------------------------------------------------------------------- checks

def check_1_setup():
    print("(1) SETUP -- chart 1, and why the census may be taken by brute force")
    C = TuitmanCurve(Q1, name="C_4")
    check(C.genus == 3 and C.dx == 4, "genus 3, d_x = 4")
    check(C.degr == 8, "deg r = 8")
    fac = [(f, m) for f, m in C.r.factor()]
    info("r = %s" % C.r.factor())
    check(len(fac) == 3 and all(m == 1 for _, m in fac),
          "r is squarefree with three irreducible factors over Q")
    check(any(f.degree() == 1 and f(0) == 0 for f, _ in fac),
          "x divides r -- i.e. r(0) = 0")
    den = lcm([QQ(c).denominator() for c in C.r.list()])
    check(den == 2, "the only prime in the denominators of r is 2 (den = %s)" % den)
    # affine smoothness: (Q, Q_x, Q_y) is the unit ideal
    I = R.ideal([Q1, Q1.derivative(x), Q1.derivative(y)])
    check(I.dimension() == -1,
          "the affine plane model is smooth: (Q, Q_x, Q_y) = (1), so for every "
          "p the affine F_p-points and the finite degree-1 places agree")
    return C


def check_2_unavoidable(C):
    print("(2) [T] THE BAD DISK OF (0,0) EXISTS AT EVERY PRIME")
    check(Q1(0, 0) == 0, "(0,0) lies on C_4")
    check(C.r(0) == 0, "r(0) = 0, so (0,0) is a VERY BAD point (Rmk 2.12)")
    info("hence for every p of good reduction the disk of (0,0) is bad: no "
         "choice of p removes the leftover-disk step of [BDM+19] Section 5.5.")


def check_3_census(C):
    print("(3) THE CENSUS AT p = %d, BY TWO ROUTES" % P_GATE)
    L = reduction(P_GATE)
    t0 = time.time()
    slow = len(L.places(1))
    t_slow = time.time() - t0
    t0 = time.time()
    fast, nbad, detail = census(P_GATE, rpoly=C.r)
    t_fast = time.time() - t0
    check(slow == fast, "Sage's places(1) and brute force agree: %d disks "
          "(%.1f s vs %.1f s)" % (slow, t_slow, t_fast))
    # E059's chi: #X(F_p) = p + 1 - a_1, and chi = prod(1 - alpha_i T) so the
    # T-coefficient is -sum alpha_i.
    npts = P_GATE + 1 + E059_CHI13[1]
    check(npts == fast, "E059's chi_13 for C_4 gives #X(F_13) = 13 + 1 + %d = "
          "%d" % (E059_CHI13[1], npts))
    check(L.genus() == 3, "the reduction still has genus 3")
    return L, detail


def check_4_classify(C, H, L, detail):
    print("(4) THE CLASSIFICATION AT p = %d" % P_GATE)
    pts, bad, ninf = detail
    check(ninf == 0, "no degree-1 place at infinity (the place over x = inf has "
          "degree 4 and stays inert)")
    check(len(bad) == 1, "exactly ONE bad residue disk out of %d; the other %d "
          "are good" % (len(pts) + ninf, len(pts) + ninf - len(bad) - ninf))
    if len(bad) != 1:
        return None
    b = bad[0]
    check(b == (GF(P_GATE)(0), GF(P_GATE)(0)),
          "the bad disk is the disk of (0,0)")
    # local structure, over Q_p
    Kp = Qp(P_GATE, prec=10, type='floating-point')
    RR = FrobeniusMatrix(C, H, P_GATE, 10).RR
    B = CurvePoint(RR, RR.base(0), y=RR.base(0))
    check(B.on_curve() and B.is_very_bad(),
          "(0,0) is on the curve and is the VERY BAD point of its disk")
    check(not B.dQ_dy_is_unit(),
          "dQ/dy(0,0) = 0, so Prop. 3.2's first case does not apply")
    check(B._dQ_dx() != 0 and B.vp(B._dQ_dx()) == 0,
          "dQ/dx(0,0) = -108 is a 13-unit, so Prop. 3.2 gives t = y = w")
    # e_P read off the reduction: cheaper than the port's own route, and
    # independent of it (check (10) compares the two).
    xx = L(L.base_field().gen())
    P0 = [P for P in L.places(1)
          if xx.valuation(P) > 0 and L.gen().valuation(P) > 0]
    check(len(P0) == 1, "exactly one degree-1 place of the reduction over x = 0")
    if P0:
        e = ZZ(xx.valuation(P0[0]))
        check(e == 2, "its ramification index over x = 0 is e_P = %d" % e)
        info("Remark 4.4 then asks for e > p e_P = %d in the ramified "
             "extension; E065(c) measured the operating point e = 2 p e_P = %d."
             % (P_GATE * e, 2 * P_GATE * e))
    return B


def check_5_points(C):
    print("(5) THE KNOWN RATIONAL POINTS AT p = %d" % P_GATE)
    Fp = GF(P_GATE)
    rp = C.r.change_ring(Fp)
    red = []
    for (t, w) in KNOWN:
        check(Q1(t, w) == 0, "(%s, %s) lies on C_4" % (t, w))
        red.append((Fp(t), Fp(w)))
    check(len(set(red)) == len(red),
          "all %d known rational points lie in DISTINCT residue disks mod %d"
          % (len(red), P_GATE))
    badpts = [KNOWN[i] for i, (a, _) in enumerate(red) if rp(a) == 0]
    check(badpts == [(0, 0)],
          "exactly one of them is in a bad disk, and it is (0,0): %s" % (badpts,))
    info("reductions: %s" % ", ".join("%s->(%s,%s)" % (KNOWN[i], red[i][0], red[i][1])
                                      for i in range(len(KNOWN))))


def check_6_poles(C, H):
    print("(6) LEMMA 5.7'S HYPOTHESIS: where do the basis differentials have poles?")
    reps, _ = H.phase4_basis()
    forms = [H.differential_of(v) for v in reps]
    L, xL, yL = C.L, C.L(C.x), C.y
    finite_ok = True
    poles_at_infty = None
    for P in H.candidate_places():
        orders = [ZZ(H.pole_order(om, P)) for om in forms]
        at_inf = ZZ(xL.valuation(P)) < 0
        info("place deg %d, v(x) = %s, v(y) = %s (%s): pole orders %s"
             % (P.degree(), xL.valuation(P), yL.valuation(P),
                "over x = infinity" if at_inf else "over a zero of r", orders))
        if at_inf:
            poles_at_infty = orders
        elif max(orders) > 0:
            finite_ok = False
    check(finite_ok, "NO basis differential has a pole at any FINITE place -- "
          "in particular none has a pole in the disk of (0,0)")
    check(poles_at_infty is not None and poles_at_infty == [0, 0, 0, 3, 3, 3],
          "the only poles are order 3 at the degree-4 place over x = infinity "
          "(E064's measurement, on the phase-4 basis)")
    L13 = reduction(P_GATE)
    check(len([P for P in infinite_places(L13) if P.degree() == 1]) == 0,
          "that place carries no F_13-point, so its disk is not one of the 21")
    info("=> [BDM+19] Lemma 5.7 applies with b' = (0,0): Section 6.6's route is "
         "open for C_4's single leftover disk.")


def check_7_chart2():
    print("(7) A SECOND CHART (the first route of Section 5.5)")
    F = R.fraction_field()
    check(3 * Q1(F(y)/3, F(x)) == F(Q2),
          "Q_2(x,y) = 3 Q_1(y/3, x): chart 2 is chart 1 with base w and fibre 3t")
    C2 = TuitmanCurve(Q2, name="C_4 chart 2")
    check(C2.genus == 3 and C2.dx == 4, "chart 2 has genus 3 and d_x = 4")
    info("r_2 = %s" % C2.r.factor())
    check(C2.r(0) != 0,
          "r_2(0) = %s is nonzero: the image (0,0) of C_4's bad point is a "
          "GOOD point of chart 2" % C2.r(0))
    check(QQ(C2.r(0)).valuation(P_GATE) == 0,
          "and r_2(0) is a %d-unit, so the disk is good at p = %d too"
          % (P_GATE, P_GATE))
    c = census(P_GATE, Qxy=Q2, rpoly=C2.r)
    check(c is not None and c[0] == 21,
          "chart 2 sees the SAME 21 residue disks at p = %d -- it is the same "
          "curve, so the census is being taken of the curve and not of the "
          "model (%s)" % (P_GATE, "%d disks, %d bad" % c[:2] if c else "none"))
    info("but chart 2 is much worse overall: %d of its %d disks are bad, "
         "against 1 of 21 in chart 1.  It is only ever needed for the one "
         "disk chart 1 cannot see." % (c[1], c[0]))
    return C2


def check_8_controls(C, H):
    print("(8) NEGATIVE CONTROLS")
    RR = FrobeniusMatrix(C, H, P_GATE, 8).RR
    B = CurvePoint(RR, RR.base(0), y=RR.base(0))
    try:
        teichmuller_point(B)
        check(False, "teichmuller_point must REFUSE the bad disk")
    except ValueError:
        check(True, "teichmuller_point((0,0)) raises: the bad disk has no "
              "Teichmuller point this construction can reach")
    # a bad but not very bad point: move off (0,0) inside its disk
    tiny = TinyIntegrals(RR)
    P1 = tiny.expansion_at(B).point_at(RR.base(P_GATE))
    check(P1.is_bad() and not P1.is_very_bad(),
          "a point of the disk at t = p is bad but not very bad")
    try:
        LocalExpansion(P1, 8)
        check(False, "LocalExpansion must REFUSE a bad-not-very-bad point")
    except ValueError:
        check(True, "LocalExpansion there raises: Algorithm 3.4(1) is enforced")
    # the classifier is not vacuous
    worse = []
    for p in [5, 11, 17, 19, 23]:
        c = census(p, rpoly=C.r)
        if c is not None:
            worse.append((p, c[1]))
    check(all(n > 1 for _, n in worse),
          "at p = 5,11,17,19,23 the classifier returns MORE than one bad disk "
          "%s -- it is not answering 1 by construction" % (worse,))


def check_9_table(C):
    print("(9) THE TABLE (chart 1)")
    print("        p    disks   good    bad   bad disks (x-value of the very bad points)")
    ones = []
    for p in primes(3, 37):
        c = census(p, rpoly=C.r)
        if c is None:
            print("      %3d    -- the reduction is not a genus-3 curve --" % p)
            continue
        n, nbad, (pts, bad, ninf) = c
        xs = sorted(set(str(a) for a, _ in bad))
        print("      %3d    %5d  %5d  %5d   %s%s"
              % (p, n, n - nbad, nbad, ",".join(xs),
                 "  + %d at infinity" % ninf if ninf else ""))
        if nbad == 1:
            ones.append(p)
        check(any(str(a) == "0" for a, _ in bad),
              "p = %d: x = 0 is among the bad disks, as check (2) forces" % p)
        sys.stdout.flush()
    check(ones == [7, 13], "exactly two primes below 37 have a SINGLE bad disk: "
          "%s -- and of the two only 13 is ordinary (E065(c))" % (ones,))
    info("THE RANGE STOPS AT 37 FOR A MEASURED REASON: the good-reduction test "
         "here is Sage's genus() on the reduction, which costs 6 s at p = 29, "
         "12 s at p = 31 and 593 s at p = 37.  Nothing in the plan needs a "
         "larger range -- check (2) already covers every prime.")


def check_10_integral(C, H):
    print("(10) TIER 2: the single integral Lemma 5.7 needs, int_b^{b'} omega")
    if os.environ.get("E080_SKIP_INTEGRAL"):
        info("skipped (E080_SKIP_INTEGRAL is set)")
        return
    N = 8
    t0 = time.time()
    FM = FrobeniusMatrix(C, H, P_GATE, N)
    FM.compute(primitives=True)
    cert = FM.certified_precision()[0]
    CI = ColemanIntegrals(FM)
    RR = FM.RR
    Bp = CurvePoint(RR, RR.base(0), y=RR.base(0))          # b' = (0,0), very bad
    b = CurvePoint(RR, RR.base(1), y=RR.base(3))           # b  = (1,3), good
    check(b.is_good() and b.on_curve(), "b = (1,3) is a good point of C_4")
    eP = CI.ramification_at(Bp)
    check(eP == 2, "e_P = %d at (0,0), as the reduction said" % eP)
    out = {}
    for e in [2 * P_GATE * eP, 3 * P_GATE * eP + 1]:
        t1 = time.time()
        v = CI.coleman_integrals_general(b, Bp, e=e)
        pred = CI.certified_precision(*CI.last_eval_points)
        parts = [qp_parts(c, e) for c in v]
        off = min(w for _, w in parts)
        info("e = %-3d  %.0f s  certified p^%s  off-Q_p part p^%s"
             % (e, time.time() - t1, pred, off))
        check(off >= pred, "e = %d: b and b' are Q_p-rational, so the integral "
              "must lie in Q_p, and its pi-components vanish to p^%s (need p^%s)"
              % (e, off, pred))
        out[e] = ([c for c, _ in parts], pred)
    es = sorted(out)
    a0, p0 = out[es[0]]
    a1, p1 = out[es[1]]
    agree = min((a0[i] - a1[i]).valuation() if a0[i] != a1[i] else infinity
                for i in range(len(a0)))
    check(agree >= min(p0, p1),
          "the two ramification degrees give the same Q_p vector to p^%s "
          "(the weaker bound is p^%s)" % (agree, min(p0, p1)))
    info("int_{(1,3)}^{(0,0)} omega = %s"
         % [str(c) for c in a1])
    info("cost of check (10): %.0f s (Phi included)" % (time.time() - t0))


def vp(a, e):
    if a == 0:
        return infinity
    return QQ(a.valuation()) / e


def qp_parts(a, e):
    """E063's splitting of an element of Q_p(p^{1/e}) into (Q_p part, rest)."""
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    off = infinity
    for i in range(1, len(c)):
        if c[i] != 0:
            off = min(off, QQ(c[i].valuation()) + QQ(i) / e)
    return (c[0] if c else 0), off


def main():
    print("=== check-c4-disks.sage --- E080: C_4's bad residue disks at p = %d ==="
          % P_GATE)
    t0 = time.time()
    C = check_1_setup()
    H = Cohomology(C)
    check_2_unavoidable(C)
    L, detail = check_3_census(C)
    check_4_classify(C, H, L, detail)
    check_5_points(C)
    check_6_poles(C, H)
    check_7_chart2()
    check_8_controls(C, H)
    check_9_table(C)
    check_10_integral(C, H)
    print("=" * 72)
    print("E080 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time() - t0))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
