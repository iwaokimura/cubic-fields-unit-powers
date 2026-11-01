# check-c4-iterated.sage --- E091: the global ITERATED Coleman integral into
# C_4's bad disk, and the prediction E090 turned the missing check into.
#
# Run: sage check-c4-iterated.sage          (E091_N, E091_E override N and e)
#
# WHAT E090 LEFT.  E090 showed that the quadratic Chabauty equation at C_4's
# bad point (0,0) costs exactly one number: with u := int_b^{(0,0)} omega
# (Algorithm 3.12, available) the transport law of (24) gives
#     alpha_phi^b(0,0) = u ,   beta_phi^b(0,0)^T = beta_phi(b,b)^T + u^T Z ,
# and everything else in (14) is computable from u, so that
#     theta_b(0,0) = gamma_phi^b(0,0) + K,     K computable from u alone,
#     gamma_phi^b(0,0) = int_b^{(0,0)} ( eta + omega^T Z int omega ) ,
# a GLOBAL ITERATED Coleman integral into a bad disk.  The port had tiny
# iterated integrals (inside a disk, E073) and single global ones (Algorithm
# 3.12, E062); it did not have this one.  E090 predicted its value from the
# other two equations of the system,
#     theta_b(0,0) = theta(-1,3) - theta(-2,6)/3 ,
# a relation with no unknown in it -- not even h_3's constant -- resting on
# E084's h_3 table, E088's measured vanishings, E089's delta-form of the Prym
# height, E090's exact computation u_0((0,0)) = 0 in E(Q), and the assumption
# h_2 = 0 at b, (-1,3), (-2,6) and (0,0).  THAT ASSUMPTION HAS NEVER BEEN
# TESTED; this gate is the test.
#
# WHAT IS NEW HERE, DERIVED BEFORE ANY CODE.  (23) evaluates the Frobenius
# structure at the Teichmuller point of a residue disk, and a BAD disk has none
# the port can reach: teichmuller_point refuses a bad point, and f, g, h do not
# converge at the very bad point in any case.  So (23) is replaced by the law it
# is a special case of.  The gauge equation of (22) says exactly that G
# intertwines the parallel transports of d + Lambda and of d + Lambda_phi:
#     G(x) I(x,x') = I(phi x, phi x') G(x') ,
# whence R(x) := (M(phi x) D)^{-1} G(x) M(x), D = diag(1,F,p), is constant on
# the connected wide open ord_p(r(x)) < 1/p where G converges -- which contains
# ]U[ TOGETHER WITH the outer annuli of the bad disks, and contains b.  At b,
# R(b) = 1 is (23) itself.  So on all of it
#     G(x) M(x) = M(phi x) D ,
# and with Itilde := I(phi x, x) -- a TINY transport, phi preserving residue
# disks -- the blocks read
#     alpha = (I-F)^{-1} (f - utilde) ,
#     beta^T = (g^T - utilde^T Z F)(F-p)^{-1} ,
#     gamma = (h + g^T alpha - vtilde - utilde^T Z alpha)/(1-p) ,
# reducing to (23) when utilde = vtilde = 0.  vtilde is a tiny ITERATED
# integral, which transport_series already computes; that is the whole reason
# this route reaches a bad disk.  padic/frobstruct.frob_triv_general.
#
# The (2,1) line is Algorithm 3.7 of [BT] with P = b, whose extra term
# int_b^{F_p(b)} omega is absent only because f(b) = 0 AND b is phi-fixed.
# Check (1) verifies the latter rather than inheriting it.
#
# THE CHECKS.
#   (1) b = (1,3) is a Frobenius fixed point (x = 1 is its own Teichmuller
#       lift), which is what normalises the law above.
#   (2) THE LAW ITSELF, at four good rational points: frob_triv_general (which
#       never forms a Teichmuller point) against frob_triv (which does).  Two
#       negative controls: the sign of vtilde, and the cross term utilde^T Z
#       alpha, each of which must break it.
#   (3) THE SAME CODE PATH ON A GOOD DISK, over Q_p(p^{1/e}): M at a rational
#       point recovered from a point at t = pi by the general law and the
#       transport back.  This is everything the bad-disk run does except the
#       very bad expansion point and Proposition 4.6's loss in f, g, h.
#   (4) THE BAD DISK, checked against Algorithm 3.12: alpha((0,0)) against
#       int_b^{(0,0)} omega, and beta((0,0)) against beta_b + u^T Z.  These
#       share no step with the transport route.
#   (5) t-ADIC STABILITY: the whole bad-disk computation again at a larger
#       t-adic truncation.  The iterated integral's truncation error is NOT
#       covered by Proposition 4.1 (which bounds single tiny integrals), so it
#       is measured rather than quoted.
#   (6) THE MEASUREMENT (H6): theta_b(0,0) against E090's prediction, with the
#       certificate of Propositions 3.7/3.8 (Phi), 4.1 (tiny) and 4.6 (the
#       values of f, g, h at the pushed-out point) printed beside it.  A
#       residual BELOW the certificate refutes one of the premises listed above
#       -- h_2 = 0 being the only one not independently established.
#   (7) theta(sigma b) = 0, which the same premises force (zero elliptic class,
#       zero Prym contribution, j_Gamma = 0), as a control on the reading of
#       the system that (6) is testing.
#   (8) WHAT THE RESIDUAL IS, if there is one: [BDMTV2023] Theorem 3.2 makes
#       every h_ell a RATIONAL multiple of log_p(ell), so residual/log_13(2)
#       and residual/log_13(3) are the two candidates for a rational, and the
#       gate prints the residue of each modulo the certified and the measured
#       precision.  Diagnostic, not a gate: an identification is [E] and means
#       nothing until it repeats at another (N, e).
#   (9) A SECOND HYPOTHESIS (H9), tested because it would have given an
#       independent high-precision route: that gamma_phi - gamma_Fil, being the
#       (3,1) slot of a trivialisation and so invariant under a change of basis
#       of V_dR, transforms between E082's two charts by the scale lambda =
#       351/4 alone.  Tested at a GOOD point, where both charts compute
#       directly and neither uses anything E091 added.
#
# check() is CORRECTNESS -- a failure means the computation is broken.
# measure() is a HYPOTHESIS the experiment exists to test -- a refutation is
# the result.  The verdict line reports the two separately.

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion
from padic.integrals import ColemanIntegrals, tprec_for, prop46_precision

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13
N = ZZ(os.environ.get("E091_N", 8))
EE = ZZ(os.environ.get("E091_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
GOOD = [SIGB, (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)]

FAIL = []
MEASURED = []


def check(cond, msg):
    """A CORRECTNESS check: the gate is RED if one of these fails."""
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def measure(cond, name, msg):
    """A HYPOTHESIS the experiment exists to test.

    Kept apart from check() on purpose: a refuted hypothesis is the result of
    the experiment, not a broken computation, and folding the two together
    would make the verdict line unreadable in exactly the case that matters.
    """
    ok = bool(cond)
    print("   %s %s: %s" % ("[HOLDS ]" if ok else "[REFUTED]", name, msg))
    MEASURED.append((name, ok))
    sys.stdout.flush()
    return ok


def info(msg):
    print("        %s" % msg)
    sys.stdout.flush()


def main():
    print("=== check-c4-iterated.sage --- E091: the iterated Coleman integral "
          "into ](0,0)[ ===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    n, g = 2 * ZZ(C.genus), ZZ(C.genus)
    t0 = time.time()
    FS = FrobeniusStructure(C, H, P_GATE, N, BASE, sx=1, sy=-1)
    cc, mu, resv = FS.solve()
    K0, cert = FS.K, FS.cert
    LH = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    info("(22) solved and the Hodge side built: N = %d, certified p^%d, "
         "residual p^%s  (%.0f s)" % (N, cert, resv, time.time() - t0))

    def vz(a, e=1):
        return QQ(N + 4) if a == 0 else QQ(a.valuation()) / e

    def qp_floor(a, e):
        """How far a computed-over-K quantity still lies in Q_p.

        b and (0,0) are rational points and Z, eta, F, the Hodge side are all
        over Q, so every number this gate compares is a Q_p-number that the
        computation merely routes through K = Q_p(p^{1/e}).  The valuation of
        the first pi-component NOT in Q_p is therefore pure accumulated error,
        and it is a direct measurement of it -- an optimistic one (an error can
        land in Q_p by accident) but one that owes nothing to Proposition 4.6.
        """
        if e == 1 or a == 0:
            return QQ(N + 4)
        best = QQ(N + 4)
        for i, c in enumerate(a.polynomial()):
            if i > 0 and c != 0:
                best = min(best, QQ(c.valuation()) + QQ(i) / e)
        return best

    def pt(c, ring=None):
        ring = ring if ring is not None else K0
        return CurvePoint(FS.RR, ring(c[0]), y=ring(c[1]), ring=ring)

    print("(1) THE BASE POINT IS A FROBENIUS FIXED POINT")
    Pb = pt(BASE)
    Fb = FS.phi_image(Pb)
    check(min(vz(Fb.x - Pb.x), vz(Fb.y - Pb.y)) >= cert,
          "phi(b) = b for b = (1,3) to p^%s: x(b) = 1 is its own Teichmuller "
          "lift and the fibre above it is a single point of the disk.  This is "
          "what makes the (2,1) block of the general law read (I-F)alpha = "
          "f - utilde with no int_b^{phi b} omega in it"
          % min(vz(Fb.x - Pb.x), vz(Fb.y - Pb.y)))

    print("(2) THE GENERAL LAW AT GOOD POINTS, AGAINST (23) + (24)")
    worst = QQ(N + 4)
    for c in GOOD:
        P = pt(c)
        M1, x0 = FS.frob_triv(P)
        M2, LE2, IP2 = FS.frob_triv_general(P)
        a1, b1, g1 = FS.read_triv(M1)
        a2, b2, g2 = FS.read_triv(M2)
        d = min([vz(a1[i] - a2[i]) for i in range(n)]
                + [vz(b1[i] - b2[i]) for i in range(n)] + [vz(g1 - g2)])
        worst = min(worst, d)
        info("%-16s agreement p^%s" % (c, d))
    check(worst >= cert,
          "frob_triv_general reproduces (23)+(24) at all four good rational "
          "points to p^%s (certified p^%d), forming no Teichmuller point on "
          "the way" % (worst, cert))

    # negative controls: the two terms of the (3,1) block that a naive reading
    # would drop or get the sign of.
    P = pt((QQ(-2), QQ(6)))
    M1, _ = FS.frob_triv(P)
    _, _, g1 = FS.read_triv(M1)
    LEc = LocalExpansion(P, 4 * N + 20)
    _, uu, ww, vv = FS.transport_series(P, LE=LEc)
    tQ = LEc.t_of(FS.phi_image(P))
    ut = vector(K0, [K0(a(tQ)) for a in uu])
    wt = vector(K0, [K0(a(tQ)) for a in ww])
    vt = K0(vv(tQ))
    f, gv, hv = FS.values_at(P)
    F = FS._in(FS.F, K0)
    alpha = (matrix.identity(K0, n) - F).inverse() * (f - ut)
    for lab, gwrong in [
            ("the sign of vtilde",
             (hv + gv * alpha + vt - wt * alpha) / K0(1 - P_GATE)),
            ("the cross term utilde^T Z alpha",
             (hv + gv * alpha - vt) / K0(1 - P_GATE))]:
        check(vz(g1 - gwrong) < cert,
              "NEGATIVE CONTROL: getting %s wrong moves gamma at (-2,6) by "
              "p^%s, i.e. it is not a term the certificate could hide"
              % (lab, vz(g1 - gwrong)))

    print("(3) THE BAD-DISK CODE PATH, RUN ON A GOOD DISK OVER Q_13(13^(1/%d))"
          % EE)
    Kx = CI.extension(EE)
    tp = tprec_for(P_GATE, N, EE)
    info("t-adic truncation l = %s (Remark 4.2 for e = %d)" % (tp, EE))
    Rq = pt((QQ(-2), QQ(6)))
    M1, _ = FS.frob_triv(Rq)
    a1, b1, g1 = FS.read_triv(M1)
    t0 = time.time()
    LEg = LocalExpansion(Rq.change_ring(Kx), tp, ring=Kx)
    P1 = LEg.point_at(Kx.gen())
    M2, _, IP1 = FS.frob_triv_general(P1, at=Rq.change_ring(Kx), LE=LEg)
    a2, b2, g2 = FS.read_triv(IP1.inverse() * M2)
    d = min([vz(Kx(a1[i]) - a2[i], EE) for i in range(n)]
            + [vz(Kx(b1[i]) - b2[i], EE) for i in range(n)]
            + [vz(Kx(g1) - g2, EE)])
    check(d >= cert,
          "M at (-2,6) recovered to p^%s from the point at t = pi of its own "
          "disk, by the general law and the transport back -- the whole "
          "bad-disk route except the very bad expansion point and "
          "Proposition 4.6's loss  (%.0f s)" % (d, time.time() - t0))

    print("(4) THE BAD DISK ITSELF")
    Pz = pt(BAD)
    PzK = Pz.change_ring(Kx)
    info("e_P = %s at (0,0), so Remark 4.4 needs e > p e_P = %d; e = %d"
         % (CI.ramification_at(Pz), P_GATE * CI.ramification_at(Pz), EE))

    def bad_run(tprec):
        LEb = LocalExpansion(PzK, tprec, ring=Kx)
        Pp = LEb.point_at(Kx.gen())
        M, _, IP = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
        return FS.read_triv(IP.inverse() * M), Pp, LEb.residual()

    t0 = time.time()
    (al, bp, gp), Pp, resid = bad_run(tp)
    info("Q(x(t),y(t)) = 0 to p^%s on the expansion at (0,0); P' has "
         "ord_p r = %s and f converges there: %s  (%.0f s)"
         % (resid, Pp.vp(Pp.rval), CI.f_converges_at(Pp), time.time() - t0))

    # Algorithm 3.12, which shares no step with the transport route
    def qp_part(a, e):
        if e == 1:
            return a
        cl = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
        return cl[0] if cl else 0

    def u_at(P):
        if P.is_good():
            return [FS.evaluate(a, P) for a in FS.u]
        LEs = LocalExpansion(P, 4)
        return [FS.series_of(a, LEs, as_form=False)[0] for a in FS.u]

    t0 = time.time()
    comp = [qp_part(a, EE)
            for a in CI.coleman_integrals_general(Pb, Pz, e=EE)]
    uP, uQ = u_at(Pb), u_at(Pz)
    uz = vector(K0, [sum((K0(QQ(FS.S[i][j])) * K0(comp[j]) for j in range(n)
                          if FS.S[i][j] != 0), K0(0)) + K0(uQ[i]) - K0(uP[i])
                     for i in range(n)])
    badprec = QQ(CI.certified_precision(*CI.last_eval_points))
    info("Algorithm 3.12 for int_b^{(0,0)} omega: %.0f s, certified p^%s"
         % (time.time() - t0, badprec))
    da = min(vz(al[i] - Kx(uz[i]), EE) for i in range(n))
    check(da >= badprec,
          "alpha_phi((0,0)) from the general law agrees with Algorithm 3.12's "
          "int_b^{(0,0)} omega to p^%s (certified p^%s), coordinate by "
          "coordinate" % (da, badprec))
    beta_b = list(LH.frob_data(Pb)[1])
    predb = [sum((Kx(uz[i]) * Kx(FS.Zk[i][j]) for i in range(n)), Kx(0))
             for j in range(n)]
    db = min(vz(bp[j] - Kx(beta_b[j]) - predb[j], EE) for j in range(n))
    check(db >= badprec,
          "beta_phi((0,0))^T = beta_phi(b,b)^T + (int_b^{(0,0)} omega)^T Z to "
          "p^%s: E090 verified this transport law at the seven good rational "
          "points, and it holds on the bad disk too" % db)

    print("(5) t-ADIC STABILITY OF THE ITERATED INTEGRAL")
    tp2 = tp + 2 * EE
    t0 = time.time()
    (al2, bp2, gp2), _, _ = bad_run(tp2)
    dst = vz(gp - gp2, EE)
    info("gamma_phi((0,0)) at l = %s against l = %s: agreement p^%s  (%.0f s)"
         % (tp, tp2, dst, time.time() - t0))
    check(dst >= badprec,
          "the t-adic truncation is not the binding error: Proposition 4.1 "
          "bounds a single tiny integral and says nothing about the iterated "
          "one, so this is measured, not quoted")
    floor = min([qp_floor(a, EE) for a in al] + [qp_floor(a, EE) for a in bp]
                + [qp_floor(gp, EE)])
    info("the computed alpha, beta, gamma at (0,0) leave Q_p at p^%s: an "
         "independent, if optimistic, measurement of the accumulated error"
         % floor)

    print("(6) THE MEASUREMENT")
    kmax = max(ZZ(FS.RR.J_range(a)[1])
               for a in [FS.h] + list(FS.g_vec) + list(FS.f))
    pv = prop46_precision(P_GATE, cert, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS.FM, "e_finite", 1)))
    gate = min(QQ(cert), pv, badprec, dst)
    info("Proposition 4.6 at P' with kmax = %s (the r-adic support of f, g AND "
         "h) gives p^%s; with Phi's p^%s and the tiny integrals' p^%s the "
         "certificate for this comparison is p^%s" % (kmax, pv, cert, badprec,
                                                      gate))
    TH = {}
    for c in GOOD + [BASE]:
        TH[c] = LH.theta(pt(c))
    gfz = LH._fn_at(LH.gamma_fil, PzK)
    th00 = LH._assemble(al, bp, gp, gfz)
    pred = Kx(TH[(QQ(-1), QQ(3))] - TH[(QQ(-2), QQ(6))] / K0(3))
    D = th00 - pred
    info("gamma_phi^b((0,0)) = int_b^{(0,0)} ( eta + omega^T Z int omega ) = %s"
         % gp)
    info("theta_b(0,0)  computed   = %s" % th00)
    info("theta_b(0,0)  E090's prediction = %s" % pred)
    info("residual has valuation %s; theta itself has valuation %s; the "
         "computed theta leaves Q_p at p^%s"
         % (vz(D, EE), vz(th00, EE), qp_floor(th00, EE)))
    measure(vz(D, EE) >= gate, "H6 (E090's prediction)",
            "theta_b(0,0) = theta(-1,3) - theta(-2,6)/3, and with it h_2 = 0 "
            "at b, (-1,3), (-2,6), (0,0).  Residual p^%s against a "
            "certificate of p^%s" % (vz(D, EE), gate))

    print("(7) CONTROLS ON THE READING OF THE SYSTEM")
    check(vz(TH[BASE]) >= cert,
          "theta(b) = 0 to p^%s, as (14) forces" % vz(TH[BASE]))
    check(vz(TH[SIGB]) >= cert,
          "theta(sigma b) = 0 to p^%s: [sigma b - b] is trivial in E(Q), its "
          "Prym contribution is (m_2/4)(hhat(kappa') - hhat(kappa')) = 0, and "
          "j_Gamma vanishes at both -- the same three premises the prediction "
          "of (6) is built from, at a point where they are checkable"
          % vz(TH[SIGB]))

    print("(8) WHAT THE RESIDUAL IS")
    info("[BDMTV2023] Theorem 3.2 makes h_ell(A_Z(b,x)) = c_ell log_p(ell) "
         "[j_Gamma(red x) - j_Gamma(red b)] with j_Gamma RATIONAL, so if the "
         "residual is a difference of local heights at one prime, "
         "residual/log_13(ell) is a rational number.  This is a diagnostic, "
         "not a gate: an identification here is [E] and has to be repeated at "
         "another (N, e) before it means anything.")
    floorD = min(qp_floor(D, EE), qp_floor(th00, EE))

    def small_residue(c, k):
        m = ZZ(P_GATE)**ZZ(k)
        a = ZZ(c.residue(ZZ(k)))
        return a - m if 2 * a > m else a

    for lab, base in [("log_13(2)", K0(2).log()), ("log_13(3)", K0(3).log())]:
        r = qp_part(D / Kx(base), EE)
        for tag, lev in [("certified", gate), ("measured ", floorD)]:
            k = ZZ(QQ(lev).floor()) - ZZ(QQ(vz(Kx(base), EE)).floor())
            if k < 1 or r == 0:
                continue
            a = small_residue(r, k)
            info("residual/%s  =  %s   mod 13^%d   [%s]%s"
                 % (lab, a, k, tag,
                    "   = %s" % factor(a) if a != 0 and abs(a) > 1 else ""))
    for nm, v in [("theta(-1,3)", Kx(TH[(QQ(-1), QQ(3))])),
                  ("theta(-2,6)", Kx(TH[(QQ(-2), QQ(6))]))]:
        if v != 0:
            info("residual / %-12s = %s" % (nm, D / v))

    print("(9) THE ITERATED INTEGRAL AGAIN, IN CHART 2")
    # E080/E082: Q_2 = 3 Q_1(y/3, x), with (x_2,y_2) = (w,3t), is a second
    # Tuitman model in which C_4's bad point (0,0) is a GOOD TEICHMULLER point,
    # so (23) applies to it directly -- no push-out, no ramified extension, no
    # Proposition 4.6 loss.
    #
    # WHAT IS COMPARABLE, and gamma_phi ALONE IS NOT.  The (3,1) slot of the
    # trivialisation is invariant under a change of basis of V_dR -- conjugating
    # M by diag(1,T,1) moves alpha and beta and fixes it -- and everything in
    # sight is linear in Z, so the two charts should differ by E082's scale
    # lambda = 351/4 alone.  But gamma_phi also depends on the CHOICE of eta,
    # which \S4.4 pins only modulo the third-kind span (E075), and the two
    # charts' hodge_eta make that choice independently.  A different eta shifts
    # gamma_phi and gamma_Fil by the SAME int_b^x (Delta eta) -- both are the
    # (3,1) entries of trivialisations of the same A_Z -- so the eta-independent
    # quantity is the DIFFERENCE, and that is what is compared here.  (This is
    # measured, not assumed: comparing gamma_phi alone fails at p^0 already at
    # a good point, which is how the eta ambiguity showed itself.)
    #
    # THE BASE POINT CANNOT BE b.  In chart 2 the residue disk of b = (1,3) is
    # BAD (r_2 is not a unit at x_2 = 3), and residue disks are intrinsic, so
    # no point of it is usable there.  The comparison is therefore anchored at
    # b'' = (-2,6), which is good in both charts, and it is made TWICE: at a
    # good point, where it tests only whether the two charts' gamma_phi
    # correspond, and at (0,0), where -- given that -- it tests the iterated
    # integral itself.
    Q2 = y**4 - 2*(y-3)**2*x**2 + 3*x**4 - 108*y
    BPP1, BPP2 = (QQ(-2), QQ(6)), (QQ(6), QQ(-6))
    lam = QQ(351) / QQ(4)
    t0 = time.time()
    C2 = TuitmanCurve(Q2, name="chart 2")
    H2 = Cohomology(C2)
    FS2 = FrobeniusStructure(C2, H2, P_GATE, N, BPP2, sx=-1, sy=1)
    FS2.solve()
    FSp = FrobeniusStructure(C, H, P_GATE, N, BPP1, sx=1, sy=-1, FM=FS.FM)
    FSp.solve()
    info("chart 2 and chart 1-at-b'' built and solved (%.0f s); certificates "
         "p^%d and p^%d" % (time.time() - t0, FS2.cert, FSp.cert))
    check(ZZ(FS.Zscale) == 13 and ZZ(FS2.Zscale) == 1,
          "the two charts' _rescale_Z factors are %s and %s, which is what "
          "makes E082's lambda = (27/4)*13 = 351/4 the whole of the "
          "difference -- the one input here that is invisible in the paper"
          % (FS.Zscale, FS2.Zscale))
    P2 = CurvePoint(FS2.RR, FS2.K(0), y=FS2.K(0))
    T2 = FS2.teichmuller(P2)
    check(P2.is_good()
          and min(P2.vp(T2.x - P2.x), P2.vp(T2.y - P2.y)) >= FS2.cert,
          "in chart 2 (0,0) is a good point and its own Teichmuller point, so "
          "(23) applies to it directly")

    LHp = LocalHeight(FSp, BPP1, fil0_correction=True)
    LH2 = LocalHeight(FS2, BPP2, fil0_correction=True)

    def gdiff(FSi, LHi, P):
        return FSi.read_triv(FSi.frob_triv(P)[0])[2] - LHi._fn_at(
            LHi.gamma_fil, P)

    # The test is made at a GOOD point, where both charts compute directly and
    # neither uses anything E091 added.  It therefore tests the
    # correspondence, not the new route -- and if the correspondence does not
    # hold there is nothing to compare on the bad disk.
    G1 = gdiff(FSp, LHp, pt((QQ(-1)/11, QQ(15)/11)))
    G2 = gdiff(FS2, LH2,
               CurvePoint(FS2.RR, FS2.K(QQ(15)/11), y=FS2.K(QQ(-3)/11)))
    d9 = vz(G1 - K0(lam) * G2)
    info("(gamma_phi - gamma_Fil)^{b''} at (-1/11,15/11):")
    info("   chart 1          %s" % G1)
    info("   lambda * chart 2 %s" % (K0(lam) * G2))
    measure(d9 >= min(QQ(FS2.cert), QQ(FSp.cert)),
            "H9 (chart-invariance)",
            "(gamma_phi - gamma_Fil)^(1) = lambda (gamma_phi - gamma_Fil)^(2) "
            "with lambda = 351/4.  Agreement p^%s against certificates p^%d "
            "and p^%d.  Comparing gamma_phi ALONE fails the same way, so the "
            "eta ambiguity is not the whole of it: identifying the "
            "discrepancy needs the block C of E082's change of basis, which "
            "E082 left undetermined" % (d9, FSp.cert, FS2.cert))

    print("=" * 72)
    print("E091 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    for nm, ok in MEASURED:
        print("   MEASURED: %-24s %s" % (nm, "holds" if ok else "REFUTED"))


main()
