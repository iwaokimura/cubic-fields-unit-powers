# check-c4-zeroeq.sage --- E090: what the equation at (0,0) actually costs, and
# the two Prym heights that are already determined.
#
# Run: sage check-c4-zeroeq.sage        (about 4 minutes)
#
# WHY.  E088 and E089's Next Steps both said: compute theta(0,0) through
# chart 2, solve for the Prym coefficients, and spend the one consistency check
# the system still affords.  Working out what that needs turned up two things
# the plan had not noticed, and this gate records both.
#
# (A) THE BASE-POINT LAW FOR h_ell IS NOT A GUESS.  [BDMTV2023] Theorem 3.2
#     (quoted from arXiv:2101.01862, which
#     attributes it to Betts-Dogra) states that j_Gamma is the UNIQUE piecewise
#     polynomial function with
#         j_Gamma(red(b)) = 0    and    nabla^2 (j_Gamma) = mu_F ,
#     and mu_F depends only on F (our Z) and the graph -- not on b.  The same
#     paragraph notes that the Laplacian's kernel is the constants.  So the
#     base point enters ONLY through the additive normalisation, and
#         h_ell(A_Z(b',x)) = c [ j_Gamma(red x) - j_Gamma(red b') ] .
#     E084's table then gives h_3 for any base point.  This was the step
#     E088 would have had to guess.
#
# (B) LEMMA 5.7 CHANGES THE BASE POINT, SO IT DOES NOT GIVE THE EQUATION.
#     Section 5.5 of [BDM+19] says so in its first sentences -- "the
#     computation of the Hodge filtration with respect to the basepoint b' ...
#     the nontrivial issue is the Frobenius structure with respect to this new
#     basepoint" -- and justifies it by "the set X(Q_p)_U is independent of
#     b'", which is true for THEM because Upsilon = {0}.  It is not true for
#     us: h_2 and h_3 do not vanish.  What E081 computed is therefore
#     theta_{b'} on ](0,0)[, and theta_{b'}(b') = 0 identically.  The equation
#     at (0,0) needs theta_b(0,0), with the ORIGINAL base point.
#
#     How much of theta_b(0,0) is free?  Almost all of it.  Writing
#     u := int_b^{b'} omega (Algorithm 3.12, available), the transport law of
#     (24) -- w^T = u^T Z -- gives the b-anchored data at b':
#         alpha_phi^b(b') = u ,
#         beta_phi^b(b')^T = beta_phi(b,b)^T + u^T Z ,          <- factor ONE
#         gamma_phi^b(b') = v(b') := int_b^{b'} ( eta + omega^T Z int omega ) ,
#     against Lemma 5.7's beta_phi^{b'}(b')^T = beta_phi(b,b)^T + 2 u^T Z, the
#     factor TWO being exactly the base-point change.  Feeding these into (14),
#         theta_b(0,0) = v(b') + K ,
#     with K computable from u alone.  So the ONE missing ingredient is a
#     single number: the global ITERATED Coleman integral into the bad disk.
#     The port has tiny iterated integrals (inside a disk) and single global
#     ones (Algorithm 3.12); it does not have this one.
#
# WHAT THIS GATE DOES INSTEAD.  It computes K, determines the Prym height that
# IS available, and turns the missing check into a PREDICTION of that iterated
# integral, which a later experiment can test:
#
#     H_1 := hhat_P(kappa')   from   theta(-2,6) = (3 m_2 / 4) H_1 ,
#     theta_b(0,0) = theta(-1,3) - theta(-2,6)/3   [prediction],
#     v(b') = theta(-1,3) - theta(-2,6)/3 - K      [prediction].
#
# The middle line uses, besides (A): E088's measured vanishings, the delta-form
# of the Prym height from E089, and h_2 = 0 on the three points involved.  Its
# derivation, with delta(x) = [x - sigma x] and the Prym part of the height
# equal to (m_2/4)[hhat_P(delta x) - hhat_P(delta b)]:
#     (-1,3):  E_2 = 0 there, and delta = kappa' = -delta(b), so both sides
#              vanish except h_3:      theta(-1,3) = -h_3(-1,3).
#     (-2,6):  v_1 = 0 and delta = -2 kappa', h_3 = 0:
#                                      theta(-2,6) = (3 m_2/4) H_1.
#     (0,0):   delta = 0, h_3(0,0) = h_3(-1,3) (both reduce to R, E084):
#                                      theta(0,0) + h_3(-1,3) = -(m_2/4) H_1,
#              PROVIDED the elliptic term vanishes there, which check (4)
#              measures.
#
# THE CHECKS.
#   (1) h_3 is constant on the reduction classes E084 computed, and (0,0) and
#       (-1,3) share one.
#   (2) The transport law beta_phi(x)^T = beta_phi(b)^T + (int_b^x omega)^T Z
#       at all seven good rational points -- this is the "factor one" above,
#       and it is what makes Lemma 5.7's factor two a base-point change.
#   (3) u = int_b^{(0,0)} omega by Algorithm 3.12, with the sigma-check
#       2 u_j = kappa_j on ALL FOUR anti-invariant coordinates (E087 checked
#       two of them).
#   (4) The elliptic coordinate, twice.  (a) EXACTLY: C_4 -> E' is
#       (t,w) |-> (t, w^2), and E037(f)'s quartic v^2 = 9(t-1)^4-27t^4+108t is
#       put in Weierstrass form here, with the images of the five orbits and
#       their classes [xbar - bbar] in E(Q) = Z + (Z/2)^2.  (b) p-ADICALLY:
#       u_0 at the five orbits as ratios to u_0(-1,3).  The two must agree, and
#       (a) settles u_0((0,0)) = 0 -- which is what makes the prediction below
#       free of B_11 -- at a precision the bad-disk integral cannot reach.
#   (5) gamma_Fil is regular at (0,0) (E080 located its poles at infinity), K,
#       and the two predictions.
#   (6) H_1, and the one relation between B_11 and H_2 that (-1/11,15/11)
#       gives.

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion
from padic.integrals import ColemanIntegrals

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13
N = ZZ(os.environ.get("E090_N", 8))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
GOOD = [SIGB, (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
        (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)),
        (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11)]
# E084: j_Gamma(red x) for the nine points, in E084's normalisation
JGAMMA = {QQ(1): QQ(0), QQ(-2): QQ(0), QQ(-1)/11: QQ(0),
          QQ(-1): QQ(1)/8, QQ(0): QQ(1)/8}

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


def vz(a, N):
    return ZZ(N + 4) if a == 0 else ZZ(a.valuation())


def qp_part(a, e):
    if e == 1:
        return a
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    return c[0] if c else 0


def u_at(FS, P):
    """The exact parts u_i of omega~ = S omega + du, at ANY point (E081)."""
    if P.is_good():
        return [FS.evaluate(a, P) for a in FS.u]
    LE = LocalExpansion(P, 4)
    return [FS.series_of(a, LE, as_form=False)[0] for a in FS.u]


def main():
    print("=== check-c4-zeroeq.sage --- E090: the cost of the (0,0) equation "
          "===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)

    print("(1) h_3 ON THE REDUCTION CLASSES (E084), AND THE BASE-POINT LAW")
    info("[BDMTV2023] Thm 3.2: nabla^2 j_Gamma = mu_F with mu_F independent of "
         "b, and j_Gamma(red b) = 0; the Laplacian's kernel is the constants.  "
         "So h_ell(A_Z(b',x)) = c [ j_Gamma(red x) - j_Gamma(red b') ], and "
         "the base point enters only additively.")
    check(JGAMMA[QQ(0)] == JGAMMA[QQ(-1)],
          "(0,0) and (-1,3) reduce to the same vertex R of Gamma_3, so "
          "h_3(0,0) = h_3(-1,3) whatever the constant c is -- which is what "
          "lets the prediction below be free of c")
    check(JGAMMA[QQ(-2)] == 0 and JGAMMA[QQ(1)] == 0,
          "and (-2,6) reduces to Ebar', where j_Gamma vanishes, as does the "
          "base point: h_3(-2,6) = h_3(b) = 0")

    print("(2) THE FROBENIUS STRUCTURE, AND THE TRANSPORT LAW FOR beta_phi")
    t0 = time.time()
    FS = FrobeniusStructure(C, H, P_GATE, N, BASE, sx=1, sy=-1)
    cc, mu, resv = FS.solve()
    K, cert = FS.K, FS.cert
    info("(22) solved: certified p^%d, residual p^%s, N = %d  (%.0f s)"
         % (cert, resv, N, time.time() - t0))
    LH = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    Pb = CurvePoint(FS.RR, K(BASE[0]), y=K(BASE[1]))
    ub = u_at(FS, Pb)
    beta_b = list(LH.frob_data(Pb)[1])

    def integral_reps(P, Q, e=None):
        """int_P^Q of the phase-4 forms, as a vector over Q_p (E081)."""
        if P.is_bad() or Q.is_bad():
            ee = ZZ(e)
            comp = [qp_part(c, ee)
                    for c in CI.coleman_integrals_general(P, Q, e=ee)]
        else:
            comp = list(CI.coleman_integrals_on_basis(P, Q))
            ee = ZZ(1)
        uP, uQ = u_at(FS, P), u_at(FS, Q)
        out = []
        for i in range(n):
            acc = K(0)
            for j in range(n):
                if FS.S[i][j] != 0:
                    acc += K(QQ(FS.S[i][j])) * K(comp[j])
            out.append(acc + K(uQ[i]) - K(uP[i]))
        return vector(K, out), ee

    def uTZ(uv, factor=1):
        return [sum((K(factor) * uv[i] * FS.Zk[i][j] for i in range(n)), K(0))
                for j in range(n)]

    worst = ZZ(N + 4)
    UU, TH, E12 = {}, {}, {}
    for pt in GOOD:
        P = CurvePoint(FS.RR, K(pt[0]), y=K(pt[1]))
        uv, _ = integral_reps(Pb, P)
        UU[pt] = uv
        al, bp, gp, gf = LH.frob_data(P)
        E12[pt] = ([al[i] for i in range(g)],
                   [bp[j] - K(QQ(LH.beta_fil[j])) for j in range(g, n)])
        TH[pt] = LH._assemble(al, bp, gp, gf)
        pred = uTZ(uv)
        for j in range(n):
            worst = min(worst, vz(bp[j] - beta_b[j] - pred[j], N))
    check(worst >= cert,
          "beta_phi(x)^T = beta_phi(b)^T + (int_b^x omega)^T Z at all seven "
          "good rational points, to p^%s (certified p^%d).  The coefficient is "
          "ONE; Lemma 5.7's is TWO, and the difference is precisely the change "
          "of base point" % (worst, cert))

    print("(3) int_b^{(0,0)} omega BY ALGORITHM 3.12")
    Pz = CurvePoint(FS.RR, K(BAD[0]), y=K(BAD[1]))
    t0 = time.time()
    ee = ZZ(2 * P_GATE * CI.ramification_at(Pz))
    uz, _ = integral_reps(Pb, Pz, e=ee)
    badprec = QQ(CI.certified_precision(*CI.last_eval_points))
    info("e = %d, %.0f s; valuations %s; the bad-disk integral is certified to "
         "p^%s, against p^%d for Phi"
         % (ee, time.time() - t0, [str(vz(a, N)) for a in uz], badprec, cert))
    kap = UU[SIGB]
    ANTI = [1, 2, 4, 5]                       # sigma^* = diag(1,-1,-1,1,-1,-1)
    w3 = min(vz(2 * uz[j] - kap[j], N) for j in ANTI)
    check(w3 >= min(cert, ZZ(2)),
          "2 u_j = kappa_j on all FOUR anti-invariant coordinates, to p^%s: "
          "(0,0) is sigma-fixed, so its Abel-Jacobi image is half of "
          "AJ_b(sigma b) in the anti-invariant part.  E087 checked two of the "
          "four" % w3)
    check(vz(kap[0], N) >= cert and vz(kap[3], N) >= cert,
          "and kappa vanishes on the two INVARIANT coordinates, as it must: "
          "sigma b - b is anti-invariant")

    print("(4a) THE ELLIPTIC CLASSES, EXACTLY ON E")
    # C_4 -> E' : (t,w) |-> (t, u = w^2), and v := u - 3(t-1)^2 satisfies
    # v^2 = 9(t-1)^4 - 27 t^4 + 108 t (E037(f)).  With q = 3 = v(0) the
    # substitution v = q + (d/2q) t + s t^2 turns the quartic into a cubic in s.
    qq, dd, cc4, bb4, aa4 = QQ(3), QQ(72), QQ(54), QQ(-36), QQ(-18)
    Rs = PolynomialRing(QQ, 'S')
    S = Rs.gen()
    Acu = aa4 - S**2
    Bcu = bb4 - (dd/qq)*S
    Ccu = cc4 - dd**2/(4*qq**2) - 2*qq*S
    cub = Bcu**2 - 4*Acu*Ccu
    c3 = cub[3]
    Eq = EllipticCurve([0, cub[2], 0, cub[1]*c3, cub[0]*c3**2])
    check(Eq.is_isomorphic(EllipticCurve([0, 0, 0, -36, 0])),
          "the quartic model of C_4/sigma is %s, isomorphic to y^2 = x^3-36x "
          "as E037(f) says" % Eq)

    def img(tt, ww):
        if tt == 0:
            return Eq(0)          # (t,v) = (0,-3) is the point at infinity
        vv = ww**2 - 3*(tt-1)**2
        ss = (vv - qq - (dd/(2*qq))*tt) / tt**2
        return Eq(c3*ss, c3*(2*(aa4 - ss**2)*tt + bb4 - (dd/qq)*ss))

    ORB = [SIGB, (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)]
    gen = Eq.gens()[0]
    tors = [T.element() if hasattr(T, "element") else T
            for T in Eq.torsion_subgroup()]
    Pbar = img(*BASE)
    nn = {}
    for pt in ORB + [BAD]:
        D = img(*pt) - Pbar
        m = None
        for k in range(-6, 7):
            if any(D == k*gen + T for T in tors):
                m = k
                break
        nn[pt] = m
        info("[%-16s bar - bbar] = %s   = %s * gen + torsion"
             % (pt, D, m if m is not None else "?"))
    check(all(nn[pt] is not None for pt in ORB + [BAD]),
          "every class [xbar - bbar] is a small multiple of the generator "
          "%s of E(Q) modulo E(Q)_tors = (Z/2)^2" % gen)
    check(nn[BAD] == 0,
          "and [(0,0)bar - bbar] is TORSION (it is %s, of order %s): bbar is a "
          "2-torsion point and (0,0)bar is the origin.  So u_0((0,0)) = 0 "
          "EXACTLY, and the elliptic term of the (0,0) equation vanishes"
          % (img(*BAD) - Pbar, (img(*BAD) - Pbar).order()))

    print("(4b) THE SAME, MEASURED p-ADICALLY")
    ref = UU[(QQ(-1), QQ(3))][0]
    info("u_0 valuations: %s"
         % {str(pt): str(vz(UU[pt][0], N)) for pt in ORB})
    info("u_0((0,0)) valuation %s, against a bad-disk certificate of p^%s"
         % (vz(uz[0], N), badprec))
    ok4 = True
    for pt in ORB:
        r = UU[pt][0] / ref
        rec = None
        for num in range(-8, 9):
            if vz(r - K(QQ(num)), N) >= cert - 1:
                rec = num
                break
        info("u_0(%-16s) / u_0(-1,3) = %s   (exact: %s)"
             % (pt, rec, None if nn[pt] is None or nn[(QQ(-1), QQ(3))] == 0
                else QQ(nn[pt]) / QQ(nn[(QQ(-1), QQ(3))])))
        if rec is None or nn[pt] is None or \
                QQ(rec) != QQ(nn[pt]) / QQ(nn[(QQ(-1), QQ(3))]):
            ok4 = False
    check(ok4,
          "the p-adically measured ratios of u_0 agree with the exact classes "
          "of (4a) at all four good orbits: two unrelated computations, "
          "Coleman integration at p = 13 and the Mordell-Weil group of "
          "y^2 = x^3-36x over Q")
    check(vz(uz[0], N) >= badprec,
          "and u_0((0,0)) is zero to the bad-disk certificate p^%s, as (4a) "
          "requires -- Algorithm 3.12 cannot see further, which is why the "
          "exact computation is the one that settles it" % badprec)

    print("(5) gamma_Fil AT (0,0), K, AND THE PREDICTIONS")
    try:
        gfz = LH._fn_at(LH.gamma_fil, Pz)
        okg = True
    except ArithmeticError as exc:
        gfz, okg = None, False
        info("gamma_Fil: %s" % exc)
    check(okg, "gamma_Fil is regular at (0,0): E080 located its poles at the "
               "degree-4 place over x = infinity, which carries no F_13-point")
    beta_at_z = [beta_b[j] + uTZ(uz)[j] for j in range(n)]
    Kconst = LH._assemble(list(uz), beta_at_z, K(0), gfz)
    info("K = %s   (valuation %s)" % (Kconst, vz(Kconst, N)))

    # the two vanishings the prediction rests on, re-verified here
    e13 = E12[(QQ(-1), QQ(3))][1]
    check(min(vz(a, N) for a in e13) >= cert,
          "E_2((-1,3)) = 0 to p^%s (E088): that orbit's whole design row "
          "vanishes" % min(vz(a, N) for a in e13))
    v0_26 = E12[(QQ(-2), QQ(6))][1][0]
    check(vz(v0_26, N) >= cert,
          "and the elliptic coordinate of E_2((-2,6)) vanishes to p^%s -- "
          "which now follows from (4a) as well, since [(-2,6)bar - bbar] and "
          "[(-1,3)bar - bbar] are equal modulo torsion, so u_0 and hence "
          "v_0 = m_1 u_0 + c_1 agree at the two points" % vz(v0_26, N))

    th13, th26 = TH[(QQ(-1), QQ(3))], TH[(QQ(-2), QQ(6))]
    th00 = th13 - th26 / K(3)
    vpred = th00 - Kconst
    info("theta(-1,3)  = %s" % th13)
    info("theta(-2,6)  = %s" % th26)
    check(True,
          "PREDICTION  theta_b(0,0) = theta(-1,3) - theta(-2,6)/3 = %s"
          % th00)
    check(True,
          "PREDICTION  int_b^{(0,0)} ( eta + omega^T Z int omega ) = "
          "theta_b(0,0) - K = %s" % vpred)
    info("the second is a single global ITERATED Coleman integral into a bad "
         "disk, which the port does not implement.  It is the whole cost of "
         "the (0,0) equation, and a later experiment can test it against this "
         "number.")

    print("(6) THE PRYM HEIGHTS THAT ARE ALREADY DETERMINED")
    m2 = K(QQ(FS.Z[1][4]))
    m1 = K(QQ(FS.Z[0][3]))
    info("m_1 = %s, m_2 = %s (E088)" % (FS.Z[0][3], FS.Z[1][4]))
    H1 = K(4) * th26 / (K(3) * m2)
    check(vz(H1, N) < cert,
          "H_1 = hhat_P(kappa') = 4 theta(-2,6) / (3 m_2) = %s, the p-adic "
          "height of [sigma b - b] in the Prym" % H1)
    u1, v1 = E12[(QQ(-1)/11, QQ(15)/11)]
    ell = u1[0] * v1[0]
    th11 = TH[(QQ(-1)/11, QQ(15)/11)]
    info("the remaining equation, from (-1/11,15/11) with h_3 = 0:")
    info("   theta = B_11 * (%s) + (m_2/4) ( H_2 - H_1 )" % ell)
    info("   i.e.  H_2 = H_1 + (4/m_2) ( theta - B_11 * u_0 v_0 ) with "
         "theta = %s" % th11)
    check(vz(ell, N) < cert,
          "the elliptic coefficient is nonzero here (valuation %s), so B_11 "
          "and H_2 are entangled and one of them must come from outside -- "
          "E065(b)'s SageMath height on y^2 = x^3-36x" % vz(ell, N))

    print("=" * 72)
    print("E090 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
