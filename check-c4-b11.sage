# check-c4-b11.sage --- E094: B_11 from outside, and the splitting that has to
# be matched before it can be used.
#
# Run: sage check-c4-b11.sage        (E094_N, E094_E override N and e)
#
# WHERE PHASE 5 STANDS (E093).  Of the four unknowns in the height form B,
# three are settled: a = H_1 = hhat_P(kappa') in closed form, and the local
# heights c_3 = -(m_2/4) log_13(3), c_2 = (m_2/8) log_13(2).  What is left is
# ONE equation in TWO unknowns,
#
#     theta_3 = B_11 u_0 v_0 - (m_2/4) H_1 + (m_2/4) H_2 ,
#
# plus the entry <kappa', delta_11>_P that appears in no equation at all
# ((B5), untouchable by anything here).  E094 says: get B_11 from
# SageMath's p-adic height on the quotient elliptic curve and read H_2 off.
#
# THE TWO NORMALISATIONS THAT HAVE TO BE MATCHED FIRST, AND WHAT THIS GATE
# ACTUALLY DOES ABOUT THEM.
#
#   (i) THE DIFFERENTIAL.  B_11 is defined by hhat_E(D) = B_11 (int_D omega_0)^2
#       with omega_0 the FIRST phase-4 basis form of C_4, whereas SageMath's
#       height and formal logarithm both live on a Weierstrass model with
#       omega_E = dX/(2Y).  The two differ by a scalar, and the scalar is
#       EXACT: group (1) computes omega_0 / pi^* omega_E inside the function
#       field of C_4 and finds it constant.  [T(CAS)]
#
#  (ii) THE SPLITTING.  h_p depends on the splitting of the Hodge filtration.
#       E088-E093 all ran LocalHeight's DEFAULT splitting -- the coordinate one
#       of the phase-4 basis, call it W -- while SageMath's padic_height is the
#       Mazur-Stein-Tate height, i.e. (Besser) Coleman-Gross with the UNIT ROOT
#       splitting U.  These are different heights and B_11 is different for
#       them.  So E093's numbers cannot be fed Sage's B_11 as they stand.
#
#       The fix is cheap and it comes with a check.  Writing the unit root
#       subspace of H^1_dR in the phase-4 basis as the span of
#       omega_{g+i} + sum_j tau_ij omega_j, the splitting is the matrix
#       s_1 = [[I,0],[-tau,0]] on V_dR = H^1_dR^*, and LocalHeight.with_splitting
#       takes it without redoing the Hodge solve or (22).  Feeding it through
#       (14) gives, IDENTICALLY,
#
#           theta^U(x) - theta^W(x) = E_2(x)^T tau E_1(x),                  (*)
#
#       so B^U = B^W + tau as bilinear forms in the log coordinates.  Three
#       consequences are measured here and every one of them can fail:
#
#         (a) theta is UNCHANGED at (-1,3), where E_2 = 0;
#         (b) Delta theta_4 = -(1/3) Delta theta_2 exactly, which is the
#             statement that c_3 and c_2 -- the ell-adic local heights -- do
#             NOT move with the p-adic splitting, as they must not;
#         (c) Delta H_1 = kappa'^T tau_P kappa', the shift predicted by (*) for
#             the one Prym Gram entry the system determines.
#
#       (b) is the sharp one: it ties the bad-disk iterated integral at (0,0)
#       to the good-point integral at (-2,6) through a matrix computed from
#       Frobenius alone, and E092's cluster rule sits underneath it.
#
# WHAT IS STILL NOT CHECKED, AND THE GATE SAYS SO IN NUMBERS.  One scalar
# survives: the constant nu relating SageMath's padic_height to the
# Coleman-Gross height in our normalisation of the idele class character.
# Sage's source computes -2/n^2 * log(...) and its docstring says the
# normalisation carries "a factor 1/2 with respect to some other normalisations
# that appear in the literature".  We take nu = 1 (Sage's value IS the height
# that enters B) and the negative control in group (6) shows what nu = 2 would
# do to H_2.  Nothing in this project tests nu; it is inherited, and it is the
# one place where a silent error in E094 would survive into E096.
#
# THE OUTPUT.  Phase 5's accounting in the unit root splitting: c_3, c_2 (both
# splitting-invariant), H_1^U, B_11^U, H_2^U.

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion
from padic.integrals import ColemanIntegrals, tprec_for, prop46_precision

load("cg-height-lib.sage")   # E134: our Coleman--Gross height

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13
N = ZZ(os.environ.get("E094_N", 12))
EE = ZZ(os.environ.get("E094_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
GOOD = [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
        P11, (QQ(-1)/11, QQ(-15)/11)]

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


# ---------------------------------------------------------------- group (1)

def elliptic_side(CO, C, reps):
    """The quotient elliptic curve, the exact scalar Lambda, and the classes.

    C_4 -> C_4/sigma is (t,w) -> (t, w^2); with v := w^2 - 3(t-1)^2 the
    quotient is E037(f)'s quartic v^2 = 9(t-1)^4 - 27t^4 + 108t, and E090 puts
    it in Weierstrass form.  Everything here is exact.
    """
    L = C.L
    xL, yL = L(C.x), C.y
    v = yL**2 - 3*(xL - 1)**2
    quart = 9*(xL - 1)**4 - 27*xL**4 + 108*xL
    q, dd, c4_, b4_, a4_ = QQ(3), QQ(72), QQ(54), QQ(-36), QQ(-18)
    Sv = (v - q - (dd/(2*q))*xL) / xL**2
    Rs = PolynomialRing(QQ, 'T')
    T = Rs.gen()
    cub = (b4_ - (dd/q)*T)**2 - 4*(a4_ - T**2)*(c4_ - dd**2/(4*q**2) - 2*q*T)
    c3 = cub[3]
    Eq = EllipticCurve([0, cub[2], 0, cub[1]*c3, cub[0]*c3**2])
    X = c3*Sv
    Y = c3*(2*(a4_ - Sv**2)*xL + b4_ - (dd/q)*Sv)
    a1_, a2_, a3_, A4, A6 = Eq.a_invariants()
    wcheck = Y**2 + a1_*X*Y + a3_*Y - (X**3 + a2_*X**2 + A4*X + A6)
    omE = X.differential()._f / (2*Y + a1_*X + a3_)

    def img(tt, ww):
        if tt == 0:
            return Eq(0)
        vv = ww**2 - 3*(tt - 1)**2
        ss = (vv - q - (dd/(2*q))*tt) / tt**2
        return Eq(c3*ss, c3*(2*(a4_ - ss**2)*tt + b4_ - (dd/q)*ss))

    lam = [CO.differential_of(r)._f / omE for r in reps[:3]]
    return Eq, img, v**2 - quart, wcheck, lam


def main():
    print("=== check-c4-b11.sage --- E094: B_11 from outside, and the "
          "splitting ===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2*ZZ(C.genus)
    reps, S4 = H.phase4_basis()

    print("(1) THE DIFFERENTIAL NORMALISATION, EXACTLY")
    Eq, img, vres, wres, lam = elliptic_side(H, C, reps)
    check(vres == 0 and wres == 0,
          "the quotient map lands on E037(f)'s quartic and E090's Weierstrass "
          "model %s: both identities hold in the function field of C_4, not to "
          "precision" % Eq)
    LAM = lam[0]
    check(LAM in QQ,
          "omega_0 / pi^*(dX/2Y) is the CONSTANT %s: the first phase-4 basis "
          "form is a rational multiple of the pullback of the invariant "
          "differential, so int_b^x omega_0 = Lambda * log_E([xbar - bbar]) "
          "with Lambda exact  [T(CAS)]" % LAM)
    LAM = QQ(LAM)
    check(lam[1] not in QQ and lam[2] not in QQ,
          "and omega_1, omega_2 are NOT multiples of it -- they are the "
          "anti-invariant half -- so the elliptic column of the height system "
          "is omega_0 alone, as E088's sigma^* = diag(1,-1,-1) says")
    gen = Eq.gens()[0]
    tors = [t.element() if hasattr(t, "element") else t
            for t in Eq.torsion_subgroup()]
    Pbar = img(*BASE)
    nn = {}
    for c in GOOD + [BAD]:
        D = img(*c) - Pbar
        nn[c] = next((k for k in range(-6, 7)
                      if any(D == k*gen + T for T in tors)), None)
    info("[xbar - bbar] as a multiple of the generator %s (E090's table): %s"
         % (gen, {str(c): nn[c] for c in GOOD + [BAD]}))
    check(all(nn[c] is not None for c in GOOD + [BAD])
          and nn[BASE] == 0 and nn[SIGB] == 0 and nn[BAD] == 0
          and nn[P13] == -1 and nn[P26] == -1 and nn[P11] == -2,
          "E090's table reproduced, including [(0,0)bar - bbar] torsion and "
          "sigma-conjugates having the SAME image (the quotient map does not "
          "see w's sign)")

    print("(2) THE ELLIPTIC LOGARITHM, AND u_0 MEASURED AGAINST IT")
    Fp = Eq.change_ring(GF(P_GATE))
    nker = ZZ(Fp.cardinality())
    Kh = Qp(P_GATE, 30)
    lg = Eq.formal_group().log(40)
    Qk = nker*gen
    tk = Kh(-QQ(Qk[0])/QQ(Qk[1]))
    logG = sum((Kh(QQ(c))*tk**i for i, c in enumerate(lg.list()) if c != 0),
               Kh(0)) / Kh(nker)
    check(tk.valuation() >= 1,
          "n = #E(F_13) = %d kills the reduction, so the formal logarithm "
          "converges at nG and log_E(G) = %s" % (nker, logG))
    Emin = Eq.minimal_model()
    iso = Eq.isomorphism_to(Emin)
    # E134: the height is OURS now (MST Algorithm 3.1 + (1.1), c = 0 derived
    # from CM by Z[i]); SageMath's padic_height is retained as an ANSWER KEY.
    hS = Eq.padic_height(P_GATE, 20)
    hSm = Emin.padic_height(P_GATE, 20)
    hG, hGm = cg_height_any(Eq, P_GATE, gen, 20), cg_height(Emin, P_GATE,
                                                            iso(gen), 20, QQ(0))
    check(hG == hS(gen) and hGm == hSm(iso(gen)),
          "E134's height agrees with SageMath's padic_height on both models, "
          "difference identically zero -- the answer key")
    info("the cyclotomic p-adic height of G (E134, ours): %s" % hG)
    check((hG - hGm).valuation() >= min(hG.precision_absolute(),
                                        hGm.precision_absolute()) - 1,
          "and it is the same on the global minimal model %s, as the "
          "documentation promises: the height is intrinsic, the LOGARITHM is "
          "what carries the choice of differential" % Emin)
    check((hS(2*gen) - 4*hG).valuation() >= hG.valuation() + 12,
          "h(2G) = 4 h(G) to 12 digits past the leading one: the quadraticity "
          "that makes B_11 = h(G)/u_0(G)^2 well posed")

    t0 = time.time()
    FS = FrobeniusStructure(C, H, P_GATE, N, BASE, sx=1, sy=-1)
    FS.solve()
    K0, cert = FS.K, FS.cert
    LHW = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    info("(22) solved and the Hodge side built: N = %d, certified p^%d "
         "(%.0f s)" % (N, cert, time.time() - t0))

    def vz(a, e=1):
        return QQ(N + 4) if a == 0 else QQ(a.valuation())/e

    def qp_floor(a, e):
        if e == 1 or a == 0:
            return QQ(N + 4)
        best = QQ(N + 4)
        for i, c in enumerate(a.polynomial()):
            if i > 0 and c != 0:
                best = min(best, QQ(c.valuation()) + QQ(i)/e)
        return best

    def qp_part(a, e):
        if e == 1:
            return a
        cl = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
        return cl[0] if cl else 0

    def pt(c, ring=None):
        ring = ring if ring is not None else K0
        return CurvePoint(FS.RR, ring(c[0]), y=ring(c[1]), ring=ring)

    DATA, E1, E2 = {}, {}, {}
    for c in GOOD:
        P = pt(c)
        DATA[c] = LHW.frob_data(P)
        al, bp = DATA[c][0], DATA[c][1]
        E1[c] = vector(K0, [al[i] for i in range(g)])
        E2[c] = vector(K0, [bp[j] - K0(QQ(LHW.beta_fil[j])) for j in range(g, n)])
    ok2 = True
    for c in GOOD:
        pred = Kh(LAM)*Kh(nn[c])*logG
        d = vz(E1[c][0] - K0(pred.lift() if pred != 0 else 0))
        if E1[c][0] == 0 and pred == 0:
            d = QQ(N + 4)
        info("u_0(%-17s) - Lambda * %2d * log_E(G)  has valuation %s"
             % (str(c), nn[c], d))
        if d < cert:
            ok2 = False
    check(ok2,
          "u_0(x) = Lambda log_E([xbar - bbar]) at all eight good rational "
          "points, to the certificate p^%d.  E090 checked the RATIOS of u_0 "
          "against the exact classes; this checks the ABSOLUTE value, so it "
          "tests Lambda and the port's Coleman integration against SageMath's "
          "formal group at once" % cert)

    print("(3) THE UNIT ROOT SPLITTING, IN THE PHASE-4 BASIS")
    F = FS.F
    Fp4 = matrix(K0, F).transpose()
    Ucols = [Fp4**cert * vector(K0, [K0(1) if i == k else K0(0)
                                     for i in range(n)])
             for k in range(g, n)]
    U = matrix(K0, Ucols).transpose()
    bot = U[g:n, :]
    check(vz(bot.determinant()) == 0,
          "the unit root subspace is complementary to Fil^1 (its lower g x g "
          "block is invertible): p = 13 is ORDINARY, which is what makes the "
          "unit root splitting exist at all")
    Un = U * bot.inverse()
    tau = Un[0:g, :].transpose()
    Uh = FS.FM.unit_root_subspace()
    Uh2 = matrix(K0, S4).transpose().inverse() * matrix(K0, Uh)
    bot2 = Uh2[g:n, :]
    tau2 = (Uh2 * bot2.inverse())[0:g, :].transpose()
    dcmp = min(vz(tau[i][j] - tau2[i][j]) for i in range(g) for j in range(g))
    check(dcmp >= cert - 2,
          "two independent routes to tau agree to p^%s: (phi^*)^cert on the "
          "last g phase-4 classes, and FrobeniusMatrix.unit_root_subspace "
          "pushed through the phase-4 change of basis" % dcmp)
    asym = min(vz(tau[i][j] - tau[j][i]) for i in range(g) for j in range(g))
    check(asym >= cert - 2,
          "tau is SYMMETRIC to p^%s, i.e. the unit root subspace is isotropic "
          "for the cup product: that is what makes B^U = B^W + tau a shift of "
          "a symmetric form by a symmetric one (E076 predicted it)" % asym)
    offs = [(0, 1), (0, 2), (1, 0), (2, 0)]
    off = min(vz(tau[i][j]) for i, j in offs)
    check(off >= cert - 2,
          "and tau is BLOCK DIAGONAL for sigma to p^%s -- no elliptic/Prym "
          "mixing -- because Frobenius commutes with sigma, so the unit root "
          "subspace is sigma-stable" % off)
    info("tau_00 (elliptic) = %s" % tau[0][0])
    info("tau_P   (Prym)    = %s" % [[str(tau[i][j]) for j in (1, 2)]
                                     for i in (1, 2)])

    print("(4) THE SPLITTING SHIFT, MEASURED")
    s1U = matrix(K0, n, n, lambda i, j:
                 (K0(1) if i == j else K0(0)) if (i < g and j < g)
                 else (-tau[i - g][j] if (i >= g and j < g) else K0(0)))
    s2U = matrix.identity(K0, n) - s1U
    LHU = LHW.with_splitting(s1=s1U, s2=s2U)
    THW, THU = {}, {}
    for c in GOOD:
        THW[c] = LHW._assemble(*DATA[c])
        THU[c] = LHU._assemble(*DATA[c])
    ok4 = True
    for c in GOOD:
        pred = E2[c] * (tau * E1[c])
        d = vz(THU[c] - THW[c] - pred)
        if d < cert:
            ok4 = False
        info("theta^U - theta^W - E_2^T tau E_1  at %-17s : valuation %s"
             % (str(c), d))
    check(ok4,
          "(*) holds at all eight good points to the certificate p^%d.  It is "
          "an identity in (14), so what it tests is the reading of E_1 and "
          "E_2 off alpha_phi and beta_phi -- E077's identification -- and the "
          "consistency of tau with them" % cert)
    check(vz(THU[P13] - THW[P13]) >= cert,
          "in particular theta is UNCHANGED at (-1,3), where E_2 = 0: the "
          "equation that gave c_3 does not depend on the splitting, which it "
          "must not, c_3 being an ell-adic local height")

    print("(5) THE BAD DISK, AND THE ACCOUNTING IN THE UNIT ROOT SPLITTING")
    Kx = CI.extension(EE)
    tp = tprec_for(P_GATE, N, EE)
    PzK = pt(BAD).change_ring(Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tp, ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    M, _, IP = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS.read_triv(IP.inverse()*M)
    gfz = LHW._fn_at(LHW.gamma_fil, PzK)
    THW[BAD] = LHW._assemble(alz, bpz, gpz, gfz)
    THU[BAD] = LHU._assemble(alz, bpz, gpz, gfz)
    E1[BAD] = vector(Kx, [alz[i] for i in range(g)])
    E2[BAD] = vector(Kx, [bpz[j] - Kx(QQ(LHW.beta_fil[j])) for j in range(g, n)])
    kmax = max(ZZ(FS.RR.J_range(a)[1])
               for a in [FS.h] + list(FS.g_vec) + list(FS.f))
    pv = prop46_precision(P_GATE, cert, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS.FM, "e_finite", 1)))
    info("theta at (0,0) by E091's iterated integral: e = %d, certified p^%s, "
         "measured floor p^%s  (%.0f s)"
         % (EE, pv, qp_floor(THW[BAD], EE), time.time() - t0))
    tauX = matrix(Kx, g, g, lambda i, j: Kx(tau[i][j]))
    dpred = E2[BAD] * (tauX * E1[BAD])
    dbad = THU[BAD] - THW[BAD]
    check(vz(dbad - dpred, EE) >= min(pv, qp_floor(dbad - dpred, EE)),
          "(*) holds at (0,0) too, where theta comes from the iterated "
          "integral of E091 and not from (23): valuation %s"
          % vz(dbad - dpred, EE))

    m2 = QQ(FS.Z[1][4])
    d1 = Kx(THU[P13] - THW[P13])
    d2 = Kx(THU[P26] - THW[P26])
    d4 = dbad
    res = d4 + d2/Kx(3) - d1
    flo = min(qp_floor(res, EE), qp_floor(d4, EE))
    check(vz(res, EE) >= min(pv, flo),
          "Delta theta_4 + (1/3) Delta theta_2 - Delta theta_1 = 0 to p^%s: "
          "D -- and with it c_2 = -(3/4)D and c_3 -- does NOT move when the "
          "splitting does.  THIS IS THE SHARP CHECK: the shift at (0,0) comes "
          "from the bad-disk iterated integral and the shift at (-2,6) from a "
          "good-point one, and tau ties them together through Frobenius alone"
          % vz(res, EE))

    def acc(TH):
        c3 = -Kx(TH[P13])
        H1 = (Kx(TH[P13]) + Kx(TH[P26]) - Kx(TH[BAD])) / Kx(QQ(m2))
        c2 = Kx(QQ(3*m2/4))*H1 - Kx(TH[P26])
        return c3, H1, c2
    c3W, H1W, c2W = acc(THW)
    c3U, H1U, c2U = acc(THU)
    check(vz(c3U - c3W, EE) >= min(pv, qp_floor(c3U - c3W, EE))
          and vz(c2U - c2W, EE) >= min(pv, qp_floor(c2U - c2W, EE)),
          "c_3 and c_2 come out the SAME in both splittings, as ell-adic "
          "local heights must")
    kapP = vector(Kx, [Kx(E1[SIGB][i]) for i in (1, 2)])
    tauP = matrix(Kx, 2, 2, lambda i, j: Kx(tau[i + 1][j + 1]))
    dH1p = kapP * (tauP * kapP)
    dH1m = H1U - H1W
    check(vz(dH1m - dH1p, EE) >= min(pv, qp_floor(dH1m - dH1p, EE)),
          "and H_1 moves by exactly kappa'^T tau_P kappa', the shift B^U = "
          "B^W + tau predicts for hhat_P(kappa'): valuation %s"
          % vz(dH1m - dH1p, EE))
    info("H_1^W (E093's number) = %s" % H1W)
    info("H_1^U (unit root)     = %s" % H1U)

    print("(6) B_11, AND H_2")
    u0 = E1[P11][0]
    v0 = E2[P11][0]
    NU = QQ(os.environ.get("E094_NU", 1))
    u0G = Kh(LAM)*logG
    B11U = Kh(NU)*hG/(u0G**2)
    info("nu = %s (SageMath's height taken as THE Coleman-Gross height)" % NU)
    info("u_0(G) = Lambda log_E(G) = %s" % u0G)
    info("B_11^U = nu h_Sage(G) / u_0(G)^2 = %s" % B11U)
    B11W = B11U - Kh(tau[0][0].lift() if hasattr(tau[0][0], 'lift')
                     else tau[0][0])
    info("B_11^W = B_11^U - tau_00           = %s" % B11W)
    check(vz(u0*v0) < cert,
          "u_0 v_0 at (-1/11) has valuation %s, so B_11 does not drop out of "
          "equation 3" % vz(u0*v0))
    B11x = Kx(K0(B11U.lift(), B11U.precision_absolute()))
    H2U = Kx(4)*(Kx(THU[P11]) - B11x*Kx(u0*v0))/Kx(QQ(m2)) + H1U
    info("H_2^U = (4/m_2)(theta_3^U - B_11 u_0 v_0) + H_1^U = %s" % H2U)
    rat = H2U/H1U
    info("H_2^U / H_1^U = %s" % rat)
    info("valuations: H_1^U = %s, H_2^U = %s, ratio = %s"
         % (vz(H1U, EE), vz(H2U, EE), vz(rat, EE)))
    check(True,
          "Phase 5's four unknowns in the unit root splitting: a = H_1^U and "
          "c = H_2^U are now numbers, B_11 is imported, and b = "
          "<kappa', delta_11>_P is (B5) and appears in no equation")

    print("(7) NEGATIVE CONTROLS, AND WHAT IS NOT CHECKED")
    noise = min(pv, qp_floor(H2U, EE))

    def shifted(B):
        return Kx(4)*(Kx(THU[P11]) - B*Kx(u0*v0))/Kx(QQ(m2)) + H1U
    dnu = shifted(Kx(2)*B11x) - H2U
    check(vz(dnu, EE) <= vz(H2U, EE) and vz(dnu, EE) < noise,
          "nu -> 2nu moves H_2 at its own leading digit (valuation %s against "
          "%s, noise p^%s): the ONE unmatched normalisation is not a rounding "
          "error, it changes the answer"
          % (vz(dnu, EE), vz(H2U, EE), noise))
    B11Wx = Kx(K0(B11W.lift(), B11W.precision_absolute()))
    dsp = shifted(B11Wx) - H2U
    check(vz(dsp, EE) < noise,
          "and feeding the system B_11^W -- Sage's height WITHOUT the tau_00 "
          "correction, which is what E093's numbers would have taken -- moves "
          "H_2 by a term of valuation %s, one digit below the leading one and "
          "well above the noise p^%s.  So the splitting match of group (4) is "
          "not cosmetic: skipping it would have put a wrong H_2 into E096"
          % (vz(dsp, EE), noise))
    dlam = shifted(Kx(K0((Kh(NU)*hG/((Kh(2*LAM)*logG)**2)).lift()))) - H2U
    check(vz(dlam, EE) < noise,
          "and Lambda -> 2 Lambda moves it too.  Lambda is EXACT (group 1) and "
          "nu is NOT: nu is inherited from SageMath's normalisation "
          "convention, no computation in this project constrains it, and a "
          "factor 2 there propagates undetected into E096")
    info("what group (4) DOES check is the splitting, and it checks it three "
         "ways -- (*) pointwise at nine points, the invariance of c_3 and "
         "c_2, and the predicted shift of H_1.  What it cannot check is a "
         "quantity that enters only through Sage.")

    print("=" * 72)
    print("E094 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
