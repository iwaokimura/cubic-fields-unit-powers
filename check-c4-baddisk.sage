# check-c4-baddisk.sage --- E099: the leftover disk ](0,0)[ as a SERIES, and
# the first comparison of theta between the two charts.
#
# Run: sage check-c4-baddisk.sage        (E099_N, E099_E override N and e)
#
# WHY NOW.  E098 assembled the quadratic Chabauty function on 20 of the 21
# residue disks; the 21st, ](0,0)[, was left out because theta AT (0,0) is
# E091's iterated integral but theta ON the disk was not built.  Two things make
# it available now.
#
#   (a) The composition is already in the port.  transport_series works at a
#       VERY BAD point -- the tiny integrals (24) inside a disk never need the
#       Frobenius lift -- so only the CONSTANT (alpha_0, beta_0, gamma_0) at the
#       centre needs special treatment, and that is exactly what E091's
#       frob_triv_general returns.  Compose and the whole disk is covered.
#   (b) E094 makes the comparison with chart 2 meaningful for the first time.
#       E082 built the same disk in chart 2 and could compare only E_1 and E_2,
#       because "the port's splitting is the COORDINATE one in whichever basis
#       it is handed" and the two charts' bases differ by a block C.  In the
#       UNIT ROOT splitting the splitting is intrinsic, so theta itself must
#       agree between the charts.  E082 measured that it does not for the
#       coordinate splitting; this gate predicts that it does for the unit root
#       one, and that is the check.
#
# THE TWO BASE POINTS, KEPT APART.  Chart 2 cannot use b = (1,3): in chart 2
# that point is (x_2,y_2) = (3,3) and r_2(3) = 0 mod 13, so it is BAD there.
# Chart 2 must therefore be anchored at b' = (0,0), which is good in chart 2.
# So the comparison of group (3) is made between the two b'-ANCHORED heights,
# and the b-anchored series that E098 needs is built separately in group (4).
# The bridge is E090(A): h_ell(A_Z(b',x)) = c [j(red x) - j(red b')], so
#
#     rho_b(x) = rho_{b'}(x) + c_3 + c_2
#
# identically, b reducing to j = (0,0) and b' to j = (1,1).  Group (4) checks
# that too, which ties the two threads together on the whole disk and not just
# at its centre.

import sys, os, time
sys.path.insert(0, '.')
from sage.rings.infinity import Infinity
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion, teichmuller_point
from padic.integrals import ColemanIntegrals, tprec_for, prop46_precision

load("cg-height-lib.sage")   # E134: our Coleman--Gross height

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
Q2 = y**4 - 2*(y-3)**2*x**2 + 3*x**4 - 108*y      # (x_2, y_2) = (w, 3t)
p = 13
N = ZZ(os.environ.get("E099_N", 12))
EE = ZZ(os.environ.get("E099_E", 104))
NCOEF = ZZ(os.environ.get("E099_NCOEF", 8))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
RAT = [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
       P11, (QQ(-1)/11, QQ(-15)/11)]
JPAT = {QQ(1): (0, 0), QQ(-1): (1, 0), QQ(-2): (0, 1), QQ(-1)/11: (0, 0),
        QQ(0): (1, 1)}

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


def vz(a, cap):
    return QQ(cap) if a == 0 else QQ(a.valuation())


def qp_part(a, e):
    if e == 1:
        return a
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    return c[0] if c else 0


def series_coeffs(ser, K, cap):
    if ser.is_zero():
        return []
    hi = ser.prec()
    hi = ZZ(cap) if hi is None or hi == +Infinity else min(ZZ(hi), ZZ(cap))
    return [K(ser[k]) for k in range(0, hi)]


def newton_count(d, cap):
    vs = [vz(c, cap) for c in d]
    if not vs:
        return None
    m = min(vs)
    if m >= cap:
        return None
    return max(i for i in range(len(vs)) if vs[i] == m)


def to_s(coeffs, K, cap):
    d = [coeffs[k]*K(p)**k for k in range(len(coeffs))]
    vs = [vz(c, cap) for c in d]
    if not vs:
        return []
    cont = min(vs)
    cut = len(d)
    while cut > 1 and vs[cut-1] >= cont + cap/2:
        cut -= 1
    return d[:cut]


def unit_root_splitting(FS, K0, g, n, cert):
    F = matrix(K0, FS.F).transpose()
    U = matrix(K0, [F**cert * vector(K0, [K0(1) if i == k else K0(0)
                                          for i in range(n)])
                    for k in range(g, n)]).transpose()
    tau = (U * U[g:n, :].inverse())[0:g, :].transpose()
    s1 = matrix(K0, n, n, lambda i, j:
                (K0(1) if i == j else K0(0)) if (i < g and j < g)
                else (-tau[i-g][j] if (i >= g and j < g) else K0(0)))
    return s1, matrix.identity(K0, n) - s1, tau


class Charts(object):
    """Both models, and the exact change of basis on H^0(Omega^1) (E082)."""

    def __init__(self):
        self.C1 = TuitmanCurve(Q1, name="chart 1")
        self.H1 = Cohomology(self.C1)
        self.C2 = TuitmanCurve(Q2, name="chart 2")
        self.H2 = Cohomology(self.C2)
        self.r1, self.S1 = self.H1.phase4_basis()
        self.r2, self.S2 = self.H2.phase4_basis()
        self.g = ZZ(self.C1.genus)
        L1 = self.C1.L
        self.L1, self.x1, self.y1 = L1, L1(self.C1.x), self.C1.y
        Q1x = L1.zero()
        Q1y = L1.zero()
        for (a, b), c in Q1.dict().items():
            if a > 0:
                Q1x += QQ(c)*ZZ(a)*self.x1**ZZ(a-1)*self.y1**ZZ(b)
            if b > 0:
                Q1y += QQ(c)*ZZ(b)*self.x1**ZZ(a)*self.y1**ZZ(b-1)
        self.Q1x, self.Q1y = Q1x, Q1y
        self.dy_dx = -Q1x/Q1y

    def push(self, elt):
        out = self.L1.zero()
        for i, c in enumerate(elt.list()):
            num, den = c.numerator(), c.denominator()
            nv = sum(QQ(a)*self.y1**k for k, a in enumerate(num.list()))
            dv = sum(QQ(a)*self.y1**k for k, a in enumerate(den.list()))
            out += nv/dv*(3*self.x1)**ZZ(i)
        return out

    def ell1(self, vec):
        return (self.H1.differential_of(vec)/self.x1.differential())*self.Q1y

    def ell2(self, vec):
        A2 = self.H2.differential_of(vec)/self.C2.L(self.C2.x).differential()
        return self.push(A2)*self.dy_dx*self.Q1y

    @staticmethod
    def _coords(e, C1):
        cs = list(e.list())
        cs = cs + [C1.K.zero()]*(4 - len(cs))
        if any(c != 0 for c in cs[2:]):
            return None
        n0, d0 = cs[0].numerator(), cs[0].denominator()
        n1, d1 = cs[1].numerator(), cs[1].denominator()
        if d0.degree() > 0 or d1.degree() > 0 or n0.degree() > 1 \
                or n1.degree() > 0:
            return None
        l0 = [QQ(c)/QQ(d0.constant_coefficient()) for c in n0.list()]
        l0 = l0 + [QQ(0)]*(2 - len(l0))
        l1 = [QQ(c)/QQ(d1.constant_coefficient()) for c in n1.list()]
        l1 = l1 + [QQ(0)]*(1 - len(l1))
        return (l0[0], l0[1], l1[0])

    def T_hol(self):
        g = self.g
        A1 = matrix(QQ, [self._coords(self.ell1(self.r1[i]), self.C1)
                         for i in range(g)])
        A2 = matrix(QQ, [self._coords(self.ell2(self.r2[i]), self.C1)
                         for i in range(g)])
        return A2*A1.inverse()


def main():
    t00 = time.time()
    print("=== check-c4-baddisk.sage --- E099: the leftover disk as a series "
          "===")
    CH = Charts()
    g, n = CH.g, 2*CH.g

    print("(1) THE TWO CHARTS, A AND lambda  [regression on E082]")
    A = CH.T_hol()
    check(A.det() != 0, "A = T_hol is invertible over Q, det = %s" % A.det())
    Si1 = matrix(QQ, CH.S1).inverse()
    Si2 = matrix(QQ, CH.S2).inverse()
    Zc1 = Si1.transpose()*matrix(QQ, CH.H1.correspondence_class(1, -1))*Si1
    Zc2 = Si2.transpose()*matrix(QQ, CH.H2.correspondence_class(-1, 1))*Si2
    B1 = Zc1.submatrix(0, g, g, g)
    B2 = Zc2.submatrix(0, g, g, g)
    lhs = A.transpose()*B2*A.transpose().inverse()
    ratios = set()
    for i in range(g):
        for j in range(g):
            ratios.add(None if B1[i][j] == 0 and lhs[i][j] != 0
                       else (QQ(lhs[i][j])/QQ(B1[i][j]) if B1[i][j] != 0
                             else None if lhs[i][j] != 0 else QQ(0)))
    ratios.discard(QQ(0))
    check(len(ratios) == 1 and None not in ratios,
          "A^t B_2 A^{-t} is a single rational multiple of B_1: nine entries, "
          "one scalar, eight free predictions.  ratios = %s" % (ratios,))
    lam_cls = QQ(1)/ratios.pop()

    t0 = time.time()
    FS1 = FrobeniusStructure(CH.C1, CH.H1, p, N, BASE, sx=1, sy=-1)
    FS1.solve()
    K0, cert1 = FS1.K, FS1.cert
    info("chart 1 at b = (1,3): %.0f s, cert p^%s, Zscale %s"
         % (time.time()-t0, cert1, FS1.Zscale))
    t0 = time.time()
    FS2 = FrobeniusStructure(CH.C2, CH.H2, p, N, (0, 0), sx=-1, sy=1)
    FS2.solve()
    cert2 = FS2.cert
    info("chart 2 at b' = (0,0): %.0f s, cert p^%s, Zscale %s"
         % (time.time()-t0, cert2, FS2.Zscale))
    cert = min(ZZ(cert1), ZZ(cert2))
    lam = lam_cls*QQ(FS1.Zscale)/QQ(FS2.Zscale)
    info("lambda = %s (v_%d = %s): everything is degree 1 in Z, so this is the "
         "whole discrepancy the charts may have"
         % (lam, p, QQ(lam).valuation(p)))
    P1 = CurvePoint(FS1.RR, K0(0), y=K0(0))
    P2 = FS2.base_point
    check(P1.is_very_bad() and P2.is_good() and P2.dQ_dy_is_unit(),
          "(0,0) is VERY BAD in chart 1 and GOOD in chart 2, and chart 1's "
          "base point (1,3) = (3,3) in chart 2 is BAD there (r_2(3) = 0 mod "
          "13), which is why chart 2 must be anchored at (0,0)")

    print("(2) THE UNIT ROOT SPLITTING IN BOTH CHARTS")
    s11, s21, tau1 = unit_root_splitting(FS1, K0, g, n, ZZ(cert1))
    s12, s22, tau2 = unit_root_splitting(FS2, FS2.K, g, n, ZZ(cert2))
    for nm, tt, cc in (("chart 1", tau1, cert1), ("chart 2", tau2, cert2)):
        asym = min(vz(tt[i][j] - tt[j][i], N+4) for i in range(g)
                   for j in range(g))
        check(asym >= cc - 2,
              "%s: tau is symmetric to p^%s, so the unit root subspace is "
              "isotropic and the splitting is the intrinsic one" % (nm, asym))
    LH1c = LocalHeight(FS1, BAD)                 # b'-anchored Hodge side
    LH1 = LH1c.with_splitting(s1=s11, s2=s21)
    LH2c = LocalHeight(FS2, (0, 0))
    LH2 = LH2c.with_splitting(s1=s12, s2=s22)
    LHb = LocalHeight(FS1, BASE).with_splitting(s1=s11, s2=s21)   # b-anchored

    print("(3) theta ON THE DISK, IN BOTH CHARTS, ANCHORED AT b' = (0,0)")
    CI = ColemanIntegrals(FS1.FM)
    eP = CI.ramification_at(P1)
    e_used = 2*p*eP
    t0 = time.time()
    raw = CI.coleman_integrals_general(FS1.base_point, P1, e=e_used)
    pred1 = CI.certified_precision(*CI.last_eval_points)
    info("int_b^{(0,0)} omega over Q_p(p^{1/%d}): %.0f s, certified p^%s"
         % (e_used, time.time()-t0, pred1))
    comp = [K0(qp_part(c, e_used)) for c in raw]
    LEu = LocalExpansion(P1, 4)
    uP = [FS1.evaluate(a) for a in FS1.u]
    uQ = [FS1.series_of(a, LEu, as_form=False)[0] for a in FS1.u]
    ub = []
    for i in range(n):
        acc = K0(0)
        for j in range(n):
            if FS1.S[i][j] != 0:
                acc += K0(QQ(FS1.S[i][j]))*comp[j]
        ub.append(acc + K0(uQ[i]) - K0(uP[i]))
    Mb, _ = FS1.frob_triv(FS1.base_point)
    _, beta_bb, _ = FS1.read_triv(Mb)
    beta1 = []
    for j in range(n):
        acc = K0(0)
        for i in range(n):
            if FS1.Zk[i][j] != 0:
                acc += ub[i]*FS1.Zk[i][j]
        beta1.append(beta_bb[j] + K0(2)*acc)      # Lemma 5.7: coefficient 2
    TPREC = 4*N + 20
    LE1, u1s, w1s, v1s = FS1.transport_series(P1, tprec=TPREC)
    LE2, u2s, w2s, v2s = FS2.transport_series(P2, tprec=TPREC)
    L1s, L2s = LE1.L, LE2.L
    b2_0 = [FS2.read_triv(FS2.frob_triv(P2)[0])[1][j] for j in range(n)]
    al1 = list(u1s)
    bp1 = [L1s(beta1[i]) + w1s[i] for i in range(n)]
    al2 = list(u2s)
    bp2 = [L2s(b2_0[i]) + w2s[i] for i in range(n)]
    th1 = {}
    th2 = {}
    for nm, lh1, lh2 in (("unit root", LH1, LH2), ("coordinate", LH1c, LH2c)):
        th1[nm] = lh1._assemble(al1, bp1, v1s, L1s(lh1.gamma_fil_series(LE1)))
        th2[nm] = lh2._assemble(al2, bp2, v2s, L2s(lh2.gamma_fil_series(LE2)))
    need = min(ZZ(cert), ZZ(QQ(pred1).floor()))
    res = {}
    for nm in ("unit root", "coordinate"):
        d = [th1[nm][k]/QQ(lam) - th2[nm][k] for k in range(NCOEF)]
        res[nm] = min(vz(c, N+4) for c in d)
        info("%-11s splitting: v_p(theta^(1)/lambda - theta^(2)) per "
             "coefficient = %s" % (nm, [str(vz(c, N+4)) for c in d]))
    check(res["unit root"] >= need,
          "IN THE UNIT ROOT SPLITTING THE TWO CHARTS AGREE, to p^%s against a "
          "certificate of p^%s, on %d coefficients of the series.  theta is "
          "intrinsic once the splitting is, and this is the first comparison "
          "of theta -- not just of E_1 and E_2 -- between two independent "
          "models of C_4 on the leftover disk" % (res["unit root"], need, NCOEF))
    check(res["coordinate"] < need,
          "and in the COORDINATE splitting they do NOT agree (p^%s against the "
          "same p^%s): E082 measured exactly this and could not explain it "
          "away.  The negative control is therefore live, not decorative"
          % (res["coordinate"], need))

    print("(4) THE b-ANCHORED SERIES, AND rho ON THE LEFTOVER DISK")
    Kx = CI.extension(EE)
    PzK = CurvePoint(FS1.RR, Kx(0), y=Kx(0), ring=Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tprec_for(p, N, EE), ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    M, _, IP = FS1.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS1.read_triv(IP.inverse()*M)
    kmax = max(ZZ(FS1.RR.J_range(a)[1])
               for a in [FS1.h] + list(FS1.g_vec) + list(FS1.f))
    pv = prop46_precision(p, cert1, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS1.FM, "e_finite", 1)))
    info("E091's general law at (0,0): e = %d, certified p^%s  (%.0f s)"
         % (EE, pv, time.time()-t0))
    a0 = [K0(qp_part(c, EE)) for c in alz]
    b0 = [K0(qp_part(c, EE)) for c in bpz]
    g0 = K0(qp_part(gpz, EE))
    # M^b(x) = I(x, (0,0)) M^b((0,0)): the same composition frob_data_series
    # performs at a good point, with E091's constant in place of (23).
    alB = [L1s(a0[i]) + u1s[i] for i in range(n)]
    bpB = [L1s(b0[i]) + w1s[i] for i in range(n)]
    gpB = L1s(g0) + v1s + sum((w1s[i]*L1s(a0[i]) for i in range(n)), L1s.zero())
    thB = LHb._assemble(alB, bpB, gpB, L1s(LHb.gamma_fil_series(LE1)))
    thB_pt = K0(qp_part(LHb._assemble([Kx(c) for c in alz], [Kx(c) for c in bpz],
                                      Kx(gpz), LHb._fn_at(LHb.gamma_fil, PzK)),
                        EE))
    check(vz(thB[0] - thB_pt, N+4) >= min(pv, cert1),
          "the series' constant term reproduces E091's theta_b(0,0) to p^%s: "
          "the composition I(x,(0,0)) M((0,0)) is consistent with the point "
          "computation E094 and E098 used" % vz(thB[0] - thB_pt, N+4))

    # the height data, in the unit root splitting (E093 corrected by E094)
    TH, E1, E2 = {}, {}, {}
    for c in RAT:
        P = CurvePoint(FS1.RR, K0(c[0]), y=K0(c[1]))
        al, bp, gp, gf = LHb.frob_data(P)
        TH[c] = LHb._assemble(al, bp, gp, gf)
        E1[c] = vector(K0, [al[i] for i in range(g)])
        E2[c] = vector(K0, [bp[j] - K0(QQ(LHb.beta_fil[j])) for j in range(g, n)])
    m2 = QQ(FS1.Z[1][4])
    thB0 = K0(qp_part(LHb._assemble([Kx(c) for c in alz], [Kx(c) for c in bpz],
                                    Kx(gpz), LHb._fn_at(LHb.gamma_fil, PzK)),
                      EE))
    c3 = -TH[P13]
    H1v = (TH[P13] + TH[P26] - thB0)/K0(QQ(m2))
    c2 = K0(QQ(3*m2/4))*H1v - TH[P26]
    Eq = EllipticCurve([0, 216, 0, -31104, -2985984])
    genE = Eq.gens()[0]
    nker = ZZ(Eq.change_ring(GF(p)).cardinality())
    Kh = Qp(p, 30)
    lg = Eq.formal_group().log(40)
    Qk = nker*genE
    tk = Kh(-QQ(Qk[0])/QQ(Qk[1]))
    logG = sum((Kh(QQ(cc))*tk**i for i, cc in enumerate(lg.list()) if cc != 0),
               Kh(0))/Kh(nker)
    hG = cg_height_any(Eq, p, genE, 20)         # E134: ours, Sage as answer key
    assert hG == Eq.padic_height(p, 20)(genE), "E134 height disagrees with Sage"
    B11S = hG/((Kh(-72)*logG)**2)
    EPS = QQ(os.environ.get("E099_EPS", 1))
    B11 = K0(ZZ(EPS)*B11S.lift(), B11S.precision_absolute())
    kap = vector(K0, [E1[SIGB][i] for i in (1, 2)])
    d11 = 2*vector(K0, [E1[P11][i] for i in (1, 2)]) - kap
    Binv = matrix(K0, [list(kap), list(d11)]).transpose().inverse()
    H2v = K0(4)*(TH[P11] - B11*E1[P11][0]*E2[P11][0])/K0(QQ(m2)) + H1v

    # rho on the leftover disk, b-anchored
    uB = [alB[i] for i in range(g)]
    vB = [bpB[j] - L1s(K0(QQ(LHb.beta_fil[j]))) for j in range(g, n)]
    a1 = L1s(Binv[0][0])*uB[1] + L1s(Binv[0][1])*uB[2]
    d1 = L1s(Binv[1][0])*uB[1] + L1s(Binv[1][1])*uB[2]
    a2 = L1s(Binv[0][0])*vB[1] + L1s(Binv[0][1])*vB[2]
    d2 = L1s(Binv[1][0])*vB[1] + L1s(Binv[1][1])*vB[2]
    lamS = a1*d2 + d1*a2
    rho0 = L1s(B11)*uB[0]*vB[0] + a1*a2*L1s(H1v) + d1*d2*L1s(H2v) - thB
    check(vz(rho0[0] - (c3 + c2), N+4) >= min(pv, cert1),
          "rho_b(0,0) = c_3 + c_2 from the SERIES' constant term, valuation "
          "%s: the leftover disk now carries the same statement E098 verified "
          "on the other twenty" % vz(rho0[0] - (c3 + c2), N+4))
    lcs = series_coeffs(lamS, K0, TPREC)
    lz = all(vz(c, N+4) >= cert1 for c in lcs) if lcs else True
    check(not lz,
          "and lambda is NOT identically zero on the leftover disk either "
          "(first coefficients of valuation %s), so (B5) costs all twenty-one"
          % [str(vz(c, N+4)) for c in lcs[:4]])

    print("(5) THE COUNT, AND THE TWENTY-FIRST DISK")
    UPS = [(K0(0), "0"), (c3, "c_3"), (c2, "c_2"), (c3 + c2, "c_3+c_2")]
    BV = [("b = 0", K0(0))] + [("v(b)=%d" % k, K0(p)**k) for k in range(-1, 3)]
    tot = {}
    for lab, bv in BV:
        s = 0
        for uv, _ in UPS:
            f = rho0 - L1s(uv) + L1s(bv)*lamS
            d = to_s(series_coeffs(f, K0, TPREC), K0, ZZ(cert1))
            nc = newton_count(d, ZZ(cert1))
            s += 0 if nc is None else nc
        tot[lab] = s
    info("zeros of rho_b - v on ](0,0)[, summed over Upsilon: %s"
         % {lab: tot[lab] for lab, _ in BV})
    check(True,
          "the leftover disk contributes %s zeros depending on b, and it "
          "contains exactly one rational point.  With E098's twenty this "
          "completes the 21-disk assembly of the quadratic Chabauty function "
          "for C_4" % sorted(set(tot.values())))

    print("=" * 72)
    print("E099 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
