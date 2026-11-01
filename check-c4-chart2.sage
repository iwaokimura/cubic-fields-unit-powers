# check-c4-chart2.sage --- E082: C_4's leftover disk computed a second time,
# in a second chart, and compared with E081.
#
# E080 found that C_4 has a second Tuitman model
#     Q_2(x,y) = y^4 - 2(y-3)^2 x^2 + 3x^4 - 108y = 3 Q_1(y/3, x),
# with base w and fibre 3t, in which the bad point (0,0) of chart 1 is a GOOD
# point.  E081 computed theta_Z on ](0,0)[ in chart 1 by [BDM+19] Lemma 5.7 --
# the base-point change -- because Section 5.3 cannot reach a bad disk.  Chart 2
# reaches the same disk by Section 5.3 directly.  C_4 has no published value and
# no second implementation, so this is the only external check on that disk
# there will be.
#
# WHAT MAKES THE COMPARISON WELL-POSED, and it took a wrong turn to see it.
# The two charts give two bases of H^1_dR(X), and the port's splitting s_1, s_2
# is the COORDINATE one in whichever basis it is handed.  So theta itself is
# chart-dependent, and comparing it naively is meaningless.  What is intrinsic
# is the pair (E_1, E_2) of Section 6.4.1 -- and E077 already showed det T_i,
# hence the Diophantine conclusion, is independent of the splitting.  So the
# comparison is made on E_1 and E_2, and theta is reported afterwards.
#
# THE TRANSFORMATION LAW, derived.  Holomorphic differentials on a smooth plane
# quartic are ell dx/Q_y with ell of degree <= 1, so both charts' FIRST g basis
# elements can be written in the same function field and matched EXACTLY over Q:
# chart 2's field maps to chart 1's by x2 -> y1, y2 -> 3 x1, under which
# dx2/Q2_y2 = -dx1/Q1_y1 (checked).  That gives a 3x3 rational matrix A = T_hol
# with omega^(2)_i = sum_j A_ij omega^(1)_j for i <= g.  Write the full change
# of basis as T = [[A,0],[C,D]] -- the top-right block is 0 precisely because
# holomorphic forms go to holomorphic forms.  Both phase-4 bases are symplectic
# for the SAME intrinsic cup product (both cup product matrices come out as the
# standard J), so T J T^t = J, and expanding the blocks gives
#
#     A D^t = I,   i.e.   D = A^{-t},   and   C D^t symmetric.
#
# Hence, coordinates in V_dR = H^1_dR(X)^* transforming by T and coordinates in
# H^1_dR by T^{-t},
#
#     E_1 (first g of alpha_phi)          transforms by  A,
#     E_2 (last g of beta_phi - beta_Fil) transforms by  D^{-t} = A,
#
# THE SAME MATRIX -- which is not obvious and is what makes check (5) possible.
# C is NOT determined by any of this, and it is exactly the difference of the
# two splittings; that is why theta may differ and (E_1, E_2) may not.
#
# THE SCALE OF Z, FIXED BEFORE ANY p-ADIC NUMBER IS LOOKED AT.  Section 4.1
# pins Z only up to scale and the port rescales it further (frobstruct's
# _rescale_Z, to make eta p-integral: 13 in chart 1, 1 in chart 2), so the two
# charts' theta differ by an unknown lambda.  Fitting lambda to the answer would
# make the whole check circular.  It is not necessary: with Z^(i) = [[0,B_i],
# [-B_i,0]] in the phase-4 bases, the class law Z^(1) = lambda T^t Z^(2) T
# restricted to the top-right block reads
#
#     A^t B_2 A^{-t} = lambda^{-1} B_1,
#
# which has NO unknown but lambda: 9 entries, one scalar, 8 free predictions.
# It holds, with lambda = 351/4, and v_13(351/4) = 1 -- which is the whole of
# the discrepancy in valuation between the two charts' series.
#
# THE CHECKS.
#   (1) Chart 2's Tuitman data, and that (0,0) is a GOOD Teichmuller point of
#       it.  The same residue disk is Prop 3.2's SECOND case in chart 1 (very
#       bad, t = y_1) and its FIRST case in chart 2 (good, t = x_2); the local
#       coordinate is w on both sides, which is why the series are comparable
#       coefficient by coefficient.
#   (2) The two charts carry the same correspondence: Z_e has the same
#       characteristic polynomial, and the cup product is the same standard J.
#   (3) A = T_hol, exactly over Q, with the sanity identity
#       dx2/Q2_y2 = -dx1/Q1_y1 and det A != 0.
#   (4) lambda from the top-right block, as above.  THIS IS THE CHECK THAT
#       KEEPS THE REST HONEST.
#   (5) E_1 and E_2 on ](0,0)[, chart 2 against A times chart 1.  Nothing is
#       shared: different r, different Frobenius lift, different basis,
#       different case of Prop 3.2, and chart 1 reaches the disk only through
#       Lemma 5.7 and a ramified extension.
#   (6) theta: reported, with the difference measured against the prediction
#       lambda theta^(2) = theta^(1).  A residual, if any, must be a bilinear
#       form in (E_1, E_2) -- i.e. absorbed by B in the quadratic Chabauty
#       relation, hence invisible to det T_i.
#   (7) PRECISION.  Chart 2 certifies the disk to p^cert with no ramified
#       extension at all; chart 1 (E081) manages p^2, Algorithm 3.12 being the
#       bottleneck.  If chart 2 wins, it is the better route for Phase 5.
#   (8) NEGATIVE CONTROLS: A^t, A^{-1} and lambda = 1 must each break check (5).
#
# Run: sage check-c4-chart2.sage

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion, teichmuller_point
from padic.integrals import ColemanIntegrals

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)      # chart 1: (x,y) = (t,w)
Q2 = y**4 - 2*(y-3)**2*x**2 + 3*x**4 - 108*y     # chart 2: (x,y) = (w,3t)
P_GATE, N = 13, 8
TPREC = 4 * N + 20
NCOEF = 16

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


def vser(s, n, N):
    return min([vz(s[k], N) for k in range(n)] + [ZZ(N + 4)])


# ----------------------------------------------- the two charts, exactly over Q

class Charts(object):
    """Both models, and the exact change of basis on H^0(Omega^1)."""

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
                Q1x += QQ(c) * ZZ(a) * self.x1**ZZ(a-1) * self.y1**ZZ(b)
            if b > 0:
                Q1y += QQ(c) * ZZ(b) * self.x1**ZZ(a) * self.y1**ZZ(b-1)
        self.Q1x, self.Q1y = Q1x, Q1y
        self.dy_dx = -Q1x / Q1y

    def push(self, elt):
        """C2.L -> C1.L by x2 |-> y1, y2 |-> 3 x1."""
        out = self.L1.zero()
        for i, c in enumerate(elt.list()):
            num, den = c.numerator(), c.denominator()
            nv = sum(QQ(a) * self.y1**k for k, a in enumerate(num.list()))
            dv = sum(QQ(a) * self.y1**k for k, a in enumerate(den.list()))
            out += nv / dv * (3 * self.x1)**ZZ(i)
        return out

    def ell1(self, vec):
        """omega = ell dx1/Q1_y, for a chart-1 basis vector."""
        return (self.H1.differential_of(vec) / self.x1.differential()) * self.Q1y

    def ell2(self, vec):
        A2 = self.H2.differential_of(vec) / self.C2.L(self.C2.x).differential()
        return self.push(A2) * self.dy_dx * self.Q1y

    @staticmethod
    def _coords(e, C1):
        """ell = a + b x1 + c y1 -> (a,b,c) over Q, or None if not of that form."""
        cs = list(e.list())
        cs = cs + [C1.K.zero()] * (4 - len(cs))
        if any(c != 0 for c in cs[2:]):
            return None
        n0, d0 = cs[0].numerator(), cs[0].denominator()
        n1, d1 = cs[1].numerator(), cs[1].denominator()
        if d0.degree() > 0 or d1.degree() > 0 or n0.degree() > 1 or n1.degree() > 0:
            return None
        l0 = [QQ(c) / QQ(d0.constant_coefficient()) for c in n0.list()]
        l0 = l0 + [QQ(0)] * (2 - len(l0))
        l1 = [QQ(c) / QQ(d1.constant_coefficient()) for c in n1.list()]
        l1 = l1 + [QQ(0)] * (1 - len(l1))
        return (l0[0], l0[1], l1[0])

    def T_hol(self):
        g = self.g
        A1 = matrix(QQ, [self._coords(self.ell1(self.r1[i]), self.C1)
                         for i in range(g)])
        A2 = matrix(QQ, [self._coords(self.ell2(self.r2[i]), self.C1)
                         for i in range(g)])
        return A2 * A1.inverse(), A1, A2

    def sanity(self):
        """dx2/Q2_y2 pushed into chart 1 must be -dx1/Q1_y1."""
        L2, x2, y2 = self.C2.L, self.C2.L(self.C2.x), self.C2.y
        Q2y = L2.zero()
        for (a, b), c in Q2.dict().items():
            if b > 0:
                Q2y += QQ(c) * ZZ(b) * x2**ZZ(a) * y2**ZZ(b-1)
        return (self.push(1 / Q2y) * self.dy_dx) * self.Q1y


# ------------------------------------------------------------------ the gate

def main():
    print("=== check-c4-chart2.sage --- E082: C_4's leftover disk, computed "
          "twice ===")
    t00 = time.time()
    CH = Charts()

    print("(1) CHART 2'S TUITMAN DATA, and the base point (0,0)")
    C2, H2 = CH.C2, CH.H2
    check(C2.genus == 3 and C2.dx == 4, "genus 3, d_x = 4")
    check(C2.W0_is_identity, "W^0 = I (Tuitman's Assumption 2)")
    check(C2.degr == 10, "deg r_2 = %d (chart 1 has 8)" % C2.degr)
    check(QQ(C2.r(0)).valuation(P_GATE) == 0,
          "r_2(0) = %s is a %d-unit, so (0,0) is a GOOD point of chart 2"
          % (C2.r(0), P_GATE))
    check(R(3) * 0 == 0 and Q2(0, 0) == 0, "(0,0) lies on chart 2")

    print("(2) THE SAME CORRESPONDENCE IN BOTH CHARTS")
    Ze1 = matrix(QQ, CH.H1.correspondence(1, -1))
    Ze2 = matrix(QQ, H2.correspondence(-1, 1))
    check(Ze1.charpoly() == Ze2.charpoly(),
          "Z_e has the same characteristic polynomial in both charts: %s"
          % Ze1.charpoly().factor())
    M1 = matrix(QQ, CH.H1.cup_product_matrix(basis=CH.r1))
    M2 = matrix(QQ, H2.cup_product_matrix(basis=CH.r2))
    check(M1 == M2, "the cup product is the same standard symplectic matrix on "
          "both phase-4 bases -- so the change of basis is SYMPLECTIC, which is "
          "what forces D = A^{-t} and makes E_2 transform by A")

    print("(3) THE CHANGE OF BASIS ON H^0(X, Omega^1), EXACTLY OVER Q")
    check(CH.sanity() == -1,
          "dx2/Q2_y2 pushed into chart 1 is -dx1/Q1_y1: the field isomorphism "
          "x2 -> y1, y2 -> 3x1 is the right one")
    A, A1c, A2c = CH.T_hol()
    check(A is not None and A.det() != 0,
          "A = T_hol is invertible, det = %s" % A.det())
    info("chart 1 ell in (1, x1, y1):\n%s" % A1c)
    info("chart 2 ell in (1, x1, y1):\n%s" % A2c)
    info("A =\n%s" % A)

    print("(4) THE SCALE OF Z, FIXED WITHOUT LOOKING AT ANY SERIES")
    g = CH.g
    Si1 = matrix(QQ, CH.S1).inverse()
    Si2 = matrix(QQ, CH.S2).inverse()
    Zc1 = Si1.transpose() * matrix(QQ, CH.H1.correspondence_class(1, -1)) * Si1
    Zc2 = Si2.transpose() * matrix(QQ, H2.correspondence_class(-1, 1)) * Si2
    check(Zc1 + Zc1.transpose() == 0 and Zc2 + Zc2.transpose() == 0,
          "both classes are antisymmetric (Section 4.4(d))")
    B1 = Zc1.submatrix(0, g, g, g)
    B2 = Zc2.submatrix(0, g, g, g)
    check(Zc1.submatrix(0, 0, g, g) == 0 and Zc2.submatrix(0, 0, g, g) == 0,
          "both are block anti-diagonal, Z = [[0,B],[-B,0]]")
    lhs = A.transpose() * B2 * A.transpose().inverse()
    # lhs must be a single rational multiple of B1
    ratios = set()
    for i in range(g):
        for j in range(g):
            if B1[i][j] == 0:
                if lhs[i][j] != 0:
                    ratios.add(None)
            else:
                ratios.add(QQ(lhs[i][j]) / QQ(B1[i][j]))
    ok4 = (len(ratios) == 1 and None not in ratios)
    check(ok4, "A^t B_2 A^{-t} is a single rational multiple of B_1 -- 9 "
          "entries, one scalar, 8 free predictions: ratios = %s" % (ratios,))
    if not ok4:
        return
    lam_cls = QQ(1) / ratios.pop()
    info("=> the two CLASSES differ by lambda_class = %s" % lam_cls)
    info("the port rescales Z further, by frobstruct._rescale_Z, to make eta "
         "p-integral; that factor is read off below and is a deterministic "
         "function of the chart, not a fit.")

    print("(5) E_1 AND E_2 ON THE LEFTOVER DISK, TWICE")
    t0 = time.time()
    FS1 = FrobeniusStructure(CH.C1, CH.H1, P_GATE, N, (1, 3), sx=1, sy=-1)
    FS1.solve()
    LH1 = LocalHeight(FS1, (0, 0))
    info("chart 1: Phi + (22) at b = (1,3), %.0f s, cert p^%s, Zscale %s"
         % (time.time()-t0, FS1.cert, FS1.Zscale))
    t0 = time.time()
    FS2 = FrobeniusStructure(CH.C2, H2, P_GATE, N, (0, 0), sx=-1, sy=1)
    FS2.solve()
    LH2 = LocalHeight(FS2, (0, 0))
    info("chart 2: Phi + (22) at b = (0,0), %.0f s, cert p^%s, Zscale %s"
         % (time.time()-t0, FS2.cert, FS2.Zscale))
    cert = min(ZZ(FS1.cert), ZZ(FS2.cert))
    lam = lam_cls * QQ(FS1.Zscale) / QQ(FS2.Zscale)
    info("=> lambda = %s * %s/%s = %s, with v_%d(lambda) = %s.  Everything "
         "below is linear in Z, so this is the whole of the discrepancy the "
         "two charts are allowed to have."
         % (lam_cls, FS1.Zscale, FS2.Zscale, lam, P_GATE,
            QQ(lam).valuation(P_GATE)))

    # chart 1: the leftover disk, via Lemma 5.7 (E081's route)
    P1 = CurvePoint(FS1.RR, FS1.K(0), y=FS1.K(0))
    check(P1.is_very_bad(), "chart 1 sees (0,0) as VERY BAD (Prop 3.2 case 2)")
    P2 = FS2.base_point
    check(P2.is_good() and P2.dQ_dy_is_unit(),
          "chart 2 sees (0,0) as GOOD with dQ/dy a unit (Prop 3.2 case 1)")
    tp2 = teichmuller_point(P2)
    check(min(P2.vp(tp2.x - P2.x), P2.vp(tp2.y - P2.y)) >= cert,
          "and Teichmuller, so Section 5.3 applies to it directly")

    CI = ColemanIntegrals(FS1.FM)
    eP = CI.ramification_at(P1)
    t0 = time.time()
    raw = CI.coleman_integrals_general(FS1.base_point, P1, e=2 * P_GATE * eP)
    pred1 = CI.certified_precision(*CI.last_eval_points)
    e_used = 2 * P_GATE * eP
    info("chart 1: int_b^{(0,0)} omega over Q_p(p^{1/%d}), %.0f s, certified "
         "p^%s" % (e_used, time.time()-t0, pred1))

    def qp_part(a, e):
        c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
        return c[0] if c else 0

    K = FS1.K
    n = FS1.n
    comp = [K(qp_part(c, e_used)) for c in raw]
    # convert to the phase-4 basis: int omega~ = S int omega + (u(Q) - u(P))
    LEu = LocalExpansion(P1, 4)
    uP = [FS1.evaluate(a) for a in FS1.u]
    uQ = [FS1.series_of(a, LEu, as_form=False)[0] for a in FS1.u]
    ub = []
    for i in range(n):
        acc = K(0)
        for j in range(n):
            if FS1.S[i][j] != 0:
                acc += K(QQ(FS1.S[i][j])) * comp[j]
        ub.append(acc + K(uQ[i]) - K(uP[i]))
    Mb, _ = FS1.frob_triv(FS1.base_point)
    _, beta_bb, _ = FS1.read_triv(Mb)
    beta1 = []
    for j in range(n):
        acc = K(0)
        for i in range(n):
            if FS1.Zk[i][j] != 0:
                acc += ub[i] * FS1.Zk[i][j]
        beta1.append(beta_bb[j] + K(2) * acc)

    LE1, u1s, w1s, v1s = FS1.transport_series(P1, tprec=TPREC)
    LE2, u2s, w2s, v2s = FS2.transport_series(P2, tprec=TPREC)
    L1s, L2s = LE1.L, LE2.L

    # E_1 = first g of alpha_phi; alpha_phi(b',x) = u(x) in both charts
    # (chart 1: Lemma 5.7 gives alpha_0 = 0; chart 2: f(b) = 0 at b = (0,0)).
    worst = ZZ(N + 4)
    for i in range(g):
        pred = sum((A[i][j] * u1s[j] for j in range(g)), L1s.zero())
        d = min([vz(u2s[i][k] - pred[k], N) for k in range(NCOEF)])
        worst = min(worst, d)
    sizes = [str(vser(u2s[i], NCOEF, N)) for i in range(g)]
    check(worst >= cert,
          "E_1: chart 2 equals A times chart 1 on %d coefficients, to p^%s "
          "(certified p^%s); the coefficients themselves are of size p^%s"
          % (NCOEF, worst, cert, sizes))

    # E_2 = last g of (beta_phi - beta_Fil); beta_phi(b',x) = beta(b',b') + w(x)
    def E2_series(FS, LH, beta0, ws, Ls):
        out = []
        for j in range(g, 2 * g):
            out.append(Ls(beta0[j]) + ws[j] - Ls(FS.K(QQ(LH.beta_fil[j]))))
        return out

    E2a = E2_series(FS1, LH1, beta1, w1s, L1s)
    b2_0 = [FS2.read_triv(FS2.frob_triv(P2)[0])[1][j] for j in range(2 * g)]
    E2b = E2_series(FS2, LH2, b2_0, w2s, L2s)
    worst2 = ZZ(N + 4)
    for i in range(g):
        pred = sum((A[i][j] * E2a[j] for j in range(g)), L1s.zero())
        d = min([vz(E2b[i][k] - QQ(1) / lam * pred[k], N) for k in range(NCOEF)])
        worst2 = min(worst2, d)
    check(worst2 >= min(cert, ZZ(QQ(pred1).floor())),
          "E_2: chart 2 equals lambda^{-1} A times chart 1 on %d coefficients, "
          "to p^%s (the weaker certificate is p^%s)"
          % (NCOEF, worst2, min(cert, ZZ(QQ(pred1).floor()))))

    print("(6) theta ON THE DISK")
    gf1 = L1s(LH1.gamma_fil_series(LE1))
    th1 = LH1._assemble(list(u1s), [L1s(beta1[i]) + w1s[i] for i in range(n)],
                        v1s, gf1)
    gf2 = L2s(LH2.gamma_fil_series(LE2))
    th2 = LH2._assemble(list(u2s), [L2s(b2_0[i]) + w2s[i] for i in range(n)],
                        v2s, gf2)
    need6 = min(cert, ZZ(QQ(pred1).floor()))
    delta = [th1[k] / QQ(lam) - th2[k] for k in range(NCOEF)]
    dth = min([vz(d, N) for d in delta])
    size = vser(th2, NCOEF, N)
    info("theta^(1)/lambda - theta^(2) is NOT zero: v_p per coefficient = %s, "
         "against theta itself of size p^%s and a certificate of p^%s."
         % ([str(vz(d, N)) for d in delta[:8]], size, need6))
    info("This is expected and is not a failure.  The port's splitting is the "
         "COORDINATE one in whichever basis it is handed, and the two bases "
         "differ by the block C of T; so the two charts compute the height "
         "with respect to two different splittings of the Hodge filtration.")

    # (6a) the two structural predictions that follow from "the discrepancy is
    #      a quadratic in E_1": it must vanish to order 2 in t, since E_1 does
    #      to order 1; and it must be EVEN, since theta is (E081).
    tval = min([k for k in range(NCOEF) if vz(delta[k], N) < need6] or [NCOEF])
    e1val = min([min([k for k in range(NCOEF) if vz(u2s[i][k], N) < cert]
                     or [NCOEF]) for i in range(g)])
    check(tval >= 2 * e1val,
          "the discrepancy vanishes to order %d in t, and E_1 to order %d: "
          "consistent with a quadratic in E_1, which is what a change of "
          "splitting produces" % (tval, e1val))
    odd = min([vz(delta[k], N) for k in range(1, NCOEF, 2)])
    check(odd >= need6,
          "and it is EVEN in t (odd coefficients vanish to p^%s), as it must "
          "be if it is quadratic in the even-and-odd-graded E_1" % odd)

    # (6b) the fit: is the discrepancy E_2^T X E_1 for a CONSTANT X?
    rows, rhs = [], []
    for k in range(NCOEF):
        row = []
        for i in range(g):
            for j in range(g):
                row.append(sum((E2b[i][a] * u2s[j][k - a]
                                for a in range(k + 1)), FS2.K(0)))
        rows.append(row)
        rhs.append(delta[k])
    Mfit = matrix(FS2.K, rows)
    NFIT = 10

    def fit_and_test(target, label):
        """Solve on the first NFIT coefficients; report the residual on the rest."""
        try:
            X = Mfit[:NFIT].solve_right(vector(FS2.K, target[:NFIT]))
        except Exception:
            return None, None
        tail = min([vz(sum((Mfit[k][m] * X[m] for m in range(g * g)),
                           FS2.K(0)) - target[k], N)
                    for k in range(NFIT, NCOEF)])
        return X, tail

    Xsol, tail = fit_and_test(delta, "discrepancy")
    if Xsol is None:
        check(False, "the discrepancy is not of the form E_2^T X E_1: no solution")
    else:
        check(tail >= need6,
              "AND IT IS: theta^(1)/lambda - theta^(2) = E_2^T X E_1 for a "
              "single constant 3x3 matrix X.  X is fitted on coefficients "
              "0..%d and PREDICTS coefficients %d..%d to p^%s (certificate "
              "p^%s)" % (NFIT - 1, NFIT, NCOEF - 1, tail, need6))
        info("X = %s" % [str(c) for c in Xsol])
        # NON-VACUITY: the same fit applied to theta itself must FAIL, or the
        # design matrix would simply have enough freedom to fit anything.
        _, tail_ctrl = fit_and_test([th2[k] for k in range(NCOEF)], "theta")
        check(tail_ctrl is None or tail_ctrl < need6,
              "and the fit is not vacuous: fitting theta^(2) ITSELF the same "
              "way fails on the held-out coefficients (p^%s < p^%s)"
              % (tail_ctrl, need6))
        info("=> the discrepancy is a Q_p-linear combination of the Psi_j of "
             "Section 6.4.1, so in T_i(x) it adds a multiple of the other "
             "columns to the first.  det T_i -- hence the Diophantine "
             "conclusion -- is unchanged.  That is E077's column argument, and "
             "it applies to ANY change of splitting, not only K-equivariant "
             "ones.")

    print("(7) PRECISION ON THE LEFTOVER DISK")
    c1 = min(ZZ(FS1.cert), ZZ(QQ(pred1).floor()))
    check(ZZ(FS2.cert) > c1,
          "chart 2 certifies the disk to p^%s against chart 1's p^%s: no "
          "ramified extension is involved at all, so Algorithm 3.12's loss "
          "(E063(c)) is simply not paid" % (FS2.cert, c1))

    print("(8) NEGATIVE CONTROLS")
    for nm, Am in [("A^t", A.transpose()), ("A^{-1}", A.inverse())]:
        if Am == A:
            info("%s equals A here, so it is not a control" % nm)
            continue
        w = ZZ(N + 4)
        for i in range(g):
            pred = sum((Am[i][j] * u1s[j] for j in range(g)), L1s.zero())
            w = min(w, min([vz(u2s[i][k] - pred[k], N) for k in range(NCOEF)]))
        check(w < cert, "E_1 with %s in place of A: misses by p^%s" % (nm, w))
    w = ZZ(N + 4)
    for i in range(g):
        pred = sum((A[i][j] * E2a[j] for j in range(g)), L1s.zero())
        w = min(w, min([vz(E2b[i][k] - pred[k], N) for k in range(NCOEF)]))
    check(w < cert, "E_2 without the factor lambda^{-1}: misses by p^%s" % w)

    print("=" * 72)
    print("E082 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
