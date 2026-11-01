# check-c4-endgame.sage --- E113: the quadratic Chabauty SET of C_4 at p = 13,
# with b known.
#
# Run: sage check-c4-endgame.sage     (E113_N, E113_E override N and e)
#
# WHAT IS NEW.  E098 assembled rho on the 20 good disks and E099 on the leftover
# one, but both had to carry b = <kappa', delta_11>_P as an unknown and could
# only TABULATE the root count as a function of it.  E109-E112 computed b.  So
# for the first time rho is a single function and {x : rho(x) in Upsilon} is a
# single finite set, which this gate computes -- not its size by a Newton
# polygon, but its ELEMENTS, by a digit-by-digit search for the roots in Z_p.
#
# THE NORMALISATION OF b, STATED BEFORE THE RUN.  E111 computed
#     b_CG = h_p(kappa',delta_11) - (5/2) log_13(2) + log_13(3)
# in the Coleman--Gross normalisation.  The assembly's B_11, H_1, H_2 are all in
# the port's theta-normalisation, and E101 measured the one scalar between them,
# theta = epsilon * h_p with epsilon = 1/2, on an independent bielliptic curve
# at two primes.  E105's next step already reads E093's c_3 that way
# (h_3 = -m_2/2 log 3 = 2 c_3).  Hence
#     b_assembly = epsilon * b_CG = b_CG / 2,
# and this is what the gate uses.  b_CG and 2 b_CG are carried alongside as
# controls, together with b = 0; the point of the controls is not to choose
# among them (B5 says the rational points cannot) but to show what the answer
# would have been.
#
# UPSILON, EXACTLY.  E093 identified the two constants by lindep at 15 digits:
#     c_3 = -(m_2/4) log_13(3),   c_2 = +(m_2/8) log_13(2),   m_2 = 16848.
# Group (1) checks the exact forms against the measured ones to the certificate
# and then uses the exact ones, which costs nothing and buys precision: the
# measured c's come through the ramified extension of degree e = 104 and H_1
# through theta(0,0), whereas the exact c_2 gives H_1 from equation 2 alone,
# i.e. from good points only.
#
# WHAT THE ANSWER IS COMPARED WITH.  C_4(Q) contains the nine points
#     (1,+-3), (-1,+-3), (-2,+-6), (-1/11,+-15/11), (0,0),
# and no point at infinity is 13-adic (E098 group 1).  The question is whether
# the solution set is exactly those nine.

import sys, os, time
sys.path.insert(0, '.')
from sage.rings.infinity import Infinity
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
p = 13
N = ZZ(os.environ.get("E113_N", 12))
EE = ZZ(os.environ.get("E113_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
RAT = [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
       P11, (QQ(-1)/11, QQ(-15)/11)]
ALLRAT = RAT + [BAD]
JPAT = {QQ(1): (0, 0), QQ(-1): (1, 0), QQ(-2): (0, 1), QQ(-1)/11: (0, 0),
        QQ(0): (1, 1)}
# The digits of h_p(kappa',delta_11), base 13, from 13^0 up.  E114 recomputed
# E112's symmetry at N = 18 and N = 22 and CERTIFIED these to p^12 and p^16
# respectively, the two agreeing with each other and with E111/E112's p^10
# reading digit for digit.  So the four digits E113 had to take on the
# strength of E112's agreement are now certified, with six more besides.
HP_DIGITS = [0, 1, 12, 2, 1, 7, 9, 0, 10, 7, 0, 4, 9, 4, 5, 11]
HPCERT = ZZ(16)      # E114, N = 22
HPMEAS = ZZ(16)
EPS = QQ(1)/2              # E101

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
    """Honest valuation: an INEXACT zero reports its own precision, not cap."""
    try:
        v = a.valuation()
    except (AttributeError, TypeError):
        return QQ(cap)
    if v is Infinity or v > cap:
        return QQ(cap)
    return QQ(v)


def vx(a, cap, e):
    return vz(a, cap * e) / QQ(e)


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
    """#zeros with |s| <= 1 of sum d[n] s^n: last index attaining min v_p."""
    vs = [vz(c, cap) for c in d]
    if not vs:
        return None
    m = min(vs)
    if m >= cap:
        return None
    return max(i for i in range(len(vs)) if vs[i] == m)


def to_s(coeffs, K, cap):
    """t = p s, with the tail dropped where it cannot matter."""
    d = [coeffs[k] * K(p)**k for k in range(len(coeffs))]
    vs = [vz(c, cap) for c in d]
    if not vs:
        return []
    cont = min(vs)
    cut = len(d)
    while cut > 1 and vs[cut-1] >= cont + cap:
        cut -= 1
    return d[:cut]


# --------------------------------------------------------------- root finding

def taylor_shift(d, c, K):
    """coefficients of f(c + u) in u, by repeated synthetic division."""
    n = len(d)
    e = list(d)
    out = []
    for _ in range(n):
        m = len(e)
        if m == 0:
            break
        q = [K(0)] * (m - 1)
        acc = e[m-1]
        for i in range(m-2, -1, -1):
            q[i] = acc
            acc = e[i] + c * acc
        out.append(acc)
        e = q
    while len(out) < n:
        out.append(K(0))
    return out


def _eval(d, a, K):
    acc = K(0)
    for k in range(len(d) - 1, -1, -1):
        acc = acc * a + d[k]
    return acc


def _newton(d, a, prec, K):
    """Hensel from a residue at which d vanishes and d' is a unit."""
    s = K(a)
    dd = [K(k) * d[k] for k in range(1, len(d))]
    for _ in range(4 * ZZ(max(prec, 1)).nbits() + 8):
        den = _eval(dd, s, K)
        if den == 0:
            break
        st = s - _eval(d, s, K)/den
        if st == s:
            break
        s = st
    return s


def zp_roots(d, prec, K, base=None, scale=None, depth=0, maxdepth=80):
    """All roots in Z_p of sum d[n] s^n, and the clusters left unseparated.

    ``d`` is normalised (min valuation 0) and reliable to p^prec; the variable
    it is written in is s, and the value reported is base + scale*s.  Returns
    (roots, clusters): a root is (value, digits known), a cluster is
    (centre, how many zeros, scale) with ``None`` for "not even countable
    here".

    The Newton polygon gives nc = #{zeros with |s| <= 1}, counted in Qbar_p.
    If nc = 1 the Weierstrass factorisation is d = (s - alpha) U with U a unit
    power series, so alpha lies in Z_p, d'(alpha) = U(alpha) is a unit, and
    d(c) = (c - alpha)U(c) is a NON-unit for exactly one residue c -- the one
    alpha reduces to.  Hensel then converges from c, so nc = 1 is a leaf.  Only
    nc >= 2 needs the digit split, which strictly consumes precision because a
    child with a root has v(d(c)) >= 1.  A multiple zero never separates and is
    reported as a cluster, which is the honest answer: the disk carries that
    many zeros in that ball and the precision does not say whether they are one
    point or several.
    """
    base = K(0) if base is None else base
    scale = K(1) if scale is None else scale
    vs = [vz(c, prec) for c in d]
    if not vs:
        return ([], [(base, None, scale)])
    m = min(vs)
    if m >= prec:
        return ([], [(base, None, scale)])
    nc = max(i for i in range(len(vs)) if vs[i] == m)
    if nc == 0:
        return ([], [])
    if prec <= 0 or depth > maxdepth:
        return ([], [(base, nc, scale)])
    if nc == 1:
        for c in range(p):
            if vz(_eval(d, K(c), K), prec) >= 1:
                r = _newton(d, K(c), prec, K)
                if vz(_eval(d, r, K), prec) >= prec - 1:
                    return ([(base + scale*r, prec)], [])
                return ([], [(base, 1, scale)])
        return ([], [(base, 1, scale)])
    res, cl = [], []
    for c in range(p):
        e = taylor_shift(d, K(c), K)
        gg = [e[k] * K(p)**k for k in range(len(e))]
        vg = [vz(z, prec) for z in gg]
        mg = min(vg) if vg else QQ(prec)
        if mg >= prec:
            cl.append((base + scale*K(c), None, scale*K(p)))
            continue
        if mg == 0:
            continue                      # d(c) is a unit: no root here
        g2 = [z / K(p)**ZZ(mg) for z in gg]
        sub, s2 = zp_roots(g2, prec - mg, K, base + scale*K(c), scale*K(p),
                           depth + 1, maxdepth)
        res += sub
        cl += s2
    return (res, cl)


def solve_disk(coeffs, K, cap):
    """(roots, clusters, newton_total) for a series in t on |t| <= p^-1."""
    d = to_s(coeffs, K, cap)
    if not d:
        return ([], [(K(0), None, K(1))], None)
    vs = [vz(z, cap) for z in d]
    m = min(vs)
    if m >= cap:
        return ([], [(K(0), None, K(1))], None)
    nt = max(i for i in range(len(vs)) if vs[i] == m)
    d = [z / K(p)**ZZ(m) for z in d]
    roots, cl = zp_roots(d, cap - m, K)
    return (roots, cl, nt)


def main():
    t00 = time.time()
    print("=== check-c4-endgame.sage --- E113: the quadratic Chabauty SET of "
          "C_4 at p = 13 ===")
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2*ZZ(C.genus)
    Fp = GF(p)
    R2p = PolynomialRing(Fp, ['X', 'Y'])
    Qb = R2p(Q1)
    aff = [(a, b) for a in Fp for b in Fp if Qb(a, b) == 0]

    print("(1) THE CONSTANTS, AND Upsilon EXACTLY")
    t0 = time.time()
    FS = FrobeniusStructure(C, H, p, N, BASE, sx=1, sy=-1)
    FS.solve()
    K0, cert = FS.K, ZZ(FS.cert)
    LHW = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    m2 = QQ(FS.Z[1][4])
    info("(22) solved: N = %d, certified p^%d, m_2 = %s  (%.0f s)"
         % (N, cert, m2, time.time() - t0))
    F = matrix(K0, FS.F).transpose()
    U = matrix(K0, [F**cert * vector(K0, [K0(1) if i == k else K0(0)
                                          for i in range(n)])
                    for k in range(g, n)]).transpose()
    tau = (U * U[g:n, :].inverse())[0:g, :].transpose()
    s1U = matrix(K0, n, n, lambda i, j:
                 (K0(1) if i == j else K0(0)) if (i < g and j < g)
                 else (-tau[i-g][j] if (i >= g and j < g) else K0(0)))
    LH = LHW.with_splitting(s1=s1U, s2=matrix.identity(K0, n) - s1U)

    def pt(c, ring=None):
        ring = ring if ring is not None else K0
        return CurvePoint(FS.RR, ring(c[0]), y=ring(c[1]), ring=ring)

    TH, E1, E2 = {}, {}, {}
    for c in RAT:
        al, bp, gp, gf = LH.frob_data(pt(c))
        TH[c] = LH._assemble(al, bp, gp, gf)
        E1[c] = vector(K0, [al[i] for i in range(g)])
        E2[c] = vector(K0, [bp[j] - K0(QQ(LH.beta_fil[j])) for j in range(g, n)])

    # the bad point, through the ramified extension (E091)
    Kx = CI.extension(EE)
    PzK = pt(BAD, Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tprec_for(p, N, EE), ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    Mz, _, IPz = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS.read_triv(IPz.inverse()*Mz)
    THBAD = LH._assemble(alz, bpz, gpz, LH._fn_at(LH.gamma_fil, PzK))
    kmax = max(ZZ(FS.RR.J_range(a)[1])
               for a in [FS.h] + list(FS.g_vec) + list(FS.f))
    pv = prop46_precision(p, cert, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS.FM, "e_finite", 1)))
    info("theta at (0,0) by E091's iterated integral: e = %d, certified p^%s  "
         "(%.0f s)" % (EE, pv, time.time() - t0))
    th4 = K0(qp_part(THBAD, EE))

    c3_meas = -TH[P13]
    H1_E093 = (TH[P13] + TH[P26] - th4)/K0(QQ(m2))
    c2_meas = K0(QQ(3*m2/4))*H1_E093 - TH[P26]
    c3 = -K0(QQ(m2)/4)*K0(3).log()
    c2 = K0(QQ(m2)/8)*K0(2).log()
    dv3, dv2 = vz(c3 - c3_meas, cert+4), vz(c2 - c2_meas, cert+4)
    info("c_3: exact -(m_2/4) log 3 = %s" % c3)
    info("     measured -theta(-1,3) = %s" % c3_meas)
    info("c_2: exact +(m_2/8) log 2 = %s" % c2)
    info("     measured                = %s" % c2_meas)
    check(dv3 >= min(cert, ZZ(QQ(pv).floor())) and
          dv2 >= min(cert, ZZ(QQ(pv).floor())),
          "E093's lindep identification of Upsilon's two constants holds to "
          "p^%s and p^%s against a certificate of p^%s: c_3 = -(m_2/4) log 3 "
          "and c_2 = (m_2/8) log 2 exactly.  [E], but now checked at N = %d "
          "as well as at E093's N" % (dv3, dv2, min(cert, ZZ(QQ(pv).floor())),
                                      N))
    # H_1 from equation 2 alone: good points only, no ramified extension
    H1 = K0(4)*(c2 + TH[P26])/K0(QQ(3*m2))
    dH = vz(H1 - H1_E093, cert+4)
    check(dH >= min(cert, ZZ(QQ(pv).floor())) - 1,
          "and H_1 from equation 2 alone -- 4(c_2 + theta(-2,6))/(3 m_2), "
          "which never touches the bad point -- agrees with E093's "
          "(theta_1+theta_2-theta_4)/m_2 to p^%s.  The endgame can therefore "
          "run at the good points' precision" % dH)

    Eq = EllipticCurve([0, 216, 0, -31104, -2985984])
    gen = Eq.gens()[0]
    nker = ZZ(Eq.change_ring(GF(p)).cardinality())
    Kh = Qp(p, 30)
    lg = Eq.formal_group().log(40)
    Qk = nker*gen
    tk = Kh(-QQ(Qk[0])/QQ(Qk[1]))
    logG = sum((Kh(QQ(cc))*tk**i for i, cc in enumerate(lg.list()) if cc != 0),
               Kh(0))/Kh(nker)
    hG = cg_height_any(Eq, p, gen, 20)          # E134: ours, Sage as answer key
    assert hG == Eq.padic_height(p, 20)(gen), "E134 height disagrees with Sage"
    B11S = hG/((Kh(-72)*logG)**2)
    B11 = K0(B11S.lift(), B11S.precision_absolute())*K0(QQ(EPS))
    kap = vector(K0, [E1[SIGB][i] for i in (1, 2)])
    d11 = 2*vector(K0, [E1[P11][i] for i in (1, 2)]) - kap
    Bas = matrix(K0, [list(kap), list(d11)]).transpose()
    check(vz(Bas.determinant(), cert+4) < cert,
          "kappa' and delta_11 are independent in the Prym plane (determinant "
          "of valuation %s against the certificate p^%d)"
          % (vz(Bas.determinant(), cert+4), cert))
    # 2026-10-28 (E142).  BDMTV (Annals 189, Section 1.4) also assume that the
    # closure of J(Q) in J(Q_p) has finite index, i.e. that the abelian
    # logarithms of J(Q) span H^0(Omega)^* over Q_p.  kappa' and delta_11 are
    # the Prym (sigma-anti-invariant) coordinates of AJ_b(sigma b) and of
    # 2 AJ_b(P_11) - AJ_b(sigma b), i.e. of the classes D(1,3) and
    # D(-1/11,15/11) up to sign, whose omega_0-coordinate is 0; phi^*(P) has
    # Prym coordinates 0 and omega_0-coordinate Lambda deg(phi) log_E(P).  So
    # the 3x3 matrix is block diagonal, and the hypothesis is the two checks:
    # the determinant above, and log_E(P) != 0.
    check(logG != 0 and vz(Bas.determinant(), cert+4) < cert,
          "hence BDMTV's finite-index hypothesis holds: log_E of the generator "
          "is %s (nonzero, P has infinite order) and the Prym determinant is "
          "nonzero, so the logarithms of phi^*(P), D(1,3), D(-1/11,15/11) span "
          "H^0(Omega)^* over Q_13 and the closure of J(Q) has finite index in "
          "J(Q_13)" % logG)
    Binv = Bas.inverse()
    H2 = K0(4)*(TH[P11] - B11*E1[P11][0]*E2[P11][0])/K0(QQ(m2)) + H1
    info("B_11 (epsilon = 1/2) = %s" % B11)
    info("H_1 = %s" % H1)
    info("H_2 = %s" % H2)

    print("(2) b, NORMALISED")
    hp = sum(K0(HP_DIGITS[k])*K0(p)**k for k in range(len(HP_DIGITS)))
    bfull = hp - K0(QQ(5)/2)*K0(2).log() + K0(3).log()
    bCG = {HPCERT: K0(bfull.lift(), HPCERT), HPMEAS: K0(bfull.lift(), HPMEAS)}
    bA = {k: K0(QQ(EPS))*bCG[k] for k in bCG}
    info("h_p(kappa',delta_11) = %s" % hp)
    info("b_CG = h_p - (5/2)log 2 + log 3 = %s" % bCG[HPMEAS])
    check(ZZ(bCG[HPCERT].lift()) % p**6 == 4658745 % p**6,
          "and modulo 13^6 that is E111's boxed 4658745, recomputed here from "
          "h_p and E108's two ell-adic terms rather than imported as a number")
    info("b_assembly = epsilon b_CG = %s   [THE VALUE USED]" % bA[HPMEAS])
    info("v_13(b_assembly) = %s" % vz(bA[HPMEAS], HPMEAS))
    check(vz(bA[HPMEAS], HPMEAS) == 1,
          "b_assembly = b_CG/2 has valuation 1, so it is not a p-adically "
          "small perturbation of the b = 0 computation E098 tabulated")

    print("(3) THE NINE RATIONAL POINTS, WITH b IN PLACE")
    def coords(v):
        return Binv * vector(v[0].parent(), [v[0], v[1]])

    okr, okl = True, True
    need = min(cert, ZZ(QQ(pv).floor()))
    for c in ALLRAT:
        if c == BAD:
            u = vector(K0, [K0(qp_part(alz[i], EE)) for i in range(g)])
            v = vector(K0, [K0(qp_part(bpz[j], EE))
                            - K0(QQ(LH.beta_fil[j])) for j in range(g, n)])
        else:
            u = vector(K0, [K0(a) for a in E1[c]])
            v = vector(K0, [K0(a) for a in E2[c]])
        a1, d1 = coords(u[1:3])
        a2, d2 = coords(v[1:3])
        lam = a1*d2 + d1*a2
        r = B11*u[0]*v[0] + a1*a2*H1 + d1*d2*H2 + bA[HPMEAS]*lam \
            - (K0(qp_part(THBAD, EE)) if c == BAD else TH[c])
        j3, j2 = JPAT[QQ(c[0])]
        dv = vz(r - (K0(j3)*c3 + K0(j2)*c2), cert+4)
        lv = vz(lam, cert+4)
        info("t = %-8s  rho - (j_3 c_3 + j_2 c_2): p^%-4s   lambda: p^%s"
             % (c[0], dv, lv))
        if dv < need:
            okr = False
        if lv < need:
            okl = False
    check(okr, "rho = j_3 c_3 + j_2 c_2 at all nine rational points with the "
               "computed b in place, to p^%d" % need)
    check(okl, "and lambda still vanishes at all nine (B5), which is why none "
               "of them tests b -- the regression is on the assembly, not on "
               "the value")

    print("(4) THE TWENTY-ONE DISKS, SOLVED")
    TPREC = 4*N + 20
    UPS = [(K0(0), "0"), (c3, "c_3"), (c2, "c_2"), (c3 + c2, "c3+c2")]
    BVARS = [("b/2 cert", bA[HPMEAS], HPMEAS),
             ("b/2 p^6", K0(QQ(EPS))*K0(bfull.lift(), 6), ZZ(6)),
             ("b_CG", bCG[HPMEAS], HPMEAS),
             ("2 b_CG", K0(2)*bCG[HPMEAS], HPMEAS),
             ("b = 0", K0(0), cert + 40)]
    PRIMARY = "b/2 cert"
    RATDISK = {}
    for (xi, yi) in ALLRAT:
        RATDISK.setdefault((Fp(xi), Fp(yi)), []).append((xi, yi))

    disks = [(a, b) for (a, b) in aff if (a, b) != (Fp(0), Fp(0))]
    series = {}
    t0 = time.time()
    for (a, b) in disks:
        P0 = CurvePoint(FS.RR, K0(ZZ(a)), y=K0(ZZ(b)))
        x0 = FS.teichmuller(P0)
        LE, al, bp, gp, gf = LH.frob_data_series(x0, tprec=TPREC)
        th = LH._assemble(al, bp, gp, gf)
        SR = th.parent()
        u = [al[i] for i in range(g)]
        v = [bp[j] - SR(K0(QQ(LH.beta_fil[j]))) for j in range(g, n)]
        a1 = SR(Binv[0][0])*u[1] + SR(Binv[0][1])*u[2]
        d1 = SR(Binv[1][0])*u[1] + SR(Binv[1][1])*u[2]
        a2 = SR(Binv[0][0])*v[1] + SR(Binv[0][1])*v[2]
        d2 = SR(Binv[1][0])*v[1] + SR(Binv[1][1])*v[2]
        lam = a1*d2 + d1*a2
        rho0 = SR(B11)*u[0]*v[0] + a1*a2*SR(H1) + d1*d2*SR(H2) - th
        series[(a, b)] = (LE, SR, rho0, lam, x0)
    info("20 good disks assembled in %.0f s" % (time.time() - t0))

    # the leftover disk, E099's group (4)
    t0 = time.time()
    P1 = CurvePoint(FS.RR, K0(0), y=K0(0))
    LE1, u1s, w1s, v1s = FS.transport_series(P1, tprec=TPREC)
    L1s = LE1.L
    a0 = [K0(qp_part(c, EE)) for c in alz]
    b0 = [K0(qp_part(c, EE)) for c in bpz]
    g0 = K0(qp_part(gpz, EE))
    alB = [L1s(a0[i]) + u1s[i] for i in range(n)]
    bpB = [L1s(b0[i]) + w1s[i] for i in range(n)]
    gpB = L1s(g0) + v1s + sum((w1s[i]*L1s(a0[i]) for i in range(n)),
                              L1s.zero())
    thB = LH._assemble(alB, bpB, gpB, L1s(LH.gamma_fil_series(LE1)))
    uB = [alB[i] for i in range(g)]
    vB = [bpB[j] - L1s(K0(QQ(LH.beta_fil[j]))) for j in range(g, n)]
    a1 = L1s(Binv[0][0])*uB[1] + L1s(Binv[0][1])*uB[2]
    d1 = L1s(Binv[1][0])*uB[1] + L1s(Binv[1][1])*uB[2]
    a2 = L1s(Binv[0][0])*vB[1] + L1s(Binv[0][1])*vB[2]
    d2 = L1s(Binv[1][0])*vB[1] + L1s(Binv[1][1])*vB[2]
    lamB = a1*d2 + d1*a2
    rho0B = L1s(B11)*uB[0]*vB[0] + a1*a2*L1s(H1) + d1*d2*L1s(H2) - thB
    series[(Fp(0), Fp(0))] = (LE1, L1s, rho0B, lamB, P1)
    info("the leftover disk ](0,0)[ assembled in %.0f s" % (time.time() - t0))
    check(vz(rho0B[0] + bA[HPMEAS]*lamB[0] - (c3 + c2), cert+4) >= need,
          "and its constant term still gives rho(0,0) = c_3 + c_2 with b in "
          "place, to p^%s"
          % vz(rho0B[0] + bA[HPMEAS]*lamB[0] - (c3+c2), cert+4))

    print("(5) THE ROOTS")
    tab, TOT = [], {}
    SOL = {}
    t0 = time.time()
    for (a, b) in disks + [(Fp(0), Fp(0))]:
        LE, SR, rho0, lam, x0 = series[(a, b)]
        lcs = series_coeffs(lam, K0, TPREC)
        vlam = min([vz(c, cert+4) for c in lcs]) if lcs else QQ(cert)
        row = [(a, b), str(vlam)]
        for (blab, bv, bpr) in BVARS:
            cap = min(cert, ZZ(bpr + vlam))
            tots, undt, nts = 0, 0, 0
            allr, allc = [], []
            for (uv, ulab) in UPS:
                f = rho0 - SR(uv) + SR(bv)*lam
                rts, cls, nt = solve_disk(series_coeffs(f, K0, TPREC), K0, cap)
                tots += len(rts)
                undt += len(cls)
                nts += 0 if nt is None else nt
                for (r, acc) in rts:
                    allr.append((ulab, r, acc))
                for cc in cls:
                    allc.append((ulab,) + cc + (nt, len(rts)))
            TOT[blab] = TOT.get(blab, 0) + tots
            row.append("%d/%d%s" % (tots, nts, "+%d?" % undt if undt else ""))
            if blab == PRIMARY:
                SOL[(a, b)] = (allr, allc, cap)
        tab.append(row)
    info("all 21 disks solved in %.0f s" % (time.time() - t0))
    info("   disk    v(lam)  " + "".join("%-12s" % l for l, _, _ in BVARS))
    for row in tab:
        info("   (%2s,%2s) %-7s " % (row[0][0], row[0][1], row[1])
             + "".join("%-12s" % c for c in row[2:]))
    info("   TOTAL           " + "".join("%-12s" % TOT[l]
                                              for l, _, _ in BVARS))
    info("(each entry is #roots in Z_p / #roots in the closed unit disk of "
         "Qbar_p, summed over the four elements of Upsilon; '+k?' counts "
         "nodes where the precision ran out)")

    print("(6) THE SOLUTION SET AGAINST C_4(Q)")
    found, extra, undtot, XS = [], [], 0, {}
    for (a, b) in disks + [(Fp(0), Fp(0))]:
        LE, SR, rho0, lam, x0 = series[(a, b)]
        allr, allc, cap = SOL[(a, b)]
        undtot += len(allc)
        known = RATDISK.get((a, b), [])
        kt = []
        for (xi, yi) in known:
            Pk = CurvePoint(FS.RR, K0(QQ(xi)), y=K0(QQ(yi)))
            kt.append(((xi, yi), K0(LE.t_of(Pk))))
        XS[(a, b)] = []
        for (ulab, r, acc) in allr:
            tval = K0(p)*r
            hit = None
            for (c, tk_) in kt:
                if vz(tval - tk_, cert+4) >= min(acc, cap):
                    hit = c
            Pt = LE.point_at(tval)
            XS[(a, b)].append((ulab, K0(Pt.x), min(acc, cap), hit))
            if hit is not None:
                found.append((hit, ulab))
            else:
                extra.append(((a, b), ulab, tval, acc, Pt))
    seen = sorted(set(z[0] for z in found), key=str)
    info("rational points isolated as simple roots: %d of 9   %s"
         % (len(seen), seen))
    inclu = []
    for (a, b) in disks + [(Fp(0), Fp(0))]:
        LE, SR, rho0, lam, x0 = series[(a, b)]
        allr, allc, cap = SOL[(a, b)]
        for (xi, yi) in RATDISK.get((a, b), []):
            if (xi, yi) in seen:
                continue
            Pk = CurvePoint(FS.RR, K0(QQ(xi)), y=K0(QQ(yi)))
            sk = K0(LE.t_of(Pk))/K0(p)
            for (ulab, ctr, cnt, sc, nt, ni) in allc:
                # inside the ball, or -- the leftover disk's case -- at a value
                # of Upsilon where NOTHING was isolated, so the point, which
                # group (3) checked is a zero there, is necessarily among the
                # zeros the finder could not separate.
                if vz(sk - ctr, cert+4) >= vz(sc, cert+4) or ni == 0:
                    inclu.append(((xi, yi), ulab,
                                  cnt if cnt is not None else nt - ni,
                                  vz(sc, cert+4)))
                    break
    for (c, ulab, cnt, vs_) in inclu:
        info("%s is NOT separated from the other zeros of rho - %s: %s zeros, "
             "none isolated, in a ball of radius p^-%s.  Group (7b) is what "
             "decides this disk" % (str(c), ulab, cnt, vs_))
    miss = [c for c in ALLRAT if c not in seen
            and c not in [z[0] for z in inclu]]
    check(not miss,
          "every one of the NINE rational points of C_4 is accounted for: "
          "isolated as a simple root, or located inside a reported cluster.  "
          "Unaccounted: %s" % (miss,))
    dupl = [(c, sorted(l for (cc, l) in found if cc == c))
            for c in seen if len([1 for (cc, _) in found if cc == c]) > 1]
    check(not dupl,
          "and each is a root for exactly ONE element of Upsilon, so the four "
          "elements are separated at this precision%s"
          % ("" if not dupl else ": %s are not" % dupl))

    print("(7) THE SIGMA-SYMMETRY OF THE SOLUTION SET")
    bad = []
    for (a, b) in disks + [(Fp(0), Fp(0))]:
        part = (a, -b)
        if part not in XS:
            bad.append(("no partner disk", (a, b)))
            continue
        for (ulab, xv, acc, hit) in XS[(a, b)]:
            ok = False
            for (ul2, xv2, acc2, _) in XS[part]:
                if ul2 == ulab and vz(xv - xv2, cert+4) >= min(acc, acc2):
                    ok = True
            if not ok:
                bad.append(((a, b), ulab, str(xv)))
    check(not bad,
          "sigma maps the solution set to itself: every root in the disk of "
          "(a,b) has a root of the same x and the same element of Upsilon in "
          "the disk of (a,-b).  %d roots checked, %d failures"
          % (sum(len(v) for v in XS.values()), len(bad)))
    if bad:
        for z in bad[:10]:
            info("   %s" % (z,))

    print("(7b) SIGMA ON THE LEFTOVER DISK, AND WHAT IT DECIDES")
    LEz, SRz, rho0z, lamz, _ = series[(Fp(0), Fp(0))]
    check(not LEz.x_is_coordinate,
          "the uniformiser at the very bad point (0,0) is y, not x (dQ/dy "
          "vanishes there and dQ/dx = -108 does not), so sigma(x,y) = (x,-y) "
          "acts on this residue disk by t -> -t and (0,0) is its only fixed "
          "point")
    fz = rho0z + SRz(bA[HPMEAS])*lamz - SRz(c3 + c2)
    czs = series_coeffs(fz, K0, TPREC)
    capz = min(cert, ZZ(HPMEAS + min([vz(c, cert+4)
                                      for c in series_coeffs(lamz, K0, TPREC)])))
    vodd = [vz(czs[k]*K0(p)**k, capz) for k in range(1, len(czs), 2)]
    veven = [vz(czs[k]*K0(p)**k, capz) for k in range(0, len(czs), 2)]
    info("v_p of the s-coefficients of rho - (c_3+c_2) on ](0,0)[: "
         "even %s ..., odd %s ..." % ([str(z) for z in veven[:6]],
                                      [str(z) for z in vodd[:6]]))
    check(min(vodd) >= capz and min(veven) < capz,
          "and rho - (c_3+c_2) is an EVEN function of t there: every odd "
          "coefficient is below the reliability p^%s while the even ones are "
          "not.  So rho is sigma-invariant on the one disk where that is a "
          "statement about a single disk rather than about a pair [measured, E]" % capz)
    ntz = [(nt, ni) for (ul, _, _, _, nt, ni) in SOL[(Fp(0), Fp(0))][1]
           if ul == "c3+c2"]
    check(min(vodd) >= capz and ntz and ntz[0] == (2, 0),
          "hence the zero at t = 0 -- the rational point (0,0), which group "
          "(4) checked is one -- has EVEN order; the Newton polygon gives "
          "%s zeros on this disk at this value in all, none of them isolated "
          "elsewhere; so, IF the evenness is exact, the order is 2 and the "
          "cluster is a double point.  The evenness is measured, not proved "
          "(E141): paper2 does not use it, and group (7c) decides this disk "
          "without it"
          % (ntz[0][0] if ntz else "?"))

    # 2026-10-28 (E141).  Group (7b)'s evenness is MEASURED: the odd
    # coefficients are below the reliability, not proved zero, so it cannot
    # exclude a second Q_13-zero next to (0,0).  paper2 now decides this disk by
    # a counting argument that uses no evenness.  Suppose z_1 != (0,0) is a
    # rational point on ](0,0)[.  Then so is sigma(z_1), and sigma(z_1) != z_1
    # because (0,0) is the only point of C_4(Q_13) fixed by sigma (checked
    # below).  Each of z_1, sigma(z_1) is a Q_13-zero of rho - v on this disk for
    # some v in Upsilon.  For v != c3+c2 those zeros are isolated and are among
    # the leftovers handed to the sieve, which removes them (check-c4-sieve.gp);
    # so v = c3+c2 for both, and with (0,0) that is three zeros of
    # rho - (c3+c2) on a disk where the Newton polygon allows two.  The checks
    # below are the premises, each as its own assertion.
    print("(7c) THE LEFTOVER DISK WITHOUT EVENNESS")
    Ft = PolynomialRing(Fp, 'T')
    TT = Ft.gen()
    check(len((TT**3 - 4).roots()) == 0,
          "T^3 - 4 has no root mod 13, so the only point of C_4(Q_13) with w = 0 "
          "(the fixed points of sigma in the affine chart) is (0,0)")
    top = y**4 - 6*x**2*y**2 + 27*x**4
    check(top.subs(x=1, y=0) != 0 and top.subs(x=0, y=1) != 0,
          "the points at infinity are [x:y:0] with y^4 - 6x^2y^2 + 27x^4 = 0; "
          "sigma fixes such a point only if x = 0 or y = 0, and neither gives a "
          "zero, so sigma has no fixed point at infinity")
    rcz = {}
    for (uv, ulab) in UPS:
        fv = rho0z + SRz(bA[HPMEAS])*lamz - SRz(uv)
        rcz[ulab] = solve_disk(series_coeffs(fv, K0, TPREC), K0, capz)
    info("on ](0,0)[: " + ", ".join(
        "%s: %d isolated, %d clusters, %s zeros in all"
        % (l, len(rcz[l][0]), len(rcz[l][1]), rcz[l][2]) for (_, l) in UPS))
    check(rcz["c3+c2"][2] == 2,
          "rho - (c3+c2) has exactly 2 zeros on ](0,0)[ over Qbar_p, counted "
          "with multiplicity (Newton polygon; its tail is certified by "
          "check-rho-tailbound.sage)")
    check(all(len(rcz[l][1]) == 0 and rcz[l][2] is not None
              for (_, l) in UPS if l != "c3+c2"),
          "for the other three values every Z_p-zero on ](0,0)[ is ISOLATED "
          "(no cluster): %s"
          % ", ".join("%s: %d" % (l, len(rcz[l][0])) for (_, l) in UPS
                      if l != "c3+c2"))
    d0 = XS[(Fp(0), Fp(0))]
    ex0 = [e for e in extra if e[0] == (Fp(0), Fp(0))]
    check(all(h is None for (_, _, _, h) in d0) and len(ex0) == len(d0)
          and len(d0) == sum(len(rcz[l][0]) for (_, l) in UPS if l != "c3+c2"),
          "and those %d isolated zeros are none of the nine rational points and "
          "are all among the leftovers written for the sieve (%s), which removes "
          "every leftover.  Hence no rational point other than (0,0) lies on "
          "](0,0)[, by the count, whatever the cluster at (0,0) is"
          % (len(d0), os.environ.get("E113_OUT", "c4-qc-leftovers.txt")))

    print("(8) WHAT IS LEFT")
    info("clusters left unseparated, over all 21 disks: %d" % undtot)
    for (a, b) in disks + [(Fp(0), Fp(0))]:
        for (ulab, ctr, cnt, sc, nt, ni) in SOL[(a, b)][1]:
            info("   disk (%s,%s)  rho = %-6s  %s zeros in s = %s + p^%s Z_p "
                 "(the value carries %s zeros in all, %s of them isolated)"
                 % (a, b, ulab, cnt if cnt is not None else nt - ni, ctr,
                    vz(sc, cert+4), nt, ni))
    info("roots NOT matched to a rational point: %d" % len(extra))
    for (dk, ulab, tval, acc, Pt) in extra:
        info("   disk (%s,%s)  rho = %-6s  x = %s" % (dk[0], dk[1], ulab, Pt.x))
    OUT = os.environ.get("E113_OUT", "c4-qc-leftovers.txt")
    with open(OUT, "w") as fh:
        fh.write("# E113: the points of X(Q_13)_U that are NOT in C_4(Q).\n")
        fh.write("# p = 13, N = %d, e = %d, b = eps*b_CG to p^%d.\n"
                 % (N, EE, HPMEAS))
        fh.write("# columns: disk_x disk_y upsilon prec x_lift y_lift\n")
        fh.write("# a point is (x, y) mod 13^prec on "
                 "y^4-6(x-1)^2y^2+27x(x^3-4) = 0.\n")
        for (dk, ulab, tval, acc, Pt) in extra:
            pr = min(ZZ(acc), ZZ(Pt.x.precision_absolute()),
                     ZZ(Pt.y.precision_absolute()))
            fh.write("%s %s %s %s %s %s\n"
                     % (dk[0], dk[1], ulab, pr,
                        ZZ(Pt.x.lift()) % p**pr, ZZ(Pt.y.lift()) % p**pr))
    info("the %d leftovers written to %s, for the Mordell-Weil sieve"
         % (len(extra), OUT))
    check(True,
          "X(Q_13)_U = %d isolated roots + %d rational point(s) inside an "
          "unseparated cluster (+ at most %d non-rational point(s) in it, "
          "group (7c)) = %d or more points, of which %d are the rational "
          "points of C_4.  "
          "%s" % (len(extra) + len(found), len(inclu), len(inclu),
                  len(extra) + len(found) + len(inclu),
                  len(found) + len(inclu),
                  "The set IS C_4(Q) and no sieve is needed" if not extra else
                  "The Mordell-Weil sieve has to cut the other %d down"
                  % len(extra)))

    print("=" * 72)
    print("E113 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
