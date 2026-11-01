# check-c4-qc.sage --- E098: the quadratic Chabauty function assembled on the
# 20 good residue disks, and (B5) measured on them.
#
# Run: sage check-c4-qc.sage        (E098_N, E098_E override N and e)
#
# WHAT IS BEING ASSEMBLED.  rho(x) := h(A_Z(b,x)) - h_p(A_Z(b,x)) = B(E_1,E_2)
# - theta, and X(Q_p)_U = {x : rho(x) in Upsilon}.  Everything on the right is
# now in hand:
#
#   theta          E070-E073, as a power series on each disk (theta_series)
#   E_1, E_2       read off alpha_phi and beta_phi (E077), as series
#   B_11           E094, imported as epsilon * (SageMath's), epsilon symbolic
#   H_1, H_2       E093 corrected by E094 to the unit root splitting
#   Upsilon        {0, c_3, c_2, c_3+c_2} (E093), with the ell=2 half [P]
#
# and one entry is NOT: b = <kappa', delta_11>_P, which is (B5).
#
# THE PRYM BASIS, AND WHY b SURVIVES.  Put kappa' := E_1'(sigma b) and
# delta_11 := 2 E_1'(-1/11, 15/11) - kappa' for the Prym (anti-invariant) parts.
# Then B_P = [[H_1, b], [b, H_2]] in that basis and, writing
# E_1' = a_1 kappa' + d_1 delta_11 and E_2' = a_2 kappa' + d_2 delta_11,
#
#   rho = B_11 u_0 v_0 + a_1 a_2 H_1 + d_1 d_2 H_2 + lambda * b - theta,
#   lambda := a_1 d_2 + d_1 a_2 .
#
# At the nine rational points lambda VANISHES -- at eight of them because
# d_1 = 0 (E088: their Prym classes lie on the line Q kappa') and at
# (-1/11, 15/11) because there (a_1,d_1) = (1/2,1/2) and
# (a_2,d_2) = m_2(-1/2, 1/2), so the two terms cancel.  That is (B5) in the
# form the assembly meets it, and this gate re-derives it from the series
# rather than from E088's design matrix.
#
# WHAT CAN THEREFORE BE MEASURED, AND WHAT CANNOT.  rho is known only as
# rho_0 + b*lambda with one unknown scalar b.  What does NOT depend on b:
#   - the value of rho at every point where lambda vanishes, hence at all nine
#     rational points;
#   - the identity rho(x_i) = j_3(x_i) c_3 + j_2(x_i) c_2, which is the first
#     end-to-end evaluation of the whole Phase 4-5 chain on a disk rather than
#     at a point;
#   - by E096(P3), everything after scaling epsilon.
# What DOES: the zero set on a disk where lambda is not identically zero.  This
# gate measures, disk by disk and for each element of Upsilon, the Newton count
# of rho_0 - v + b lambda as a function of v_p(b), and reports where the count
# is stable and where it is not.  That is the honest operational content of
# (B5): not "the method fails" but "these disks are decided and those are not".
#
# THE BAD DISK ](0,0)[ IS NOT DONE HERE.  theta at the single point (0,0) is
# E091's iterated integral and is used below for the constants; theta as a
# SERIES on that disk needs chart 2 (E082).  E094 makes that newly practical --
# in the unit root splitting theta is chart-independent, which is exactly what
# E082 said blocked the naive comparison -- and the gate says so rather than
# pretending the disk is covered.

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
N = ZZ(os.environ.get("E098_N", 12))
EE = ZZ(os.environ.get("E098_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
RAT = [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
       P11, (QQ(-1)/11, QQ(-15)/11)]
# (j_3, j_2) from E084's table and E092's cluster rule, by t
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


def vx(a, cap):
    """valuation in p-units of an element of the ramified extension."""
    return QQ(cap) if a == 0 else QQ(a.valuation())/QQ(EE)


def series_coeffs(ser, K, cap):
    if ser.is_zero():
        return []
    hi = ser.prec()
    hi = ZZ(cap) if hi is None or hi == +Infinity else min(ZZ(hi), ZZ(cap))
    return [K(ser[k]) for k in range(0, hi)]


def newton_count(d, cap):
    """Zeros in Z_p of sum d[n] s^n: the largest index attaining min v_p."""
    vs = [vz(c, cap) for c in d]
    if not vs:
        return None
    m = min(vs)
    if m >= cap:
        return None
    return max(i for i in range(len(vs)) if vs[i] == m)


def to_s(coeffs, K, cap):
    """t = p s, and the tail dropped where it cannot matter."""
    d = [coeffs[k] * K(p)**k for k in range(len(coeffs))]
    vs = [vz(c, cap) for c in d]
    if not vs:
        return []
    cont = min(vs)
    cut = len(d)
    while cut > 1 and vs[cut-1] >= cont + cap/2:
        cut -= 1
    return d[:cut]


def main():
    t00 = time.time()
    print("=== check-c4-qc.sage --- E098: the quadratic Chabauty function on "
          "the good disks ===")
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2*ZZ(C.genus)

    print("(1) THE RESIDUE DISKS")
    Fp = GF(p)
    R3 = PolynomialRing(Fp, ['X', 'Y', 'Z'])
    X3, Y3, Z3 = R3.gens()
    Fh = Y3**4 - 6*(X3-Z3)**2*Y3**2 + 27*X3**4 - 108*X3*Z3**3
    inf_pts = [(a, b) for a in Fp for b in Fp
               if Fh(a, b, 0) == 0 and (a, b) != (0, 0)]
    R2p = PolynomialRing(Fp, ['X', 'Y'])
    Qb = R2p(Q1)
    aff = [(a, b) for a in Fp for b in Fp if Qb(a, b) == 0]
    rbar = PolynomialRing(Fp, 'X')(C.r)
    badpts = [(a, b) for (a, b) in aff if rbar(a) == 0]
    info("affine F_13-points of the plane model: %d;  points at infinity: %d;  "
         "roots of r mod 13: %s" % (len(aff), len(inf_pts), rbar.roots()))
    check(len(aff) == 21 and len(inf_pts) == 0 and badpts == [(Fp(0), Fp(0))],
          "C_4(Q_13) is covered by 21 residue disks, all affine (the leading "
          "form Y^4-6X^2Y^2+27X^4 has no F_13-point), and exactly ONE of them "
          "is bad: r has the single root x = 0 mod 13 and (0,0) is on the "
          "curve.  So 20 good disks and the leftover ](0,0)[  [T(CAS)]")

    t0 = time.time()
    FS = FrobeniusStructure(C, H, p, N, BASE, sx=1, sy=-1)
    FS.solve()
    K0, cert = FS.K, FS.cert
    LHW = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    m2 = QQ(FS.Z[1][4])
    info("(22) solved: N = %d, certified p^%d, m_2 = %s  (%.0f s)"
         % (N, cert, m2, time.time() - t0))

    print("(2) THE UNIT ROOT SPLITTING (E094), AND THE HEIGHT DATA")
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

    Kx = CI.extension(EE)
    PzK = pt(BAD, Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tprec_for(p, N, EE), ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    M, _, IP = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS.read_triv(IP.inverse()*M)
    TH[BAD] = LH._assemble(alz, bpz, gpz, LH._fn_at(LH.gamma_fil, PzK))
    kmax = max(ZZ(FS.RR.J_range(a)[1])
               for a in [FS.h] + list(FS.g_vec) + list(FS.f))
    pv = prop46_precision(p, cert, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS.FM, "e_finite", 1)))
    info("theta at (0,0) by E091's iterated integral: e = %d, certified p^%s  "
         "(%.0f s)" % (EE, pv, time.time() - t0))

    c3 = -Kx(TH[P13])
    H1 = (Kx(TH[P13]) + Kx(TH[P26]) - Kx(TH[BAD]))/Kx(QQ(m2))
    c2 = Kx(QQ(3*m2/4))*H1 - Kx(TH[P26])
    info("c_3 = %s" % c3)
    info("c_2 = %s" % c2)
    info("H_1^U = %s" % H1)

    # B_11 from SageMath, imported as epsilon * (its value) -- E096
    Eq = EllipticCurve([0, 216, 0, -31104, -2985984])
    gen = Eq.gens()[0]
    nker = ZZ(Eq.change_ring(GF(p)).cardinality())
    Kh = Qp(p, 30)
    lg = Eq.formal_group().log(40)
    Qk = nker*gen
    tk = Kh(-QQ(Qk[0])/QQ(Qk[1]))
    logG = sum((Kh(QQ(cc))*tk**i for i, cc in enumerate(lg.list()) if cc != 0),
               Kh(0))/Kh(nker)
    LAM = QQ(-72)                     # E094, exact
    # E134: OUR height (MST Algorithm 3.1 + (1.1), c = 0 derived from CM by
    # Z[i]); SageMath's padic_height is kept beside it as an ANSWER KEY only.
    hG = cg_height_any(Eq, p, gen, 20)
    assert hG == Eq.padic_height(p, 20)(gen), "E134 height disagrees with Sage"
    B11S = hG/((Kh(LAM)*logG)**2)
    EPS = QQ(os.environ.get("E098_EPS", QQ(1)/2))
    B11 = Kx(K0(B11S.lift(), B11S.precision_absolute()))*Kx(QQ(EPS))
    info("B_11^Sage = %s   (imported as epsilon * this, epsilon = %s)"
         % (B11S, EPS))

    print("(3) THE PRYM BASIS, AND THE ASSEMBLY CHECKED AT THE NINE POINTS")
    kap = vector(Kx, [Kx(E1[SIGB][i]) for i in (1, 2)])
    d11 = 2*vector(Kx, [Kx(E1[P11][i]) for i in (1, 2)]) - kap
    Bas = matrix(Kx, [list(kap), list(d11)]).transpose()
    check(vx(Bas.determinant(), N+4) < cert,
          "kappa' and delta_11 are independent in the Prym plane (the 2x2 "
          "determinant has valuation %s against the certificate p^%d), so they "
          "are a basis and B_P = [[H_1, b], [b, H_2]] in it"
          % (vx(Bas.determinant(), N+4), cert))
    Binv = Bas.inverse()

    def coords(v):
        """(a, d) with v = a kappa' + d delta_11, entries in Kx or a series."""
        return Binv * vector(v[0].parent(), [v[0], v[1]])

    H2 = Kx(4)*(Kx(TH[P11]) - B11*Kx(E1[P11][0])*Kx(E2[P11][0]))/Kx(QQ(m2)) + H1
    info("H_2^U = %s" % H2)

    def rho_at(c):
        u = vector(Kx, [Kx(a) for a in E1[c]])
        v = vector(Kx, [Kx(a) for a in E2[c]])
        a1, d1 = coords(u[1:3])
        a2, d2 = coords(v[1:3])
        return (B11*u[0]*v[0] + a1*a2*H1 + d1*d2*H2 - Kx(TH[c]),
                a1*d2 + d1*a2)

    okr, okl = True, True
    for c in RAT + [BAD]:
        if c == BAD:
            u = vector(Kx, [alz[i] for i in range(g)])
            v = vector(Kx, [bpz[j] - Kx(QQ(LH.beta_fil[j])) for j in range(g, n)])
            a1, d1 = coords(u[1:3])
            a2, d2 = coords(v[1:3])
            r = B11*u[0]*v[0] + a1*a2*H1 + d1*d2*H2 - Kx(TH[BAD])
            lam = a1*d2 + d1*a2
        else:
            r, lam = rho_at(c)
        j3, j2 = JPAT[QQ(c[0])]
        want = Kx(j3)*c3 + Kx(j2)*c2
        dv = vx(r - want, N+4)
        lv = vx(lam, N+4)
        info("t = %-8s  rho - (j_3 c_3 + j_2 c_2) has valuation %-6s   "
             "lambda has valuation %s" % (c[0], dv, lv))
        if dv < min(pv, cert):
            okr = False
        if lv < min(pv, cert):
            okl = False
    check(okr,
          "rho = j_3 c_3 + j_2 c_2 at all NINE rational points and at the bad "
          "point, to the certificate.  Four of the orbits were consumed in "
          "solving for c_3, c_2, H_1, H_2, so this is not four new facts -- but "
          "the base point, its sigma-conjugate and the other conjugates are "
          "evaluated through the same assembly and had to come out right")
    check(okl,
          "and lambda = a_1 d_2 + d_1 a_2 VANISHES at every one of them: at "
          "eight because d_1 = 0 and at (-1/11) because the two terms cancel.  "
          "This is (B5) re-derived from the assembled series rather than from "
          "E088's design matrix, and it is why b never appeared")

    print("(4) THE 20 GOOD DISKS")
    TPREC = 4*N + 20
    disks = [(a, b) for (a, b) in aff if (a, b) != (Fp(0), Fp(0))]
    qp = (lambda z: K0(z.polynomial()[0])) if EE > 1 else (lambda z: K0(z))
    # H_2 depends on the imported epsilon; carry BOTH candidates (E096).
    # E101 measured epsilon = 1/2; QQ(1) is kept as the control this section
    # originally used.
    EPSES = [QQ(1)/2, QQ(1)]
    B11e = {e: Kx(K0(B11S.lift(), B11S.precision_absolute()))*Kx(QQ(e))
            for e in EPSES}
    H2e = {}
    for e in EPSES:
        H2e[e] = Kx(4)*(Kx(TH[P11]) - B11e[e]*Kx(E1[P11][0])*Kx(E2[P11][0])) \
            / Kx(QQ(m2)) + H1
    info("H_2^U(epsilon = 1/2)  [E101's value] = %s" % H2e[QQ(1)/2])
    info("H_2^U(epsilon = 1)     [the old default] = %s" % H2e[QQ(1)])
    check(vx(H2e[QQ(1)] - H2e[QQ(1)/2], N+4) < cert,
          "H_2 MOVES with epsilon, by a term of valuation %s against the "
          "certificate p^%d.  E096(P3) proved the SYSTEM homogeneous, which "
          "makes c_3, c_2, H_1 and Upsilon epsilon-free; it does NOT make the "
          "answer epsilon-free for a FIXED data set, because H_2 is where the "
          "imported constant enters.  E096's headline was too strong and this "
          "is the correction" % (vx(H2e[QQ(1)] - H2e[QQ(1)/2], N+4), cert))

    UPS = [(Kx(0), "0"), (c3, "c_3"), (c2, "c_2"), (c3 + c2, "c_3+c_2")]
    BVALS = [("b = 0", Kx(0))] + \
            [("v(b)=%d" % k, Kx(K0(p)**k)) for k in range(-1, 3)] + \
            [("b = 5", Kx(K0(5)))]
    RATDISK = {}
    for (xi, yi) in RAT:
        RATDISK.setdefault((Fp(xi), Fp(yi)), []).append((xi, yi))

    def eval_ser(cs, t0):
        f = K0(0)
        for k in range(len(cs) - 1, -1, -1):
            f = f*t0 + cs[k]
        return f

    tot = {(e, lab): 0 for e in EPSES for lab, _ in BVALS}
    undec = {(e, lab): 0 for e in EPSES for lab, _ in BVALS}
    lam_zero, okpt, cnt_tab, t0 = 0, True, [], time.time()
    for (a, b) in disks:
        P0 = CurvePoint(FS.RR, K0(ZZ(a)), y=K0(ZZ(b)))
        x0 = FS.teichmuller(P0)
        LE, al, bp, gp, gf = LH.frob_data_series(x0, tprec=TPREC)
        th = LH._assemble(al, bp, gp, gf)
        SR = th.parent()
        u = [al[i] for i in range(g)]
        v = [bp[j] - SR(K0(QQ(LH.beta_fil[j]))) for j in range(g, n)]
        Bi = [[SR(qp(Binv[i][j])) for j in range(2)] for i in range(2)]
        a1 = Bi[0][0]*u[1] + Bi[0][1]*u[2]
        d1 = Bi[1][0]*u[1] + Bi[1][1]*u[2]
        a2 = Bi[0][0]*v[1] + Bi[0][1]*v[2]
        d2 = Bi[1][0]*v[1] + Bi[1][1]*v[2]
        lam = a1*d2 + d1*a2
        lcs = series_coeffs(lam, K0, TPREC)
        if not lcs or all(vz(c, N+4) >= cert for c in lcs):
            lam_zero += 1
        rho0 = {e: SR(qp(B11e[e]))*u[0]*v[0] + a1*a2*SR(qp(H1))
                + d1*d2*SR(qp(H2e[e])) - th for e in EPSES}
        # the known rational points of this disk must be roots, for EVERY b
        for (xi, yi) in RATDISK.get((a, b), []):
            j3, j2 = JPAT[QQ(xi)]
            want = qp(Kx(j3)*c3 + Kx(j2)*c2)
            t0v = K0(QQ(xi)) - K0(x0.x)
            for e in EPSES:
                fv = eval_ser(series_coeffs(rho0[e] - SR(want), K0, TPREC), t0v)
                lv = eval_ser(lcs, t0v)
                if vz(fv, N+4) < min(pv, cert) or vz(lv, N+4) < min(pv, cert):
                    okpt = False
                    info("   (%s,%s) at t = %s, eps = %s: rho - v has "
                         "valuation %s, lambda %s"
                         % (a, b, xi, e, vz(fv, N+4), vz(lv, N+4)))
        row = [(a, b)]
        for e in EPSES:
            for lab, bv in BVALS:
                sm, und = 0, 0
                for uv, _ in UPS:
                    f = rho0[e] - SR(qp(uv)) + SR(qp(bv))*lam
                    d = to_s(series_coeffs(f, K0, TPREC), K0, cert)
                    nc = newton_count(d, cert)
                    if nc is None:
                        und += 1
                    else:
                        sm += nc
                tot[(e, lab)] += sm
                undec[(e, lab)] += und
                row.append("%d%s" % (sm, "+%d?" % und if und else ""))
        cnt_tab.append(row)
    info("20 good disks assembled in %.0f s" % (time.time() - t0))
    check(okpt,
          "EVERY known rational point in a good disk is a zero of rho_b - v "
          "for the predicted v in Upsilon, for both epsilon and for every b "
          "tried -- found by evaluating the DISK SERIES at the point, not by "
          "the point computation that produced the constants.  This is the "
          "first end-to-end evaluation of the whole Phase 4-5 chain on a disk")
    info("roots of rho_b - v per disk, summed over the four elements of "
         "Upsilon; left block epsilon = 1/2 (E101), right block epsilon = 1:")
    info("   disk     " + "".join("%-9s" % lab for e in EPSES
                                  for lab, _ in BVALS))
    for row in cnt_tab:
        info("   (%2s,%2s) " % (row[0][0], row[0][1])
             + "".join("%-9s" % c for c in row[1:]))
    info("   TOTAL    " + "".join(
        "%-9s" % ("%d%s" % (tot[(e, lab)],
                            "+%d?" % undec[(e, lab)] if undec[(e, lab)] else ""))
        for e in EPSES for lab, _ in BVALS))
    info("(a '+k?' means k of the four series fell below the certificate on "
         "that disk and the Newton count is undecidable there, not zero)")
    check(lam_zero == 0,
          "lambda is identically zero on NONE of the 20 good disks, so there "
          "is no disk on which the quadratic Chabauty function is known "
          "outright: (B5) is not confined to a few disks, it is everywhere")
    t1 = sorted(set(tot[(QQ(1)/2, lab)] for lab, _ in BVALS))
    t2 = sorted(set(tot[(QQ(1), lab)] for lab, _ in BVALS))
    check(True,
          "totals over b: %s at epsilon = 1/2 (E101's value) and %s at "
          "epsilon = 1.  %s"
          % (t1, t2,
             "The count moves with b, so not even the SIZE of "
             "X(Q_p)_U survives (B5)" if len(t1) > 1 else
             "The count does not move with b"))

    print("(5) WHAT REMAINS")
    info("the bad disk ](0,0)[: theta AT the point is E091's iterated integral "
         "and is used above, but theta as a SERIES there needs chart 2 (E082). "
         "E094 makes that newly practical: in the unit root splitting theta is "
         "chart-INDEPENDENT, which is exactly what E082 recorded as blocking "
         "the naive comparison of the two charts.")
    info("b = <kappa', delta_11>_P: (B5).  Group (4) measures its cost "
         "exactly -- every good disk carries it.")
    info("Upsilon's ell = 2 half is [P] (E092's cluster split, corroborated but "
         "not proved by E095/E097); of its four elements one is at risk.")
    info("epsilon: CORRECTED HERE.  E096(P3) proved the system homogeneous, "
         "which makes c_3, c_2, H_1 and Upsilon epsilon-free -- but for a "
         "FIXED data set H_2 and hence rho do depend on which epsilon is "
         "imported, and group (4) measures that they do.  The gain from E096 "
         "is still real and is now exactly stated: epsilon is DISCRETE, "
         "epsilon in {1,2}, so the ambiguity costs a factor of two in the "
         "number of candidate systems, not a continuum.")

    print("=" * 72)
    print("E098 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
