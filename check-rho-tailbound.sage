# check-rho-tailbound.sage --- E120 Phase A: the tail of rho is empty of zeros.
#
# Run: sage check-rho-tailbound.sage     (E120_N, E120_E override N and e)
#
# WHAT THIS CLOSES.  E113 computed X(Q_13)_U by taking, on each of the 21
# residue disks and for each of the four elements of Upsilon, the TRUNCATED
# power series of rho - upsilon and reading its Newton polygon.  A Newton
# polygon of a truncation is not the Newton polygon of the series: a coefficient
# beyond the truncation could have a valuation at or below the content and carry
# further zeros.  Nothing in E113-E115 excluded that, and it is the reason
# Theorem D of paper2 is [E] and not [T(CAS)].
#
# BDMTV close the same hole for X_s(13) in the published Annals paper, S6.4.1:
# if F_i in Z_p[[t]] and
#     G(t) = sum c_n t^n = sum a_ij Int F_i (Int F_j) + sum a_i Int F_i
#                                                     + sum b_i F_i
# then  v_p(c_n) >= min{v_p(a_i), v_p(a_ij), v_p(b_i)} - 2 floor(log_p n),
# so the slopes beyond the computed range are > -1 and cannot carry a zero in
# the disk.  This gate does that estimate for OUR rho.  Three things have to be
# supplied that the sentence in BDMTV does not:
#
#   (A) rho is not given as such a combination.  It is a QUADRATIC expression in
#       the coordinates alpha_i, beta_j of the Frobenius trivialisation, each of
#       which is (constant + Q_p-combination of single integrals), plus the one
#       iterated integral v, plus gamma_Fil.  Group (3) writes it out as an
#       explicit quadratic form in u_0..u_5 with Q_p coefficients and CHECKS the
#       rewriting against the assembled series.  A product of two single
#       integrals is a sum of two double integrals (integration by parts), so
#       the resulting shape is BDMTV's.
#
#   (B) F_i in Z_p[[t]] is a hypothesis, not a given.  Group (2) proves it, for
#       the twenty good disks and for the leftover one, from the shape of the
#       curve; the finitely many exact facts it rests on are checked here.
#
#   (C) BDMTV's estimate is stated but not turned into a number of terms.  The
#       disk is |t| <= 1/p, so with t = p s the coefficients are d_n = c_n p^n
#       and the bound reads v(d_n) >= C + n - 2 floor(log_p n), which is NOT
#       monotone in n.  Group (4) proves floor(log_p n) <= (n-1)/4 for p >= 5,
#       hence C + (n+1)/2 as a monotone minorant, and uses it to make the
#       search for "the last n that can attain the content" FINITE and exact.
#
# WHAT IS NOT IN SCOPE.  The rank bound rank Jac(C_4)(Q) = 3 = g.  (An earlier
# version of this comment said it rests on the finiteness of Sha[2^infty] and
# that Theorem D stays [C(Sha)].  That has been false since E118: the upper bound
# comes from a 2-Selmer group, which needs no Sha hypothesis, and since
# 2026-10-28 check-selmer-local.gp certifies its class and unit groups.)  Nor
# does this gate decide the leftover disk ](0,0)[: E113 group (7b)'s evenness is
# measured, not proved, and paper2 now uses E141's sigma-count (group (7c) of
# check-c4-endgame.sage) instead.  What this gate does give the leftover disk is
# the same tail bound as the others, so its Newton COUNT (2 zeros at c3+c2) is
# certified, and that count is a premise of (7c).

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
N = ZZ(os.environ.get("E120_N", 12))
EE = ZZ(os.environ.get("E120_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
RAT = [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
       P11, (QQ(-1)/11, QQ(-15)/11)]
# E114's certified digits of h_p(kappa',delta_11), base 13, from 13^0 up.
HP_DIGITS = [0, 1, 12, 2, 1, 7, 9, 0, 10, 7, 0, 4, 9, 4, 5, 11]
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
    """Honest valuation: an INEXACT zero reports its own precision, not cap.

    Always a LOWER BOUND for the true p-adic valuation, which is what every use
    below needs: a min of these is a valid C, and a coefficient reported at
    valuation k really does have valuation >= k.
    """
    try:
        v = a.valuation()
    except (AttributeError, TypeError):
        return QQ(cap)
    if v is Infinity or v > cap:
        return QQ(cap)
    return QQ(v)


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


# ----------------------------------------------------- quadratic forms in u_k
#
# A form is a dict {(): const, (k,): linear, (k,l): quadratic with k <= l}.

def qf_const(c):
    return {(): c}


def qf_add(A, B):
    out = dict(A)
    for k, v in B.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def qf_scale(A, c):
    return {k: c * v for k, v in A.items() if c * v != 0}


def qf_mul(A, B):
    out = {}
    for ka, va in A.items():
        for kb, vb in B.items():
            if len(ka) + len(kb) > 2:
                raise ArithmeticError("degree > 2: rho is not quadratic in u")
            k = tuple(sorted(ka + kb))
            out[k] = out.get(k, 0) + va * vb
    return {k: v for k, v in out.items() if v != 0}


def qf_eval(A, us, L):
    """Substitute the series u_k, dropping the constant term."""
    out = L.zero()
    for k, v in A.items():
        if not k:
            continue
        term = L(v)
        for i in k:
            term = term * us[i]
        out += term
    return out


def main():
    t00 = time.time()
    print("=== check-rho-tailbound.sage --- E120 Phase A: the tail of rho ===")
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2*ZZ(C.genus)
    Fp = GF(p)
    R2p = PolynomialRing(Fp, ['X', 'Y'])
    Qb = R2p(Q1)
    aff = [(a, b) for a in Fp for b in Fp if Qb(a, b) == 0]

    # ------------------------------------------------------------------ (1)
    print("(1) THE SETUP OF E113, REPRODUCED")
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

    Kx = CI.extension(EE)
    PzK = pt(BAD, Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tprec_for(p, N, EE), ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    Mz, _, IPz = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS.read_triv(IPz.inverse()*Mz)
    info("the very bad point (0,0) through the ramified extension e = %d "
         "(%.0f s)" % (EE, time.time() - t0))

    c3 = -K0(QQ(m2)/4)*K0(3).log()
    c2 = K0(QQ(m2)/8)*K0(2).log()
    H1 = K0(4)*(c2 + TH[P26])/K0(QQ(3*m2))
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
    Binv = Bas.inverse()
    H2 = K0(4)*(TH[P11] - B11*E1[P11][0]*E2[P11][0])/K0(QQ(m2)) + H1
    hp = sum(K0(HP_DIGITS[k])*K0(p)**k for k in range(len(HP_DIGITS)))
    bfull = hp - K0(QQ(5)/2)*K0(2).log() + K0(3).log()
    hpr = min(HPMEAS, ZZ(K0.precision_cap()))
    bA = K0(QQ(EPS))*K0(bfull.lift(), hpr)
    kb = min(ZZ(6), hpr)
    check(vz(bA, hpr) == 1 and ZZ(K0(bfull.lift(), hpr).lift()) % p**kb
          == 4658745 % p**kb,
          "the constants are E113's: b_assembly = b_CG/2 of valuation 1, and "
          "b_CG = 4658745 mod 13^%d (E111).  b is carried to p^%d here"
          % (kb, hpr))
    info("v(B_11) = %s, v(H_1) = %s, v(H_2) = %s, v(b) = %s, v(c_3) = %s, "
         "v(c_2) = %s" % (vz(B11, cert+4), vz(H1, cert+4), vz(H2, cert+4),
                          vz(bA, HPMEAS), vz(c3, cert+4), vz(c2, cert+4)))
    info("v(Binv) = %s, v(beta_Fil) = %s, v(Z) = %s"
         % (min(vz(z, cert+4) for z in Binv.list()),
            min(vz(K0(QQ(z)), cert+4) for z in LH.beta_fil if z != 0),
            min(vz(K0(QQ(z)), cert+4) for z in matrix(FS.Z).list() if z != 0)))

    # ------------------------------------------------------------------ (2)
    print("(2) THE F_i ARE p-INTEGRAL:  W_k, eta, gamma_Fil  in  Z_p[[t]]")
    # (a) the curve and r, exactly, over Q.
    Qcoeffs = [QQ(c) for c in Q1.coefficients()]
    check(all(QQ(c).denominator() % p != 0 for c in Qcoeffs)
          and Q1.coefficient({y: 4}) == 1,
          "Q = y^4 - 6(x-1)^2y^2 + 27x(x^3-4) is monic in y and lies in "
          "Z_(13)[x,y], so a Newton iteration for y over Z_p[[t]] stays there")
    rr = C.r
    rlist = [QQ(c) for c in rr.list()]
    check(all(QQ(c).denominator() % p != 0 for c in rlist),
          "r = %s lies in Z_(13)[x]: every denominator (only a 2) is prime to "
          "13, so min_c v_13(c) = 0" % rr)
    check(rlist[0] == 0 and QQ(rlist[1]) == 2 and QQ(rlist[1]).valuation(p) == 0,
          "r(x) = x*s(x) with s(0) = 2 a unit, which is what makes r(x(t)) a "
          "unit times a power of t on the leftover disk")

    # (b) the A_j of every F_i, and their p-adic content.
    nus = []
    def content_of_radic(a, label):
        best = QQ(cert + 40)
        for j, aj in a.items():
            for coef in FS.RR.Ry(aj).list():
                for cc in coef.list():
                    if cc != 0:
                        best = min(best, vz(cc, cert + 40))
        nus.append((label, best, sorted(a.keys())))
        return best
    for k in range(n):
        content_of_radic(FS.radic_form(FS.reps[k]), "omega_%d" % k)
    if any(cc != 0 for cc in FS.eta):
        content_of_radic(FS.radic_form(FS.eta), "eta")
    for lab, v_, ks in nus:
        info("%-8s digits %s, content of the A_j: p^%s" % (lab, ks, v_))
    nu_forms = min(v_ for _, v_, _ in nus)
    gflist = [c for c in LH.gamma_fil.list()]
    gfden = [c.denominator() for c in gflist]
    nu_gamma = QQ(cert + 40)
    for c in gflist:
        for cc in c.numerator().list():
            if cc != 0:
                nu_gamma = min(nu_gamma, QQ(QQ(cc).valuation(p)))
    check(all(d == 1 for d in gfden),
          "gamma_Fil is a POLYNOMIAL in x and y (no denominator), so it needs "
          "no unit-denominator hypothesis on any disk")
    info("gamma_Fil: content p^%s" % nu_gamma)
    AA = min(nu_forms, nu_gamma)
    check(AA >= 0,
          "so every F_i -- the six basis forms, eta, and gamma_Fil -- has "
          "p-adic content >= p^%s, i.e. A = %s" % (AA, AA))

    # (c) the leftover disk: x(t) = t^2 X(t) with X a UNIT of Z_p[[t]].
    RX = PolynomialRing(QQ, ['X', 'T'])
    Xv, Tv = RX.gens()
    Gpol = RX(Q1.subs({x: Tv**2*Xv, y: Tv}) / Tv**2)
    G0 = Gpol.subs({Tv: 0})
    dG = Gpol.derivative(Xv).subs({Tv: 0})
    X0 = QQ(-1)/18
    check(all(QQ(c).denominator() % p != 0 for c in Gpol.coefficients()),
          "the substitution x = t^2 X, y = t turns Q/t^2 into "
          "G(X,t) = %s in Z_(13)[X,t]" % Gpol)
    check(G0.subs({Xv: X0}) == 0 and QQ(dG.subs({Xv: X0})) == -108
          and QQ(-108).valuation(p) == 0 and QQ(X0).valuation(p) == 0,
          "G(X,0) = -6 - 108X has the simple root X = -1/18, a 13-adic unit, "
          "at which dG/dX = -108 is a unit; so Hensel over Z_p[[t]] gives a "
          "unique X(t) in Z_p[[t]]^* with x(t) = t^2 X(t).  Hence "
          "r(x(t)) = t^2 * (unit of Z_p[[t]]) and x'(t) is in t Z_p[[t]]")
    info("[T] On a GOOD disk r(x_0) is a unit and x(t) = x_0 + t, so W_k = "
         "(sum_j A_j r^-j) x'(t) lies in p^A Z_p[[t]] outright.  On the "
         "leftover disk the same expression lies in p^A t^-M Z_p[[t]] for some "
         "M, and _antiderivative has already REFUSED a pole, so its t-valuation "
         "is >= 0 and it lies in p^A Z_p[[t]] as well.")

    # ------------------------------------------------------------------ (3)
    print("(3) rho AS A QUADRATIC FORM IN THE SINGLE INTEGRALS")
    TPREC = 4*N + 20
    UPS = [(K0(0), "0"), (c3, "c_3"), (c2, "c_2"), (c3 + c2, "c3+c2")]
    disks = [(a, b) for (a, b) in aff if (a, b) != (Fp(0), Fp(0))]

    def model(a0, b0):
        """The quadratic form Qf with rho = Qf(u) + gamma_Fil - v + const."""
        A = [qf_add(qf_const(a0[i]), {(i,): K0(1)}) for i in range(n)]
        B = [qf_add(qf_const(b0[i]),
                    {(k,): K0(FS.Z[k][i]) for k in range(n)
                     if FS.Z[k][i] != 0}) for i in range(n)]
        Bf = [qf_add(B[i], qf_const(-K0(QQ(LH.beta_fil[i])))) for i in range(n)]
        a1 = qf_add(qf_scale(A[1], Binv[0][0]), qf_scale(A[2], Binv[0][1]))
        d1 = qf_add(qf_scale(A[1], Binv[1][0]), qf_scale(A[2], Binv[1][1]))
        a2 = qf_add(qf_scale(Bf[4], Binv[0][0]), qf_scale(Bf[5], Binv[0][1]))
        d2 = qf_add(qf_scale(Bf[4], Binv[1][0]), qf_scale(Bf[5], Binv[1][1]))
        out = qf_scale(qf_mul(A[0], Bf[3]), B11)
        out = qf_add(out, qf_scale(qf_mul(a1, a2), H1))
        out = qf_add(out, qf_scale(qf_mul(d1, d2), H2))
        out = qf_add(out, qf_scale(qf_add(qf_mul(a1, d2), qf_mul(d1, a2)), bA))
        # -theta = -gamma_phi + gamma_Fil + sum_i beta_i (s1 alpha)_i
        #                                 + sum_i betaFil_i (s2 alpha)_i,
        # and gamma_phi = g0 + v + sum_i (beta_i - b0_i) a0_i.
        for i in range(n):
            out = qf_add(out, qf_scale(qf_add(B[i], qf_const(-b0[i])), -a0[i]))
            s1a = {}
            s2a = {}
            for j in range(n):
                s1a = qf_add(s1a, qf_scale(A[j], LH.s1[i][j]))
                s2a = qf_add(s2a, qf_scale(A[j], LH.s2[i][j]))
            out = qf_add(out, qf_mul(B[i], s1a))
            out = qf_add(out, qf_scale(s2a, K0(QQ(LH.beta_fil[i]))))
        return out

    # the constants of every disk, and the disk series themselves
    DATA = {}
    t0 = time.time()
    for (a, b) in disks:
        P0 = CurvePoint(FS.RR, K0(ZZ(a)), y=K0(ZZ(b)))
        x0 = FS.teichmuller(P0)
        LE = LocalExpansion(x0, TPREC)
        _, us, ws, vs_ = FS.transport_series(x0, LE=LE)
        M0 = FS.frob_triv_teich(x0)
        a0, b0, g0 = FS.read_triv(M0)
        a0 = [K0(z) for z in a0]
        b0 = [K0(z) for z in b0]
        L = LE.L
        al = [L(a0[i]) + us[i] for i in range(n)]
        bp = [L(b0[i]) + ws[i] for i in range(n)]
        gp = L(g0) + vs_ + sum((ws[i]*L(a0[i]) for i in range(n)), L.zero())
        gfs = L(LH.gamma_fil_series(LE))
        th = LH._assemble(al, bp, gp, gfs)
        u_ = [al[i] for i in range(g)]
        v_ = [bp[j] - L(K0(QQ(LH.beta_fil[j]))) for j in range(g, n)]
        a1 = L(Binv[0][0])*u_[1] + L(Binv[0][1])*u_[2]
        d1 = L(Binv[1][0])*u_[1] + L(Binv[1][1])*u_[2]
        a2 = L(Binv[0][0])*v_[1] + L(Binv[0][1])*v_[2]
        d2 = L(Binv[1][0])*v_[1] + L(Binv[1][1])*v_[2]
        lam = a1*d2 + d1*a2
        rho0 = L(B11)*u_[0]*v_[0] + a1*a2*L(H1) + d1*d2*L(H2) - th
        DATA[(a, b)] = dict(L=L, rho=rho0 + L(bA)*lam, us=us, v=vs_, gfs=gfs,
                            qf=model(a0, b0), LE=LE, lam=lam)
    info("20 good disks assembled and modelled in %.0f s" % (time.time() - t0))

    # the leftover disk, exactly as E113 group (4) builds it
    t0 = time.time()
    P1 = CurvePoint(FS.RR, K0(0), y=K0(0))
    LE1 = LocalExpansion(P1, TPREC)
    _, us, ws, vs_ = FS.transport_series(P1, LE=LE1)
    L = LE1.L
    a0 = [K0(qp_part(c, EE)) for c in alz]
    b0 = [K0(qp_part(c, EE)) for c in bpz]
    g0 = K0(qp_part(gpz, EE))
    al = [L(a0[i]) + us[i] for i in range(n)]
    bp = [L(b0[i]) + ws[i] for i in range(n)]
    gp = L(g0) + vs_ + sum((ws[i]*L(a0[i]) for i in range(n)), L.zero())
    gfs = L(LH.gamma_fil_series(LE1))
    th = LH._assemble(al, bp, gp, gfs)
    u_ = [al[i] for i in range(g)]
    v_ = [bp[j] - L(K0(QQ(LH.beta_fil[j]))) for j in range(g, n)]
    a1 = L(Binv[0][0])*u_[1] + L(Binv[0][1])*u_[2]
    d1 = L(Binv[1][0])*u_[1] + L(Binv[1][1])*u_[2]
    a2 = L(Binv[0][0])*v_[1] + L(Binv[0][1])*v_[2]
    d2 = L(Binv[1][0])*v_[1] + L(Binv[1][1])*v_[2]
    lam = a1*d2 + d1*a2
    rho0 = L(B11)*u_[0]*v_[0] + a1*a2*L(H1) + d1*d2*L(H2) - th
    DATA[(Fp(0), Fp(0))] = dict(L=L, rho=rho0 + L(bA)*lam, us=us, v=vs_,
                                gfs=gfs, qf=model(a0, b0), LE=LE1, lam=lam)
    info("the leftover disk ](0,0)[ assembled and modelled in %.0f s"
         % (time.time() - t0))

    ALLD = disks + [(Fp(0), Fp(0))]
    worst, wd = QQ(cert + 40), None
    for dk in ALLD:
        D = DATA[dk]
        L = D["L"]
        mod = qf_eval(D["qf"], D["us"], L) + D["gfs"] - D["v"]
        diff = D["rho"] - mod
        cs = series_coeffs(diff, K0, TPREC)
        # the constant terms are not modelled (they cannot carry a zero test)
        vv = min([vz(c, cert+4) for c in cs[1:]]) if len(cs) > 1 else QQ(cert)
        if vv < worst:
            worst, wd = vv, dk
    check(worst >= cert - 2,
         "the rewriting is right: on every one of the 21 disks the assembled "
         "rho + b lambda agrees with  Qf(u) + gamma_Fil - v  in every "
         "coefficient of t^n, n >= 1, to p^%s (worst disk %s) against a "
         "certificate of p^%d.  So rho IS a Q_p-quadratic form in the six "
         "single integrals, plus one iterated integral and one polynomial "
         "series" % (worst, wd, cert))

    # ------------------------------------------------------------------ (4)
    print("(4) THE COEFFICIENT BOUND, AND HOW MANY TERMS IT NEEDS")
    info("[T] Lemma.  Let F_i lie in p^A Z_p[[t]] and let")
    info("      G = sum b_i F_i + sum a_i Int F_i + sum a_ij Int F_i(Int F_j).")
    info("    Then for n >= 1,  v_p(c_n(G)) >= C - 2 floor(log_p n)  with")
    info("      C = min(v(b_i) + A, v(a_i) + A, v(a_ij) + 2A).")
    info("    Proof.  (Int F)_n = F_{n-1}/n has v >= A - v_p(n) >= "
         "A - floor(log_p n).")
    info("    (F_i Int F_j)_n = sum_{a+b=n, b>=1} F_{i,a}(Int F_j)_b has "
         "v >= 2A - floor(log_p n)")
    info("    since b <= n; integrating divides by n once more.  A product of "
         "two single")
    info("    integrals is (Int F_i)(Int F_j) = Int F_i(Int F_j) + "
         "Int F_j(Int F_i), so it is")
    info("    of the third kind.  QED")
    # the monotone minorant, proved here and used to make the scan finite
    def flog(nn):
        return ZZ(nn).exact_log(p)
    bad = [nn for nn in range(1, 4000) if flog(nn) > QQ(nn - 1)/4]
    check(not bad,
          "[T] floor(log_p n) <= (n-1)/4 for p = 13 and every n >= 1: the "
          "binding case of each step is n = 13^k, where k <= (13^k - 1)/4 by "
          "induction.  (Scanned to n < 4000 as well: %d exceptions)" % len(bad))
    info("[T] Hence  C + n - 2 floor(log_p n) >= C + (n+1)/2,  which is "
         "strictly increasing;")
    info("    so 'no n > N attains the content m' can be decided by a FINITE "
         "scan up to")
    info("    n_1 = ceil(2(m - C)), beyond which C + (n+1)/2 > m outright.")

    def bound_C(qf):
        """C for one disk: the minimum over every scalar that appears."""
        lin = [vz(v_, cert+4) for k, v_ in qf.items() if len(k) == 1]
        qua = [vz(v_, cert+4) for k, v_ in qf.items() if len(k) == 2]
        zs = [vz(K0(QQ(z)), cert+4) for z in matrix(FS.Z).list() if z != 0]
        cands = [z + AA for z in lin] + [z + 2*AA for z in qua] \
            + [AA, AA] + [z + 2*AA for z in zs]
        #        ^ gamma_Fil (a b_i F_i term) and Int eta (an a_i term), both
        #          with scalar 1; the double integrals inside v carry Z_ij.
        return min(cands)

    print("(5) DISK BY DISK: TERMS NEEDED AGAINST TERMS COMPUTED")
    info("WHAT THE THRESHOLD HAS TO BE.  E113 does not merely read one Newton "
         "polygon:")
    info("when a value of Upsilon carries two or more zeros its root finder "
         "splits the")
    info("digit, s = c + p s', and reads the Newton polygon of the SHIFTED "
         "series, and")
    info("so on down.  Asking only that the tail miss the content of the top "
         "series")
    info("would certify the top count and nothing below it.  So the threshold "
         "used here")
    info("is the stronger one: every coefficient beyond the truncation must "
         "lie BELOW")
    info("THE RELIABILITY, v(d_n) >= max(m,0) + cap with cap = "
         "min(cert, prec(b) + v(lambda)),")
    info("prec(b) the absolute precision to which b is known (not v(b)) -- "
         "E113's own.")
    info("A substitution s -> c + p s' with c in Z_p never lowers "
         "a")
    info("valuation, so a tail below the reliability at the top is below it at "
         "every")
    info("node of the recursion: the whole search sees exactly what it would "
         "have seen")
    info("with the true series in hand.")
    info("THE COMPARISON MUST BE AGAINST AN UPPER BOUND FOR THE CONTENT.  A "
         "computed")
    info("coefficient reports a valuation that is a LOWER bound for the true "
         "one (an")
    info("inexact zero reports its own precision), so the minimum over the "
         "computed")
    info("coefficients is a lower bound for the content m -- and 'the tail "
         "beats a")
    info("lower bound' is not the statement wanted.  What is wanted is a "
         "coefficient")
    info("that is GENUINELY nonzero, i.e. whose valuation is strictly below "
         "its own")
    info("precision: its valuation is exact and is an upper bound for m.  "
         "That is the")
    info("number used, and the gate fails if the minimum is not attained by "
         "such a one.")
    info("  disk      C     cap  upsilon   m(content)  n_req  n_have")
    allok, rows = True, []

    def genuine(z):
        """z is nonzero, not merely zero to its own precision."""
        try:
            return QQ(z.valuation()) < QQ(z.precision_absolute())
        except (AttributeError, TypeError, OverflowError):
            return z != 0

    for dk in ALLD:
        D = DATA[dk]
        L, rho = D["L"], D["rho"]
        Cb = bound_C(D["qf"])
        lcs = series_coeffs(D["lam"], K0, TPREC)
        vlam = min([vz(z, cert+4) for z in lcs]) if lcs else QQ(cert)
        cap = min(QQ(cert), QQ(hpr) + vlam)      # E113's own reliability
        for (uv, ulab) in UPS:
            f = rho - L(uv)
            cs = series_coeffs(f, K0, TPREC)
            if not cs:
                rows.append((dk, Cb, ulab, "empty", None, None))
                info("  (%2s,%2s) %6s %4s  %-8s the series is identically zero"
                     % (dk[0], dk[1], Cb, cap, ulab))
                allok = False
                continue
            d = [cs[k]*K0(p)**k for k in range(len(cs))]
            nhave = len(cs) - 1
            gen = [QQ(z.valuation()) for z in d if genuine(z)]
            if not gen:
                rows.append((dk, Cb, ulab, "none exact", None, None))
                info("  (%2s,%2s) %6s %4s  %-8s no coefficient is genuinely "
                     "nonzero" % (dk[0], dk[1], Cb, cap, ulab))
                allok = False
                continue
            m = min(gen)          # an UPPER bound for the true content
            thr = max(m, QQ(0)) + cap
            n1 = max(ZZ(1), ZZ(QQ(2*(thr - Cb)).ceil()))
            nreq = 0
            for nn in range(1, n1 + 1):
                if Cb + nn - 2*flog(nn) < thr:
                    nreq = nn
            ok = nreq <= nhave
            allok = allok and ok
            rows.append((dk, Cb, ulab, m, nreq, nhave))
            info("  (%2s,%2s) %6s %4s  %-8s %-11s %-6s %-6s %s"
                 % (dk[0], dk[1], Cb, cap, ulab, m, nreq, nhave,
                    "" if ok else "  <-- FAILS"))
    check(allok,
          "on every one of the 21 disks and for every one of the four elements "
          "of Upsilon, the number of terms E113 computed EXCEEDS the number "
          "the bound needs.  So every coefficient beyond the truncation lies "
          "below E113's own reliability; the Newton polygon of the truncation "
          "IS the Newton polygon of the series, the digit search sees what it "
          "would have seen with the true series, and X(Q_13)_U contains no "
          "point that E113 did not see")
    marg = [QQ(r[5]) - QQ(r[4]) for r in rows if r[4] is not None]
    info("worst margin over the %d pairs: n_have - n_req = %s"
         % (len(rows), min(marg) if marg else "n/a"))

    print("=" * 72)
    print("E120 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
