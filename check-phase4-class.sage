# check-phase4-class.sage --- E065 (E048 Phase 4) GATE, part 6.
#
# E071.  [BDM+19] use one symbol Z for two different matrices.  §4.1 defines it
# as a CLASS, Z = sum Z_ij omega_i (x) omega_j in H^1_dR (x) H^1_dR, subject to
#
#   (a) Z in (H^1 (x) H^1)^{phi = p},  i.e.  F^T Z F = p Z   with  phi^* omega
#       = F omega + df  for the COLUMN OF FORMS, so F = Phi^T;
#   (b) Z in Fil^1(H^1 (x) H^1);
#   (c) Z |-> 0 under the cup product;
#   (d) Z |-> 0 under symmetrisation, i.e. Z antisymmetric;
#
# and §4.4 then writes "the matrix of the correspondence Z on H^1_dR(X) ...
# acting on column vectors" for the same symbol.  E067--E070 read that second
# sentence and used the ENDOMORPHISM matrix Z_e throughout §4.5.  That is wrong:
# (22) of §5.2 is derived from F^T Z F = pZ, and Z_e satisfies neither that nor
# (b) nor (d).  The class is
#
#     Z = Z_e M^{-1}      (M the cup product matrix, E066),
#
# and each of §4.1's conditions is one of E067's properties of Z_e -- so the
# correction is a theorem, and this gate checks both the theorem and the claim
# that the uncorrected matrix really does fail.
#
#   (1) Z_e is Rosati-symmetric, trace zero, Fil^1-preserving, and commutes
#       with Phi (E067's four properties, re-measured -- they are the
#       hypotheses of the correction).
#   (2) THE CLASS SATISFIES (a)-(d).  (a) is p-adic and is compared with the
#       CERTIFIED precision of Phi, not with p^N.
#   (3) THE ENDOMORPHISM DOES NOT: (a), (b), (d) all fail.  Both readings of
#       (a) -- Phi Z Phi^T and Phi^T Z Phi -- are tried, so this is not a
#       transpose convention.
#   (4) UNIQUENESS UP TO SCALE, which is what makes the choice canonical: the
#       space of classes satisfying (a)-(d) is computed as the kernel mod p of
#       an exact linear map on the Q-space cut out by (b)(c)(d).  A kernel of
#       dimension 1 over F_p bounds the Q_p-solution space by 1, since a
#       solution space of dimension k meets Z_p^n in a saturated rank-k lattice.
#   (5) THE CHANGE OF BASIS LAW.  A class transforms as S^-T Z S^-1 and an
#       endomorphism as S^-T Z_e S^T, where the rows of S give the phase4 basis
#       in terms of the computational one.  E070's gate used the class law; that
#       is now the right law for the right object, and the check here is that
#       (a)-(d) survive the transport, with Phi |-> S^-T Phi S^T and M |-> J.
#   (6) NEGATIVE CONTROL: a class satisfying (b)(c)(d) but not built from an
#       endomorphism fails (a).
#   (7) THE GAUGE EQUATION (18), the second correction this section makes.
#       Solving G^-1 dG = Lambda for G = [[1,0,0],[A,1,0],[c,b^T,1]] gives
#       A = -Omega, b^T = -Omega^T Z and dc = Omega^T Z omega - eta, whereas
#       (19) prints A = +Omega with dOmega = omega -- already inconsistent with
#       (17)'s sign -- and dg_x = dOmega^T Z Omega - Omega^T (Z - Z^T) omega -
#       eta = Omega^T (2Z^T - Z) omega - eta.  The two agree if and only if Z is
#       SYMMETRIC.  E067--E070 used the endomorphism matrix, which is symmetric,
#       so this error and the one above cancelled and neither was visible.
#       Checked here as a Laurent series identity at every place of D, with the
#       printed formula as the negative control.
#   (8) VACUITY WARNING: for a hyperelliptic curve whose only automorphism is
#       the hyperelliptic involution, Z_e = 0 and so is the class, so every
#       Z-dependent check in E067--E071 is vacuous on it.  Printed, not scored.
#
# AFTER the derivation above and this gate were written, and only then (the
# order the project agreed on), the upstream Magma was read.  QCMod's
# hecke_correspondence.m builds Z as (2g*A - Tr(A)*I) * C^-1 with C the cup
# product matrix -- an endomorphism times the INVERSE CUP PRODUCT, which is the
# correction of check (2) -- and hodge.m integrates dg_x = omega^T Z Omega + eta
# with no (Z - Z^T) term, which is the correction of check (7) with the opposite
# sign of Z.  Their solve also has only g unknowns for beta, confirming E070.
# One thing in hodge.m is in neither the paper nor here: g_x is corrected by
# Omega^T Z s_2 Omega before step (iii).  That is left OPEN for E072.
#
# Run: sage check-phase4-class.sage      (E071_ONLY=<substring> for one curve)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix


R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def val(Mx, N):
    vs = [c.valuation() for c in Mx.list() if c != 0]
    return min(vs) if vs else N


def one(label, Qxy, sx, sy, p, N):
    print("-" * 72)
    print("%s   p = %d, N = %d" % (label, p, N))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g = ZZ(C.genus)
    n = 2 * g
    ok = True

    M = H.cup_product_matrix()
    Ze = matrix(QQ, H.correspondence(sx, sy))
    if Ze == 0:
        print("   (8) *** Z_e = 0: this curve has no nice correspondence, and "
              "every Z-dependent check of E067-E071 is VACUOUS on it ***")
        print("   (%.0f s)" % (time.time() - t0))
        return True
    Z = matrix(QQ, H.correspondence_class(sx, sy))
    reps, S = H.phase4_basis()
    S = matrix(QQ, S)
    Si = S.inverse()
    J = matrix(QQ, n, n, lambda i, j: 1 if (i < g and j == i + g)
               else (-1 if (i >= g and j == i - g) else 0))

    FM = FrobeniusMatrix(C, H, p, N)
    Phi = FM.compute()
    cert = ZZ(FM.certified_precision()[0])
    K = FM.base

    def toK(Mq):
        return matrix(K, [[K(QQ(c)) for c in row] for row in Mq.rows()])

    Mk, Zk, Zek = toK(M), toK(Z), toK(Ze)
    print("   Phi computed, certified precision %d  (%.0f s)"
          % (cert, time.time() - t0))
    sys.stdout.flush()

    # ---------------------------------- (1) the four properties of Z_e (E067)
    ZeS = S.inverse().transpose() * Ze * S.transpose()     # endomorphism law
    r1 = M * Ze == Ze.transpose() * M
    r2 = Ze.trace() == 0
    r3 = all(ZeS[i][j] == 0 for i in range(g, n) for j in range(g))
    v4 = val(Phi * Zek - Zek * Phi, N)
    r4 = v4 >= cert
    m1 = r1 and r2 and r3 and r4
    print("   (1) Z_e: Rosati %s, trace zero %s, preserves Fil^1 %s, "
          "commutes with Phi to p^%s (cert %d)  %s"
          % (r1, r2, r3, v4, cert, "ok" if m1 else "*** NO ***"))
    ok = ok and m1

    # ------------------------------------------- (2) the class satisfies (a)-(d)
    ZS = Si.transpose() * Z * Si                            # class law
    va = val(Phi * Zk * Phi.transpose() - p * Zk, N)
    ca = va >= cert
    cb = all(ZS[i][j] == 0 for i in range(g, n) for j in range(g, n))
    cc = (Z.transpose() * M).trace() == 0
    cd = Z.transpose() == -Z
    m2 = ca and cb and cc and cd
    print("   (2) class Z = Z_e M^-1: (a) F^T Z F = pZ to p^%s (cert %d), "
          "(b) Fil^1 %s, (c) cup 0 %s, (d) antisym %s  %s"
          % (va, cert, cb, cc, cd, "ok" if m2 else "*** NO ***"))
    ok = ok and m2

    # ------------------------------------ (3) the endomorphism does not satisfy them
    ea = val(Phi * Zek * Phi.transpose() - p * Zek, N)
    ea2 = val(Phi.transpose() * Zek * Phi - p * Zek, N)
    eb = all(ZeS[i][j] == 0 for i in range(g, n) for j in range(g, n))
    ed = Ze.transpose() == -Ze
    m3 = (ea < cert) and (ea2 < cert) and (not eb) and (not ed)
    print("   (3) endomorphism Z_e: (a) fails at p^%s and p^%s (cert %d), "
          "(b) %s, (d) %s  %s"
          % (ea, ea2, cert, eb, ed, "ok" if m3 else "*** NO ***"))
    ok = ok and m3
    sys.stdout.flush()

    # --------------------------------------------- (4) uniqueness up to scale
    # basis over Q of {antisymmetric, lower-right g x g block zero, cup 0},
    # in the phase4 basis where M = J
    Mp4 = H.cup_product_matrix(basis=reps)
    if Mp4 != J:
        raise ArithmeticError("phase4_basis is not symplectic")
    gens = []
    for i in range(n):
        for j in range(i + 1, n):
            if i >= g and j >= g:
                continue
            A = matrix(QQ, n, n)
            A[i, j] = 1
            A[j, i] = -1
            gens.append(A)
    W = list(gens)                        # then impose (c): tr(A^T J) = 0
    Ccond = matrix(QQ, 1, len(W), lambda a, b: (W[b].transpose() * J).trace())
    Wbas = [sum((QQ(c) * W[k] for k, c in enumerate(v)),
                matrix(QQ, n, n)) for v in Ccond.right_kernel().basis()]
    Sik = matrix(K, [[K(QQ(c)) for c in row] for row in Si.rows()])
    Sk = matrix(K, [[K(QQ(c)) for c in row] for row in S.rows()])
    Phi4 = Sik.transpose() * Phi * Sk.transpose()
    Jk = toK(J)
    vcal = val(Phi4.transpose() * Jk * Phi4 - p * Jk, N)
    # the map A |--> Phi4 A Phi4^T - p A on Wbas, reduced mod p
    # The map is p-adically small -- reducing it mod p loses everything (its
    # image sits in the unit root space, which is isotropic) -- so the rank has
    # to be read off the elementary divisors instead.  A divisor of valuation
    # < cert is one the certified precision of Phi actually determines; the rest
    # are indistinguishable from zero, so
    #     dim of the solution space  <=  dim W - #{divisors of valuation < cert}
    # and one nonzero solution is already in hand.
    def to_ZZ(c):
        if c == 0:
            return ZZ(0)
        if c.valuation() < 0:
            raise ArithmeticError("the map is not p-integral: valuation %s"
                                  % c.valuation())
        return ZZ(c.residue(cert))

    rows = []
    for A in Wbas:
        Ak = toK(A)
        D = Phi4 * Ak * Phi4.transpose() - p * Ak
        rows.append([to_ZZ(c) for c in D.list()])
    Amap = matrix(ZZ, rows)
    D = Amap.smith_form(transformation=False)
    divs = [D[i, i] for i in range(min(D.nrows(), D.ncols())) if D[i, i] != 0]
    seen = sum(1 for d in divs if ZZ(d).valuation(p) < cert)
    kdim = len(Wbas) - seen
    m4 = (kdim == 1) and (vcal >= cert)
    print("   (4) uniqueness: dim{(b)(c)(d)} = %d over Q, elementary divisors "
          "of (a) below p^%d: %d, so dim{(a)(b)(c)(d)} <= %d  (transported "
          "calibration to p^%s)  %s"
          % (len(Wbas), cert, seen, kdim, vcal, "ok" if m4 else "*** NO ***"))
    ok = ok and m4
    sys.stdout.flush()

    # ------------------------------------------- (5) the change of basis law
    Z4 = Si.transpose() * Z * Si
    va4 = val(Phi4 * toK(Z4) * Phi4.transpose() - p * toK(Z4), N)
    b4 = all(Z4[i][j] == 0 for i in range(g, n) for j in range(g, n))
    c4 = (Z4.transpose() * J).trace() == 0
    d4 = Z4.transpose() == -Z4
    # and the bijection back: Z M = Z_e up to the primitive scaling
    back = Z * M
    lam = None
    for i in range(n):
        for j in range(n):
            if Ze[i][j] != 0:
                lam = back[i][j] / Ze[i][j]
                break
        if lam is not None:
            break
    m5 = (va4 >= cert) and b4 and c4 and d4 and (back == lam * Ze)
    print("   (5) transported to the phase4 basis: (a) to p^%s, (b) %s, (c) %s,"
          " (d) %s; and Z M = %s Z_e  %s"
          % (va4, b4, c4, d4, lam, "ok" if m5 else "*** NO ***"))
    ok = ok and m5

    # ------------------------------------------------- (6) negative control
    bad = None
    for A in Wbas:
        Ak = toK(A)
        if val(Phi4 * Ak * Phi4.transpose() - p * Ak, N) < cert:
            bad = A
            break
    m6 = bad is not None
    print("   (6) [negative control] a class with (b)(c)(d) but not (a) "
          "exists: %s" % ("ok" if m6 else "*** NO ***"))
    ok = ok and m6

    # ------------------------------------------- (7) the gauge equation (18)
    # G = [[1,0,0],[A,1,0],[c,b^T,1]] with A = -Omega, b^T = -Omega^T Z and
    # dc = Omega^T Z omega - eta must satisfy G^-1 dG = Lambda of (17), entry
    # by entry.  Done here as a Laurent series identity at every place of D --
    # which is a check on the TRANSCRIPTION of (17) and on the integrator; that
    # (17) itself is the connection of (15) is a derivation, not a measurement.
    # The same test with (19)'s printed dg_x must FAIL, by 4 Omega^T Z omega.
    basis, _ = H.H1X_basis()
    nb = len(basis)
    forms = [H.differential_of(v) for v in basis]
    poles = H._pole_places(forms)
    prec = 40
    xL = C.L(C.x)
    worst_ok, worst_bad, prec_used = None, None, None
    for pr, tag in ((False, "gauge"), (True, "printed")):
        _, eta, _, _ = H.hodge_eta(Z, printed=pr)
        etaform = H.differential_of(eta) if any(c != 0 for c in eta) else None
        for P in poles:
            m, ser, _, _ = H.local_data(P, prec)
            Om = [H._integrate_series(s) for s in ser]
            A = [-o for o in Om]
            bT = [-sum(Om[i] * QQ(Z[i][j]) for i in range(nb))
                  for j in range(nb)]
            dc = H._dg_expr(Z, ser, Om, nb, printed=pr)
            if etaform is not None:
                dtdx = P.local_uniformizer().derivative()
                dc = dc - m(etaform / xL.differential() / dtdx)
            c = H._integrate_series(dc)
            # (2,1): A' = -omega ; (3,2): (b^T)' = -omega^T Z ;
            # (3,1): c' - b^T A' = -eta
            res = [A[i].derivative() + ser[i] for i in range(nb)]
            res += [bT[j].derivative()
                    + sum(ser[i] * QQ(Z[i][j]) for i in range(nb))
                    for j in range(nb)]
            e31 = c.derivative() - sum(bT[i] * A[i].derivative()
                                       for i in range(nb))
            if etaform is not None:
                dtdx = P.local_uniformizer().derivative()
                e31 = e31 + m(etaform / xL.differential() / dtdx)
            res.append(e31)
            # _integrate_series returns an EXACT series (it sums monomials), so
            # a residual carries no big-oh of its own and would show spurious
            # terms past the precision the input actually had.  dc inherits the
            # honest precision from the expansions, so truncate there.
            bound = dc.prec()
            res = [r.add_bigoh(bound) for r in res]
            v = min([QQ(r.valuation()) for r in res if not r.is_zero()]
                    + [QQ(bound)])
            if pr:
                worst_bad = v if worst_bad is None else min(worst_bad, v)
            else:
                worst_ok = v if worst_ok is None else min(worst_ok, v)
            if not pr:
                prec_used = bound if prec_used is None \
                    else min(prec_used, bound)
    m7 = (worst_ok >= prec_used) and (worst_bad < prec_used)
    print("   (7) gauge equation (18) for dg_x = Omega^T Z omega - eta: "
          "residual vanishes to t^%s (the expansions carry t^%s); with (19) "
          "as printed it does NOT (t^%s)  %s"
          % (worst_ok, prec_used, worst_bad, "ok" if m7 else "*** NO ***"))
    ok = ok and m7
    print("   Z (computational basis) = %s" % (Z.list(),))
    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-class.sage --- E065 gate: the correspondence "
          "as a CLASS, not an endomorphism (E071) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 1, -1, 11, 8),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, 7, 8),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 13, 8),
    ]
    only = os.environ.get("E071_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E071_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
              % (only, len(cases)))
    for (label, Qxy, sx, sy, p, N) in cases:
        try:
            r = one(label, Qxy, sx, sy, p, N)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    if only:
        print("E071 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E071 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
