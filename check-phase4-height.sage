# check-phase4-height.sage --- E065 (E048 Phase 4) GATE, part 9.
#
# E074.  Lemma 5.4 of [BDM+19]: the local height itself,
#
#   theta(x) = h_p(A_Z(b,x)) = gamma_phi - gamma_Fil
#                              - beta_phi^T s_1(alpha_phi)
#                              - beta_Fil^T s_2(alpha_phi),
#
# assembled from the Hodge side (E068-E070) and the Frobenius side (E072-E073).
# Two readings have to be supplied before it can be written down at all, and
# padic/height.py derives both; this gate measures them.
#
# WHAT s_1 AND s_2 ARE.  The middle slot of A_Z is V_dR = H^1_dR(X)^* in the
# DUAL basis ([BDM+19] §4.2), so Fil^0 V_dR = Ann(Fil^1 H^1_dR) is the span of
# the LAST g dual basis vectors once the first g omega_i are holomorphic ([BT]
# Def 2.16(1) = phase4_basis).  So s_2 is the projection onto the last g
# coordinates, s_1 onto the first g, and beta^T . v is a plain dot product.
# E070 read the pairing as a CUP product instead; its measurement was right and
# its inference was not, and check (3) keeps the old reading as a control.
#
# WHAT THE PAPER'S STEP (iii) IS MISSING.  Fil^0 A_Z maps isomorphically onto
# Fil^0 A_1, so the column of G_x s^Fil over the Q_p-slot may -- and must, since
# the poles of Omega_x live in exactly those directions -- first be reduced
# modulo the Fil^0 V_dR-columns, which carry -Omega_x^T Z v.  The condition is
#
#   g_x - Omega_x^T Z s_2 Omega_x - gamma - beta^T Omega_x  in  K[[t_x]],
#
# not the printed one.  This settles the question E071 left [OPEN] about the
# correction in QCMod's hodge.m; it was derived before that code was reread.
#
#   (1) THE Fil^0 SUBBUNDLE CONDITION, exactly and over Q, at every place of D,
#       for both solves.  The pair produced by the PRINTED condition must FAIL
#       it: that is the negative control, and it is the whole content of the
#       correction.  (Vacuous wherever Omega^T Z s_2 Omega happens to be
#       regular -- which is the case on the hyperelliptic test curves, so only
#       C_4 tests this.)
#   (2) theta(b) = 0: alpha_phi(b) = 0, gamma_phi(b) = 0 and gamma_Fil(b) = 0,
#       so the two halves must cancel exactly at the base point.  This is the
#       one check that couples the two normalisations.
#   (3) INVARIANCE UNDER THE beta_Fil AMBIGUITY (E069: beta_Fil is not unique).
#       Shifting beta_Fil by a holomorphic direction must not move theta.  Two
#       NEGATIVE CONTROLS: the naive reading (s_2 = the first g coordinates,
#       dot product) must break it, and E070's cup-product reading is reported
#       for comparison -- it is invariant too, so invariance does not decide
#       between it and ours; the dual basis of §4.2 does, and E075 will settle
#       it against published values.
#   (4) theta AS A POWER SERIES against theta point by point, at two points of
#       a residue disk.  The series route uses (24) and the expansion of
#       gamma_Fil; the pointwise route uses frob_triv and evaluates gamma_Fil
#       in the function field.  They share no step after (23).
#   (5) THE SIZE OF THE CORRECTION: v_p(theta_corrected - theta_printed).  It
#       must be well inside the certified precision, i.e. the correction is not
#       something a precision argument could absorb.
#   (6) VACUITY WARNING for a curve with Z = 0: theta vanishes identically
#       there and every check above says nothing.
#
# NOT SETTLED HERE, AND NOT CLAIMED: the overall sign and normalisation of
# theta against the published X_s(13) values, and any independent test of
# gamma_phi.  Both are E075.
#
# Run: sage check-phase4-height.sage     (E074_ONLY=<substring> for one curve)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion


R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def vz(a, N):
    """Valuation of a p-adic number, N for an exact zero."""
    return ZZ(N) if a == 0 else ZZ(a.valuation())


def pole_order(s):
    """Order of the pole of a Laurent series, 0 if it is regular."""
    if s.is_zero():
        return ZZ(0)
    return max(ZZ(0), -ZZ(s.valuation()))


def fil0_defect(H, FS, LH, g, n):
    """Pole orders of  g_x - Omega^T Z s_2 Omega - gamma - beta^T Omega.

    Returns (worst pole order, worst pole order of the correction alone).
    The (beta, gamma) used are the SOLVER's, i.e. the negatives of the entries
    of s_0^{-1} s^Fil that LocalHeight stores; the condition is the one the
    solver's sign convention writes.
    """
    info = LH.info
    beta = [-QQ(c) for c in LH.beta_fil]
    worst, worstA = ZZ(0), ZZ(0)
    for (P, Om, gx_used) in info["local"]:
        A = H._fil0_quadratic(FS.Z, Om, n, g)
        # g_x as it came out of step (ii), before any correction
        gx = gx_used + A if info["fil0_correction"] else gx_used
        e = gx - A - H.gamma_series(P, info["prec"], info)
        for i in range(n):
            if beta[i] != 0:
                e = e - beta[i] * Om[i]
        worst = max(worst, pole_order(e))
        worstA = max(worstA, pole_order(A))
    return worst, worstA


def cup_reading(H, FS, g, n):
    """(s_1, s_2) of E070's cup-product reading, kept as a control.

    E070 paired beta with the cup product and projected alpha onto Fil^1 H^1_dR
    (the first g) and its complement.  In a symplectic basis the cup product is
    J, so that reading is s_1 = J P_last, s_2 = J P_first.
    """
    J = matrix(QQ, n, n, lambda i, j:
               QQ(1) if (i < g and j == i + g) else
               (QQ(-1) if (i >= g and j == i - g) else QQ(0)))
    Pf = matrix(QQ, n, n, lambda i, j: QQ(1) if (i == j and i < g) else QQ(0))
    Pl = matrix(QQ, n, n, lambda i, j: QQ(1) if (i == j and i >= g) else QQ(0))
    return J * Pl, J * Pf


def one(label, Qxy, sx, sy, p, N, bpt, hodge_base):
    print("-" * 72)
    print("%s   p = %d, N = %d, base point %s" % (label, p, N, (bpt,)))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)
    ok = True

    FS = FrobeniusStructure(C, H, p, N, bpt, sx=sx, sy=sy)
    K, cert = FS.K, FS.cert
    vacuous = FS.Z == 0
    c, mu, resv = FS.solve()
    print("   (22) solved: certified precision %d, residual p^%s, Z rescaled "
          "by %s  (%.0f s)" % (cert, resv, FS.Zscale, time.time() - t0))
    if vacuous:
        print("   (6) *** Z = 0 on this curve: theta vanishes identically and "
              "every check below is VACUOUS ***")
    sys.stdout.flush()

    LH = LocalHeight(FS, hodge_base, fil0_correction=True)
    LHp = LocalHeight(FS, hodge_base, fil0_correction=False)
    print("   Hodge side at b (corrected): beta_Fil = %s"
          % list(LH.beta_fil))
    print("   Hodge side at b (printed)  : beta_Fil = %s"
          % list(LHp.beta_fil))
    print("   gamma_Fil (corrected) = %s" % LH.gamma_fil)
    print("   (%.0f s)" % (time.time() - t0))
    sys.stdout.flush()

    # -------------------------------------------- (1) the Fil^0 subbundle test
    d1, dA = fil0_defect(H, FS, LH, g, n)
    d1p, _ = fil0_defect(H, FS, LHp, g, n)
    if dA == 0:
        print("   (1) Omega^T Z s_2 Omega is REGULAR at every place of D here: "
              "the two conditions coincide and (1) is vacuous (corrected pair "
              "defect %s, printed pair defect %s)" % (d1, d1p))
        m1 = (d1 == 0) and (d1p == 0)
    else:
        m1 = (d1 == 0) and (d1p > 0)
        print("   (1) Fil^0 subbundle condition: the corrected pair leaves a "
              "pole of order %s, the printed pair one of order %s "
              "(Omega^T Z s_2 Omega has a pole of order %s)  %s"
              % (d1, d1p, dA, "ok" if m1 else "*** NO ***"))
    ok = ok and m1
    sys.stdout.flush()

    # ------------------------------------------------------------ (2) theta(b)
    b = FS.base_point
    tb = LH.theta(b)
    v2 = vz(tb, N)
    m2 = v2 >= cert
    print("   (2) theta(b) = 0 to p^%s (cert %d)  %s"
          % (v2, cert, "ok" if m2 else "*** NO ***"))
    ok = ok and m2
    sys.stdout.flush()

    # -------------------------------------- (3) invariance under the ambiguity
    x0 = FS.teichmuller(b)
    LE0 = LocalExpansion(x0, 4 * N + 20)
    Q = LE0.point_at(K(p))
    # (23) and (24) are computed ONCE at Q; the variants below differ only in
    # how (14) reads the result, or in beta_Fil, or in gamma_Fil.
    data = LH.frob_data(Q)
    tq = LH._assemble(*data)
    s1c, s2c = cup_reading(H, FS, g, n)
    naive = matrix(QQ, n, n, lambda i, j: QQ(1) if (i == j and i < g)
                   else QQ(0))
    variants = [("ours", LH),
                ("naive", LH.with_splitting(s2=naive)),
                ("cup", LH.with_splitting(s1=s1c, s2=s2c))]
    dv, dvn, dvc = ZZ(N), ZZ(N), ZZ(N)
    for k in range(g):
        cvec = [QQ(1) if i == k else QQ(0) for i in range(n)]
        for (tag, L0) in variants:
            L1 = L0.with_splitting(beta_fil=L0.beta_fil + vector(QQ, cvec))
            dd = vz(L1._assemble(*data) - L0._assemble(*data), N)
            if tag == "ours":
                dv = min(dv, dd)
            elif tag == "naive":
                dvn = min(dvn, dd)
            else:
                dvc = min(dvc, dd)
    m3 = (dv >= cert) and (vacuous or dvn < cert)
    print("   (3) beta_Fil -> beta_Fil + c, c holomorphic (%d directions): "
          "theta moves by p^%s with s_2 = the last g (ours), by p^%s with "
          "s_2 = the first g (naive reading), by p^%s with E070's cup reading"
          "  %s" % (g, dv, dvn, dvc, "ok" if m3 else "*** NO ***"))
    ok = ok and m3
    print("       theta with E070's cup reading differs from ours by p^%s"
          % vz(variants[2][1]._assemble(*data) - tq, N))
    sys.stdout.flush()

    # ------------------------------------------- (4) the series against points
    LEs, th = LH.theta_series(x0, LE=LE0)
    v4 = ZZ(N)
    for tv in (K(p), K(2) * K(p)):
        P = LE0.point_at(tv)
        v4 = min(v4, vz(th(tv) - LH.theta(P), N))
    m4 = v4 >= cert
    print("   (4) theta as a series vs. point by point, at t = p and 2p: "
          "agree to p^%s (cert %d)  %s"
          % (v4, cert, "ok" if m4 else "*** NO ***"))
    ok = ok and m4
    sys.stdout.flush()

    # --------------------------------------------- (5) the size of the effect
    alpha, bphi, gphi, _ = data
    tqp = LHp._assemble(alpha, bphi, gphi, LHp._fn_at(LHp.gamma_fil, Q))
    dth = vz(tq - tqp, N)
    if dA == 0:
        print("   (5) the correction is regular here, so it changes nothing: "
              "theta_corrected - theta_printed = p^%s" % dth)
        m5 = dth >= cert
    else:
        m5 = dth < cert
        print("   (5) theta_corrected - theta_printed at t = p has valuation "
              "%s, against a certified precision of %d  %s"
              % (dth, cert, "ok" if m5 else "*** NO ***"))
    ok = ok and m5
    print("   theta(b + p) = %s" % tq)
    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-height.sage --- E065 gate: Lemma 5.4, the "
          "local height theta(x) (E074) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 1, -1, 11, 8, (2, None), None),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, 7, 8, (0, 1), (0, 1)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 13, 8, (1, 3), (1, 3)),
    ]
    only = os.environ.get("E074_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E074_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
              % (only, len(cases)))
    for (label, Qxy, sx, sy, p, N, bpt, hb) in cases:
        try:
            if bpt[1] is None:
                # As in E072 and E073: y^2 = x^5-1 has no convenient rational
                # point off the Weierstrass locus, so b is taken over Q_p at
                # x = 2 -- and then gamma_Fil cannot be normalised at b.  It
                # does not matter there: Z = 0, so gamma_Fil = 0 anyway.
                Kp = Qp(p, prec=N, type='floating-point')
                bpt = (bpt[0], Kp(ZZ(bpt[0])**5 - 1).sqrt())
            r = one(label, Qxy, sx, sy, p, N, bpt, hb)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    if only:
        print("E074 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E074 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
