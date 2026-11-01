# check-phase4-frob.sage --- E065 (E048 Phase 4) GATE, part 7.
#
# E072.  Equation (22) of [BDM+19] §5.2: the Frobenius structure on A_Z, i.e.
# the matrix G = [[1,0,0],[f,F,0],[h,g^T,p]] solving the gauge equation
# Lambda_phi G + dG = G Lambda.  Expanding it gives exactly three nonempty
# blocks -- see padic/frobstruct.py, where the expansion is written out --
#
#   (2,1)  phi^*omega = F omega + df,
#   (3,2)  dg^T = df^T Z F                       (uses §4.1(a), F^T Z F = pZ),
#   (3,1)  dh  = (phi^*omega)^T Z f - g^T omega + phi^*eta - p eta,
#
# and these ARE (22) as printed: unlike (19), which E071 had to correct, §5.2
# survives the derivation intact.  What it does not contain is the constant of
# integration in g.  Z F is constant, so (3,2) integrates in closed form,
#
#     g^T = f^T Z F + c^T,
#
# and (22) fixes f(b) = 0 and h(b) = 0 but says nothing about c.  c is
# nonetheless forced: h exists only if the (3,1) right-hand side is exact on
# ]Y[, and writing the class of its c = 0 version as lambda^T omega + mu^T theta
# (theta = the third-kind basis) forces c = lambda, with mu = 0 left over as a
# PREDICTION of the theory.  Measured here: c is NOT zero, on both curves that
# have a nonzero correspondence.  So g(b) = c^T != 0 -- the reading the printed
# system invites, g normalised at b like f and h, admits no h at all.
#
#   (1) THE (2,1) BLOCK, and with it the transport of Phi and of the primitives
#       f from the saturated computational basis to the basis of [BT] Def
#       2.16(1) made symplectic (E070).  Checked by TINY INTEGRAL: for P, Q in
#       one good disk, f~_i(Q) - f~_i(P) = int_P^Q (phi^*omega~_i - F~ omega~).
#       The right-hand side is computed from local expansions, which share no
#       step with the reduction pipeline that produced Phi and f.
#   (2) §4.1(a) IN THE PHASE4 BASIS, F~^T Z~ F~ = p Z~ to the certified
#       precision of Phi -- the hypothesis the (3,2) block consumes -- together
#       with its negative half, that the ENDOMORPHISM matrix fails it (E071).
#   (3) mu = 0: the third-kind part of the class of the (3,1) right-hand side
#       vanishes.  Not imposed anywhere; if the theory or our eta were wrong,
#       there would be no h and this is where it would show.
#   (4) THE (3,1) BLOCK, by tiny integral again: h(Q) - h(P) = int_P^Q dh.
#       NEGATIVE CONTROL: the same check with c = 0 must FAIL, and it does.
#   (5) NORMALISATIONS: f(b) = 0, h(b) = 0, g(b) = c.
#   (6) I - F~ and F~ - p invertible -- what (23) inverts.  A consequence of
#       the Weil bounds (eigenvalues of absolute value sqrt(p)), so a failure
#       here is a failure of Phi, not of the prime.
#   (7) THE BASE POINT IS TEICHMULLER, phi(b) = b, and then (23) applies at
#       x_0 = b: the matrix M of (23) must satisfy G(b) M = M diag(1, F~, p).
#       This is NOT vacuous precisely because g(b) = c != 0.  Where b is not a
#       Frobenius fixed point the check is skipped, not scored.
#   (8) VACUITY WARNING for a curve with Z_e = 0: checks (3),(4),(5:h),(7) say
#       nothing there, and are reported as skipped rather than as passes.
#
# THE BASE POINT HAS TO BE A GOOD POINT, which is a constraint §5 does not
# mention and which E068-E070 did not feel: the Hodge side runs in the function
# field over Q and takes b = (0,0) for C_4 quite happily, but r(0) = 0 there, so
# the r-adic representation of f, g, h does not converge in that disk ([BT]
# Prop 4.3, Rmk 4.4) and no value at b can be read off.  Phase 4 therefore moves
# C_4's base point to the rational point (t,w) = (1,3), which is good at p = 13
# and, as check (7) measures, Teichmuller.  gamma_Fil must be renormalised at
# the same b before Lemma 5.4 is assembled.
#
# Run: sage check-phase4-frob.sage        (E072_ONLY=<substring> for one curve)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.points import CurvePoint


R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def vz(a, N):
    """Valuation of a p-adic number, N for an exact zero."""
    return ZZ(N) if a == 0 else ZZ(a.valuation())


def vmin(elts, N):
    vs = [vz(a, N) for a in elts]
    return min(vs) if vs else ZZ(N)


def one(label, Qxy, sx, sy, p, N, bpt, tval):
    print("-" * 72)
    print("%s   p = %d, N = %d, base point %s" % (label, p, N, (bpt,)))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    n = 2 * ZZ(C.genus)
    ok = True

    FS = FrobeniusStructure(C, H, p, N, bpt, sx=sx, sy=sy)
    K, cert = FS.K, FS.cert
    vacuous = FS.Z == 0
    print("   Phi and f computed, certified precision %d, Z rescaled by %s "
          "(eta's p-denominator)  (%.0f s)" % (cert, FS.Zscale, time.time() - t0))
    if vacuous:
        print("   (8) *** Z = 0: no nice correspondence on this curve, so "
              "checks (3),(4),(5h),(7) are VACUOUS and are skipped ***")
    sys.stdout.flush()

    P = CurvePoint(FS.RR, K(bpt[0]), y=K(bpt[1]))
    if not P.is_good():
        raise ArithmeticError("the base point is not a good point")

    # ------------------------------------------- (1) the (2,1) block, locally
    d1 = FS.check_f_locally(P, K(tval))
    v1 = vmin(d1, N)
    m1 = v1 >= cert
    print("   (1) phi^*omega~ = F~ omega~ + df~ by tiny integral: agree to "
          "p^%s (cert %d)  %s" % (v1, cert, "ok" if m1 else "*** NO ***"))
    ok = ok and m1
    sys.stdout.flush()

    # ------------------------------------------------ (2) §4.1(a), and its fail
    Zk, F = FS.Zk, FS.F
    v2 = vmin((F.transpose() * Zk * F - p * Zk).list(), N)
    Ze = matrix(QQ, H.correspondence(sx, sy))
    if Ze == 0:
        v2e, m2 = None, v2 >= cert
        print("   (2) F~^T Z~ F~ = p Z~ to p^%s (cert %d); Z_e = 0 so the "
              "negative half is empty  %s" % (v2, cert, "ok" if m2 else "*** NO ***"))
    else:
        Zes = FS.Si.transpose() * Ze * FS.S.transpose()      # endomorphism law
        Zek = FS._toK(Zes)
        v2e = vmin((F.transpose() * Zek * F - p * Zek).list(), N)
        m2 = (v2 >= cert) and (v2e < cert)
        print("   (2) F~^T Z~ F~ = p Z~ to p^%s (cert %d); the endomorphism "
              "fails it at p^%s  %s" % (v2, cert, v2e, "ok" if m2 else "*** NO ***"))
    ok = ok and m2
    sys.stdout.flush()

    # -------------------------------------------- the solve: c, mu, g and h
    c, mu, resv = FS.solve()
    print("   solved (22): residual p^%s, c = %s  (%.0f s)"
          % (resv, [str(v) for v in c], time.time() - t0))
    sys.stdout.flush()

    # ------------------------------------------------------------ (3) mu = 0
    if vacuous:
        print("   (3) skipped (Z = 0)")
        m3 = True
    else:
        vmu = vmin(list(mu), N)
        m3 = vmu >= cert
        print("   (3) third-kind part of the class: mu = 0 to p^%s (cert %d)  "
              "%s" % (vmu, cert, "ok" if m3 else "*** NO ***"))
        ok = ok and m3

    # --------------------------------- (4) the (3,1) block, and the c = 0 control
    if vacuous:
        print("   (4) skipped (Z = 0)")
        m4 = True
    else:
        d4 = FS.check_h_locally(P, K(tval))
        v4 = vz(d4, N)
        zero = vector(K, [K(0)] * n)
        d4b = FS.check_h_locally(P, K(tval), c=zero)
        v4b = vz(d4b, N)
        m4 = (v4 >= cert) and (v4b < cert)
        print("   (4) h(Q)-h(P) = int dh to p^%s (cert %d); with c = 0 it "
              "fails at p^%s  %s" % (v4, cert, v4b, "ok" if m4 else "*** NO ***"))
        ok = ok and m4
    sys.stdout.flush()

    # ------------------------------------------------------ (5) normalisations
    vf = vmin([FS.evaluate(a) for a in FS.f], N)
    vh = vz(FS.evaluate(FS.h), N)
    gb = [FS.evaluate(a) for a in FS.g_vec]
    vg = vmin([gb[k] - c[k] for k in range(n)], N)
    m5 = (vf >= cert) and (vh >= cert) and (vg >= cert)
    print("   (5) f(b) = 0 to p^%s, h(b) = 0 to p^%s, g(b) = c to p^%s "
          "(cert %d)  %s" % (vf, vh, vg, cert, "ok" if m5 else "*** NO ***"))
    ok = ok and m5

    # -------------------------------------------------------- (6) invertibility
    I = identity_matrix(K, n)
    dA, dB = (I - F).determinant(), (F - p * I).determinant()
    m6 = (dA != 0 and dA.valuation() < N) and (dB != 0 and dB.valuation() < N)
    print("   (6) det(I - F~) has valuation %s, det(F~ - p) has valuation %s  "
          "%s" % (vz(dA, N), vz(dB, N), "ok" if m6 else "*** NO ***"))
    ok = ok and m6

    # -------------------------------------- (7) b is Teichmuller, and (23) there
    RR = FS.RR
    xb, yb = K(bpt[0]), K(bpt[1])
    phix = xb**p
    phiy = RR.evaluate(RR.frobenius_apply(
        RR.normalize({0: RR.Ry.gen()}), FS.FM.lift.alpha, FS.FM.lift.beta),
        xb, yb)
    vT = min(vz(phix - xb, N), vz(phiy - yb, N))
    teich = vT >= cert
    if vacuous or not teich:
        why = "Z = 0" if vacuous else "b is not a Frobenius fixed point"
        print("   (7) phi(b) - b has valuation %s; (23) skipped (%s)"
              % (vT, why))
        m7 = True
    else:
        # (23) at x_0 = b, where f(b) = h(b) = 0 and g(b) = c
        alpha = (I - F).inverse() * vector(K, [K(0)] * n)
        beta = (F - p * I).inverse().transpose() * c
        Gb = block_matrix(K, 3, 3, [
            matrix(K, 1, 1, [K(1)]), matrix(K, 1, n), matrix(K, 1, 1),
            matrix(K, n, 1, [K(0)] * n), F, matrix(K, n, 1),
            matrix(K, 1, 1, [K(0)]), matrix(K, 1, n, list(c)),
            matrix(K, 1, 1, [K(p)])], subdivide=False)
        M = block_matrix(K, 3, 3, [
            matrix(K, 1, 1, [K(1)]), matrix(K, 1, n), matrix(K, 1, 1),
            matrix(K, n, 1, list(alpha)), I, matrix(K, n, 1),
            matrix(K, 1, 1, [K(0)]), matrix(K, 1, n, list(beta)),
            matrix(K, 1, 1, [K(1)])], subdivide=False)
        D = block_matrix(K, 3, 3, [
            matrix(K, 1, 1, [K(1)]), matrix(K, 1, n), matrix(K, 1, 1),
            matrix(K, n, 1), F, matrix(K, n, 1),
            matrix(K, 1, 1), matrix(K, 1, n), matrix(K, 1, 1, [K(p)])],
            subdivide=False)
        v7 = vmin((Gb * M - M * D).list(), N)
        m7 = teich and (v7 >= cert)
        print("   (7) phi(b) = b to p^%s; (23): G(b) M = M diag(1,F~,p) to "
              "p^%s (cert %d)  %s"
              % (vT, v7, cert, "ok" if m7 else "*** NO ***"))
    ok = ok and m7

    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-frob.sage --- E065 gate: equation (22), the "
          "Frobenius structure on A_Z (E072) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 1, -1, 11, 8, (2, None), 11),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, 7, 8, (0, 1), 7),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 13, 8, (1, 3), 13),
    ]
    only = os.environ.get("E072_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E072_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
              % (only, len(cases)))
    for (label, Qxy, sx, sy, p, N, bpt, tval) in cases:
        try:
            if bpt[1] is None:
                # y^2 = x^5 - 1 has no convenient rational point off the
                # Weierstrass locus (where dQ/dy vanishes and the disk is bad),
                # so the base point is taken over Q_p: at x = 2, y = sqrt(31).
                Kp = Qp(p, prec=N, type='floating-point')
                bpt = (bpt[0], Kp(ZZ(bpt[0])**5 - 1).sqrt())
            r = one(label, Qxy, sx, sy, p, N, bpt, tval)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    if only:
        print("E072 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E072 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
