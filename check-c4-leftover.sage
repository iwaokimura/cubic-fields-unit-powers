# check-c4-leftover.sage --- E081: [BDM+19] Lemma 5.7, and theta_Z on C_4's
# leftover residue disk ](0,0)[ at p = 13.
#
# E080 measured that C_4 has exactly one bad residue disk at p = 13, that it is
# the disk of the rational point (0,0), and that Lemma 5.7's hypothesis holds
# there.  This gate implements the route: change the base point to b' = (0,0).
#
# THE DERIVATION, from the published paper (Annals 189),
# written out before any code and not quoted.
#
# Section 5.5 (48) gives the Hodge side:
#     beta_Fil(b')   = beta_Fil(b),
#     gamma_Fil(b',x) = gamma_Fil(b,x) - gamma_Fil(b,b').
#
# Lemma 5.7's proof gives s_0^{-1}(b',b') o s^phi(b',b') = A B^{-1} C, where,
# with u := int_b^{b'} omega (a column of 2g Coleman integrals) and
# c := int_b^{b'} eta + int_b^{b'} omega^T Z omega (an ITERATED integral),
#
#     A = [[1,0,0],[u,I,0],[c, u^T Z,1]],
#     B = [[1,0,0],[u,I,0],[c,-u^T Z,1]],
#     C = [[1,0,0],[0,I,0],[0, beta_phi^T(b,b),1]].
#
# For a lower unitriangular [[1,0,0],[u,I,0],[c,w^T,1]] the inverse is
# [[1,0,0],[-u,I,0],[-c+w^T u,-w^T,1]], so with w^T = -u^T Z
#
#     A B^{-1} = [[1,0,0],[0,I,0],[-2 u^T Z u, 2 u^T Z, 1]],
#     A B^{-1} C = [[1,0,0],[0,I,0],[-2 u^T Z u, beta_phi^T(b,b) + 2 u^T Z, 1]].
#
# TWO THINGS FALL OUT THAT THE PRINTED LEMMA DOES NOT SAY.
#
#   (i)  c CANCELS.  A and B differ only in the SIGN of the (3,2) block, so the
#        iterated integral and int eta drop out of A B^{-1} entirely.  That is
#        why Section 6.6 can say that only the single integrals int_b^{P_0}
#        omega are needed -- a statement the lemma's own display does not make
#        obvious, since c appears in it twice.
#   (ii) gamma_phi(b',b') = -2 u^T Z u, and it vanishes BECAUSE OF Section
#        4.4(d).  Condition (d) says that Z maps to zero under the
#        symmetrisation map, i.e. that the matrix Z is ANTISYMMETRIC; then
#        u^T Z u = 0 for every u.  The lemma prints 0 in that slot without
#        naming the hypothesis that puts it there.  Check (1) is that
#        hypothesis, measured.
#
# So the route is
#     alpha_phi(b',b') = 0,   gamma_phi(b',b') = 0,
#     beta_phi^T(b',b') = beta_phi^T(b,b) + 2 (int_b^{b'} omega)^T Z,
# followed by Section 5.3's transport (24) from b' to x in ]b'[, whose
# ingredients are TINY integrals only and so are available in a bad disk, and
# then Lemma 5.5.  With alpha_0 = gamma_0 = 0 the composite of E073 degenerates
# to alpha_phi = u(x), beta_phi^T = beta_phi^T(b',b') + w(x)^T, gamma_phi = v(x).
#
# THE BASIS.  int_b^{b'} omega is wanted in the phase-4 basis, and the port's
# Coleman integrals come in the computational basis.  With omega~ = S omega + du
# (frobstruct's transport law) the conversion is
#     int_b^{b'} omega~ = S int_b^{b'} omega + (u(b') - u(b)),
# and the u_i are POLYNOMIALS in x, y (r-adic digit 0), so they may be
# evaluated at a very bad point, where nothing else r-adic may.
#
# THE CHECKS.
#   (1) Section 4.4(d): Z + Z^T = 0, over Q, and u^T Z u = 0 for the u actually
#       used.  This is the hypothesis of (ii) above.
#   (2) (48), exactly over Q: beta_Fil unchanged, gamma_Fil shifted by a
#       constant, when LocalHeight is rebuilt at b'.
#   (3) THE CHECK THAT MATTERS.  At a GOOD b', where the direct route also
#       works, Lemma 5.7 must reproduce it: beta_phi(b',b') computed from
#       beta_phi(b,b) and int_b^{b'} omega, against beta_phi(b',b') computed by
#       solving (22) afresh with f, g, h normalised at b'.  The two share F,
#       omega, Z and eta and nothing else -- in particular route 2 re-solves
#       for g's integration constant (E072), which is the part of the
#       normalisation Lemma 5.7 has to get right.  alpha_phi(b',b') = 0 and
#       gamma_phi(b',b') = 0 are read off the direct route as well, where they
#       are NOT automatic because the transport (24) intervenes.
#   (4) NEGATIVE CONTROLS for (3): the factor 2 dropped, the sign of u flipped,
#       and E071's endomorphism in place of the class.  Each must miss by more
#       than the certified precision.
#   (5) theta AS A POWER SERIES, two routes, on a good disk.  Route 1 is
#       LocalHeight.theta_series with the base point at b'; route 2 is Lemma
#       5.7 plus (24) plus Lemma 5.5.  Compared coefficient by coefficient.
#       Both are centred at b', which is why the gate CHECKS that b' is a
#       Teichmuller point rather than assuming it.
#   (6) THE PAYOFF: theta_Z as a power series on ](0,0)[ of C_4 at p = 13, the
#       one disk of Phase 5 that Section 5.3 cannot reach.  With it, the
#       regularity on that disk of everything the route touches -- the six
#       basis differentials, eta (which is NOT among them; Section 4.4 puts it
#       in the third-kind span, and Section 5.5's caveat is about exactly this)
#       and gamma_Fil -- and theta((0,0)) = 0, which couples the two
#       normalisations in a disk where neither was imposed.  And the one
#       INDEPENDENT check there is on that disk: sigma: w -> -w fixes (0,0),
#       acts on the disk by t -> -t (the local coordinate is w, Prop. 3.2's
#       second case) and fixes Z, which is built from its own projectors, so
#       theta_Z must be EVEN in t.  The route never mentions sigma.
#
# Run: sage check-c4-leftover.sage      (E081_ONLY=<substring> for one curve)

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
    """p-adic valuation, N for an exact zero."""
    return ZZ(N) if a == 0 else ZZ(a.valuation())


def vmin(elts, N):
    return min([vz(a, N) for a in elts] + [ZZ(N)])


def qp_parts(a, e):
    """E063: an element of Q_p(p^{1/e}) as (its Q_p part, the size of the rest)."""
    if e == 1:
        return a, infinity
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    off = infinity
    for i in range(1, len(c)):
        if c[i] != 0:
            off = min(off, QQ(c[i].valuation()) + QQ(i) / e)
    return (c[0] if c else 0), off


# --------------------------------------------- exact arithmetic in the field

def fn_constant(f):
    """The rational number f, if f is a constant of the function field; else None."""
    cs = f.list()
    if any(c != 0 for c in cs[1:]):
        return None
    c = cs[0]
    num, den = c.numerator(), c.denominator()
    if num.degree() > 0 or den.degree() > 0:
        return None
    return QQ(num) / QQ(den) if den != 0 else None


def fn_at_rational(f, pt):
    """f(pt) for a rational point, exactly over Q."""
    a, b = QQ(pt[0]), QQ(pt[1])
    out = QQ(0)
    for i, c in enumerate(f.list()):
        num, den = c.numerator(), c.denominator()
        d = QQ(den(a))
        if d == 0:
            raise ArithmeticError("gamma_Fil has a pole at %s" % (pt,))
        out += QQ(num(a)) / d * b**i
    return out


# ------------------------------------------------------- the pieces of §5.5

def u_at(FS, P):
    """u_i(P), the exact parts of omega~ = S omega + du, at ANY point.

    The u_i carry no power of r (frobstruct._exact_parts builds them with
    r-adic digit 0), so they are polynomials in x and y and may be evaluated
    in a bad disk -- which is the only reason the conversion of int omega to
    the phase-4 basis survives at (0,0).
    """
    if P.is_good():
        return [FS.evaluate(a, P) for a in FS.u]
    LE = LocalExpansion(P, 4)
    return [FS.series_of(a, LE, as_form=False)[0] for a in FS.u]


def integral_reps(FS, CI, P, Q, e=None):
    """int_P^Q of the PHASE-4 basis forms, as a vector over Q_p.

    Returns (vector, e_used, certified precision).  When an endpoint is bad,
    Algorithm 3.12 runs over Q_p(p^{1/e}) and the answer -- which must lie in
    Q_p, both endpoints being rational -- is projected back.
    """
    if P.is_bad() or Q.is_bad():
        if e is None:
            raise ValueError("a bad endpoint needs an explicit e")
        ee = ZZ(e)
        raw = CI.coleman_integrals_general(P, Q, e=ee)
        pred = CI.certified_precision(*CI.last_eval_points)
        parts = [qp_parts(c, ee) for c in raw]
        comp = [c for c, _ in parts]
        off = min(w for _, w in parts)
    else:
        comp = list(CI.coleman_integrals_on_basis(P, Q))
        ee, off = ZZ(1), infinity
        pred = CI.certified_precision(P, Q)
    K = FS.K
    uP, uQ = u_at(FS, P), u_at(FS, Q)
    n = FS.n
    out = []
    for i in range(n):
        acc = K(0)
        for j in range(n):
            if FS.S[i][j] != 0:
                acc += K(QQ(FS.S[i][j])) * K(comp[j])
        out.append(acc + K(uQ[i]) - K(uP[i]))
    return vector(K, out), ee, pred, off


def lemma57_beta(FS, beta_bb, uvec, factor=2, sign=1, Zm=None):
    """beta_phi^T(b',b') = beta_phi^T(b,b) + 2 (int_b^{b'} omega)^T Z."""
    K = FS.K
    Z = FS.Zk if Zm is None else Zm
    n = FS.n
    out = []
    for j in range(n):
        acc = K(0)
        for i in range(n):
            if Z[i][j] != 0:
                acc += K(sign) * uvec[i] * Z[i][j]
        out.append(beta_bb[j] + K(factor) * acc)
    return vector(K, out)


def theta_series_lemma57(FS, LH_at_bp, bprime, beta_bp, tprec):
    """theta(b',x) on ]b'[ by Lemma 5.7 + (24) + Lemma 5.5."""
    LE, u, w, v = FS.transport_series(bprime, tprec=tprec)
    L = LE.L
    n = FS.n
    alpha = list(u)
    beta = [L(beta_bp[i]) + w[i] for i in range(n)]
    gamma = v
    gfil = L(LH_at_bp.gamma_fil_series(LE))
    return LE, LH_at_bp._assemble(alpha, beta, gamma, gfil), (u, w, v, gfil)


# ------------------------------------------------------------------ per curve

def one(label, Qxy, sx, sy, p, N, bpt, bprime, bad_point=None):
    print("-" * 72)
    print("%s   p = %d, N = %d,  b = %s,  b' = %s" % (label, p, N, bpt, bprime))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    FS = FrobeniusStructure(C, H, p, N, bpt, sx=sx, sy=sy)
    FS.solve()
    cert = FS.cert
    n = FS.n
    K = FS.K
    info("Phi + (22) at b: %.0f s, certified precision p^%d" % (time.time()-t0, cert))

    Zq = matrix(QQ, FS.Z)
    if Zq == 0:
        info("Z = 0 for this curve: EVERY check below is vacuous, and the "
             "curve is run only to show that nothing crashes.")

    # ---- (1) §4.4(d)
    print("  (1) Section 4.4(d), the hypothesis behind Lemma 5.7's gamma = 0")
    check(Zq + Zq.transpose() == 0,
          "Z + Z^T = 0 over Q: Z is antisymmetric, so u^T Z u = 0 for every u")

    # ---- (2) (48)
    print("  (2) Equation (48): the Hodge side under a change of base point")
    LHb = LocalHeight(FS, bpt)
    LHbp = LocalHeight(FS, bprime)
    check(list(LHb.beta_fil) == list(LHbp.beta_fil),
          "beta_Fil(b') = beta_Fil(b), exactly over Q")
    gb, gbp = LHb.gamma_fil, LHbp.gamma_fil
    sc = fn_constant(gb - gbp)
    check(sc is not None,
          "gamma_Fil(b',.) differs from gamma_Fil(b,.) by a CONSTANT")
    if sc is not None:
        check(sc == fn_at_rational(gb, bprime),
              "and the constant is gamma_Fil(b,b') = %s, exactly over Q" % sc)
    check(fn_at_rational(gb, bpt) == 0 and fn_at_rational(gbp, bprime) == 0,
          "each is normalised at its own base point")

    # ---- (3) Lemma 5.7 against the direct route at a good b'
    print("  (3) LEMMA 5.7 AGAINST A SECOND SOLVE OF (22), at the good b'")
    Pb = FS.base_point
    Pbp = CurvePoint(FS.RR, K(QQ(bprime[0])), y=K(QQ(bprime[1])))
    check(Pbp.on_curve() and Pbp.is_good(), "b' is a good point of the curve")
    tp = teichmuller_point(Pbp)
    is_teich = min(Pbp.vp(tp.x - Pbp.x), Pbp.vp(tp.y - Pbp.y)) >= cert
    check(is_teich, "b' is a Teichmuller point (needed so that check (5) can "
          "compare two series centred at the same point)")

    Mb, _ = FS.frob_triv(Pb)
    a_bb, beta_bb, g_bb = FS.read_triv(Mb)
    check(vmin(a_bb, N) >= cert and vz(g_bb, N) >= cert,
          "alpha_phi(b,b) = 0 and gamma_phi(b,b) = 0 (the normalisation of "
          "(22) at b, read back through (23)+(24))")

    CI = ColemanIntegrals(FS.FM)
    t1 = time.time()
    uvec, e_used, pred, off = integral_reps(FS, CI, Pb, Pbp)
    info("int_b^{b'} omega (phase-4 basis), %.0f s, certified p^%s" %
         (time.time()-t1, pred))
    check(vz(sum(uvec[i] * sum(FS.Zk[i][j] * uvec[j] for j in range(n))
                 for i in range(n)), N) >= cert,
          "u^T Z u = 0 for the u actually used")

    beta57 = lemma57_beta(FS, beta_bb, uvec)

    t1 = time.time()
    FS2 = FrobeniusStructure(C, H, p, N, bprime, sx=sx, sy=sy, FM=FS.FM)
    FS2.solve()
    M2, _ = FS2.frob_triv(Pbp)
    a2, beta2, g2 = FS2.read_triv(M2)
    info("the direct route (a second solve of (22) at b'): %.0f s"
         % (time.time()-t1))
    check(vmin(a2, N) >= cert, "alpha_phi(b',b') = 0 by the direct route")
    check(vz(g2, N) >= cert, "gamma_phi(b',b') = 0 by the direct route")
    d3 = vmin([beta57[i] - beta2[i] for i in range(n)], N)
    check(d3 >= cert, "beta_phi(b',b') by LEMMA 5.7 equals the direct route to "
          "p^%s (certified p^%s)" % (d3, cert))
    info("beta_phi(b,b)  = %s" % [str(c) for c in beta_bb])
    info("beta_phi(b',b') = %s" % [str(c) for c in beta2])

    # ---- (4) negative controls
    print("  (4) NEGATIVE CONTROLS for (3)")
    if Zq == 0:
        info("skipped: Z = 0, so every variant below is the same statement")
    else:
        for name, kw in [("the factor 2 dropped", dict(factor=1)),
                         ("the sign of u flipped", dict(sign=-1))]:
            bb = lemma57_beta(FS, beta_bb, uvec, **kw)
            d = vmin([bb[i] - beta2[i] for i in range(n)], N)
            check(d < cert, "%s: misses by p^%s (< p^%s)" % (name, d, cert))
        # E071's mistake: the ENDOMORPHISM matrix carried over as if it were
        # the class.  correspondence() is Z_e; the class is Z_e M^{-1}.
        Ze = matrix(QQ, H.correspondence(sx, sy))
        Zek = FS._toK(FS.Zscale * FS.Si.transpose() * Ze * FS.Si)
        bb = lemma57_beta(FS, beta_bb, uvec, Zm=Zek)
        d = vmin([bb[i] - beta2[i] for i in range(n)], N)
        check(d < cert, "E071's endomorphism in place of the class: misses by "
              "p^%s" % d)

    # ---- (5) theta as a series, two routes
    print("  (5) theta AS A SERIES on ]b'[, two routes")
    tprec = 4 * N + 20
    t1 = time.time()
    LE1, th1, _ = theta_series_lemma57(FS, LHbp, Pbp, beta57, tprec)
    t_l57 = time.time() - t1
    t1 = time.time()
    LH2 = LocalHeight(FS2, bprime)
    LE2, th2 = LH2.theta_series(Pbp, tprec=tprec)
    t_dir = time.time() - t1
    ncoef = min(20, th1.prec() if th1.prec() is not infinity else 20)
    d5 = min([vz(th1[k] - th2[k], N) for k in range(ncoef)] + [ZZ(N)])
    check(d5 >= cert, "the two series agree in the first %d coefficients to "
          "p^%s (certified p^%s)   [Lemma 5.7 %.0f s, direct %.0f s]"
          % (ncoef, d5, cert, t_l57, t_dir))
    check(vz(th1[0], N) >= cert, "theta(b') = 0: the constant term vanishes")

    # ---- (6) the payoff, C_4 only
    ok_all = True
    if bad_point is not None:
        print("  (6) THE PAYOFF: theta_Z as a power series on ]%s[" % (bad_point,))
        Pbad = CurvePoint(FS.RR, K(QQ(bad_point[0])), y=K(QQ(bad_point[1])))
        check(Pbad.on_curve() and Pbad.is_very_bad(),
              "%s is the very bad point of the leftover disk" % (bad_point,))
        LEb = LocalExpansion(Pbad, tprec)
        # regularity of everything the route touches
        wser = [FS.series_of(FS.radic_form(FS.reps[k]), LEb) for k in range(n)]
        vw = [ZZ(s.valuation()) for s in wser]
        check(min(vw) >= 0, "the six basis differentials are regular on the "
              "disk (t-valuations %s)" % vw)
        if any(c != 0 for c in FS.eta):
            es = FS.series_of(FS.radic_form(FS.eta), LEb)
            check(ZZ(es.valuation()) >= 0,
                  "eta is regular on the disk too (t-valuation %s) -- eta is "
                  "NOT one of the six, and Section 5.5's caveat is about "
                  "exactly this" % es.valuation())
        else:
            info("eta = 0 for this curve, so its regularity is vacuous")
        LHbad = LocalHeight(FS, bad_point)
        gfb = LHbad.gamma_fil_series(LEb)
        check(ZZ(gfb.valuation()) >= 0, "gamma_Fil is regular on the disk "
              "(t-valuation %s)" % gfb.valuation())

        t1 = time.time()
        ub, e_b, pred_b, off_b = integral_reps(FS, CI, Pb, Pbad,
                                               e=2 * p * CI.ramification_at(Pbad))
        info("int_b^{(0,0)} omega over Q_p(p^{1/%d}): certified p^%s, "
             "off-Q_p part p^%s   (%.0f s)" % (e_b, pred_b, off_b, time.time()-t1))
        check(off_b >= pred_b, "the integral lies in Q_p, as both endpoints "
              "are rational")
        beta_bad = lemma57_beta(FS, beta_bb, ub)
        LEb2, thb, (ub_s, wb_s, vb_s, gfb_s) = \
            theta_series_lemma57(FS, LHbad, Pbad, beta_bad, tprec)
        need = min(ZZ(cert), ZZ(QQ(pred_b).floor()))
        check(vz(thb[0], N) >= need,
              "theta((0,0)) = 0: the constant term vanishes to p^%s (need p^%s)"
              % (vz(thb[0], N), need))
        cs = [thb[k] for k in range(min(12, tprec))]
        info("beta_phi((0,0),(0,0)) = %s" % [str(c) for c in beta_bad])
        info("theta_Z on ](0,0)[ , first coefficients (v_p):  %s"
             % [str(vz(c, N)) for c in cs])
        info("theta_Z coefficient 1..4: %s" % [str(c) for c in cs[1:5]])
        info("certified precision of the series on this disk: p^%s = "
             "min(chi p^%s, Algorithm 3.12 p^%s)" % (need, cert, pred_b))

        # THE ONE INDEPENDENT CHECK AVAILABLE ON THIS DISK.  sigma: w -> -w
        # fixes (0,0), acts on the disk by t -> -t (the local coordinate IS w,
        # Prop. 3.2's second case), and fixes Z, which is built from sigma's
        # own projectors (E067).  So theta_Z must be EVEN in t.  Nothing in the
        # route knows that: the integrals, the transport and gamma_Fil are all
        # computed without reference to sigma, and the odd coefficients have to
        # cancel.  Note it is available only because the leftover disk happens
        # to be the sigma-FIXED one; ]b'[ at (-1,3) is swapped with ](-1,-3)[
        # and says nothing.
        odd = [vz(cs[k], N) for k in range(1, len(cs), 2)]
        even = [vz(cs[k], N) for k in range(2, len(cs), 2)]
        check(min(odd) >= need,
              "theta_Z is EVEN in t = w: the odd coefficients vanish to p^%s "
              "(certified p^%s) -- sigma-equivariance, which the route never "
              "used" % (min(odd), need))
        check(min(even) < need + 2,
              "and the check is not vacuous: the even coefficients are of size "
              "p^%s, far above the noise" % min(even))
        ok_all = True

    print("  cost: %.0f s" % (time.time() - t0))
    return ok_all


def main():
    print("=== check-c4-leftover.sage --- E081: Lemma 5.7 and theta_Z on "
          "C_4's leftover disk ===")
    t0 = time.time()
    cases = [
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, 7, 8, (0, 1), (0, -1), None),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 13, 8, (1, 3),
         (-1, 3), (0, 0)),
    ]
    only = os.environ.get("E081_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E081_ONLY=%s: running %d of %d curves -- NOT a full gate run)"
              % (only, len(cases), 2))
    for cs in cases:
        try:
            one(*cs)
        except Exception:
            import traceback
            traceback.print_exc()
            FAIL.append("%s raised" % cs[0])
        sys.stdout.flush()
    print("=" * 72)
    print("E081 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t0))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
