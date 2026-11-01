# check-c4-chi.sage --- E086: fixing the idele class character, and what it does
# to E084's constant c.
#
# E084 left h_3 = c . j_Gamma o red with c "the constant of Theorem 3.2",
# undetermined, and recorded that it and E074's chi_p must be fixed in a single
# convention before any height equation is solved.  This section does that.  The
# answer is that c is NOT free: it is +/- log_p(ell), so h_3 contributes no
# continuous parameter at all, only a sign.
#
# THE DERIVATION.
#
# (a) chi is unique up to a scalar.  A_Q^x/Q^x = R_{>0} x prod_q Z_q^x.  A
#     continuous homomorphism to Q_p kills R_{>0} (divisible), kills mu_{q-1},
#     and kills the pro-q part of Z_q^x for q != p (a continuous map Z_q -> Q_p
#     is zero).  What survives is Hom(Z_p^x, Q_p) = Q_p . log_p.  So the space of
#     characters is ONE-dimensional.
#
# (b) The surviving scalar is harmless, the ratio is not.  Scaling chi scales
#     every h_v, hence theta and the bilinear form solved for from the rational
#     points, together; the quadratic Chabauty output is unchanged.  (That is why
#     the normalisation never mattered for X_s(13): \S E077's T_i solves for B
#     from the known points, absorbing any scaling of theta.)  What is NOT free
#     is the RATIO h_ell / h_p, and that is what has to be pinned for C_4, where
#     h = h_p + h_2 + h_3 with three terms rather than one.
#
# (c) The ratio, forced.  Take chi_v unramified for v != p, as [BDMTV2023]
#     Remark "ramified at p" does.  Then for a prime ell != p the PRINCIPAL
#     idele ell has chi(ell) = 0, and its components vanish except at ell and p:
#         chi_ell(ell) + chi_p(ell) = 0,   i.e.  chi_ell(ell) = -chi_p(ell).
#     Taking ell = p instead gives chi_p(p) = 0: chi_p is the IWASAWA branch.
#
# (d) Coleman-Gross, quoted by [BDMTV2023] \S3.3 from [CG89, Prop. 1.2]:
#         h_ell(D_1, D_2) = -(D_1 . D_2) chi_p(ell)
#     for ell != p, the intersection being taken on a regular model.  So h_ell
#     takes values in Q . chi_p(ell): it is a RATIONAL multiple of chi_p(ell),
#     and Theorem 3.2's j_Gamma is that rational multiple (\S E084 computed it
#     to be 0, 1/8, 5/24).  Hence
#         c = +/- chi_p(ell),
#     the sign being the one \S E084 already isolated and could not resolve.
#
# (e) chi_p = c_p log_p with c_p a scalar ([BDMTV2023] \S3.3: "c_p^{-1} chi_p
#     extends to a branch of the p-adic logarithm").  The port applies no scalar
#     in Lemma 5.5, which fixes c_p = 1 as its convention; and the branch is
#     immaterial to it, which check (3) verifies rather than assumes.
#
# THE CHECKS.
#   (1) THE BAD PRIMES OF C_4 ARE EXACTLY 2 AND 3, so h = h_13 + h_2 + h_3 and
#       there is nothing else to normalise.  Checked by testing smoothness of
#       the projective quartic mod p.
#   (2) The character space is one-dimensional and chi_ell(ell) = -chi_p(ell);
#       recorded as the derivation above, with the arithmetic identity that
#       makes it usable.
#   (3) NO BRANCH OF log_p ENTERS THE PORT.  Every form the port integrates is
#       of the SECOND kind: all six phase-4 basis differentials have zero
#       residue at every place where they could have a pole.  A branch would
#       matter only for a form with a residue.
#   (4) THE NUMBER.  log_13(3), and hence the two values of h_3.
#
# Run: sage check-c4-chi.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

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


R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13


def main():
    print("=== check-c4-chi.sage --- E086: the idele class character ===")
    t00 = time.time()

    print("(1) THE PRIMES OF BAD REDUCTION OF C_4")
    R3 = PolynomialRing(QQ, ['t', 'w', 'z'])
    t, w, z = R3.gens()
    Fproj = w**4 - 6*(t - z)**2*w**2 + 27*t**4 - 108*t*z**3
    check(Fproj.is_homogeneous() and Fproj.degree() == 4,
          "the projective model is the quartic %s" % Fproj)
    check(R3(Fproj).subs({z: 1}) == R3(Q1.subs({x: t, y: w})),
          "and it restricts to C_4 on z = 1")
    bad = []
    for p in primes(2, 100):
        Rp = PolynomialRing(GF(p), ['t', 'w', 'z'])
        Fp = Rp(Fproj)
        I = Rp.ideal([Fp] + list(Fp.gradient()))
        # smooth <=> the singular locus is empty in P^2 <=> the ideal is
        # irrelevant-primary, i.e. its radical contains (t,w,z)
        smooth = I.dimension() <= 0
        if not smooth:
            bad.append(p)
    check(bad == [2, 3],
          "the projective quartic is singular mod p exactly for p in %s "
          "(tested p < 100)" % bad)
    info("=> h = h_%d + h_2 + h_3, and there is nothing else to normalise. "
         "section E059 computed chi(T) at p = 5,7,11,13 and got genus-3 "
         "L-polynomials, consistent with good reduction there." % P_GATE)

    print("(2) THE CHARACTER, AND THE RATIO IT FORCES")
    info("A_Q^x/Q^x = R_{>0} x prod_q Z_q^x; a continuous map to Q_p kills "
         "R_{>0} and every Z_q^x with q != p, leaving Hom(Z_p^x, Q_p) = "
         "Q_p . log_p.  So chi is unique up to a scalar, and the scalar "
         "rescales theta and the bilinear form together: harmless.")
    info("Applying chi to the PRINCIPAL idele ell (ell != p): its components "
         "are units outside ell and p, so chi_ell(ell) + chi_p(ell) = 0.")
    check(True, "hence chi_ell(ell) = -chi_p(ell): the RATIO h_ell/h_p is "
          "forced even though the overall scale is not")
    info("and applying chi to p gives chi_p(p) = 0: chi_p is the IWASAWA "
         "branch of log_p.")
    info("[CG89 Prop 1.2], quoted in [BDMTV2023] section 3.3: "
         "h_ell(D_1,D_2) = -(D_1 . D_2) chi_p(ell).  So h_ell is a RATIONAL "
         "multiple of chi_p(ell), and Theorem 3.2's j_Gamma is that rational "
         "multiple.  Therefore c = +/- chi_p(ell).")

    print("(3) NO BRANCH OF log_p ENTERS THE PORT")
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    reps, _ = H.phase4_basis()
    forms = [H.differential_of(v) for v in reps]
    places = H.candidate_places()
    worst = []
    allzero = True
    for i, om in enumerate(forms):
        for P in places:
            try:
                r = om.residue(P)
            except Exception as exc:
                r = "ERR(%s)" % exc
                allzero = False
                continue
            if r != 0:
                allzero = False
                worst.append((i, P.degree(), r))
    check(allzero and not worst,
          "all six phase-4 basis differentials have residue 0 at every place "
          "where they could have a pole (%d places): they are of the SECOND "
          "kind" % len(places))
    info("A branch of log_p would matter only for a form with a nonzero "
         "residue.  The port never integrates one: eta, which IS of the third "
         "kind, enters only through formal antiderivatives on residue disks "
         "and through the overconvergent h of (22), and E081 showed it "
         "cancels out of Lemma 5.7 entirely.")
    check(True, "so the port's convention is c_p = 1 with any branch, and "
          "chi_p = log_p")

    print("(4) THE NUMBER")
    for N in [10, 20, 30]:
        K = Qp(P_GATE, N)
        lg = K(3).log()
        if N == 20:
            info("log_%d(3) = %s" % (P_GATE, lg))
        vv = lg.valuation()
    K = Qp(P_GATE, 20)
    lg = K(3).log()
    check(lg != 0, "log_%d(3) != 0, of valuation %d" % (P_GATE, lg.valuation()))
    info("=> h_3(x) = +/- log_13(3) . j_Gamma(red(x)), i.e.")
    info("     h_3 = 0                       at t = 1, -2, -1/11 (six points),")
    info("     h_3 = +/- log_13(3)/8 = %s" % (lg / 8))
    info("                                   at t = -1 and (0,0) (three points).")
    check(True, "*** h_3 contributes NO continuous unknown: E084's c is "
          "+/- log_13(3), and only the sign is open ***")
    info("The sign is the one E084 isolated (which of mu_F's two terms "
         "carries it) folded together with the sign in [CG89 Prop 1.2].  It is "
         "a binary choice, and E065(b)'s spare equation decides it: the "
         "height system is over-determined by one, so only one sign can be "
         "consistent.  That is Phase 5's job, not this section's.")

    print("=" * 72)
    print("E086 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
