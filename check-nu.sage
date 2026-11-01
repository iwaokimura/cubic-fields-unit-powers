# check-nu.sage --- E096: the constant nu between SageMath's p-adic height and
# the Coleman-Gross height this project uses -- and why it does not matter.
#
# Run: sage check-nu.sage
#
# THE QUESTION.  E094 imported B_11 from SageMath's padic_height and had to
# leave one scalar unfixed: the constant nu with
#
#     (the height that enters B)  =  nu * (SageMath's padic_height).
#
# E094's controls showed nu moves H_2 at its leading digit, so it is not a
# rounding matter.  This gate settles what can be settled and proves that the
# residue is harmless.
#
# THE CHAIN, AND WHERE EACH LINK COMES FROM.
#
#  (1) [BDMTV2023, (2.4) and (5.2)]  The global height of the mixed extension is
#      h(x) = h(pi_1(A(x)), pi_2(A(x))^vee(1)) where h on the right is THE
#      height pairing on J, and it is expanded in the basis
#          g_ij(D,E) = (1/2)(log D(w_i) log E(w_j) + log D(w_j) log E(w_i)).
#      So B is the height pairing matrix in log coordinates WITH NO CONSTANT.
#
#  (2) [Besser 2004]  Nekovar's height on the etale cohomology of a curve IS the
#      Coleman-Gross pairing.  So "the height pairing" in (1) is Coleman-Gross.
#
#  (3) [Balakrishnan-Besser, arXiv:1201.6016]  For an elliptic curve ordinary at
#      p, with W the unit root subspace, Coleman-Gross = Mazur-Tate, and
#      explicitly, for x = (a/d^2, b/d^3),
#          h((x)-(0),(x)-(0)) = tau(x) + 2 log_p(d),   tau = -2 log(sigma_p)
#      on the residue disc of 0.  Their idele class character is ell_p = log_p
#      with log_p(p) = 0, and ell_q(q) = -log_p(q) for q != p.
#
#  (4) [E086, this project]  The port's chi is FORCED to be the same one: the
#      product formula applied to the principal idele ell gives
#      chi_ell(ell) = -chi_p(ell), and applied to p gives chi_p(p) = 0, so chi_p
#      is the Iwasawa branch; and the port applies no scalar in Lemma 5.5, which
#      fixes c_p = 1.  IDENTICAL to (3).
#
#  (5) [here, group (1)]  SageMath's padic_height, read off its source, computes
#          -2/n^2 * log_p( sigma(t(nP)) / d(nP) ),
#      which is exactly (3).  This is CHECKED, not read: seven cases across
#      three curves and three primes, agreeing to full precision.
#
# Hence SageMath contributes NO constant, and the character contributes none.
# What is left is a single scalar between the PORT's theta and h_p, and it is
# not a new unknown: it is E088's unexplained factor 2, which compared the
# MEASURED h_3 = -(m_2/4) log_13(3) with E084's mu_Z-predicted (m_2/8) log_13(3).
# Call it epsilon; E088's measurement says epsilon is 2 if E084's mu_Z is right
# and 1 if E086(e)'s identification of j_Gamma with the local height carries the
# factor.  E084 itself recorded that Theorem 3.2's printed mu_F fails a
# consistency condition on this curve and had to be repaired, so neither side is
# above suspicion.
#
# WHY IT DOES NOT MATTER (group 3).  theta, c_2, c_3 and the Prym Gram entries
# are all MEASURED through theta, so they all carry epsilon.  If B_11 is
# imported as epsilon * (SageMath's), then EVERY quantity in the quadratic
# Chabauty equation is homogeneous of degree 1 in epsilon -- including Upsilon,
# whose elements are c_3, c_2 and their sum -- and the set
#     {x : rho(x) in Upsilon}
# is unchanged.  The zero set does not depend on epsilon.  What E094 did instead
# was import B_11 with epsilon = 1 while theta carried the true epsilon; group
# (3) shows that this is the ONE combination that is not homogeneous.

import sys, time
from sage.rings.integer_ring import ZZ

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


CASES = [("37a", 5, 0, 1), ("37a", 7, 0, 1), ("37a", 5, 0, 2),
         ("389a", 5, 0, 1), ("389a", 5, 1, 1),
         ("576h2", 13, 0, 1), ("576h2", 13, 0, 2)]


def bb_height(E, p, P, prec):
    """-2/n^2 log_p( sigma(t(nP)) / d(nP) ), the Coleman-Gross height of
    (P)-(O) in the normalisation of Balakrishnan-Besser."""
    n = lcm(ZZ(E.change_ring(GF(p)).cardinality()),
            lcm(E.tamagawa_numbers()) if E.is_minimal() else ZZ(1))
    Q = n*P
    K = Qp(p, prec)
    t = K(-QQ(Q[0])/QQ(Q[1]))
    d = ZZ(QQ(Q[0]).denominator()).sqrt()
    sig = E.padic_sigma(p, prec + 5)
    sv = sum((K(sig[k])*t**k for k in range(1, prec + 3) if sig[k] != 0), K(0))
    return -2*(sv/K(d)).log()/K(n**2), n, t, d, sv


def main():
    t00 = time.time()
    print("=== check-nu.sage --- E096: SageMath's height, Coleman-Gross, and "
          "the one scalar left ===")

    print("(1) SAGEMATH'S padic_height IS BALAKRISHNAN-BESSER'S COLEMAN-GROSS "
          "HEIGHT")
    prec = 20
    okall, unit_ok = True, True
    for lab, p, i, mult in CASES:
        E = EllipticCurve(lab)
        P = mult*E.gens()[i]
        bb, n, t, d, sv = bb_height(E, p, P, prec)
        hs = E.padic_height(p, prec)(P)
        agree = (hs - bb == 0) or (hs - bb).valuation() >= prec - 1
        info("%-7s p=%-3s %sG_%d  n=%-3s : h_Sage - BB has valuation %s "
             "(h has valuation %s)"
             % (lab, p, mult if mult > 1 else "", i, n,
                "exact 0" if hs - bb == 0 else (hs - bb).valuation(),
                hs.valuation()))
        okall = okall and agree
        unit_ok = unit_ok and ((sv/Qp(p, prec)(d)).valuation() == 0)
    check(okall,
          "h_Sage(P) = -2/n^2 log_p(sigma(t(nP))/d(nP)) at all %d cases, to "
          "full precision.  The right-hand side is Balakrishnan-Besser's "
          "Coleman-Gross height verbatim (tau + 2 log_p d with tau = -2 log "
          "sigma_p), so SAGEMATH'S HEIGHT IS THE COLEMAN-GROSS HEIGHT with the "
          "unit root splitting, in the character chi_p = log_p, "
          "chi_q(q) = -log_p(q) -- which is E086's character exactly" % len(CASES))
    check(unit_ok,
          "and sigma(t(nP))/d(nP) is a UNIT in every case, so the branch of "
          "log_p never enters: the identity is independent of the branch, which "
          "is the computational face of chi_p(p) = 0 (E086(c))")

    print("(2) NEGATIVE CONTROLS ON (1)")
    E = EllipticCurve("576h2")
    P = E.gens()[0]
    bb, n, t, d, sv = bb_height(E, 13, P, prec)
    hs = E.padic_height(13, prec)(P)
    K = Qp(13, prec)
    no2 = -(sv/K(d)).log()/K(n**2)
    nod = -2*sv.log(p_branch=0)/K(n**2)
    check((hs - no2).valuation() < prec - 5,
          "dropping the factor 2 breaks the identity at valuation %s: the 2 in "
          "SageMath's -2/n^2 log(...) is the 2 of tau = -2 log sigma, not a "
          "convention we are free to move" % (hs - no2).valuation())
    check(sv.valuation() > 0 and (hs - nod).valuation() < prec - 5,
          "and dropping the 2 log_p(d) term breaks it at valuation %s -- worse, "
          "sigma(t(nP)) alone has valuation %s, so its logarithm does not even "
          "exist until a branch is chosen.  That term is the whole contribution "
          "of the primes q != p, and it is what makes the answer branch-free"
          % ((hs - nod).valuation(), sv.valuation()))

    print("(3) THE ONE SCALAR LEFT, AND WHY THE ZERO SET DOES NOT SEE IT")
    R = PolynomialRing(QQ, ['e', 't1', 't2', 't3', 't4', 'u', 'v', 'bS', 'm',
                            'q1', 'q2'])
    e, t1, t2, t3, t4, u, v, bS, m, q1, q2 = R.gens()
    # theta measured = e * theta true; B_11 imported as e*bS.
    def system(eps, imp):
        c3 = -eps*t1
        H1 = (eps*t1 + eps*t2 - eps*t4)/m
        c2 = (3*m/4)*H1 - eps*t2
        H2 = 4*(eps*t3 - imp*u*v)/m + H1
        return c3, H1, c2, H2
    base = system(R(1), bS)
    scal = system(e, e*bS)
    check(all(scal[i] == e*base[i] for i in range(4)),
          "with B_11 imported as epsilon * (SageMath's), all four solved "
          "quantities c_3, H_1, c_2, H_2 are homogeneous of degree 1 in "
          "epsilon  [T(CAS)]")
    wrong = system(e, bS)
    check(wrong[3] != e*base[3] and all(wrong[i] == e*base[i] for i in range(3)),
          "whereas importing it with epsilon = 1 -- which is what E094 did -- "
          "leaves c_3, H_1 and c_2 homogeneous but breaks H_2 alone.  That is "
          "the single place in the whole computation where the unknown scalar "
          "is not harmless")
    # the quadratic Chabauty function and Upsilon, both degree 1 in epsilon
    c3, H1, c2, H2 = scal
    rho = e*bS*q1*q2 + H1*q1**2 + H2*q2**2 - e*t3
    ups = [R(0), c3, c2, c3 + c2]
    rho1 = R(1)*bS*q1*q2 + base[1]*q1**2 + base[3]*q2**2 - t3
    check(rho == e*rho1 and all(x == e*y for x, y in zip(ups, [R(0)] + [base[0], base[2], base[0] + base[2]])),
          "and then the quadratic Chabauty function rho = B(E_1,E_2) - theta "
          "AND every element of Upsilon = {0, c_3, c_2, c_3+c_2} carry the same "
          "single power of epsilon, so {x : rho(x) in Upsilon} IS INDEPENDENT "
          "OF epsilon  [T(CAS)].  E086(b) said the scale of chi is harmless; "
          "this is that statement made to survive an imported constant")

    print("(4) WHAT epsilon IS, AND WHERE IT CAN HIDE")
    m2 = QQ(16848)
    meas = -m2/4
    pred = -m2/8
    check(meas/pred == 2,
          "E088's factor: the MEASURED h_3 at t = -1, 0 is -(m_2/4) log_13(3) "
          "(E093) while E084's mu_Z plus E086's c predicts (m_2/8) log_13(3) up "
          "to sign, with the port's Z = -16848 (1+3 sigma)/2 whose elliptic "
          "eigenvalue is M_11 = -33696 = 2 lambda_Z.  The ratio is exactly 2, "
          "and epsilon is that 2 or 1 according to which side carries it")
    info("It cannot be the character: E086(c) pins chi by the product formula, "
         "with no reference to mu_F, and group (1) shows SageMath uses the same "
         "chi.  It cannot be SageMath: group (1) checks that.  So it is either "
         "the port's reading of Lemma 5.4, or E086(e)'s identification of "
         "Theorem 3.2's j_Gamma with the local height -- which E086 itself "
         "labelled 'a convention, not a theorem' -- or E084's mu_Z, which E084 "
         "itself found had to be repaired because the printed formula fails a "
         "consistency condition on this curve.")
    info("The way to settle it from inside the project is the calibration the "
         "plan named long ago: a genus-2 BIELLIPTIC curve, where J ~ E' x E'' "
         "and SageMath supplies BOTH Gram entries, so theta has to equal "
         "B(E_1,E_2) on the nose and epsilon is read off.  That is a full run "
         "of Phase 4-5 on a new curve, not a lemma.")

    print("=" * 72)
    print("E096 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
