# check-c4-ell2.sage --- E085: what can and cannot be settled at ell = 2, and an
# independent confirmation of E083 at ell = 3.
#
# E084 left one piece of mathematics in the plan: the local height h_2.  Three
# routes were on the table -- (1) a stable model by hand, (2) MCLF, (3) carry
# h_2 as unknowns, measuring first how many unknowns that is.  This gate runs
# (3) and then (2), and reports honestly on both.
#
# WHY (3) CANNOT SETTLE IT, stated before running it.  h_2 = c_2 . j_Gamma o red
# depends on x only through red(x), so two rational points with the SAME
# reduction have the same h_2 and the number of unknowns is
# (number of distinct reduction classes) - 1.  Proving two points have the same
# reduction is a statement about the stable model, which is exactly what is
# missing.  Distances bound it in the wrong direction: they can only show two
# points are close, and "close enough" is measured in a metric the model
# defines.  So (3) yields data and no bound.  It is run anyway because the data
# is exact, cheap, and needed by whichever route succeeds.
#
# THE CHECKS.
#   (1) E AT 2.  Kodaira type, conductor exponent, and j = 1728 with v_2(j) >= 0;
#       E has CM by Z[i] and so potentially good reduction at every prime.  So
#       whatever degeneration C_4 has at 2 is in the Prym, as at 3.
#   (2) THE BRANCH LOCUS AT 2, exactly, in Q(zeta_3, 4^{1/3}).  Unlike ell = 3,
#       where the four points sit at v(tau) = 0, 1/3, 1/3, 1/3 with a nested
#       cluster, at ell = 2 they are PAIRWISE EQUIDISTANT at v_2 = 2/3: one
#       cluster, no sub-clusters, maximal symmetry.
#   (3) THE NINE RATIONAL POINTS.  C_4 mod 2 is (t+w)^4, so the naive reduction
#       is a quadruple line and says nothing; the natural depth v_2(t+w) spreads
#       the nine points over 1,1,1,2,2,2,3,4,infinity.  Reported, not used.
#   (4) MCLF AT ell = 2: REFUSED.  SemistableModel dispatches to AdmissibleModel
#       only when gcd(p, deg) = 1, and to SuperpModel only for a superelliptic
#       curve of degree p over the projective line.  Here deg = 4 and p = 2, and
#       C_4 is a non-hyperelliptic plane quartic, so it has no degree-2 map to
#       P^1 at all.  NotImplementedError.  This reproduces [BDMTV2023]'s own
#       report that MCLF did not suffice for their wild prime.
#   (5) MCLF AT ell = 3: it works, and it CONFIRMS \S E083 independently.
#       Exactly two components of positive genus, both of genus 1, one of them
#       literally u^4 + x^2 u^2 + 2 over F_3 -- which is E083's W^4 + T^2W^2 - 1,
#       derived there by hand from a substitution into C_4.  And MCLF's
#       reduction_genus, documented as (sum of the genera of the upper
#       components) + (number of loops), returns 3 against a genus sum of 2:
#       so the number of loops is 1.  TORIC RANK 1, from a second
#       implementation sharing no step with E083.
#
# Run: sage check-c4-ell2.sage

import sys, time

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


Rt = PolynomialRing(QQ, 't')
t = Rt.gen()
KNOWN = [(QQ(1), QQ(3)), (QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
         (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)),
         (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11), (QQ(0), QQ(0))]


def v2(x):
    return +Infinity if x == 0 else QQ(x).valuation(2)


def main():
    print("=== check-c4-ell2.sage --- E085: ell = 2, and MCLF ===")
    t00 = time.time()

    print("(1) E AT ell = 2")
    E = EllipticCurve([-36, 0])
    ld = E.local_data(2)
    check(E.has_cm() and E.cm_discriminant() == -4,
          "E = y^2 = x^3-36x has CM by Z[i], so potentially good reduction "
          "everywhere")
    check(E.j_invariant() == 1728 and QQ(E.j_invariant()).valuation(2) >= 0,
          "j = 1728 with v_2(j) = %s >= 0"
          % QQ(E.j_invariant()).valuation(2))
    info("Kodaira %s, conductor exponent %s, v_2(disc) %s, Tamagawa %s"
         % (ld.kodaira_symbol(), ld.conductor_valuation(),
            ld.discriminant_valuation(), ld.tamagawa_number()))
    info("=> whatever degeneration C_4 has at 2 lives in the Prym, as at 3.")

    print("(2) THE BRANCH LOCUS AT ell = 2, EXACTLY")
    L0 = NumberField([t**2 + t + 1, t**3 - 4], ['z', 'c'])
    L = L0.absolute_field('a')
    _, to = L.structure()
    z, c = [to(u) for u in L0.gens()]
    Pr = L.primes_above(2)[0]
    e = ZZ(Pr.ramification_index())

    def v(u):
        return +Infinity if u == 0 else QQ(L(u).valuation(Pr)) / e

    check(len(L.primes_above(2)) == 1 and e == 3,
          "2 has a single prime in Q(zeta_3, 4^(1/3)), with e = 3, f = 2")
    check(v(c) == QQ(2)/3 and v(z - 1) == 0,
          "v_2(4^(1/3)) = 2/3 and zeta_3 - 1 is a unit (Q_2(zeta_3) is "
          "unramified)")
    taus = [L(-1), c - 1, c*z - 1, c*z**2 - 1]
    pw = set()
    for i in range(4):
        for j in range(i + 1, 4):
            pw.add(v(taus[i] - taus[j]))
    check(pw == {QQ(2)/3},
          "the four branch points are PAIRWISE EQUIDISTANT at v_2 = 2/3: one "
          "cluster with no sub-clusters (at ell = 3 they were 0, 1/3, 1/3, 1/3 "
          "with a nested cluster)")
    check(all(v(x) == 0 for x in taus), "all four have v_2(tau) = 0")

    print("(3) THE NINE RATIONAL POINTS AT ell = 2 -- DATA, NOT A BOUND")
    Rxy = PolynomialRing(GF(2), ['x', 'y'])
    X, Y2 = Rxy.gens()
    Q2 = Rxy(Y2**4 - 6*(X-1)**2*Y2**2 + 27*X*(X**3-4))
    check(Q2 == (X + Y2)**4,
          "C_4 mod 2 is (t+w)^4: the naive reduction is a quadruple line and "
          "distinguishes nothing")
    depths = [v2(a + b) for (a, b) in KNOWN]
    info("v_2(t+w) at the nine points: %s" % [str(d) for d in depths])
    check(len(set(depths)) == 5,
          "they take %d distinct values, so the points are spread rather than "
          "clustered" % len(set(depths)))
    info("*** this is DATA AND NOT A BOUND: h_2(x) depends only on red(x), so "
         "equal reductions give equal h_2, but proving two points have equal "
         "reduction is a statement about the stable model -- which is what is "
         "missing.  Option (3) cannot settle the number of unknowns. ***")

    print("(4) MCLF AT ell = 2")
    from mclf import SmoothProjectiveCurve, SemistableModel
    F0 = FunctionField(QQ, 'x')
    xf = F0.gen()
    Ry = PolynomialRing(F0, 'y')
    yf = Ry.gen()
    F = F0.extension(yf**4 - 6*(xf-1)**2*yf**2 + 27*xf*(xf**3-4), 'y')
    Yc = SmoothProjectiveCurve(F)
    check(Yc.genus() == 3 and Yc.covering_degree() == 4,
          "MCLF sees the curve: genus 3, degree 4 over P^1")
    check(gcd(2, Yc.covering_degree()) != 1,
          "gcd(2, 4) = %d != 1, so the cover is WILD at 2 and MCLF's "
          "AdmissibleModel branch does not apply" % gcd(2, Yc.covering_degree()))
    refused = False
    try:
        SemistableModel(Yc, QQ.valuation(2))
    except NotImplementedError:
        refused = True
    check(refused, "SemistableModel(C_4, v_2) raises NotImplementedError")
    info("MCLF's other branch, SuperpModel, needs a superelliptic curve of "
         "degree p over P^1; C_4 is a non-hyperelliptic plane quartic and has "
         "no degree-2 map to P^1 at all, so it does not apply either.")
    info("=> option (2) is exhausted.  [BDMTV2023] report the same for their "
         "own wild prime, and did the blow-ups by hand.")

    print("(5) MCLF AT ell = 3: AN INDEPENDENT CHECK ON E083")
    t0 = time.time()
    M = SemistableModel(Yc, QQ.valuation(3))
    check(M.is_semistable(), "MCLF builds a semistable model at 3 (%.0f s)"
          % (time.time() - t0))
    pos = M.components_of_positive_genus()
    gs = sorted(C.genus() for C in pos)
    check(gs == [1, 1],
          "exactly two components of positive genus, of genera %s -- E083 has "
          "Ebar' and F, both of genus 1, and R of genus 0" % gs)
    # the component over Ebar, as E083 derived it by hand
    want = None
    R3 = PolynomialRing(GF(3), 'u')
    u = R3.gen()
    for C in pos:
        f = C.function_field().polynomial()
        if f.degree() == 4:
            want = f
    check(want is not None, "one of them is a degree-4 cover: %s" % want)
    if want is not None:
        cs = [str(cc) for cc in want.list()]
        check(cs == ['2', '0', 'x^2', '0', '1'],
              "and its equation is u^4 + x^2 u^2 + 2 over F_3, which is "
              "E083's W^4 + T^2W^2 - 1 -- derived there by hand from the "
              "substitution tau = sqrt3 T, w = 3W")
    rg = M.reduction_tree().reduction_genus()
    check(rg == 3, "MCLF's reduction_genus is %s" % rg)
    b1 = rg - sum(gs)
    check(b1 == 1,
          "reduction_genus is documented as (sum of the genera of the upper "
          "components) + (number of loops), so the number of loops is "
          "%d - %d = %d: *** TORIC RANK 1 AT ell = 3, CONFIRMED BY A SECOND "
          "IMPLEMENTATION ***" % (rg, sum(gs), b1))
    try:
        info("MCLF's conductor exponent at 3: %s" % M.conductor_exponent())
    except Exception as exc:
        info("conductor_exponent failed: %s" % exc)

    print("=" * 72)
    print("E085 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
