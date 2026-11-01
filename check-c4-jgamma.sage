# check-c4-jgamma.sage --- E084: j_Gamma at ell = 3 for C_4, and the values of
# h_3 on the known rational points.
#
# E083 determined the reduction of C_4 at ell = 3.  The dual graph Gamma of the
# stable model has three vertices and three edges:
#
#        e_1
#   Ebar' ==== R ---- F          Ebar' : genus 1 (over Ebar), sigma-stable
#        e_2   e_3               R     : genus 0 (over the middle P^1)
#                                F     : genus 1 (over the end P^1)
#
# with e_1, e_2 the two preimages of the UNBRANCHED node and e_3 the single
# preimage of the BRANCHED one.  b_1(Gamma) = 1 and sigma swaps e_1, e_2.
#
# EDGE LENGTHS.  On the base, the three components sit at levels v(s) = 0, 1/6,
# 1/3 of the residue disk of infinity on Ebar (E083's cluster data), so the two
# base annuli have modulus 1/6 each.  Upstairs, the unbranched node lifts to two
# annuli mapping isomorphically (length 1/6 each) and the branched node to a
# single annulus mapping by z -> z^2, whose modulus is therefore HALVED:
#     l(e_1) = l(e_2) = 1/6,     l(e_3) = 1/12.
#
# [BDMTV2023] Theorem 3.2 (= [BeD19] Thm 1.1.2, Lemma 12.1.1, Cor 12.1.3) says
# h_ell = c . j_Gamma o red with j_Gamma the unique piecewise polynomial function
# with j_Gamma(red(b)) = 0 and Laplacian
#
#   nabla^2(g) = - sum_e g''(x_e) . e
#                + sum_v ( sum_{s(e)=v} g'(0) - sum_{t(e)=v} g'(l(e)) ) . v ,
#   mu_F = sum_e (1/l(e)) e^* F(pi(e)) . e + (1/2) sum_w Tr(F|V_p(X_w)) . w .
#
# A CONSISTENCY CONDITION, AND A SIGN.  Summing the vertex part of nabla^2(g)
# over all v gives sum_e (g'_e(0) - g'_e(l_e)) = -sum_e g''_e l_e, so ANY mu in
# the image of nabla^2 satisfies
#
#        sum_v mu_v  =  sum_e mu_e . l(e).                             (*)
#
# For mu_F exactly as printed, sum_e mu_e l(e) = sum_e e^* F(pi(e)) = Tr(F|H_1),
# while sum_v mu_v = (1/2) Tr(F|gr^W_1) = -Tr(F|H_1) because Tr(F|V_p) = 0 and
# gr^W_0, gr^W_2 are both H_1 up to duality.  So (*) reads Tr(F|H_1) = 0, which
# is an extra hypothesis nothing in the set-up supplies.  For C_4 at ell = 3 it
# FAILS: Tr(Z|H_1(Gamma)) = -1.  Check (3) measures this.
#
# It does not block the computation.  The discrepancy is exactly a sign on one
# of the two terms of mu_F, and the two possible corrections differ by an
# overall sign of mu, hence give j_Gamma and -j_Gamma -- and Theorem 3.2's
# constant c is undetermined anyway, so it absorbs it.  Check (5) verifies that.
#
# THE CHECKS.
#   (1) The graph, the edge lengths, and Z's action, transcribed from E083.
#   (2) mu_Z: the edge part from pi and Z|H_1, the vertex part from the traces.
#   (3) The consistency condition (*), for the printed mu_F and for both sign
#       corrections.  THIS IS THE FALSIFIABLE ONE.
#   (4) j_Gamma solved exactly over Q, and nabla^2 j_Gamma = mu verified by
#       substitution -- not by construction.
#   (5) The two sign corrections give j and -j.
#   (6) Where the nine known rational points reduce, from E083's valuations.
#   (7) h_3 on them, up to the constant c.
#
# Run: sage check-c4-jgamma.sage

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


# ---------------------------------------------------------------- the graph
# vertices 0 = Ebar', 1 = R, 2 = F
VNAME = ["Ebar'", "R", "F"]
# edges: (source, target, length)
EDGES = [(0, 1, QQ(1)/6), (0, 1, QQ(1)/6), (1, 2, QQ(1)/12)]
ENAME = ["e_1", "e_2", "e_3"]
# Z on the graded pieces (E083 check (7)): (dim, Z-eigenvalue)
ZGRADED = {"H_1": (1, -1), "Ebar'": (2, 2), "R": (0, 0), "F": (2, -1)}


def laplacian(quad, lin, const):
    """nabla^2 of the piecewise polynomial with g|_e = const[e] + lin[e] x
    + quad[e] x^2 : returns (edge coefficients, vertex coefficients)."""
    ec = [-2 * quad[i] for i in range(3)]          # -g''
    vc = [QQ(0)] * 3
    for i, (s, tt, L) in enumerate(EDGES):
        vc[s] += lin[i]                            # g'(0)
        vc[tt] -= lin[i] + 2 * quad[i] * L         # -g'(l(e))
    return ec, vc


def main():
    print("=== check-c4-jgamma.sage --- E084: j_Gamma at ell = 3 ===")
    t0 = time.time()

    print("(1) THE GRAPH AND THE EDGE LENGTHS (from E083)")
    check(len(EDGES) == 3 and len(VNAME) == 3,
          "V = 3, E = 3, so b_1(Gamma) = %d" % (len(EDGES) - len(VNAME) + 1))
    check([e[2] for e in EDGES] == [QQ(1)/6, QQ(1)/6, QQ(1)/12],
          "edge lengths 1/6, 1/6 (unbranched node, two isomorphic annuli) and "
          "1/12 (branched node, the annulus is a degree-2 cover so its modulus "
          "is halved)")
    check(ZGRADED["H_1"][1] == -1,
          "sigma swaps e_1 and e_2, so sigma = -1 on H_1(Gamma) and "
          "Z = (1+3 sigma)/2 acts by -1")

    print("(2) mu_Z")
    # H_1 is spanned by gamma = e_1 - e_2; pi is the orthogonal projection.
    gam = vector(QQ, [1, -1, 0])
    pi = [gam * (gam[i] / (gam * gam)) for i in range(3)]
    zH = ZGRADED["H_1"][1]
    edge_mu = [QQ(zH) * pi[i][i] / EDGES[i][2] for i in range(3)]
    check(edge_mu == [-3, -3, 0],
          "edge part (1/l(e)) e^* Z(pi(e)) = %s" % edge_mu)
    vert_mu = [QQ(ZGRADED[VNAME[k]][0] * ZGRADED[VNAME[k]][1]) / 2
               for k in range(3)]
    check(vert_mu == [2, 0, -1],
          "vertex part (1/2) Tr(Z|V_p(X_w)) = %s" % vert_mu)

    print("(3) THE CONSISTENCY CONDITION (*)")
    lhs = sum(vert_mu)
    rhs = sum(edge_mu[i] * EDGES[i][2] for i in range(3))
    trH1 = QQ(ZGRADED["H_1"][0] * ZGRADED["H_1"][1])
    check(rhs == trH1, "sum_e mu_e l(e) = Tr(Z|H_1) = %s" % rhs)
    check(lhs == -trH1, "sum_v mu_v = -Tr(Z|H_1) = %s" % lhs)
    check(lhs != rhs,
          "*** as printed, (*) FAILS for C_4 at ell = 3: %s != %s, because "
          "Tr(Z|H_1(Gamma)) = %s is not 0 ***" % (lhs, rhs, trH1))
    info("nothing in the set-up forces Tr(F|H_1) = 0; [BDMTV2023]'s own "
         "examples have H_1 = 0 or F acting trivially on the graph, where the "
         "question does not arise.")
    variants = {"edge part negated": ([-c for c in edge_mu], vert_mu),
                "vertex part negated": (edge_mu, [-c for c in vert_mu])}
    for nm, (em, vm) in variants.items():
        check(sum(vm) == sum(em[i] * EDGES[i][2] for i in range(3)),
              "with the %s, (*) holds" % nm)

    print("(4) j_Gamma, SOLVED EXACTLY AND VERIFIED BY SUBSTITUTION")
    sols = {}
    for nm, (em, vm) in variants.items():
        R9 = PolynomialRing(QQ, ['A', 'a', 'a3'])
        A, a, a3 = R9.gens()
        quad = [-em[i] / 2 for i in range(3)]      # g'' = -mu_e
        # continuity: both e_1, e_2 start at Ebar' with value A and, having the
        # same length, must have the same linear coefficient; e_3 starts at R.
        lin = [a, a, a3]
        vR = A + a * EDGES[0][2] + quad[0] * EDGES[0][2]**2
        const = [A, A, vR]
        ec, vc = laplacian(quad, lin, const)
        eqs = [vc[k] - vm[k] for k in range(3)]
        # continuity of e_2 at R is automatic; solve the vertex equations
        M = matrix(QQ, [[e.coefficient({A: 1}), e.coefficient({a: 1}),
                         e.coefficient({a3: 1})] for e in eqs])
        rhsv = vector(QQ, [-e.constant_coefficient() for e in eqs])
        # the system is rank 2 (a and a3); A is fixed by the normalisation.
        sol = M.submatrix(0, 1, 3, 2).solve_right(rhsv)
        aval, a3val = QQ(sol[0]), QQ(sol[1])
        quadn = [QQ(q) for q in quad]
        linn = [aval, aval, a3val]
        # normalisation j(red(b)) = 0 with b = (1,3), which reduces to Ebar'
        Aval = QQ(0)
        vRn = Aval + aval * EDGES[0][2] + quadn[0] * EDGES[0][2]**2
        constn = [Aval, Aval, vRn]
        ecn, vcn = laplacian(quadn, linn, constn)
        ok = (ecn == em and vcn == vm)
        check(ok, "[%s] nabla^2 j = mu verified by substitution: edges %s, "
              "vertices %s" % (nm, ecn, vcn))
        jv = [Aval, vRn, vRn + a3val * EDGES[2][2]]
        sols[nm] = jv
        info("[%s] g'' = %s, slopes a = %s, a_3 = %s" % (nm, quadn, aval, a3val))
        info("[%s] j_Gamma at (%s) = %s"
             % (nm, ", ".join(VNAME), [str(x) for x in jv]))

    print("(5) THE TWO SIGN CORRECTIONS GIVE j AND -j")
    ks = list(variants)
    check(sols[ks[0]] == [-x for x in sols[ks[1]]],
          "%s and %s give j_Gamma and -j_Gamma, so Theorem 3.2's undetermined "
          "constant c absorbs the ambiguity" % (ks[0], ks[1]))
    J = sols["edge part negated"]

    print("(6) WHERE THE KNOWN RATIONAL POINTS REDUCE")
    # E083: the disk of infinity on Ebar is {v(tau) < 1/2}, in which
    # v(s) = 1/2 - v(tau); the middle component sits at v(s) = 1/6, i.e.
    # v(tau) = 1/3, and the end one at v(s) = 1/3, i.e. v(tau) = 1/6.
    KNOWN = [(QQ(1), QQ(3)), (QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
             (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)),
             (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11), (QQ(0), QQ(0))]
    where = {}
    for (tt, ww) in KNOWN:
        tau = tt - 1
        vt = +Infinity if tau == 0 else QQ(tau.valuation(3))
        if vt > QQ(1)/2:
            comp = "Ebar'"
        else:
            vs = QQ(1)/2 - vt
            comp = "R" if vs > QQ(1)/6 else "(edge or beyond)"
        where[(tt, ww)] = comp
        info("t = %-6s w = %-7s v(tau) = %-4s -> %s" % (tt, ww, vt, comp))
    onE = [k for k in KNOWN if where[k] == "Ebar'"]
    onR = [k for k in KNOWN if where[k] == "R"]
    check(len(onE) == 6 and len(onR) == 3,
          "six of the nine reduce to Ebar' (t = 1, -2, -1/11) and three to R "
          "(t = -1 and (0,0))")
    check(where[(QQ(1), QQ(3))] == "Ebar'",
          "the Phase-4 base point b = (1,3) reduces to Ebar', so the "
          "normalisation j_Gamma(red(b)) = 0 is the one used above")

    print("(7) h_3 ON THE KNOWN RATIONAL POINTS")
    info("h_3(x) = c . j_Gamma(red(x)) with j_Gamma = %s at (%s)"
         % ([str(x) for x in J], ", ".join(VNAME)))
    check(J[0] == 0 and J[1] == QQ(1)/8 and J[2] == QQ(5)/24,
          "j_Gamma = 0, 1/8, 5/24 at Ebar', R, F")
    info("=> h_3 = 0            at t = 1, -2, -1/11 (six points), and")
    info("   h_3 = c/8          at t = -1 and at (0,0) (three points).")
    info("So h_3 costs the height equations ONE unknown, the constant c of "
         "Theorem 3.2 -- not one unknown per point, and not an unknown "
         "function.  The sign ambiguity of check (5) is inside c.")

    print("=" * 72)
    print("E084 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t0))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
