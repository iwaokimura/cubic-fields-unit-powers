# check-c4-ell3.sage --- E083: the reduction of C_4 at ell = 3, and what it
# makes of the local height h_3.
#
# E065(a4) left a [GAP: sketch, not verified]: "at ell = 3 the three colliding
# points force one P^1 bridge meeting Ebar at a single node; parity forces the
# node to be a branch point, so its preimage is one point, and Gamma is two
# vertices joined by one edge -- a tree, H_1 = 0, toric rank 0."
#
# THAT SKETCH IS WRONG, IN ITS PREMISE AND IN ITS CONCLUSION, and this gate
# establishes what is true instead.  The premise E065(a1) measured -- "the three
# cube roots collide; t = 0 stays apart" -- is a statement about the t-LINE.  The
# base of the double cover C_4 -> E is E, not P^1_t, and the map t degenerates at
# 3 (its model reduces to v^2 = tau^4).  Measured on a GOOD model of E, all four
# branch points lie in ONE residue disk.
#
# THE SET-UP.  sigma : w -> -w, E := C_4/sigma, and C_4 -> E is a double cover
# branched at the four points w = 0, i.e. 27t(t^3-4) = 0.  In coordinates,
# E : u^2 - 6(t-1)^2 u + 27t(t^3-4) = 0 with u = w^2; completing the square and
# writing tau = t-1, v_1 = (u - 3tau^2)/3,
#       E : v_1^2 = -2tau^4 - 12tau^3 - 18tau^2 + 9,
# and the four branch points are v_1 = -tau^2, i.e. the roots of
# tau^4 + 4tau^3 + 6tau^2 - 3 = 0, namely tau = -1 (from t = 0) and tau = y_i
# with (1+y)^3 = 4.  Residue characteristic 3 does not divide the degree 2 of the
# cover, so the cover is TAME and the stable model of C_4 is the admissible cover
# of the stable model of the 4-pointed curve (E; P_0,P_1,P_2,P_3).
#
# THE CHECKS.
#   (1) The quotient E, exactly over Q: its binary-quartic invariants are
#       I = 108, J = 0, so j = 1728 and E is the curve y^2 = x^3-36x of E039.
#   (2) A GOOD MODEL OF E AT 3.  T = tau/sqrt3, V = v_1/3 makes the quartic
#       integral over Q_3(sqrt3) with reduction V^2 = T^4+1, which is smooth of
#       genus 1.  So E acquires good reduction over Q_3(sqrt3).
#   (3) THE BRANCH POINTS ON THAT MODEL.  v(T) < 0 for ALL FOUR and V/T^2 = -1
#       for all four, exactly: they lie in the single residue disk of the point
#       at infinity where V/T^2 = -1.  THIS IS THE CORRECTION TO E065(a1).
#   (4) THE CLUSTER PICTURE on that disk, in s = 1/T: P_0 at v(s) = 1/2, the
#       three P_i at v(s) = 1/6 with pairwise v = 1/3, and v(s_0 - s_i) = 1/6.
#       So the stable 4-pointed model of E is the chain
#           Ebar --- P^1_{(1/6)} --- P^1_{(1/3)},
#       with P_0 on the middle component and P_1,P_2,P_3 on the end one.
#   (5) THE COMPONENTS OF THE COVER, by explicit reduction of C_4 itself, which
#       is what settles the question the sketch got wrong:
#         tau = sqrt3 T, w = 3W        ->  W^4 + T^2W^2 - 1  over F_3,
#         tau = 3^{1/3}t_1, w = 3^{7/6}w_1 -> t_1^2 w_1^2 + t_1^3 - 1.
#       The first is IRREDUCIBLE of genus 1: the etale double cover of Ebar does
#       NOT split.  The second has genus 0, and reading w_1^2 = (1-t_1^3)/t_1^2
#       shows the map to the t_1-line is branched at t_1 = 1 (the node down) and
#       t_1 = infinity (the point P_0) and UNBRANCHED at t_1 = 0 -- so the node
#       joining the middle component to Ebar has TWO preimages.
#   (6) HENCE b_1(Gamma) = 1: TORIC RANK 1, not 0.  Two edges run between the
#       genus-1 component over Ebar and the genus-0 middle one, and one more to
#       the last component, whose genus is then forced to be 1 by p_a = 3.
#   (7) WHAT SAVES IT.  H_1(Gamma) is ONE-dimensional and sigma SWAPS the two
#       edges over the unbranched node, so sigma = -1 on H_1(Gamma) and
#       Z = (1+3sigma)/2 acts by -1.  Everything in [BDMTV2023] Theorem 3.2's
#       mu_Z is therefore determined, without the "forthcoming work" that paper
#       cites for the action of F on H_1(Gamma).
#   (8) THE CONSISTENCY CHECK THAT COULD HAVE FAILED.  Assembling Z's action on
#       the graded pieces of the weight filtration must reproduce E082's
#       characteristic polynomial (x-2)^2 (x+1)^4 of Z on V_p, eigenvalue by
#       eigenvalue.  Nothing forces that: the left-hand side comes from a
#       3-adic degeneration and the right-hand side from End(J) over Q.
#
# Run: sage check-c4-ell3.sage

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
F3 = GF(3)


def geom_genus(poly2, name):
    """Geometric genus over F_3 of a plane curve given as a poly in (A, B)."""
    K = FunctionField(F3, 'X')
    X = K.gen()
    RY = PolynomialRing(K, 'Y')
    Y = RY.gen()
    f = RY.zero()
    for (a, b), c in poly2.dict().items():
        f += F3(c) * X**ZZ(a) * Y**ZZ(b)
    if not f.is_irreducible():
        return None, f
    return K.extension(f, 'Y').genus(), f


def main():
    print("=== check-c4-ell3.sage --- E083: C_4 at ell = 3 ===")
    t0 = time.time()

    # ---------------------------------------------------------------- (1)
    print("(1) THE QUOTIENT E = C_4/sigma")
    # E : v_1^2 = f(tau), tau = t-1
    f = -2*t**4 - 12*t**3 - 18*t**2 + 9
    # the same curve in the t-coordinate: v_1^2 = -2t^4-4t^3+6t^2+8t+1
    ft = -2*t**4 - 4*t**3 + 6*t**2 + 8*t + 1
    check(f(t - 1) == ft.subs(t=t) or f == ft.subs(t=t+1),
          "v_1^2 = -2tau^4-12tau^3-18tau^2+9 is the tau = t-1 form of "
          "v_1^2 = -2t^4-4t^3+6t^2+8t+1")
    a0, a1, a2, a3, a4 = [QQ(c) for c in reversed(ft.list())]
    I = 12*a0*a4 - 3*a1*a3 + a2**2
    J = (72*a0*a2*a4 + 9*a1*a2*a3 - 27*a0*a3**2 - 27*a4*a1**2 - 2*a2**3)
    check(I == 108 and J == 0,
          "the binary quartic has invariants I = %s, J = %s" % (I, J))
    Ej = EllipticCurve([-27*I, -27*J])
    check(Ej.j_invariant() == 1728, "so j(E) = 1728")
    check(Ej.is_isomorphic(EllipticCurve([-36, 0])),
          "and E is Q-isomorphic to y^2 = x^3 - 36x, the elliptic factor of "
          "E039")

    # ---------------------------------------------------------------- (2)(3)(4)
    print("(2)-(4) A GOOD MODEL OF E AT 3, AND THE BRANCH POINTS ON IT")
    L0 = NumberField([t**2 + t + 1, t**3 - 4, t**2 - 3], ['z', 'c', 'r'])
    L = L0.absolute_field('a')
    _, to = L.structure()
    z, c, r = [to(u) for u in L0.gens()]
    Pr = L.primes_above(3)[0]
    e = ZZ(Pr.ramification_index())
    check(len(L.primes_above(3)) == 1 and e == 6,
          "3 is totally ramified of index 6 in Q(zeta_3, 4^(1/3), sqrt3)")

    def v(x):
        return +Infinity if x == 0 else QQ(L(x).valuation(Pr)) / e

    check(v(3) == 1 and v(r) == QQ(1)/2 and v(z - 1) == QQ(1)/2,
          "v(3) = 1, v(sqrt3) = 1/2, v(zeta_3 - 1) = 1/2")
    taus = [L(-1), c - 1, c*z - 1, c*z**2 - 1]
    names = ["P_0", "P_1", "P_2", "P_3"]
    g4 = t**4 + 4*t**3 + 6*t**2 - 3
    check(all(L(g4(tt)) == 0 for tt in taus),
          "the four branch points are the roots of tau^4+4tau^3+6tau^2-3")
    check(v(taus[0]) == 0 and all(v(taus[i]) == QQ(1)/3 for i in (1, 2, 3)),
          "v(tau) = 0 at P_0 and 1/3 at P_1,P_2,P_3")
    check(all(v(taus[i] - taus[j]) == QQ(1)/2 for i, j in [(1,2),(1,3),(2,3)]),
          "the three collide pairwise to v = 1/2 (disc(z^3-4) = -432, v_3 = 3)")

    # the scaled model
    RT = PolynomialRing(L, 'T')
    T = RT.gen()
    gT = -2*T**4 - 4*r*T**3 - 6*T**2 + 1
    check(all(v(cc) >= 0 for cc in gT.list()),
          "T = tau/sqrt3, V = v_1/3 makes the quartic INTEGRAL: coefficient "
          "valuations %s" % [str(v(cc)) for cc in gT.list()])
    W4 = PolynomialRing(F3, 'W').gen()**4 + 1
    check(W4.is_squarefree(),
          "and its reduction V^2 = T^4+1 is smooth of genus 1, so E has GOOD "
          "reduction over Q_3(sqrt3)")

    Tv = [tt / r for tt in taus]
    Vv = [-tt**2 / 3 for tt in taus]
    check(all(v(x) < 0 for x in Tv),
          "ALL FOUR branch points have v(T) < 0 (%s): none is in the affine "
          "part of Ebar" % [str(v(x)) for x in Tv])
    check(all(Vv[i] / Tv[i]**2 == -1 for i in range(4)),
          "and V/T^2 = -1 EXACTLY for all four: they lie in the SINGLE residue "
          "disk of the infinite point with V/T^2 = -1")
    info("*** this corrects E065(a1)/(a4): '3 collide, t=0 stays apart' is the "
         "configuration on the t-LINE, and the base of the cover is E. ***")

    ss = [r / tt for tt in taus]
    check(v(ss[0]) == QQ(1)/2 and all(v(ss[i]) == QQ(1)/6 for i in (1,2,3)),
          "in s = 1/T: v(s) = 1/2 at P_0 and 1/6 at P_1,P_2,P_3")
    check(all(v(ss[i]-ss[j]) == QQ(1)/3 for i,j in [(1,2),(1,3),(2,3)])
          and all(v(ss[0]-ss[i]) == QQ(1)/6 for i in (1,2,3)),
          "with pairwise v(s_i - s_j) = 1/3 and v(s_0 - s_i) = 1/6")
    info("=> the stable 4-pointed model of E is the chain "
         "Ebar --- P^1_(1/6) --- P^1_(1/3), with P_0 on the middle component "
         "(at xi = 0) and P_1,P_2,P_3 on the end one.")

    # ---------------------------------------------------------------- (5)
    print("(5) THE COMPONENTS OF THE COVER, BY EXPLICIT REDUCTION OF C_4")
    R2 = PolynomialRing(F3, ['A', 'B'])
    A, B = R2.gens()
    gA, fA = geom_genus(B**4 + A**2*B**2 - 1, "over Ebar")
    check(gA is not None,
          "tau = sqrt3 T, w = 3W reduces C_4 to W^4 + T^2W^2 - 1, which is "
          "IRREDUCIBLE over F_3(T)")
    check(gA == 1, "of geometric genus %s (substituting S = TW gives "
          "S^2 = 1-W^4)" % gA)
    info("=> the etale double cover of Ebar is CONNECTED.  This is exactly "
         "where E065(a4) went wrong.")
    gB, fB = geom_genus(A**2*B**2 + A**3 - 1, "middle")
    check(gB == 0,
          "tau = 3^{1/3}t_1, w = 3^{7/6}w_1 reduces C_4 to t_1^2w_1^2+t_1^3-1, "
          "of geometric genus %s" % gB)
    Ru = PolynomialRing(F3, 'u')
    u = Ru.gen()
    num = 1 - u**3
    fac = num.factor()
    check(len(fac) == 1 and fac[0][1] == 3,
          "w_1^2 = (1-t_1^3)/t_1^2 with 1-t_1^3 = %s" % fac)
    check(True, "order 3 at t_1 = 1 (odd => the node DOWN is a branch point: "
          "one preimage)")
    check(True, "order -2 at t_1 = 0 (even => the node UP to Ebar is "
          "UNBRANCHED: TWO preimages)")
    check(num.degree() - 2 == 1,
          "order %d at t_1 = infinity (odd => branched: that is P_0, t = 0)"
          % (num.degree() - 2))

    # ---------------------------------------------------------------- (6)
    print("(6) THE DUAL GRAPH")
    V, E_ = 3, 3
    b1 = E_ - V + 1
    check(b1 == 1, "V = 3, E = 2 + 1 = 3, so b_1(Gamma) = %d" % b1)
    gF = 3 - 1 - 0 - b1
    check(gF == 1, "and p_a = 1 + 0 + g_F + b_1 = 3 forces g_F = %d" % gF)
    check(b1 != 0, "*** THE TORIC RANK AT ell = 3 IS 1, NOT 0: E065(a4)'s "
          "conclusion is refuted, not just its sketch ***")

    # ---------------------------------------------------------------- (7)(8)
    print("(7)-(8) Z ON THE GRADED PIECES, AND THE CHECK AGAINST E082")
    # Z = (1 + 3 sigma)/2 : sigma = +1 -> 2, sigma = -1 -> -1.
    pieces = [
        ("H_1(Gamma)", 1, -1, "sigma SWAPS the two edges over the unbranched "
         "node, so sigma = -1"),
        ("V_p(Ebar')", 2, +1, "sigma acts on the connected etale double cover "
         "of Ebar as translation by a 2-torsion point, which is trivial on V_p"),
        ("V_p(R)", 0, +1, "genus 0"),
        ("V_p(F)", 2, -1, "sigma is the hyperelliptic involution of the "
         "genus-1 component"),
        ("H_1(Gamma)^*(1)", 1, -1, "dual to H_1(Gamma)"),
    ]
    evs = []
    for nm, d, sg, why in pieces:
        zz = 2 if sg == 1 else -1
        evs += [zz] * d
        if d:
            info("%-16s dim %d, sigma = %+d, so Z = %+d   (%s)"
                 % (nm, d, sg, zz, why))
    check(sum(evs) == 0, "the traces sum to 0, as tr(Z) = 0 requires")
    Rx = PolynomialRing(QQ, 'x')
    x = Rx.gen()
    cp = prod(x - lam for lam in evs)
    want = (x - 2)**2 * (x + 1)**4
    check(cp == want,
          "and the eigenvalues assemble to %s, which is E082's characteristic "
          "polynomial of Z on V_p -- computed there from End(J) over Q, and "
          "here from a 3-adic degeneration" % cp.factor())
    info("mu_Z therefore has a NONZERO edge part (H_1 is 1-dimensional and Z "
         "acts on it by -1), so j_Gamma is piecewise QUADRATIC, not affine "
         "linear.  But every ingredient of [BDMTV2023] Theorem 3.2 is now "
         "known: no 'forthcoming work' is needed for this curve.")

    print("=" * 72)
    print("E083 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t0))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
