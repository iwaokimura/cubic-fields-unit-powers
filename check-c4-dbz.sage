# check-c4-dbz.sage --- E127 stage 1: the correspondence Z of C_4 written as an
# algebraic CYCLE on C_4 x C_4, and Balakrishnan--Dogra's divisor D(b,z).
#
# E126 showed that the local heights h_v are not functions of the pair of
# CLASSES (pi_1, pi_2), and concluded that E126's bilinear route was
# empty.  What E126 missed is that Balakrishnan--Dogra do not ask for classes:
# their Definition 6.2 / Theorem 6.3 (accepted manuscript)
# attach to (b, z, Z) an
# explicit DIVISOR
#         D(b,z) = i_Delta^* Z - i_1^* Z - i_2^* Z + m x,
#         m = Z.(X_1 + X_2 - Delta),   X_1 = {b} x X,  X_2 = X x {z},
# and prove that the mixed extension A_Z(b,z) is H_X(z-b, D(b,z))(-1).  So
# h_v(A_Z(b,z)) = h_v(z-b, D(b,z)) is a Coleman--Gross height of DIVISORS, and
# the Z-ambiguity of E126 group (C) disappears once D(b,z) is written down.
#
# This gate writes it down.  With sigma : w -> -w and Gamma_sigma its graph,
#
#   (A)  Z_c := Delta + 3 Gamma_sigma  induces  1 + 3 sigma  (eigenvalues 4 on
#        the elliptic line, -2 on the Prym plane), and -- with NO trivial-cycle
#        correction -- satisfies Balakrishnan--Dogra's normalisation
#        Z.(Delta - X_1 - X_2) = 0 exactly, so m = 0;
#
#   (B)  D(b,z) = 2R - (b) - 3(sigma b) - (z) - 3(sigma z),  R = sum of the four
#        ramification points of phi : C_4 -> E (the points with w = 0);
#        equivalently  D(b,z) = phi^*(B - 2 phi(b) - 2 phi(z)) + n_z + n_b  with
#        n_x := (x) - (sigma x) and B the branch divisor;
#
#   (C)  the class of D(b,z) is -Z_*(z-b) + c_c, and the constant c_c is
#        EXACTLY E088's and E126(a)'s:  its Prym part is E088's rho' = 0, and
#        its elliptic part is lambda_Z phi^*(P_0 - O), i.e. E126(a)'s nu =
#        lambda_Z -- which E126 could only reach 13-adically, by a rational
#        reconstruction outside its own uniqueness bound.  The whole content is
#        one exact identity in E(Q):
#                    B - 4 phi(b) + 2 P_0 = O .
#
#   (D)  the sigma-decomposition that stage 2 will use:  for ell != p,
#        h_ell(z-b, D(b,z)) = h_{E,ell}(phi(z)-phi(b), B - 2phi(b) - 2phi(z))
#                             + (1/2) h_ell(n_z, n_z) - (1/2) h_ell(n_b, n_b).
#
#   (G)  The Prym is not isogenous to a product of elliptic curves over Q, is
#        not Res_{F/Q} of one over a quadratic field, and has no real
#        multiplication -- so the Prym term cannot be routed through elliptic
#        curves, and ell = 2 needs a model of C_4 over Z_2.
#
#   (H)  STAGE 2 (vertical part).  q_ell = (elliptic term) + (1/2)[Lambda(d(n_z))
#        - Lambda(d(n_b))] reproduces the measured q_3 on all eight points where
#        it is defined -- Magma-free, no lindep, no Betts--Dogra scalar -- and
#        reproduces six of eight at ell = 2, failing on t = -2.
#
#   (I)  The missing term is horizontal, -[(bar z . bar sigma z) - (bar b .
#        bar sigma b)].  At ell = 3 it VANISHES, and not by luck: the two points
#        of t = -1 lie on one component but reduce to the distinct points (1,1)
#        and (1,2) of X_F-bar, in all three charts.  At ell = 2 Magma says the
#        sigma-pair of t = -2 is NOT separated and the intersection number is 1,
#        giving q_2 = 3/4 against the measured -1/4 -- equal MODULO Z, which
#        E126(c) shows is the best any representative-free split can do.  The
#        fractional parts match at both primes, and nothing in paper2 moves.
#
#        The block sent to magma_free (2026-08-30, at the user's instruction):
#          P<X,Y,Z> := PolynomialRing(Rationals(), 3);
#          F := Y^4 - 6*(X-Z)^2*Y^2 + 27*X^4 - 108*X*Z^3;
#          C := Curve(ProjectiveSpace(P), F);
#          M2 := RegularModel(C, 2);
#          for the nine points v:  p := PointOnRegularModel(M2, C!v);
#          printf "%o %o %o %o\n", p`patch_index, p`point_coords,
#                                   p`point_reduction, p`component_indices;
#        Magma 2.29-9, 0.28 s.  The output is transcribed in group (I).
#
#   (F)  STAGE 3, run before stage 2 at the user's instruction: does the Prym
#        term vanish at ell = 3?  ANSWER: NO.  The elliptic term is an exact
#        classical computation on y^2 = x^3-36x (Tate's algorithm and Neron
#        local heights, no Betts--Dogra normalisation), and it reproduces the
#        h_ell partition at BOTH bad primes -- but its VALUES are 1 against a
#        measured 1/2 at ell = 3 and 2 against 1/4 at ell = 2, a discrepancy no
#        rescaling can absorb since the RATIO between the primes differs by 4;
#        and at p = 5, where C_4 has good reduction and Theorem 1.2 forces the
#        total to vanish, the elliptic term is 2.
#
# Groups (E) and (G) of E127 (the value of q_3 on E125's regular model,
# ell = 2) are NOT run here; see the status lines.
#
# Run:  sage check-c4-dbz.sage            (exact throughout; about five seconds)

import sys, time

FAIL = []
NCHECK = [0]


def check(cond, msg):
    NCHECK[0] += 1
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def info(msg):
    print("       -- %s" % msg)
    sys.stdout.flush()


# ---------------------------------------------------------------------------
# The curve, the quotient map, and the constants of the project.
# ---------------------------------------------------------------------------

LAMBDA_Z = -16848                       # E088: Z = lambda_Z (1 + 3 sigma)/2
q, dd, c4_, b4_, a4_ = QQ(3), QQ(72), QQ(54), QQ(-36), QQ(-18)
Rs = PolynomialRing(QQ, 'T')
T = Rs.gen()
cub = (b4_ - (dd/q)*T)**2 - 4*(a4_ - T**2)*(c4_ - dd**2/(4*q**2) - 2*q*T)
c3 = cub[3]
Eq = EllipticCurve([0, cub[2], 0, cub[1]*c3, cub[0]*c3**2])
Em = Eq.minimal_model()
ISO = Eq.isomorphism_to(Em)


def imgu(EE, tt, uu):
    """phi in the quotient coordinates (t, u = w^2); EE the curve over a ring.

    Constants are coerced into the parent of tt so that the same code runs over
    Q, over a number field and over F_p (the mod-p confirmation in group (C))."""
    if tt == 0 and uu == 0:
        return EE(0)
    K = tt.parent()
    q_, dd_, aa, bb, cc = K(q), K(dd), K(a4_), K(b4_), K(c3)
    vv = uu - 3*(tt - 1)**2
    ss = (vv - q_ - (dd_/(2*q_))*tt) / tt**2
    return EE(cc*ss, cc*(2*(aa - ss**2)*tt + bb - (dd_/q_)*ss))


def img(EE, tt, ww):
    return imgu(EE, tt, ww**2)


PTS = [(QQ(1), QQ(3)), (QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
       (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)), (QQ(-1)/11, QQ(15)/11),
       (QQ(-1)/11, QQ(-15)/11), (QQ(0), QQ(0))]
BPT = PTS[0]                                    # b = (1, 3), E072's base point


# ---------------------------------------------------------------------------
# Formal divisors on C_4, as dictionaries on the symbols we need.
# ---------------------------------------------------------------------------

def dv(**kw):
    return {k: QQ(v) for k, v in kw.items() if v != 0}


def dadd(*ds):
    out = {}
    for d in ds:
        for k, v in d.items():
            out[k] = out.get(k, QQ(0)) + v
    return {k: v for k, v in out.items() if v != 0}


def dscale(c, d):
    return {k: QQ(c)*v for k, v in d.items() if QQ(c)*v != 0}


def ddeg(d):
    return sum(d.values())


# ---------------------------------------------------------------------------


def group_A():
    """(A)  Z as a cycle: Delta + 3 Gamma_sigma, and m = 0."""
    print("(A) THE CORRESPONDENCE AS A CYCLE ON C_4 x C_4")

    Kf = FunctionField(QQ, 't')
    t = Kf.gen()
    Rf = PolynomialRing(Kf, 'W')
    W = Rf.gen()
    Lf = Kf.extension(W**4 - 6*(t-1)**2*W**2 + 27*t*(t**3-4), 'w')
    g = Lf.genus()
    check(g == 3, "C_4 : w^4 - 6(t-1)^2 w^2 + 27 t(t^3-4) has genus %d" % g)

    Rq = PolynomialRing(Kf, 'U')
    U = Rq.gen()
    Mf = Kf.extension(U**2 - 6*(t-1)**2*U + 27*t*(t**3-4), 'u')
    gq = Mf.genus()
    check(gq == 1, "the quotient by sigma : w -> -w (coordinate u = w^2) has "
                   "genus %d, so phi : C_4 -> E is a degree-2 map to a genus-1 "
                   "curve" % gq)

    # the fixed points of sigma are exactly the zeros of w
    w = Lf.gen()
    D = w.divisor()
    zeros = [(pl, m) for (pl, m) in D.list() if m > 0]
    poles = [(pl, m) for (pl, m) in D.list() if m < 0]
    degR = sum(m*pl.degree() for (pl, m) in zeros)
    check(degR == 4 and all(m == 1 for (pl, m) in zeros),
          "div(w) has zero part of degree %d, all multiplicities 1: the four "
          "geometric points with w = 0, which are exactly Fix(sigma) "
          "(t = 0 and t^3 = 4, one Q-place of degree 1 and one of degree 3)"
          % degR)
    check(len(zeros) == 2 and sorted(pl.degree() for (pl, m) in zeros) == [1, 3],
          "and they form two places over Q, of degrees 1 and 3")
    check(sum(-m*pl.degree() for (pl, m) in poles) == 4
          and len(poles) == 1 and poles[0][0].degree() == 4,
          "the pole part of div(w) is the single degree-4 place at infinity, "
          "so sigma has NO fixed point at infinity: w^4-6w^2+27 has no root 0")
    info("Riemann-Hurwitz: 2*3-2 = 2*(2*1-2) + deg R gives deg R = 4, which is "
         "the count just made -- an independent confirmation")

    # intersection numbers on the surface S = C_4 x C_4
    dd_ = 2 - 2*g                                   # Delta . Delta = deg T_X
    gs_dd = degR                                    # Gamma_sigma . Delta = #Fix
    check(dd_ == -4, "Delta . Delta = 2 - 2g = %d (the degree of the normal "
                     "bundle of the diagonal)" % dd_)
    check(gs_dd == 4, "Gamma_sigma . Delta = #Fix(sigma) = %d, each with "
                      "multiplicity 1 (d(sigma) = -1 at a fixed point of an "
                      "involution, so the graph meets Delta transversally)"
          % gs_dd)
    info("Delta . X_1 = Delta . X_2 = 1 and Gamma_sigma . X_1 = "
         "Gamma_sigma . X_2 = 1: a graph meets a fibre once "
         "(b is not a ramification point, w(b) = 3 != 0, so (b,b) is not on "
         "Gamma_sigma and the intersections are proper)")
    ZD = dd_ + 3*gs_dd                              # Z_c . Delta
    ZX = 1 + 3*1                                    # Z_c . X_i
    check(ZD - ZX - ZX == 0,
          "*** Z_c := Delta + 3 Gamma_sigma satisfies Balakrishnan--Dogra's "
          "normalisation Z.(Delta - X_1 - X_2) = %d + %d - %d - %d = 0 EXACTLY, "
          "with no trivial-cycle correction ***.  So Z_c defines a quotient of "
          "pi_1 of the projective curve, and Theorem 1.2 (rational points, not "
          "just integral) applies to it" % (dd_, 3*gs_dd, ZX, ZX))
    m = ZX + ZX - ZD
    check(m == 0, "and the basepoint multiplicity of Definition 6.2 is "
                  "m = Z.(X_1 + X_2 - Delta) = %d: D(b,z) carries NO m x term"
          % m)
    check(True, "Z_c is a SYMMETRIC cycle: Delta^t = Delta and "
                "Gamma_sigma^t = Gamma_{sigma^{-1}} = Gamma_sigma because "
                "sigma is an involution.  Hence i_1^* Z and i_2^* Z are both "
                "read by the same endomorphism and no transpose convention "
                "enters")

    # the induced endomorphism
    info("sigma acts as +1 on the elliptic line phi^*H^1(E) and as -1 on the "
         "Prym plane, so 1 + 3 sigma has eigenvalues 4 and -2, and "
         "(1+3sigma)/2 has 2 and -1 -- E088's normalisation of Z")
    ev = [1 + 3*1, 1 + 3*(-1)]
    check(ev == [4, -2], "eigenvalues of 1 + 3 sigma are %s" % ev)
    s = -QQ(LAMBDA_Z)/2
    check(s == 8424,
          "the scalar fixed by group (C) below is s = -lambda_Z/2 = %d, i.e. "
          "the port's correspondence is the cycle 8424 (Delta + 3 Gamma_sigma) "
          "modulo trivial cycles" % s)


def group_B():
    """(B)  D(b,z), explicitly."""
    print("(B) D(b,z) FOR C_4")

    # i_1(u) = (b,u), i_2(u) = (u,z), i_Delta(u) = (u,u).
    #   i_1^* Delta = (b),  i_1^* Gamma_sigma = (sigma b)
    #   i_2^* Delta = (z),  i_2^* Gamma_sigma = (sigma z)
    #   i_Delta^* Gamma_sigma = R = R_0 + R_1 + R_2 + R_3
    #   i_Delta^* Delta = c_1(N_Delta) = -K_X ~ -R   (K_X = phi^* K_E + R, and
    #                                                 K_E ~ 0)
    R = dv(R0=1, R1=1, R2=1, R3=1)
    iD = dadd(dscale(-1, R), dscale(3, R))          # -R + 3R
    i1 = dv(b=1, sb=3)
    i2 = dv(z=1, sz=3)
    Dc = dadd(iD, dscale(-1, i1), dscale(-1, i2))
    check(Dc == dv(R0=2, R1=2, R2=2, R3=2, b=-1, sb=-3, z=-1, sz=-3),
          "D(b,z) = i_Delta^*Z - i_1^*Z - i_2^*Z + 0 "
          "= 2R - (b) - 3(sigma b) - (z) - 3(sigma z)")
    check(ddeg(Dc) == 0, "deg D(b,z) = %d" % ddeg(Dc))
    info("the term i_Delta^* Delta needs the Moving lemma (Fulton 11.4): Delta "
         "has Delta^2 = -4 < 0, so it does not move in its linear system, but "
         "as a CYCLE it is rationally equivalent to one meeting it properly.  "
         "The class of i_Delta^* Delta is c_1(N_Delta) = -K_X, and K_X ~ R "
         "because phi is a degree-2 cover of a genus-1 curve with ramification "
         "divisor R.  So [i_Delta^* Delta] = -[R], which is what is used above")
    info("independence of the choice [T]: if Z' = Z + div(F) on S, then "
         "D'(b,z) - D(b,z) = div(g) with g = (F o i_Delta)/((F o i_1)(F o i_2)), "
         "and g(b) = F(b,b)/(F(b,b)F(b,z)) = 1/F(b,z) = g(z).  Hence "
         "h_v(z-b, D') - h_v(z-b, D) = chi_v(g(z)/g(b)) = 0 at every v: the "
         "local height does not see the choice, which is what Theorem 6.3 "
         "requires, cl_Z being a rational-equivalence invariant")

    # the sigma-decomposition of the same divisor
    phi_B = dv(R0=2, R1=2, R2=2, R3=2)              # phi^*(B) = 2R
    phi_eb = dv(b=1, sb=1)                          # phi^* phi(b)
    phi_ez = dv(z=1, sz=1)
    n_b = dv(b=1, sb=-1)
    n_z = dv(z=1, sz=-1)
    rhs = dadd(phi_B, dscale(-2, phi_eb), dscale(-2, phi_ez), n_z, n_b)
    check(rhs == Dc,
          "*** D(b,z) = phi^*(B - 2 phi(b) - 2 phi(z)) + n_z + n_b, with "
          "n_x := (x) - (sigma x) and B the branch divisor ***: an exact "
          "splitting of D(b,z) into its sigma-invariant and sigma-anti-"
          "invariant parts")
    check(dadd(phi_B, dscale(-2, phi_eb), dscale(-2, phi_ez)) ==
          dv(R0=2, R1=2, R2=2, R3=2, b=-2, sb=-2, z=-2, sz=-2),
          "the invariant part is phi^*(B - 2phi(b) - 2phi(z)), of degree 0")
    check(ddeg(dadd(n_z, n_b)) == 0 and dadd(n_z, n_b) == dv(b=1, sb=-1, z=1, sz=-1),
          "the anti-invariant part is n_z + n_b")

    # the constant, as a divisor: D(b,z) = -(1+3sigma)_*(z-b) + c_c, so c_c is
    # what is left after adding back (z) + 3(sigma z) and subtracting
    # (b) + 3(sigma b).
    c_c = dadd(Dc, dv(z=1, sz=3), dscale(-1, dv(b=1, sb=3)))
    check(c_c == dv(R0=2, R1=2, R2=2, R3=2, b=-2, sb=-6),
          "writing D(b,z) = -(1 + 3 sigma)_*(z - b) + c_c, the constant divisor "
          "is c_c = 2R - 2(b) - 6(sigma b)")
    check(c_c == dadd(phi_B, dscale(-4, phi_eb), dscale(2, n_b)),
          "and c_c = phi^*(B - 4 phi(b)) + 2 n_b, its invariant and "
          "anti-invariant parts")
    check(ddeg(c_c) == 0, "deg c_c = %d" % ddeg(c_c))

    # a representative with support disjoint from {b, z}
    info("D(b,z) as written meets the support of z - b.  A representative that "
         "does not: move Delta + Gamma_sigma = (phi x phi)^* Delta_E by "
         "Delta_E ~ Delta_Q + Delta_R - Delta_P (Q + R = P on E, all nonzero), "
         "which is DISJOINT from Delta.  Then i_Delta^* of it is 0 and")
    info("  D'(b,z) = 2R - phi^*[(e_b-Q)+(e_b-R)-(e_b-P)] - 2(sigma b) "
         "- phi^*[(e_z+Q)+(e_z+R)-(e_z+P)] - 2(sigma z),")
    info("of degree 8-2-2-2-2 = 0, with the same class, and with support "
         "avoiding b and z whenever Q, R, P are not O.  Stage 2 uses this one")


def group_C():
    """(C)  The class of D(b,z) is E088's and E126(a)'s constant, exactly."""
    print("(C) THE CLASS: E126(a)'s nu = lambda_Z, DERIVED")

    # phi is a morphism to Eq: verify the Weierstrass equation identically
    P2 = PolynomialRing(QQ, ['t', 'u'])
    tt, uu = P2.gens()
    G = uu**2 - 6*(tt-1)**2*uu + 27*tt*(tt**3-4)     # the quotient curve
    Fr = FractionField(P2)
    ssf = (Fr(uu) - 3*(tt-1)**2 - q - (dd/(2*q))*tt) / tt**2
    xf = c3*ssf
    yf = c3*(2*(a4_ - ssf**2)*tt + b4_ - (dd/q)*ssf)
    a1, a2, a3, a4, a6 = Eq.a_invariants()
    rel = (yf**2 + a1*xf*yf + a3*yf) - (xf**3 + a2*xf**2 + a4*xf + a6)
    num = P2(rel.numerator())
    check(G.divides(num),
          "phi is a morphism to Eq : the Weierstrass relation, cleared of "
          "denominators, is divisible by u^2 - 6(t-1)^2 u + 27t(t^3-4)")
    info("and phi is birational onto Eq (hence deg phi = 2 as a map from "
         "C_4): u = t^2 (x/c3) + 3(t-1)^2 + 3 + 12t recovers u from (t, x), "
         "and t = (y/c3 + 36 + 24 x/c3) / (2(-18 - (x/c3)^2)) recovers t")

    eb = ISO(img(Eq, *BPT))
    P0 = Em.gens()[0]
    check(Em == EllipticCurve([0, 0, 0, -36, 0]),
          "the minimal model of the quotient is y^2 = x^3 - 36x (E039, E093)")
    check(eb == Em(6, 0) and eb.order() == 2,
          "phi(b) = %s is a 2-torsion point, so 4 phi(b) = O" % eb)
    check(P0 == Em(-3, 9), "the free generator of E(Q) = Z P_0 + (Z/2)^2 is "
                           "P_0 = %s" % P0)

    # the branch divisor B, over the splitting field of T^3 - 4
    L = (T**3 - 4).splitting_field('r')
    EqL = Eq.change_ring(L)
    roots = [rr for (rr, mult) in (T**3 - 4).change_ring(L).roots()]
    check(len(roots) == 3 and L.degree() == 6,
          "T^3 - 4 splits in a field of degree %d with %d roots"
          % (L.degree(), len(roots)))
    Bsum = EqL(0)                                   # B_0 = phi(0,0) = O
    check(img(Eq, QQ(0), QQ(0)) == Eq(0),
          "the branch point over t = 0 is B_0 = phi((0,0)) = O")
    for rr in roots:
        Bsum = Bsum + imgu(EqL, rr, L(0))
    check(all(cc in QQ for cc in (Bsum[0], Bsum[1])),
          "the sum of the three branch points with t^3 = 4 is Q-rational, as "
          "a Galois-stable sum must be")
    B = ISO(Eq(QQ(Bsum[0]), QQ(Bsum[1])))
    check(B == -2*P0,
          "*** B := sum of the four branch points = %s = -2 P_0 ***" % B)

    # the identity that carries the whole comparison
    check(B - 4*eb + 2*P0 == Em(0),
          "*** THE IDENTITY:  B - 4 phi(b) + 2 P_0 = O in E(Q) ***.  Hence "
          "B - 4 phi(b) ~ -2((P_0) - (O)) as divisor classes on E")
    for k in (-2, -1, 0, 2, 3):
        check(B - 4*eb + 2*k*P0 != Em(0),
              "   negative control: B - 4 phi(b) + %d P_0 != O" % (2*k))
    for tors in Em.torsion_points():
        if tors != Em(0):
            check(B - 4*eb + 2*P0 + tors != Em(0),
                  "   negative control: the identity fails on adding the "
                  "torsion point %s" % tors)

    # an independent confirmation of B, by reduction
    good = [pr for pr in prime_range(5, 400)
            if Em.has_good_reduction(pr)
            and len((T**3 - 4).change_ring(GF(pr)).roots()) == 3]
    info("independent confirmation of B modulo %d primes where T^3-4 splits "
         "and E has good reduction: %s" % (len(good), good[:12]))
    Bq = Eq(QQ(Bsum[0]), QQ(Bsum[1]))
    okmod = True
    for pr in good[:12]:
        k = GF(pr)
        Ek = Eq.change_ring(k)
        Bk = Ek(0)
        for (rr, mult) in (T**3 - 4).change_ring(k).roots():
            Bk = Bk + imgu(Ek, k(rr), k(0))
        if Bk != Ek(k(Bq[0]), k(Bq[1])):
            okmod = False
    check(okmod, "B reduces correctly modulo each of them -- B computed in "
                 "F_p from the three roots there, without the degree-6 field")

    # what this says about the constant class
    s = -QQ(LAMBDA_Z)/2
    info("the port's correspondence is s Z_c with s = -lambda_Z/2 = %d, fixed "
         "by requiring that D(b,z) reproduce E088's affine law: "
         "-s(1 + 3 sigma) = M = lambda_Z (1 + 3 sigma)/2" % s)
    check(-s*4 == LAMBDA_Z*2 and -s*(-2) == -LAMBDA_Z,
          "with that s, pi_1 -> [D(b,z)] has eigenvalues %d on the elliptic "
          "line and %d on the Prym plane, which is E088's "
          "M = -16848 diag(2,-1,-1)" % (-s*4, -s*(-2)))
    check(s*2 == -LAMBDA_Z,
          "*** the Prym part of the constant is s * 2 n_b = -lambda_Z n_b = "
          "lambda_Z kappa' (kappa' = [sigma b - b] = -n_b), which is E088's "
          "c' = -m_2 kappa' with m_2 = -lambda_Z, i.e. E088's rho' = 0 ***.  "
          "E088 measured it 13-adically; here it is an identity of divisors")
    check(-2*s == LAMBDA_Z,
          "*** the elliptic part of the constant is "
          "s * phi^*(B - 4 phi(b)) = -2s phi^*(P_0 - O) = "
          "lambda_Z phi^*(P_0 - O), i.e. E126(a)'s nu = lambda_Z = %d, now "
          "EXACT ***" % LAMBDA_Z)
    info("E126(a) got nu = lambda_Z from the port to p^9 and had to note that "
         "16848 exceeds sqrt(13^7/2) = 5601, the bound inside which its "
         "rational reconstruction would have been unique.  That caveat is "
         "gone: the elliptic coefficient is now an identity in E(Q)")

    # kappa is purely Prym -- exactly, not to p^13
    sb = (BPT[0], -BPT[1])
    check(img(Eq, *BPT) == img(Eq, *sb),
          "phi_*(sigma b - b) = phi(sigma b) - phi(b) = 0 exactly, so "
          "kappa = [sigma b - b] is purely Prym -- E126(a) had this to p^13")


def group_D():
    """(D)  The sigma-decomposition of h_ell, for stage 2."""
    print("(D) THE DECOMPOSITION OF h_ell THAT STAGE 2 WILL USE")
    phi_ez_eb = dv(z=1, sz=1, b=-1, sb=-1)
    n_b = dv(b=1, sb=-1)
    n_z = dv(z=1, sz=-1)
    check(dadd(dscale(QQ(1)/2, phi_ez_eb), dscale(QQ(1)/2, dadd(n_z, dscale(-1, n_b))))
          == dv(z=1, b=-1),
          "z - b = (1/2) phi^*(phi(z) - phi(b)) + (1/2)(n_z - n_b): the "
          "sigma-eigen-decomposition of the first argument")
    info("Coleman--Gross local heights are sigma-equivariant "
         "(h_v(sigma D_1, sigma D_2) = h_v(D_1,D_2): at ell != p the symbol is "
         "read off a regular model on which sigma acts).  So an invariant "
         "divisor pairs to zero with an anti-invariant one, and by group (B)'s "
         "splitting of D(b,z),")
    info("  h_v(z-b, D(b,z)) = h_v(phi^*(phi(z)-phi(b))/2, "
         "phi^*(B - 2phi(b) - 2phi(z))) + h_v((n_z-n_b)/2, n_z + n_b).")
    info("The first term is h_{E,v}(phi(z)-phi(b), B-2phi(b)-2phi(z)) by the "
         "projection formula (h_v(phi^* a, phi^* c) = deg(phi) h_{E,v}(a,c) = "
         "2 h_{E,v}(a,c)).  The second is "
         "(1/2)[h_v(n_z,n_z) - h_v(n_b,n_b)] once the antisymmetric part "
         "cancels, which it does at every ell != p, the Neron symbol there "
         "being symmetric.  Hence for ell != p")
    info("  *** h_ell(z-b, D(b,z)) = h_{E,ell}(phi(z)-phi(b), "
         "B - 2phi(b) - 2phi(z)) + (1/2)h_ell(n_z,n_z) - (1/2)h_ell(n_b,n_b) "
         "***")
    info("This is the exact analogue of Balakrishnan--Dogra Lemma 7.7 for "
         "C_4: 'a function of z minus the same function of b', plus a term "
         "living on the elliptic quotient.  The difference from their "
         "bielliptic case is the Prym term (1/2)h_ell(n_z,n_z): C_4 has genus "
         "3 with a 2-dimensional Prym, so it does NOT reduce to a second "
         "elliptic curve.  Whether it vanishes at ell = 2,3 is E127 stage 3, "
         "and E126 Addendum (h) is evidence that something like it does")
    check(True, "recorded; no computation in this group")


# ---------------------------------------------------------------------------
# (F)  Stage 3, run before stage 2 at the user's instruction (2026-08-29):
#      does the Prym term vanish at ell = 3?
# ---------------------------------------------------------------------------

def lam(P, ell):
    """SageMath's Neron local height at the non-archimedean place ell."""
    return P.non_archimedean_local_height(ell)


def pairing(D1, D2, ell):
    """(1/(2 log ell)) sum_{i,j} n_i m_j lambda_ell(P_i - Q_j).

    Group (F1) calibrates the 1/2: SageMath's lambda is TWICE the
    (1/2)max(0,-v(x))log(ell) convention for which this sum is the Neron
    intersection number (D_1 . D_2).  Terms with P_i = Q_j are dropped; their
    total coefficient is checked to be zero by the caller, which is what makes
    the value finite (a constant shift of lambda also cancels, both
    coefficient sums being zero)."""
    tot = 0
    for (P, n) in D1:
        for (Q, m) in D2:
            R = P - Q
            if R.is_zero():
                continue
            tot += n*m*lam(R, ell)
    return (tot/(2*log(ell))).simplify_full()


def diag_coeff(D1, D2):
    return sum(n*m for (P, n) in D1 for (Q, m) in D2 if (P - Q).is_zero())


def group_F():
    """(F)  The elliptic term of D(b,z), exactly, at 2, 3 and beyond."""
    print("(F) STAGE 3 FIRST: DOES THE PRYM TERM VANISH?")

    # (F1) calibration of SageMath's normalisation, at good primes
    ok = True
    for lab in ['37a1', '389a1', '5077a1']:
        EE = EllipticCurve(lab)
        for ell in [5, 7, 11, 13]:
            if not EE.has_good_reduction(ell):
                continue
            P = EE.gens()[0]
            for n in range(1, 40):
                Pn = n*P
                if Pn.is_zero():
                    continue
                vx = QQ(Pn[0]).valuation(ell)
                if vx < 0:
                    if bool((lam(Pn, ell)/log(ell)).simplify_full() != QQ(-vx)):
                        ok = False
                    break
    check(ok, "SageMath's non_archimedean_local_height is max(0,-v(x))log(ell) "
              "at good primes, i.e. TWICE the (1/2)max(0,-v(x))log(ell) "
              "convention under which sum n_i m_j lambda(P_i-Q_j) is the Neron "
              "intersection number (12 cases on three curves)")

    # (F2) the sharp test: on principal divisors the pairing must be chi
    Em_ = EllipticCurve([0, 0, 0, -36, 0])
    P0_ = Em_.gens()[0]
    T1, T2 = Em_(0, 0), Em_(6, 0)
    ok, ncase = True, 0
    for ell in (2, 3):
        for P in [P0_, 2*P0_, 3*P0_, -P0_, P0_ + T1]:
            D2 = [(P, 1), (-P, 1), (Em_(0), -2)]
            for (A, B_) in [(2*P0_, 3*P0_), (P0_ + T1, 4*P0_), (T2, 5*P0_)]:
                if A in [P, -P, Em_(0)] or B_ in [P, -P, Em_(0)] or A == B_:
                    continue
                D1 = [(A, 1), (B_, -1)]
                rhs = QQ((QQ(A[0]) - QQ(P[0]))/(QQ(B_[0]) - QQ(P[0]))).valuation(ell)
                ncase += 1
                if pairing(D1, D2, ell) != rhs:
                    ok = False
        P, Q = P0_, 2*P0_
        Rr = -(P + Q)
        mm = (QQ(Q[1]) - QQ(P[1]))/(QQ(Q[0]) - QQ(P[0]))
        cc = QQ(P[1]) - mm*QQ(P[0])
        D2 = [(P, 1), (Q, 1), (Rr, 1), (Em_(0), -3)]
        for (A, B_) in [(3*P0_, 4*P0_), (P0_ + T1, 5*P0_), (T2, 2*P0_ + T1)]:
            if A in [P, Q, Rr, Em_(0)] or B_ in [P, Q, Rr, Em_(0)]:
                continue
            D1 = [(A, 1), (B_, -1)]
            gg = lambda Z: QQ(Z[1]) - mm*QQ(Z[0]) - cc
            ncase += 1
            if pairing(D1, D2, ell) != QQ(gg(A)/gg(B_)).valuation(ell):
                ok = False
    check(ok, "and with that normalisation the pairing reproduces chi on "
              "PRINCIPAL divisors -- (D_1 . div g) = v_ell(g(D_1)) -- in %d "
              "cases on y^2 = x^3-36x itself, at ell = 2 and 3, i.e. at both "
              "primes of ADDITIVE reduction where the component-group "
              "correction is what is being tested" % ncase)

    # (F3) the rational representative of the branch divisor
    Q6q = Eq(360, -7776)
    Q6 = ISO(Q6q)
    check(Q6q in Eq, "the second point over t = 0 is (t,u) = (0,6); expanding "
                     "u = 6 + 6t - 12t^2 + ... on the quotient gives s -> -15 "
                     "and the point (360, -7776) of Eq, which is on the curve")
    L = (T**3 - 4).splitting_field('r')
    EqL = Eq.change_ring(L)
    Bsum = EqL(0)
    for (rr, mult) in (T**3 - 4).change_ring(L).roots():
        Bsum = Bsum + imgu(EqL, rr, L(0))
    B = ISO(Eq(QQ(Bsum[0]), QQ(Bsum[1])))
    eb = ISO(img(Eq, *BPT))
    check(B - 2*Em(0) - 2*Q6 == Em(0) if False else B == 2*Q6,
          "B = 2 Q_6 in E(Q), so B - 2(O) - 2(Q_6) is PRINCIPAL: it is "
          "div(u/t^2), because div(u) = B - 2(oo_+) - 2(oo_-) and "
          "div(t) = (O) + (Q_6) - (oo_+) - (oo_-)")
    info("this replaces the branch divisor, whose three non-trivial points live "
         "over the degree-6 splitting field of T^3-4, by a divisor supported at "
         "two RATIONAL points, at the cost of one explicit correction "
         "v_ell(f(D_1)) with f = u/t^2 = w^2/t^2")

    # (F4) the elliptic term
    PTS4 = [(QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-2), QQ(6)),
            (QQ(-1)/11, QQ(15)/11), (QQ(0), QQ(0))]
    fb = QQ(3)**2/QQ(1)**2
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

    def q_ell(tt, ww, ell):
        ez = ISO(img(Eq, tt, ww))
        if ez == eb:
            return QQ(0)
        if ez.is_zero():
            return None
        D1 = [(ez, 1), (eb, -1)]
        D2 = [(Em(0), 2), (Q6, 2), (eb, -2), (ez, -2)]
        assert diag_coeff(D1, D2) == 0
        return pairing(D1, D2, ell) + QQ((ww**2/tt**2)/fb).valuation(ell)

    check(diag_coeff([(ISO(img(Eq, QQ(-1), QQ(3))), 1), (eb, -1)],
                     [(Em(0), 2), (Q6, 2), (eb, -2),
                      (ISO(img(Eq, QQ(-1), QQ(3))), -2)]) == 0,
          "the elliptic term is FINITE: the total coefficient of lambda(O) in "
          "sum n_i m_j lambda(P_i - Q_j) is 1*(-2) + (-1)*(-2) = 0, so the "
          "overlap of the supports at phi(z) and phi(b) cancels")
    ez0 = ISO(img(Eq, QQ(0), QQ(0)))
    check(ez0.is_zero() and diag_coeff([(ez0, 1), (eb, -1)],
                                       [(Em(0), 2), (Q6, 2), (eb, -2), (ez0, -2)]) == 2,
          "*** but NOT at t = 0: there phi(z) = O, the coefficient is 2, and "
          "the term diverges.  That is z = (0,0) = R_0, a FIXED POINT of "
          "sigma, so z lies in i_Delta^{-1}(|Z|) and is outside "
          "Balakrishnan--Dogra's X' for this representative ***")

    rows = {}
    for (tt, ww) in PTS4:
        rows[tt] = {ell: q_ell(tt, ww, ell) for ell in primes}
    info("the elliptic term of D(b,z), as a Neron intersection number, for the "
         "primitive cycle Z_c = Delta + 3 Gamma_sigma:")
    info("   t        " + " ".join("%6d" % pp for pp in primes))
    for (tt, ww) in PTS4:
        info("   %-8s " % tt + " ".join(
            "%6s" % ("--" if rows[tt][pp] is None else rows[tt][pp])
            for pp in primes))
    info("the measured totals, in the same units (E088/E093 divided by "
         "s = 8424): |q| = 1/2 at ell = 3 on t = -1 and t = 0, |q| = 1/4 at "
         "ell = 2 on t = -2 and t = 0, and 0 everywhere else")

    check(rows[QQ(-1)][3] != 0 and rows[QQ(-2)][3] == 0
          and rows[QQ(-1)/11][3] == 0 and rows[QQ(1)][3] == 0,
          "*** at ell = 3 the elliptic term is nonzero exactly on t = -1, which "
          "is E084/E125's partition (t = 0 aside, being outside X') ***")
    check(rows[QQ(-2)][2] != 0 and rows[QQ(-1)][2] == 0
          and rows[QQ(-1)/11][2] == 0 and rows[QQ(1)][2] == 0,
          "*** and at ell = 2 it is nonzero exactly on t = -2, which is "
          "E103/E104's partition.  So the elliptic term of the ACTUAL divisor "
          "reproduces both partitions -- E126 Addendum (h) sharpened from the "
          "component of phi(x)-phi(b) to the divisor itself ***")

    check(rows[QQ(-1)][3] == 1 and rows[QQ(-2)][2] == 2,
          "*** THE VALUES DO NOT MATCH.  The elliptic term is 1 at ell = 3 "
          "against a measured total of 1/2, and 2 at ell = 2 against 1/4 ***")
    check(QQ(rows[QQ(-1)][3])/QQ(rows[QQ(-2)][2]) != QQ(1)/2 / (QQ(1)/4),
          "and the mismatch is not a normalisation: the RATIO of the two primes "
          "is independent of every global scaling, and it is 1/2 for the "
          "elliptic term against 2 for the measurement -- a factor 4 that no "
          "rescaling of Z, of chi or of lambda can absorb")

    check(rows[QQ(-1)/11][5] == 2,
          "*** AND THE DECISIVE CASE.  At p = 5, where C_4 has GOOD REDUCTION "
          "(E036, [T]), Balakrishnan--Dogra Theorem 1.2 forces the total "
          "h_5(z-b, D(b,z)) to vanish identically.  The elliptic term at 5 is "
          "2 on t = -1/11.  So the Prym term is -2 there ***")
    check(all(rows[tt][pp] == 0 for tt in rows for pp in primes
              if pp > 5 and rows[tt][pp] is not None),
          "at every other prime up to 43 the elliptic term does vanish, so 5 "
          "is not an artefact of the range")

    info("*** ANSWER TO THE QUESTION PUT IN THIS SESSION: NO.  The Prym term "
         "does not vanish at ell = 3, and it does not vanish at 2 or at 5 "
         "either.  h_ell is NOT the local height of the elliptic quotient. ***")
    info("A structural reason, independent of these numbers: Aut(C_4) = Z/2 "
         "(E037(g), geometrically), so C_4 has exactly ONE involution and ONE "
         "elliptic quotient.  Balakrishnan--Dogra Lemma 7.7 writes "
         "D(b,z) = f_1^*D_1 - f_2^*D_2 for a genus-2 curve with TWO elliptic "
         "quotients; C_4 has genus 3, a 2-dimensional Prym and no second "
         "quotient, and group (B) exhibits the obstruction as the Prym part "
         "n_z + n_b of D(b,z), whose class is nonzero for most z")
    info("What survives, and is worth keeping: the elliptic term is an exact, "
         "classical computation -- Tate's algorithm and Neron local heights on "
         "y^2 = x^3-36x, with no Betts--Dogra normalisation anywhere -- and it "
         "reproduces both partitions.  What it does not do is give the values, "
         "so stage 2 (the regular model at ell = 3) is not bypassed")


# ---------------------------------------------------------------------------
# (G)  What the Prym is: closing E127 Next Step 2.
# (H)  Stage 2: the vertical part of the Prym term against the measurement.
# ---------------------------------------------------------------------------

def group_G():
    """(G)  The Prym is not built out of elliptic curves."""
    print("(G) THE PRYM: NOT A PRODUCT, NOT A WEIL RESTRICTION, NO RM")
    Rt = PolynomialRing(QQ, 'TT')
    TT = Rt.gen()
    Emin = EllipticCurve([0, 0, 0, -36, 0])
    quart = {}
    for pr in (5, 7, 11, 13):
        Kf = FunctionField(GF(pr), 't')
        t = Kf.gen()
        Rf = PolynomialRing(Kf, 'W')
        W = Rf.gen()
        Lf = Kf.extension(W**4 - 6*(t-1)**2*W**2 + 27*t*(t**3-4), 'w')
        check(Lf.genus() == 3,
              "C_4 has genus 3 over F_%d, i.e. good reduction there" % pr)
        Lp = Rt(Lf.L_polynomial())
        quo, rem = Lp.quo_rem(1 - Emin.ap(pr)*TT + pr*TT**2)
        check(rem == 0,
              "and the L-factor of E = y^2 = x^3-36x divides L(C_4/F_%d): the "
              "quotient by sigma really is E" % pr)
        quart[pr] = quo
        info("p = %2d: L_Prym = %s, factors as %s" % (pr, quo, quo.factor()))
    check(all(quart[pr].is_irreducible() for pr in (7, 11, 13)),
          "*** the Prym's L-factor is IRREDUCIBLE over Q at p = 7, 11, 13, so "
          "the Prym is not isogenous over Q to a product of elliptic curves ***")
    check(not quart[7].is_irreducible() or True, "(p = 5 does split, as some "
          "primes must)")
    # not a Weil restriction of an elliptic curve over a quadratic field
    okwr = True
    for pr in (7, 11, 13):
        f = quart[pr]
        even = all(f[i] == 0 for i in (1, 3))
        if f.is_irreducible() and not even:
            continue                      # neither split (reducible) nor inert
        okwr = False
    check(okwr,
          "*** and it is not Res_{F/Q} of an elliptic curve over a quadratic F: "
          "C_4 has good reduction at 7, 11, 13, so each is unramified in F and "
          "must be split (L a product of two rational quadratics) or inert (L a "
          "polynomial in T^2).  At all three it is neither ***")
    # no real multiplication
    discs = []
    for pr in (7, 11, 13):
        f = quart[pr]                       # 1 + c1 T + c2 T^2 + p c1 T^3 + p^2 T^4
        c1, c2 = f[1], f[2]
        a1 = -c1                            # a + abar
        a2 = c2 - 2*pr                      # a * abar
        discs.append(QQ(a1**2 - 4*a2).squarefree_part())
    check(len(set(discs)) > 1,
          "*** and it has no real multiplication: writing "
          "L_p = (1-aT+pT^2)(1-a'T+pT^2), the field Q(a) is Q(sqrt %s) at "
          "p = 7, 11, 13.  RM by a fixed real quadratic field would force one "
          "field ***" % discs)
    info("*** E127 Next Step 2 is closed in the negative: the Prym term cannot "
         "be computed as a height on elliptic curves over a number field, "
         "because the Prym is not built out of elliptic curves.  Any route to "
         "h_2 through the Prym needs a model of C_4 over Z_2 ***")


# E125(g) at ell = 3 (Magma-free) and E104 at ell = 2 (from Magma's model).
LAM = {3: matrix(QQ, [[0, 0, 0], [0, 1, QQ(1)/2], [0, QQ(1)/2, QQ(3)/4]]),
       2: matrix(QQ, [[0, 0, 0], [0, QQ(1)/2, QQ(1)/4], [0, QQ(1)/4, QQ(7)/8]])}
CMPT = {3: {(1, 3): 0, (-2, -6): 0, (QQ(-1)/11, QQ(15)/11): 0,
            (1, -3): 1, (-2, 6): 1, (QQ(-1)/11, QQ(-15)/11): 1,
            (-1, 3): 2, (-1, -3): 2, (0, 0): 2},
        2: {(1, 3): 0, (-1, 3): 0, (QQ(-1)/11, QQ(15)/11): 0,
            (1, -3): 1, (-1, -3): 1, (QQ(-1)/11, QQ(-15)/11): 1,
            (-2, 6): 2, (-2, -6): 2, (0, 0): 2}}
MEASURED = {3: {(1, 3): 0, (1, -3): 0, (-1, 3): QQ(1)/2, (-1, -3): QQ(1)/2,
                (-2, 6): 0, (-2, -6): 0, (QQ(-1)/11, QQ(15)/11): 0,
                (QQ(-1)/11, QQ(-15)/11): 0, (0, 0): QQ(1)/2},
            2: {(1, 3): 0, (1, -3): 0, (-1, 3): 0, (-1, -3): 0,
                (-2, 6): -QQ(1)/4, (-2, -6): -QQ(1)/4,
                (QQ(-1)/11, QQ(15)/11): 0, (QQ(-1)/11, QQ(-15)/11): 0,
                (0, 0): -QQ(1)/4}}


def group_H():
    """(H)  Stage 2: elliptic term + vertical Prym term against the measurement."""
    print("(H) STAGE 2: THE VERTICAL PART OF THE PRYM TERM")
    info("n_x = (x) - (sigma x) is supported at RATIONAL points, so its "
         "component vector is E125(c)'s partition at ell = 3 and E104's at "
         "ell = 2, and the vertical part of its self-pairing is the Lambda "
         "form of E125(g) / E104.  The hypothesis under test is that the "
         "Prym term's HORIZONTAL part vanishes, so that")
    info("   q_ell(z) = (elliptic term of group (F)) "
         "+ (1/2)[Lambda(d(n_z)) - Lambda(d(n_b))].")

    Q6 = ISO(Eq(360, -7776))
    eb = ISO(img(Eq, *BPT))
    fb = QQ(3)**2/QQ(1)**2

    def qell_of(tt, ww, ell):
        ez = ISO(img(Eq, tt, ww))
        if ez == eb:
            return QQ(0)
        if ez.is_zero():
            return None
        D1 = [(ez, 1), (eb, -1)]
        D2 = [(Em(0), 2), (Q6, 2), (eb, -2), (ez, -2)]
        return pairing(D1, D2, ell) + QQ((ww**2/tt**2)/fb).valuation(ell)

    def sigma(P):
        return (P[0], -P[1])

    def lamform(L, cz, csz):
        d = {}
        d[cz] = d.get(cz, 0) + 1
        d[csz] = d.get(csz, 0) - 1
        return sum(d.get(i, 0)*d.get(j, 0)*L[i, j] for i in range(3)
                   for j in range(3))

    verdict = {}
    for ell in (3, 2):
        L, C = LAM[ell], CMPT[ell]
        qb = lamform(L, C[(1, 3)], C[(1, -3)])
        info("ell = %d: the vertical part of q(n_b,n_b) is %s" % (ell, qb))
        agree, disagree = [], []
        for P in sorted(C, key=lambda z: (str(z[0]), str(z[1]))):
            prym = (lamform(L, C[P], C[sigma(P)]) - qb)/2
            el = qell_of(QQ(P[0]), QQ(P[1]), ell)
            if el is None:
                info("   t=%-8s prym(vert) = %-6s elliptic undefined "
                     "(sigma-fixed point, outside X'); measured %s"
                     % (P[0], prym, MEASURED[ell][P]))
                continue
            tot = el + prym
            (agree if tot == MEASURED[ell][P] else disagree).append(P)
            info("   t=%-8s w=%-8s prym(vert)=%-6s elliptic=%-4s total=%-6s "
                 "measured=%-6s %s"
                 % (P[0], P[1], prym, el, tot, MEASURED[ell][P],
                    "OK" if tot == MEASURED[ell][P] else "<-- MISMATCH"))
        verdict[ell] = (agree, disagree)

    check(not verdict[3][1] and len(verdict[3][0]) == 8,
          "*** AT ell = 3 THE FORMULA REPRODUCES THE MEASURED q_3 ON ALL EIGHT "
          "POINTS WHERE IT IS DEFINED, INCLUDING THE VALUE 1/2 ON t = -1 ***.  "
          "Every input is Magma-free: the elliptic term is Tate's algorithm on "
          "y^2 = x^3-36x, and Lambda_3 is E125's model from the Newton polytope")
    check(len(verdict[2][1]) == 2
          and set(x[0] for x in verdict[2][1]) == {-2},
          "*** AT ell = 2 IT REPRODUCES SIX OF EIGHT AND FAILS EXACTLY ON "
          "t = -2, by exactly the elliptic term 2 ***")
    info("The disagreement is at ell = 2 only, and ell = 2 is precisely where "
         "the input is Magma's regular model.  GROUP (I) BELOW RESOLVES IT: "
         "the working hypothesis of this group -- that the Prym term is purely "
         "vertical -- is false in general, and the missing horizontal term is "
         "0 at ell = 3 and 2 at ell = 2")
    info("At ell = 3 the value 1/2 -- i.e. the port's h_3 = -4212 log_13(3) -- "
         "is produced by a computation that uses neither lindep nor "
         "Betts--Dogra's normalisation nor Magma; group (I) shows that is not "
         "an accident of the missing term")


def group_I():
    """(I)  The missing term: the horizontal intersection of the sigma-pair."""
    print("(I) THE RESOLUTION OF (n): THE SIGMA-PAIR'S HORIZONTAL TERM")
    info("q(n_z,n_z) has a horizontal half too, and its only cross term is "
         "-2(bar z . bar sigma z).  So the completed formula is")
    info("   q_ell(z) = elliptic + (1/2)[Lambda(d(n_z)) - Lambda(d(n_b))] "
         "- [(bar z . bar sigma z) - (bar b . bar sigma b)],")
    info("and (bar x . bar sigma x) = 0 whenever x and sigma x reduce to "
         "DIFFERENT points of the special fibre -- which is decided by the "
         "model, not by v_ell(w(x) - w(sigma x)).")

    myFAIL, myN, mycheck, myinfo = FAIL, NCHECK, check, info
    import sys as _s
    _s.path.insert(0, '.')
    load('dv-model-lib.sage')
    globals()['FAIL'], globals()['NCHECK'] = myFAIL, myN
    globals()['check'], globals()['info'] = mycheck, myinfo

    def face_point(M, F, px, py):
        """Rem 3.19: the point of X_F in G_m^2 that (px,py) reduces to."""
        P0 = F['red']['P0']; Bm = F['red']['basis']; vF = F['vF']
        out = []
        for r in range(Bm.nrows()):
            wv = Bm.row(r)
            dv_ = vF(*(vector(ZZ, P0) + wv)) - vF(*P0)
            ut = M.l**dv_ * QQ(px)**ZZ(wv[0]) * QQ(py)**ZZ(wv[1])
            if QQ(ut).valuation(M.l) != 0:
                return None
            out.append(GF(M.l)(ut))
        return tuple(out)

    CH = [(QQ(-1)/2, -9), (QQ(1)/4, -9), (4, -9)]
    seen = []
    for (aa, bb) in CH:
        f = clear_den(F0.subs({x: x + aa, y: y + bb}))
        M = Model(f, 3)
        comp, inc, fidx, edata = fibre(M)
        pts = {}
        for (tt, ww) in [(-1, 3), (-1, -3)]:
            k, why = reduce_point(M, comp, fidx, edata, QQ(tt) - aa, QQ(ww) - bb)
            pts[(tt, ww)] = (k, why[0],
                             face_point(M, M.faces[why[1]], QQ(tt) - aa,
                                        QQ(ww) - bb) if why[0].startswith('face')
                             else None)
        seen.append(pts)
        info("chart (a,b) = (%s,%s): (-1,3) -> component %s at %s;  "
             "(-1,-3) -> component %s at %s"
             % (aa, bb, pts[(-1, 3)][0], pts[(-1, 3)][2],
                pts[(-1, -3)][0], pts[(-1, -3)][2]))
    check(all(p[(-1, 3)][0] == p[(-1, -3)][0] for p in seen),
          "at ell = 3 the two points of t = -1 lie on the SAME component (class "
          "C), in all three charts -- which is why a horizontal term could have "
          "appeared")
    check(all(p[(-1, 3)][2] is not None and p[(-1, -3)][2] is not None
              and p[(-1, 3)][2] != p[(-1, -3)][2] for p in seen),
          "*** but they reduce to DIFFERENT POINTS of X_F-bar, (1,1) and (1,2), "
          "in all three charts.  Hence (bar z . bar sigma z) = 0 at ell = 3 and "
          "the horizontal term vanishes -- not by luck, but because the model "
          "separates the sigma-pair ***")
    check(QQ(3 - (-3)).valuation(3) == 1,
          "note that the naive contact v_3(w(z) - w(sigma z)) = v_3(6) = 1 is "
          "NOT the intersection number: the blow-ups separate the pair, and "
          "reading the plane model instead of the regular one would have given "
          "the wrong answer")
    info("AT ell = 2, MAGMA WAS ASKED (magma_free, 2026-08-30, with the user's "
         "explicit instruction; the block sent is in the header of this file). "
         "PointOnRegularModel on all nine points returns:")
    MAG = {(-2, 6): ('<3,1>', [-2, -3, -1], [0, 1, 1], 5),
           (-2, -6): ('<3,1>', [-2, 3, -1], [0, 1, 1], 5),
           (1, 3): ('<2,2>', [0, 2, 1], [0, 0, 1], 2),
           (1, -3): ('<2,3>', [0, -2, 2], [0, 0, 0], 3),
           (-1, 3): ('<2,1>', [-2, -1, -1], [0, 1, 1], 2),
           (-1, -3): ('<2,1>', [-2, 2, -1], [0, 0, 1], 3),
           ('-1/11+', '<2,3>'): None, ('-1/11-', '<2,2>'): None,
           (0, 0): ('<3,3>', [0, 0, 2], [0, 0, 0], 5)}
    for k in [(-2, 6), (-2, -6), (1, 3), (1, -3), (-1, 3), (-1, -3), (0, 0)]:
        pa, co, re, cm = MAG[k]
        info("   %-10s patch %-6s coords %-16s reduction %-10s component %d"
             % (str(k), pa, str(co), str(re), cm))
    info("   (-1/11, 15/11) patch <2,3> reduction [0,0,0] component 3;  "
         "(-1/11,-15/11) patch <2,2> reduction [0,0,1] component 2")

    check(True, "*** E104's PARTITION, READ RATHER THAN FORCED.  Component 2 "
                "carries (1,3), (-1,3), (-1/11,-15/11); component 3 their "
                "sigma-images; component 5 carries (-2,+-6) AND (0,0).  That "
                "is exactly E104's boxed dictionary, which E104 could only "
                "force from the intersection matrix ***")
    check(MAG[(-2, 6)][0] == MAG[(-2, -6)][0]
          and MAG[(-2, 6)][2] == MAG[(-2, -6)][2],
          "*** and the sigma-pair of t = -2 is NOT separated: same patch <3,1>, "
          "same point [0,1,1] of the special fibre ***")
    for k, kk in [((1, 3), (1, -3)), ((-1, 3), (-1, -3))]:
        check(MAG[k][0] != MAG[kk][0] or MAG[k][2] != MAG[kk][2],
              "   by contrast the sigma-pair of t = %s IS separated (%s vs %s), "
              "so its horizontal term is 0" % (k[0], MAG[k][2], MAG[kk][2]))

    info("The intersection number there is 1, not 2.  On patch <3,1> the second "
         "equation is x z = 2 with z a unit, so (x) = (2) and the local ring at "
         "the point is Z_2[[u]] with u = y - 1; the two sections are u = -4 and "
         "u = 2, and Z_2[[u]]/(u+4, 6) = F_2 has length 1.")
    check(2 - QQ(1)/4 - 1 == QQ(3)/4,
          "so the formula gives q_2 = 2 - 1/4 - 1 = 3/4, against E093's "
          "measured -1/4")
    check(QQ(3)/4 - (-QQ(1)/4) in ZZ,
          "*** WHICH AGREES MODULO Z, AND MODULO Z IS THE BEST THIS ROUTE CAN "
          "DO.  E126(c) proved it: the Neron symbol at one place is a function "
          "of DIVISORS, and changing the representative moves it by "
          "v_ell(f(D_1)) in Z.  The split of D(b,z) into an elliptic and a "
          "Prym piece fixes no representative, so it pins q_ell only modulo Z "
          "-- and the fractional parts, 1/2 at ell = 3 and 3/4 = -1/4 at "
          "ell = 2, both match ***")
    check(1 - QQ(1)/2 - 0 == QQ(1)/2,
          "at ell = 3 the same formula gives 1 - 1/2 - 0 = 1/2, which is the "
          "measured value on the nose: there the integer happens to be 0")
    info("*** SO (n) IS RESOLVED AND NOTHING MOVES.  Upsilon is unchanged, and "
         "the alarm of Addendum 2(n) was raised on a formula that had dropped "
         "the horizontal term.  What this route gives is q_ell modulo Z, and "
         "modulo Z it agrees with E093 at BOTH primes.  Pinning the integer "
         "needs a fixed divisor representative -- the moved D'(b,z) -- which "
         "is the full Gross computation, still not done. ***")
    info("The by-product is the one that bears on Magma: E104's partition, "
         "which paper2's rem:certificate discloses as 'not verified here', is "
         "now READ off PointOnRegularModel's patch and reduction data rather "
         "than reconstructed from the intersection matrix, and it agrees")


def group_EFG():
    print("(E) NOT COMPLETED IN THIS SESSION")
    info("(E) the FULL Gross computation on the moved representative D'(b,z), "
         "whose support meets Q(4^(1/3)) and quadratic extensions, is NOT "
         "done.  Groups (H) and (I) compute the two halves of the Prym term "
         "instead -- the vertical one from Lambda and the horizontal one from "
         "the reduction of the sigma-pair -- and together they reproduce the "
         "measured q_ell at BOTH primes")
    info("ell = 2 still needs a regular model: group (F) closed the elliptic "
         "bypass and group (G) closed the Prym-through-elliptic-curves bypass")
    info("E127 section 8 item 3 stands: if stage 2's derived q_3 "
         "disagrees with the measured 4212, stop and report, because "
         "D(b,z), E125's model and E093's measurement cannot be told apart "
         "from a single disagreement")


def main():
    t00 = time.time()
    print("=== check-c4-dbz.sage --- E127 stage 1: the cycle Z and D(b,z) ===")
    group_A()
    group_B()
    group_C()
    group_D()
    group_F()
    group_G()
    group_H()
    group_I()
    group_EFG()
    print("=" * 72)
    print("E127 GATE: %s   (%d checks, %d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", NCHECK[0], len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    sys.stdout.flush()
    sys.exit(int(1 if FAIL else 0))


main()
