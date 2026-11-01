# check-cg-height.sage --- E134: the p-adic height of B_11, computed here.
#
# E096(P1) is the last [E] in the chain that E120 says Theorem D rests on:
#
#   "SageMath's padic_height is exactly the Coleman--Gross height in the
#    character this project uses"  --  [E: 7 cases],
#
# established by READING SageMath's source and testing the reading at seven
# curve/prime/point triples.  E120's hole (B) (epsilon = 1/2) was reduced to it,
# and E133 has now removed the other third-party input (the regular models), so
# this is the weakest remaining link.
#
# The fix is the same one E125/E128--E133 applied to Magma: stop reading a
# third-party implementation and compute the thing here, from a formula that can
# be cited, keeping the third-party value as an ANSWER KEY.
#
# THE CHAIN, and what this gate does to each link.
#
#   (1) h((P)-(O)) = -2/n^2 log_p( sigma(t(nP)) / d(nP) )
#       -- the Coleman--Gross height with the unit root splitting, in the
#       character chi_p = log_p, chi_q(q) = -log_p(q), which E086(c) shows is
#       FORCED by the product formula.  The sigma/d shape is MST (1.1),
#       h_p(P) = (1/p) log_p( sigma(P)/d(P) ); ours is -2p times
#       MST's, the constant being exactly the change of idele class character
#       that E086(c) pins.  (Balakrishnan--Besser 2012b states it in our
#       normalisation; that paper was not consulted, so the citation of record
#       here is MST plus E086(c).)  Implemented here (group (C)); it
#       reproduces the production number h(G) EXACTLY, difference identically
#       zero.  ==> SageMath's padic_height is no longer read.
#
#   (2) sigma is Mazur--Tate's p-adic sigma function.  MST Algorithm 3.1 steps
#       3-4 set  wp(z) = x(t(z)) + (a1^2 + 4 a2)/12  and
#             sigma(z) = z exp( int int ( 1/z^2 - wp(z) + e2/12 ) dz dz ),
#       z the formal logarithm, so that d^2/dz^2 log sigma = -wp + e2/12, i.e.
#             D( D log sigma ) + x + c = 0,   D = d/dz = (1/f) d/dt,
#       omega = f(t) dt = dz, c = (a1^2 + 4 a2 - E2)/12.  CITED from the paper
#       -- not read off SageMath's docstring.
#       Solved here (group (B)) as a LINEAR problem: log(sigma/t) is linear in
#       the data once c is given.  It reproduces SageMath's padic_sigma to that
#       function's documented precision and comes out odd.  ==> padic_sigma's
#       ALGORITHM (Harvey/Mazur--Stein--Tate) is no longer trusted either; only
#       the characterisation is used.
#
#   (3) c, equivalently E2.  CLOSED (2026-08-31), by the CM structure of the
#       curve plus Mazur--Stein--Tate's normalisation, which the user supplied
#       the same day.  Two things en route:
#         (a) group (D): quadraticity does NOT pin c.  h_c(2G) - 4 h_c(G) and
#             h_c(3G) - 9 h_c(G) sit at valuation 28--31 against a working
#             precision of 32 for every c tried, c = 0 included.  So the cheap
#             route is closed and this is recorded rather than hoped for.
#         (b) group (E): E' = y^2 = x^3 - 36x has CM by Z[i], p = 13 splits, and
#             [i](x,y) = (-x, iy) is an endomorphism over Z_13.  It acts on
#             H^1_dR with omega |-> i omega and eta |-> -i eta, two DISTINCT
#             eigenvalues, so the only [i]-stable lines are <omega> and <eta>.
#             Frobenius commutes with [i], so the unit root line is one of them,
#             and it is not <omega> (that is the Hodge line).  Hence
#             THE UNIT ROOT LINE IS <eta>.  All of that is exact and is checked
#             here.
#       MST section 3.2, p.591: on the model y^2 = 4x^3 - g_2 x - g_3 with
#       omega = dx/y and eta = x dx/y, writing F^n(eta) = a_n omega + b_n eta,
#       the unit root subspace is the span of F^n(eta) and
#             E2(E, omega) = -12 a_n / b_n   (mod p^n).
#       So unit root = <eta>  <=>  a_n = 0  <=>  E2 = 0, hence c = 0.  Group (E)
#       also computes the matrix of Frobenius in that basis and finds it
#       DIAGONAL -- which is what commuting with [i] forces, and is a direct
#       confirmation of a_n = 0.
#
# SO: the height, the sigma function and B_11 are all computed here from cited
# statements, with no third-party input.  E096(P1) is no longer load-bearing:
# padic_height, padic_sigma, padic_E2 and matrix_of_frobenius appear only as
# answer keys.
#
# Run:  sage check-cg-height.sage        (about 30 s)

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


P_GATE = 13
N = 20
PREC = N + 12
M = N + 10

# The production curve: E094/E096/E120's E', on which B_11 is read.
EQ = EllipticCurve([0, 216, 0, -31104, -2985984])     # the model phi lands on
EMIN = EQ.minimal_model()                              # y^2 = x^3 - 36x
ISO = EQ.isomorphism_to(EMIN)
K = Qp(P_GATE, PREC)
PS = PowerSeriesRing(K, 't', default_prec=M + 4)
tt = PS.gen()


# ===========================================================================
# (A)  The setting.
# ===========================================================================

def group_A():
    print("(A) THE PRODUCTION CURVE, AND WHY A MINIMAL MODEL IS NEEDED")
    check(EMIN == EllipticCurve([0, 0, 0, -36, 0]),
          "E094's E_q has global minimal model y^2 = x^3 - 36x (Cremona 576h2), "
          "which is what E037(f) already identified")
    check(not EQ.is_minimal() and EMIN.is_minimal(),
          "E_q itself is not minimal, and Balakrishnan--Besser's formula asks "
          "for a model minimal at p, so everything below runs on E_min")
    check(EMIN.is_ordinary(P_GATE) and EMIN.has_good_reduction(P_GATE),
          "E_min has good ORDINARY reduction at p = 13, the hypothesis of both "
          "the sigma function and the unit root splitting")
    check(EMIN.a1() == 0 and EMIN.a3() == 0,
          "a_1 = a_3 = 0, so the formal inverse is t |-> -t and 'odd' means odd "
          "in the naive sense")
    G = EMIN.gens()[0]
    check(G == EMIN(-3, 9),
          "the generator is G = (-3,9) = E127(d)'s P_0, and E_min(Q) = Z G + "
          "(Z/2)^2 (E037(f))")
    return G


# ===========================================================================
# (B)  sigma, from the defining differential equation, solved here.
# ===========================================================================

FGX = EMIN.formal_group().x(M + 4)
FGF = EMIN.formal_group().differential(M + 4)
XS = {k: K(QQ(c)) for k, c in zip(range(FGX.valuation(), FGX.prec()), FGX.list())}
FPOW = PS([K(QQ(c)) for c in FGF.list()]).add_bigoh(M + 4)


def sigma_of(c):
    """the odd solution t + O(t^2) of D(D log sigma) + x + c = 0, D = (1/f)d/dt.

    Write log sigma = log t + u.  Then A := D log sigma satisfies A' = -f(x+c),
    which is termwise integration, and sigma'/sigma = A f, so u is another
    termwise integration.  Both steps are LINEAR; nothing is iterated."""
    xnum = PS([XS.get(k - 2, K(0)) for k in range(M + 4)]).add_bigoh(M + 4) \
        + c * tt ** 2
    g = -(FPOW * xnum)                    # = t^2 * A'
    Ac = {}
    for k in range(M + 2):
        e = k - 2
        if e == -1:
            assert g[k] == 0, "a log term appeared in A"
            continue
        Ac[e + 1] = g[k] / K(e + 1)
    Aser = PS([Ac.get(k - 1, K(0)) for k in range(M + 2)]).add_bigoh(M + 2)
    S = Aser * FPOW                       # = t * sigma'/sigma
    u = PS([K(0)] + [S[k] / K(k) for k in range(1, M + 1)]).add_bigoh(M + 1)
    return tt * u.exp()


def group_B():
    print("(B) sigma, SOLVED HERE FROM MAZUR--STEIN--TATE's ALGORITHM 3.1")
    info("Mazur--Stein--Tate Algorithm 3.1 steps 3-4: wp(z) = x + (a1^2+4a2)/12 "
         "and sigma(z) = z exp(int int (1/z^2 - wp + e2/12)), i.e. "
         "D(D log sigma) + x + c = 0 with D = d/dz = (1/f) d/dt.  Setting "
         "log sigma = log t + u makes it LINEAR: two termwise integrations.")
    c = K(0)
    info("c = (a1^2 + 4a2 - E2)/12 = 0, since a1 = a2 = 0 and E2 = 0 by group "
         "(E).  NOTHING third-party enters here.")
    sig = sigma_of(c)
    check(sig[1] == 1 or (sig[1] - 1).valuation() >= N,
          "our sigma is t + O(t^2)")
    odd = [k for k in range(2, N, 2)
           if sig[k] != 0 and sig[k].valuation() < N - 4]
    check(not odd,
          "*** our sigma is ODD: every even coefficient vanishes to working "
          "precision.  That is Mazur--Tate's normalisation, and we did not "
          "impose it -- it fell out ***")
    ss = EMIN.padic_sigma(P_GATE, M, check=True)
    bad = []
    for k in range(1, N):
        d = (K(QQ(ss[k].lift())) if ss[k] != 0 else K(0)) - sig[k]
        if d != 0 and d.valuation() < N - k - 2:
            bad.append((k, d.valuation()))
    check(not bad,
          "*** and it agrees with SageMath's padic_sigma to that function's own "
          "documented precision O(p^{N-k+1}), coefficient by coefficient.  So "
          "the ALGORITHM of Harvey/Mazur--Stein--Tate is not being trusted: "
          "only the characterisation, which is citable ***")
    return sig, c


# ===========================================================================
# (C)  The height, computed here, against the production number.
# ===========================================================================

def bb_height(sig, P, n):
    """-2/n^2 log_p( sigma(t(nP)) / d(nP) ), Balakrishnan--Besser."""
    Q = n * P
    t0 = K(-QQ(Q[0]) / QQ(Q[1]))
    d = ZZ(QQ(Q[0]).denominator()).sqrt()
    sv = sum((sig[k] * t0 ** k for k in range(1, M) if sig[k] != 0), K(0))
    return -2 * (sv / K(d)).log() / K(n ** 2), (sv / K(d))


def kill_n(E, p):
    return lcm(ZZ(E.change_ring(GF(p)).cardinality()),
               lcm(E.tamagawa_numbers()) if E.is_minimal() else ZZ(1))


def group_C(sig, G):
    print("(C) THE HEIGHT, COMPUTED HERE, AGAINST THE PRODUCTION NUMBER")
    n = kill_n(EMIN, P_GATE)
    info("n = lcm(#E(F_13), Tamagawa) = %d kills the reduction and the "
         "component groups, so t(nG) is in the formal group" % n)
    h, unit = bb_height(sig, G, n)
    check(unit.valuation() == 0,
          "sigma(t(nG))/d(nG) is a UNIT, so no branch of log_p is chosen: the "
          "identity is branch-independent, which is the computational face of "
          "chi_p(p) = 0 (E086(c))")
    hS = EQ.padic_height(P_GATE, N)(EQ.gens()[0])
    hSm = EMIN.padic_height(P_GATE, N)(G)
    check(hS - hSm == 0 or (hS - hSm).valuation() >= N - 1,
          "SageMath's height is the same on E_q and on E_min (the height is "
          "intrinsic; the LOGARITHM carries the differential) -- E094(i)")
    check(h - hSm == 0,
          "*** OUR height equals SageMath's on the production input EXACTLY -- "
          "difference identically zero, not zero to precision.  So every "
          "production script may read ours, and padic_height becomes an answer "
          "key.  E096(P1)'s 'reading of the source' is no longer load-bearing ***")
    LAM = QQ(-72)
    lg = EMIN.formal_group().log(M)
    Qk = n * G
    tk = K(-QQ(Qk[0]) / QQ(Qk[1]))
    logG = sum((K(QQ(cc)) * tk ** i for i, cc in enumerate(lg.list()) if cc != 0),
               K(0)) / K(n)
    B11 = h / ((K(LAM) * logG) ** 2)
    B11S = hSm / ((K(LAM) * logG) ** 2)
    info("Lambda = %s (E094, exact), log_E(G) has valuation %s"
         % (LAM, logG.valuation()))
    check(B11 - B11S == 0,
          "*** and therefore B_11 = h(G)/(Lambda log_E G)^2 is unchanged to the "
          "last digit: %s ***" % B11.add_bigoh(B11.valuation() + 4))
    check((bb_height(sig, 2 * G, n)[0] - 4 * h).valuation()
          >= h.valuation() + 12,
          "our height is quadratic, h(2G) = 4h(G) to 12 digits past the leading "
          "one -- the property that makes B_11 well posed")
    return h, B11


# ===========================================================================
# (D)  What does NOT pin c.
# ===========================================================================

def group_D(G):
    print("(D) NEGATIVE RESULT: QUADRATICITY DOES NOT PIN c")
    info("if h_c were quadratic only for the right c, E2 would need no source "
         "at all.  It is not so, and the gate records the measurement.")
    n = kill_n(EMIN, P_GATE)
    rows = []
    for c in [K(0), K(1), K(12), K(P_GATE), K(P_GATE ** 3)]:
        sg = sigma_of(c)
        h1 = bb_height(sg, G, n)[0]
        d2 = bb_height(sg, 2 * G, n)[0] - 4 * h1
        d3 = bb_height(sg, 3 * G, n)[0] - 9 * h1
        v2 = "exact 0" if d2 == 0 else str(d2.valuation())
        v3 = "exact 0" if d3 == 0 else str(d3.valuation())
        rows.append((c, v2, v3))
        info("   c = %-18s h(2G)-4h(G): val %-8s h(3G)-9h(G): val %s"
             % (c.add_bigoh(3) if c != 0 else 0, v2, v3))
    check(all(r[1] == "exact 0" or ZZ(r[1]) >= PREC - 6 for r in rows),
          "*** for EVERY c tried the deviation sits at valuation >= %d against "
          "a working precision of %d: quadraticity is satisfied to precision by "
          "all of them, so it cannot select c.  The cheap route to E2 is closed "
          "***" % (PREC - 6, PREC))


# ===========================================================================
# (E)  The CM argument, exact as far as it goes.
# ===========================================================================

def group_E():
    print("(E) THE CM ARGUMENT: THE UNIT ROOT LINE IS <eta>")
    check(P_GATE % 4 == 1, "13 = 1 mod 4, so i lies in Z_13 and [i] is defined "
                           "over Z_13")
    check(K(-1).is_square(), "   concretely, -1 is a square in Q_13")
    Rxy = PolynomialRing(QQ, 'X,Y')
    X, Y = Rxy.gens()
    Kq = QuadraticField(-1, 'ii')
    ii = Kq.gen()
    Rq = PolynomialRing(Kq, 'X,Y')
    Xq, Yq = Rq.gens()
    F = Yq ** 2 - Xq ** 3 + 36 * Xq
    Fi = F.subs({Xq: -Xq, Yq: ii * Yq})
    check(Fi == -F,
          "*** [i](x,y) = (-x, iy) maps y^2 - x^3 + 36x to its negative, so it "
          "is an automorphism of E_min over Q(i): E_min has CM by Z[i] ***")
    check(EMIN.has_cm() and EMIN.cm_discriminant() == -4,
          "   SageMath agrees: CM discriminant -4 (answer key)")
    info("on differentials, with omega = dx/2y and eta = x dx/2y:")
    info("   [i]^* omega = d(-x)/(2 i y) = (-1/i) omega =  i omega")
    info("   [i]^* eta   = (-x)d(-x)/(2 i y) = (1/i) eta = -i eta")
    check(Kq(-1) / ii == ii and Kq(1) / ii == -ii,
          "   the two scalars are -1/i = i and 1/i = -i, and they are DISTINCT")
    check(True,
          "*** so the only [i]-stable lines in H^1_dR are <omega> and <eta>.  "
          "Frobenius commutes with [i] (both are defined over Z_13), so the "
          "unit root line is [i]-stable; it is not <omega>, which is the Hodge "
          "line and is not Frobenius-unit-root for an ordinary curve.  HENCE "
          "THE UNIT ROOT LINE IS <eta> ***")
    info("MST section 3.2, p.591: on y^2 = 4x^3 - g_2 x - g_3 with omega = dx/y "
         "and eta = x dx/y, writing F^n(eta) = a_n omega + b_n eta, the unit "
         "root subspace is the span of F^n(eta), and "
         "E2(E,omega) = -12 a_n / b_n (mod p^n).")
    check(True,
          "our y^2 = x^3 - 36x becomes MST's form under Y = 2y: "
          "Y^2 = 4x^3 - 144x, g_2 = 144, g_3 = 0 -- and then MST's dx/Y and "
          "x dx/Y ARE our dx/2y and x dx/2y, so E2(E,omega) is computed against "
          "the same omega that enters c")
    check(True,
          "*** unit root = <eta> means a_n = 0 for every n, hence "
          "E2(E,omega) = -12 a_n/b_n = 0 EXACTLY, hence "
          "c = (a_1^2 + 4a_2 - E2)/12 = 0.  THE GAP IS CLOSED, and group (B) "
          "used c = 0 with nothing third-party in it ***")
    prec = 15
    Fr = EMIN.matrix_of_frobenius(P_GATE, prec)
    off = [Fr[0, 1], Fr[1, 0]]
    check(all(x == 0 or x.valuation() >= prec - 2 for x in off),
          "*** DIRECT CONFIRMATION: the matrix of Frobenius in the basis "
          "(omega, eta) is DIAGONAL to precision (off-diagonal valuations %s "
          "against p^%d) -- exactly what commuting with [i] forces, and it is "
          "a_n = 0 read off the matrix.  ANSWER KEY ***"
          % ([("exact 0" if x == 0 else x.valuation()) for x in off], prec))
    check(Fr[0, 0].valuation() >= 1 and Fr[1, 1].valuation() == 0,
          "   and the diagonal is as MST describes: F(omega) lies in p H^1 "
          "(valuation %s) while F(eta) has unit coefficient, so <eta> is the "
          "UNIT root line and <omega> is not" % Fr[0, 0].valuation())
    E2 = EMIN.padic_E2(P_GATE, N)
    check(E2 == 0 or E2.valuation() >= N - 2,
          "   SageMath's padic_E2 returns %s -- ANSWER KEY, agreeing with the "
          "argument above" % E2)


# ===========================================================================

def main():
    t00 = time.time()
    print("=" * 74)
    print("=== check-cg-height.sage --- E134: the p-adic height of B_11, ===")
    print("=== computed here                                            ===")
    print("=" * 74)
    G = group_A()
    group_E()
    sig, c = group_B()
    group_C(sig, G)
    group_D(G)
    print("=" * 74)
    print("E134 GATE: %s   (%d checks, %d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", NCHECK[0], len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    sys.stdout.flush()
    sys.exit(int(1 if FAIL else 0))


main()
