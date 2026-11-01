# check-isotypic.sage --- E051: a K-point of C_4 that is not rational, and the
# rho-component test that turns it into rank P(Q) = 2, unconditionally.
#
# WHAT THIS IS FOR.  E049(g) reduced the last open question at q = 4 to a single
# equivalence: with rank_K Jac X <= 3 (E044(g), its Selmer convention calibrated
# over K in E050) and rank_Q P >= 2 (E046(b)),
#
#     rank_Q P = 2   <=>   c_P >= 1   <=>   some class in P(K) has nonzero
#                                            rho-component,
#
# where rank_K = rank_Q + c_P for the non-Galois cubic K = Q(2^(1/3)).  E046(d)
# looked for such a class among K-points of C_4 and found only the ramification
# point (a^2, 0), whose class is iota-invariant and so contributes nothing.
#
# WHY E046 MISSED IT.  E046 searched K-points by BOXES OF HEIGHT in t.  Its own
# lesson on the Q side was the opposite technique -- "iterate over the unit, not
# over b" (E021), i.e. walk the Mordell-Weil group -- and that is what turned up
# the rational point t = -1/11 there.  The same technique over K finds a
# non-rational K-point at n = (-1,-1), i.e. immediately: the point is not deep,
# it is only invisible to a height box because its coordinates have denominator
# 11.
#
# THE TEST (E041(b), E043(d), transplanted).  For D in A(K) with A/Q, the trace
# Tr(D) = sum over the three embeddings lands in A(Q), so Z = 3D - Tr(D) lies in
# A(K) and is killed by the trace, i.e. lies in the rho-part.  If Z is
# non-torsion then c_P >= 1.  Non-torsion is certified exactly by reduction: at
# a prime p that splits completely in K, the three embeddings K -> F_p give
# three reductions D_1, D_2, D_3 in J(F_p), and
#
#     Zbar = 3 D_1 - (D_1 + D_2 + D_3) = 2 D_1 - D_2 - D_3 .
#
# If the order of Zbar does not divide the bound on #A(K)_tors -- which injects
# into J(F_p) at every good odd degree-1 prime -- then Z is non-torsion.
#
# WHAT IT GIVES.  c_P >= 1 with rank_K <= 3 gives rank_Q P <= 2, and with
# E046(b) rank_Q P = 2 -- with no parity conjecture and no finiteness of Sha,
# so E047(f) stops being [C(parity)] and quadratic Chabauty's hypothesis
# rank Jac(C_4)(Q) = 3 = g becomes a theorem.
#
# Everything here is exact: group arithmetic in finite groups, and equalities in
# a cubic field.  No regulator, no floating point, nothing remote.
#
# Failure counts are printed explicitly; the run ends with a VERDICT block.

import sys


def say(s=""):
    print(s)
    sys.stdout.flush()


NQ = 60             # box in E(Q) for the calibration of section 1
NK = 8              # box in E(K), two generators

# Two different jobs need two different sets of primes, and conflating them is
# what makes this computation expensive.
#   * The torsion bound needs primes of K of DEGREE 1: Jac(C_4)(K)_tors injects
#     into J(F_p) for every good odd such prime.  x^3 - 2 has a root mod p for
#     every p = 2 mod 3 and for a third of the p = 1 mod 3, so these are cheap
#     and plentiful, and small p can be used.
#   * The rho-test needs p SPLIT COMPLETELY in K, so that all three embeddings
#     K -> F_p exist and the three conjugate classes live in the same J(F_p).
#     Those are the p = x^2 + 27 y^2 -- 31, 43, 109, ... -- and #J(F_p) grows
#     like p^3, so only the smallest are usable.
PTORS = 32          # torsion bound from good degree-1 primes below this
PTEST = 50          # rho-test at split-completely primes below this

# C_4 in the canonical plane model of E037(c), used only for the good(p) test
P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
QUARTIC = (27*X^4 - 108*X^3*Y + 156*X^2*Y^2 - 96*X*Y^3 + 22*Y^4
           - 108*X^3*Z + 312*X^2*Y*Z - 276*X*Y^2*Z + 76*Y^3*Z
           + 156*X^2*Z^2 - 264*X*Y*Z^2 + 90*Y^2*Z^2
           - 192*X*Z^3 + 148*Y*Z^3 + 112*Z^4)

# the genus-1 quotient H : y^2 = AA t^4 + BB t^3 + 54 t^2 + DD t + QQq^2,
# from w^2 = 3(t-1)^2 +- y ; and its Weierstrass model
AA, BB, DD, QQq = -18, -36, 72, 3
AL = -8*QQq

fails = 0

R0 = PolynomialRing(QQ, 'T')
T = R0.gen()
Ka = NumberField(T^3 - 2, 'a')
a = Ka.gen()          # a = 2^(1/3);  the w of E048/E049 is a^2 = 4^(1/3)


def c4_points(F, pts):
    """Given points of E : y^2 = x^3 - 36x over F, return the points (t,w) of
    C_4 above them: t comes from the quartic model of H, and w^2 = 3(t-1)^2 + y
    has to be a square in F."""
    EW = EllipticCurve(F, [0, 216, 0, -31104, -2985984])
    Em = EllipticCurve(F, [0, 0, 0, -36, 0])
    iso = Em.isomorphism_to(EW)
    out = []
    for P in pts:
        if P.is_zero():
            continue
        Q = iso(P)
        m, nn = Q[0]/AL, Q[1]/AL
        if AA - m^2 == 0:
            continue
        t = (nn - BB + DD*m/QQq)/(2*(AA - m^2))
        v = QQq + DD*t/(2*QQq) + m*t^2
        u = 3*(t - 1)^2 + v
        if u == 0:
            out.append((t, F(0)))
        elif u.is_square():
            out.append((t, u.sqrt()))
    return out


def on_C4(t, w):
    return w^4 - 6*(t - 1)^2*w^2 + 27*t*(t^3 - 4) == 0


# ============================================================ 1. calibration
say("=== 1. calibration: the same walk over Q reproduces E046(a) ===")
say()
Em = EllipticCurve(QQ, [0, 0, 0, -36, 0])
P0 = Em(-3, 9)
torsQ = [Em(0), Em(0, 0), Em(-6, 0), Em(6, 0)]
ptsQ = [n*P0 + Tt for n in range(-NQ, NQ + 1) for Tt in torsQ]
resQ = c4_points(QQ, ptsQ)
tQ = sorted(set([t for (t, w) in resQ if w != 0]))
say("  t with w != 0, |n| <= %d :  %s" % (NQ, tQ))
if tQ != [-2, -1, -1/11, 1]:
    say("  *** FAIL: E046(a) lists -2, -1, -1/11, 1 ***")
    fails += 1
else:
    say("  ok: exactly E046(a)'s four points")
for (t, w) in resQ:
    if not on_C4(t, w):
        say("  *** FAIL: (%s,%s) is not on C_4 ***" % (t, w))
        fails += 1
say()


# ============================================================ 2. the K-point
say("=== 2. walking E(K), K = Q(a), a^3 = 2 ===")
say("    generators of E(K) from E043(b); torsion (Z/2)^2")
say()
EmK = EllipticCurve(Ka, [0, 0, 0, -36, 0])
G1 = EmK(25*a^2 + 26*a + 28, -210*a^2 - 252*a - 354)
G2 = EmK(-2, 8)
torsK = [EmK(0), EmK(0, 0), EmK(-6, 0), EmK(6, 0)]
for (nm, G) in [("G1", G1), ("G2", G2)]:
    if G.has_finite_order():
        say("  *** FAIL: %s is torsion ***" % nm)
        fails += 1

newpts = []
for n1 in range(-NK, NK + 1):
    A1 = n1*G1
    for n2 in range(-NK, NK + 1):
        for Tt in torsK:
            for (t, w) in c4_points(Ka, [A1 + n2*G2 + Tt]):
                if not on_C4(t, w):
                    say("  *** FAIL: (%s,%s) not on C_4 ***" % (t, w))
                    fails += 1
                    continue
                if w == 0 or t in QQ:
                    continue
                if (t, w) not in newpts and (t, -w) not in newpts:
                    newpts.append((t, w))
                    say("  n = (%d,%d):  t = %s" % (n1, n2, t))
                    say("               w = %s" % w)

say()
say("  %d K-point(s) of C_4 with w != 0 and t not rational, |n| <= %d"
    % (len(newpts), NK))
say("  (the ramification point (a^2, 0) also shows up, at n = (1,2); it is")
say("   iota-invariant and contributes nothing -- that is what E046(d) found)")
if not newpts:
    say("  *** FAIL: no usable K-point; the rho-test below cannot run ***")
    fails += 1
say()


# ============================================================ 3. the rho-test
say("=== 3. the rho-component test by reduction ===")
say()


def good(p):
    if p in (2, 3, 11):
        return False
    S = PolynomialRing(GF(p), ['X', 'Y', 'Z'])
    Qp = S(QUARTIC)
    return S.ideal([Qp.derivative(v) for v in S.gens()] + [Qp]).dimension() <= 0


def place_at(L, t0, w0):
    k0 = L.base_field().constant_base_field()
    tt = L.base_field().gen()
    for Pl in L.places_above((tt - k0(t0)).zeros()[0]):
        k, _, to_k = Pl.residue_field()
        if L.gen().valuation(Pl) >= 0 and to_k(L.gen()) == k(k0(w0)):
            return Pl
    return None


def order_of(x, N):
    o = N
    for (q, e) in factor(N):
        for _ in range(e):
            if (o // q) * x == 0 * x:
                o //= q
            else:
                break
    return o


RF = PolynomialRing(QQ, 'z')
z = RF.gen()


def jacobian_at(p):
    """(J, #J(F_p)) for the smooth model of C_4 over F_p, or (None, None)."""
    FK = FunctionField(GF(p), 't')
    tt = FK.gen()
    RW = PolynomialRing(FK, 'w')
    ww = RW.gen()
    L = FK.extension(ww^4 - 6*(tt - 1)^2*ww^2 + 27*tt*(tt^3 - 4), 'W')
    if L.genus() != 3:
        return None, None, None
    J = L.jacobian(model='hess', base_div=3*L.places(1)[0].divisor())
    return L, J, J.group().order()


# --- 3a. the torsion bound, from good degree-1 primes of K (cheap)
say("  (a) torsion bound.  Jac(C_4)(K)_tors injects into J(F_p) at every good")
say("      odd prime of K of residue degree 1, i.e. whenever x^3 - 2 has a root")
say("      mod p.  Those are cheap, so small p are used here.")
say()
tbound = 0
used = []
for p in prime_range(5, PTORS):
    if not good(p):
        continue
    if not (z^3 - 2).change_ring(GF(p)).roots():
        continue
    L, J, N = jacobian_at(p)
    if N is None:
        continue
    tbound = gcd(tbound, N)
    used.append(p)
    say("      p = %3d   #J(F_p) = %s" % (p, N))
say()
say("      primes used: %s" % used)
say("      #Jac(C_4)(K)_tors divides %s = %s"
    % (tbound, factor(tbound) if tbound else "-"))
if tbound == 0:
    say("  *** FAIL: no usable prime for the torsion bound ***")
    fails += 1
say()

# --- 3b. the rho-test, at primes split completely in K
say("  (b) the class.  At p split completely in K the three embeddings")
say("      K -> F_p give D_1, D_2, D_3 in J(F_p), and Zbar = 2 D_1 - D_2 - D_3")
say("      is the reduction of Z = 3D - Tr(D).")
say()
results = []
if newpts and tbound:
    t0, w0 = newpts[0]
    say("      D = [(t0,w0) - (t0,-w0)] for the point at n = (-1,-1)")
    say()
    say("       p    #J(F_p)         ord(Zbar)   ord | %d ?" % tbound)
    for p in prime_range(5, PTEST):
        if not good(p):
            continue
        rts = [r for (r, e) in (z^3 - 2).change_ring(GF(p)).roots()]
        if len(rts) != 3:                      # want p split completely in K
            continue
        L, J, N = jacobian_at(p)
        if N is None:
            continue
        Ds = []
        for r in rts:
            # K -> F_p, a |-> r.  The coordinates have denominator 11, which is
            # a unit here since good(11) is False, so change_ring is safe.
            ti = t0.polynomial().change_ring(GF(p))(r)
            wi = w0.polynomial().change_ring(GF(p))(r)
            Pp, Pm = place_at(L, ti, wi), place_at(L, ti, -wi)
            if Pp is None or Pm is None:
                Ds = None
                break
            Ds.append(J(Pp.divisor() - Pm.divisor()))
        if Ds is None:
            continue
        Zb = 2*Ds[0] - Ds[1] - Ds[2]
        o = order_of(Zb, N)
        results.append((p, N, o))
        say("      %3d  %-14s  %-10s  %s"
            % (p, N, o, "yes" if tbound % o == 0 else "NO  <== non-torsion"))
        if tbound % o != 0:
            # one prime is a complete certificate; #J(F_p) grows like p^3 and
            # the next split prime (43) costs several minutes for nothing
            say("      (stopping: a single prime certifies non-torsion)")
            break
    say()
    witness = [(p, N, o) for (p, N, o) in results if tbound % o != 0]
    if witness:
        p, N, o = witness[0]
        say("      at p = %d the order of Zbar is %d, which does not divide the"
            % (p, o))
        say("      torsion bound %d.  Since reduction is a homomorphism,"
            % tbound)
        say("      ord(Zbar) | ord(Z), so Z = 3D - Tr(D) is NOT torsion:")
        say("      ==> D has nonzero rho-component, c_P >= 1.")
    else:
        say("      *** no prime separates ord(Zbar) from the torsion bound ***")
        say("      (that does not prove Z torsion; this certificate failed)")
        fails += 1
say()


# ============================================================ 4. conclusion
say("=== 4. what follows ===")
say()
if newpts and results and [r for r in results if tbound % r[2] != 0]:
    say("  c_P >= 1.  With rank_K Jac X = rank_K P <= 3 (E044(g), whose Selmer")
    say("  convention E050 calibrated over K) and rank_K = rank_Q P + c_P:")
    say("      rank_Q P <= 3 - 1 = 2,")
    say("  and with rank_Q P >= 2 (E046(b)):")
    say("      rank_Q P = 2       -- no parity conjecture, no finiteness of Sha")
    say("      rank Jac(C_4)(Q) = 1 + 2 = 3 = g")
    say("  So E047(f)'s [C(parity)] is retired and quadratic Chabauty's")
    say("  hypothesis at q = 4 is unconditional.")
    say("  Also, by E049(e)'s counting, c_P = 1 exactly and rank_K = 3.")
say()

say("=== VERDICT ===")
say("  failures: %d" % fails)
if fails == 0:
    say("  [T(CAS)] C_4 has a K-point with w != 0 and t irrational, and its")
    say("  Prym class has nonzero rho-component; hence c_P >= 1 and")
    say("  [T(CAS)] rank P(Q) = 2, rank Jac(C_4)(Q) = 3 = g, unconditionally.")
else:
    say("  a step failed; see the *** FAIL *** lines above.")
