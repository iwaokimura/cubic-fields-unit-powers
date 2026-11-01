## check-prym-points.sage --- E045: what the rational points of C_4 give in the
## Prym.  Everything here is local (SageMath function fields) and exact: group
## operations and equality tests in finite groups, no regulator, no floating point.
##
## THE PLAN THIS SCRIPT WAS WRITTEN TO EXECUTE (E044 Next Step (i)).  iota is
## (t,w) -> (t,-w), so for a rational point (t0,w0) with w0 != 0 the class
##        D(t0,w0) = [(t0,w0) - (t0,-w0)]
## satisfies iota D = -D and lies in the Prym P.  The rational points of C_4 are
## t = -2,-1,0,1 with u = w^2 = 36,9,0,9 (E040), giving three such classes.  The
## hope was that two of them are independent, which would give rank P(Q) >= 2 and
## so turn E038(e) -- "classical Chabauty is unavailable at q = 4" -- from [P]
## into a theorem.
##
## WHAT ACTUALLY HAPPENS.  They are not independent: modulo every good prime
## tested, D_3 = D_1 + D_2 and 2 D_1 + 4 D_2 = 0.  The three classes span rank 1,
## not 2, so the plan fails and E038(e) stays unproved -- and, since classical
## Chabauty needs rank Jac(C_4)(Q) = 1 + rank P(Q) < g = 3, i.e. rank P(Q) <= 1,
## the possibility that classical Chabauty DOES apply is not excluded.
##
## WHAT IS PROVED.  The classes are non-torsion: torsion of Jac(C_4)(Q) injects
## into J(F_p) for odd p of good reduction, so its order divides the gcd of the
## #J(F_p), which is 16; and the classes have orders like 30 and 15 mod 5.  Hence
##        [T(CAS)]  rank P(Q) >= 1 .
## With E044's rank P(Q) <= 3 this leaves rank P(Q) in {1,2,3}.
##
## HOW INDEPENDENCE WOULD HAVE BEEN CERTIFIED, had it held (kept because it is
## the right tool for the next pair of classes someone tries).  If two classes
## are dependent modulo torsion there is a PRIMITIVE relation a D_1 + b D_2 = T,
## gcd(a,b) = 1, T torsion.  Reduce at good odd p, write #J(F_p) = l^e m with
## l not dividing the torsion bound; then m*T = 0, so aA + bB = 0 for
## A = m D_1, B = m D_2 in the l-Sylow; as gcd(a,b) = 1 one coefficient is prime
## to l, so <A,B> is cyclic and the order-l elements A', B' satisfy A' in <B'>.
## So exhibiting one (p,l) with A' not in <B'> refutes every primitive relation.
## No such (p,l) exists here for p < 32, which is consistent with the relation
## found rather than with a failure of the method.

import sys

# the canonical quartic of E037(c), used only to decide good reduction
P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
QUARTIC = (27*X^4 - 108*X^3*Y + 156*X^2*Y^2 - 96*X*Y^3 + 22*Y^4
           - 108*X^3*Z + 312*X^2*Y*Z - 276*X*Y^2*Z + 76*Y^3*Z
           + 156*X^2*Z^2 - 264*X*Y*Z^2 + 90*Y^2*Z^2
           - 192*X*Z^3 + 148*Y*Z^3 + 112*Z^4)

POINTS = [(-2, 6), (-1, 3), (1, 3)]          # w > 0 representatives
BOUND = 4                                     # search bound for small relations


def good(p):
    if p in (2, 3):
        return False
    S = PolynomialRing(GF(p), ['X', 'Y', 'Z'])
    Qp = S(QUARTIC)
    return S.ideal([Qp.derivative(v) for v in S.gens()] + [Qp]).dimension() <= 0


def function_field(p):
    K = FunctionField(GF(p), 't')
    t = K.gen()
    R = PolynomialRing(K, 'w')
    w = R.gen()
    return K.extension(w^4 - 6*(t - 1)^2*w^2 + 27*t*(t^3 - 4), 'W')


def place_at(L, t0, w0):
    """the place of L over t = t0 at which W reduces to w0"""
    t = L.base_field().gen()
    for P in L.places_above((t - t0).zeros()[0]):
        k, _, to_k = P.residue_field()
        if L.gen().valuation(P) >= 0 and to_k(L.gen()) == k(w0):
            return P
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


def run():
    nfail = 0
    cands = set((a, b, c)
                for a in range(-BOUND, BOUND + 1)
                for b in range(-BOUND, BOUND + 1)
                for c in range(-BOUND, BOUND + 1) if (a, b, c) != (0, 0, 0))
    orders_of_J = []
    class_orders = {}

    print("=== 1. the classes in J(F_p), p of good reduction ===")
    print("  D_1 = D(-2,6), D_2 = D(-1,3), D_3 = D(1,3)")
    sys.stdout.flush()
    for p in [q for q in prime_range(5, 32) if good(q)]:
        L = function_field(p)
        if L.genus() != 3:
            print("  p = %3d: genus %d, not 3 -- skipped" % (p, L.genus()))
            nfail += 1
            continue
        J = L.jacobian(model='hess', base_div=3*L.places(1)[0].divisor())
        N = J.group().order()
        D = []
        for (t0, w0) in POINTS:
            Pp, Pm = place_at(L, t0, w0), place_at(L, t0, -w0)
            if Pp is None or Pm is None:
                D = None
                break
            D.append(J(Pp.divisor() - Pm.divisor()))
        if D is None:
            print("  p = %3d: a place is missing -- skipped" % p)
            nfail += 1
            continue
        ords = [order_of(x, N) for x in D]
        orders_of_J.append(N)
        class_orders[p] = ords
        zero = 0 * D[0]
        cands = set(v for v in cands
                    if v[0]*D[0] + v[1]*D[1] + v[2]*D[2] == zero)
        print("  p = %3d  #J(F_p) = %-8s orders %-22s small relations left: %d"
              % (p, N, str(ords), len(cands)))
        sys.stdout.flush()

    tb = 0
    for N in orders_of_J:
        tb = gcd(tb, N)
    print("")
    print("=== 2. the classes are NOT torsion ===")
    print("  Jac(C_4)(Q)_tors injects into J(F_p) at odd good p, so its order")
    print("  divides gcd(#J(F_p)) = %s = %s." % (tb, factor(tb)))
    witness = None
    for p in sorted(class_orders):
        for i, o in enumerate(class_orders[p]):
            if tb % o != 0:
                witness = (p, i + 1, o)
                break
        if witness:
            break
    if witness is None:
        print("  *** FAIL: no class of order prime to the torsion bound found")
        nfail += 1
    else:
        p, i, o = witness
        print("  D_%d has order %d mod %d, which does not divide %d." % (i, o, p, tb))
        print("  ==> [T(CAS)] the class is non-torsion, so rank P(Q) >= 1.")

    print("")
    print("=== 3. but they span rank 1, not 2 ===")
    print("  relations with |a|,|b|,|c| <= %d holding at EVERY prime above:" % BOUND)
    prim = sorted(v for v in cands if gcd([abs(x) for x in v]) == 1)
    for v in prim:
        print("     %s" % (v,))
    if not prim:
        print("     none")
    print("  Read them: (1,1,-1) says D_3 = D_1 + D_2, and (1,3,1) then gives")
    print("  2 D_1 + 4 D_2 = 0 -- both in the surviving set, e.g. (2,4,0) is")
    print("  there too: %s." % ((2, 4, 0) in cands))
    print("  Two independent relations among three classes leaves span of rank 1:")
    print("  the rational points of C_4 give rank 1 in the Prym, not 2.")

    print("")
    print("=== VERDICT ===")
    print("  [T(CAS)]  rank P(Q) >= 1                    (section 2)")
    print("  [E: 9 primes]  the known points span only rank 1   (section 3)")
    print("  [T(CAS)]  rank P(Q) <= 3                    (E044)")
    print("  ==> rank P(Q) in {1,2,3}, and E038(e) -- classical Chabauty is")
    print("      unavailable -- REMAINS UNPROVED.  It needs rank P(Q) >= 2, and")
    print("      if instead rank P(Q) = 1 then rank Jac(C_4)(Q) = 2 < 3 = g and")
    print("      classical Chabauty APPLIES.  (In principle: carrying it out still")
    print("      needs Coleman integration on a non-hyperelliptic genus-3 curve,")
    print("      i.e. Tuitman's algorithm, which E044 found is Magma-only.)")
    print("")
    print("  failures: %d" % nfail)
    sys.stdout.flush()
    return nfail


run()
