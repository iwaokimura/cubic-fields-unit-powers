## check-prym-indep.sage --- E046: rank P(Q) >= 2, proved.  All local, all exact.
##
## WHAT E045 GOT WRONG.  E045 tested the Prym classes coming from "the rational
## points of C_4" and found they span rank 1, and concluded that the case against
## classical Chabauty had collapsed.  The list of points was incomplete.  E040
## recorded only the points that give an INTEGRAL b -- t = -2, -1, 0, 1 -- because
## those are the ones that answer the arithmetic question; but C_4(Q) is bigger,
## and for the rank of the Prym every rational point counts.  Walking E(Q) turns
## up
##        t = -1/11,  u = 225/121,  w = 15/11,
## which lies on C_4 (checked exactly below) and which E045 never used.
##
## THE ARGUMENT.  For a rational point with w != 0, D(t0,w0) = [(t0,w0)-(t0,-w0)]
## satisfies iota D = -D and so lies in the Prym.  Put
##        Lambda = {(a,b) : a D_i + b D_j is torsion}.
## Lambda is SATURATED (if n(a,b) in Lambda then (a,b) in Lambda), so if the two
## classes are dependent modulo torsion, Lambda contains a PRIMITIVE vector.
## Torsion of Jac(C_4)(Q) injects into J(F_p) at odd primes of good reduction, so
## its order divides gcd_p #J(F_p) = 16; hence for (a,b) in Lambda and any such p,
##        a(16 Dbar_i) + b(16 Dbar_j) = 0 ,
## i.e. Lambda is contained in the exactly computable lattice
##        L_p = {(a,b) : a A* + b B* = 0},   A* = 16 Dbar_i,  B* = 16 Dbar_j.
## Intersecting the L_p over several p gives a lattice of content 15, i.e. one
## contained in 15*ZZ^2, which has no primitive vector.  So Lambda = 0.
##
## Everything above is group arithmetic and equality in finite groups: exact, no
## regulator, no floating point.  SageMath's function-field Jacobians work on the
## smooth model of C_4 over F_p, so no plane model is needed either.

import sys

P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
QUARTIC = (27*X^4 - 108*X^3*Y + 156*X^2*Y^2 - 96*X*Y^3 + 22*Y^4
           - 108*X^3*Z + 312*X^2*Y*Z - 276*X*Y^2*Z + 76*Y^3*Z
           + 156*X^2*Z^2 - 264*X*Y*Z^2 + 90*Y^2*Z^2
           - 192*X*Z^3 + 148*Y*Z^3 + 112*Z^4)

NMAX = 60          # box in the Mordell-Weil group of E(Q) for the point search
PBOUND = 32        # good primes used


def good(p):
    """good reduction of C_4, and p not the denominator of the new point"""
    if p in (2, 3, 11):
        return False
    S = PolynomialRing(GF(p), ['X', 'Y', 'Z'])
    Qp = S(QUARTIC)
    return S.ideal([Qp.derivative(v) for v in S.gens()] + [Qp]).dimension() <= 0


def rational_points():
    """C_4(Q) with w != 0, by walking E(Q); returns [(t, w), ...]"""
    EW = EllipticCurve([0, 216, 0, -31104, -2985984])
    Em = EllipticCurve([0, 0, 0, -36, 0])
    iso = Em.isomorphism_to(EW)
    P0 = Em(-3, 9)
    tors = [Em(0), Em(0, 0), Em(-6, 0), Em(6, 0)]
    aa, bb, dd, qq = -18, -36, 72, 3
    al = -8*qq
    out = []
    for n in range(-NMAX, NMAX + 1):
        for T in tors:
            P = n*P0 + T
            if P.is_zero():
                continue
            Q = iso(P)
            m = Q[0]/al
            nn = Q[1]/al
            if aa - m^2 == 0:
                continue
            t = (nn - bb + dd*m/qq)/(2*(aa - m^2))
            v = qq + dd*t/(2*qq) + m*t^2
            u = 3*(t - 1)^2 + v
            if u > 0 and u.is_square():
                w = sqrt(u)
                if (t, w) not in out:
                    out.append((t, w))
    return sorted(set(out))


def place_at(L, t0, w0):
    k0 = L.base_field().constant_base_field()
    t = L.base_field().gen()
    for P in L.places_above((t - k0(t0)).zeros()[0]):
        k, _, to_k = P.residue_field()
        if L.gen().valuation(P) >= 0 and to_k(L.gen()) == k(k0(w0)):
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


def relation_lattice(A, B, N):
    """the exact lattice {(a,b) : aA + bB = 0} in ZZ^2"""
    nA, nB = order_of(A, N), order_of(B, N)
    span = {}
    x = 0 * B
    for k in range(nB):
        span[x] = k
        x = x + B
    rows = [vector(ZZ, [nA, 0]), vector(ZZ, [0, nB])]
    y = 0 * A
    for a in range(1, nA):
        y = y + A
        if -y in span:
            rows.append(vector(ZZ, [a, span[-y]]))
            break
    return (ZZ^2).span(rows)


def run():
    nfail = 0

    print("=== 1. the rational points of C_4, by walking E(Q) ===")
    pts = rational_points()
    for (t, w) in pts:
        chk = w^4 - 6*(t - 1)^2*w^2 + 27*t*(t^3 - 4)
        flag = "known (integral b)" if t in (-2, -1, 0, 1) else "MISSED BY E045"
        print("  t = %-10s w = %-8s on C_4: %s   %s" % (t, w, chk == 0, flag))
        if chk != 0:
            nfail += 1
    print("  (|n| <= %d in the Mordell-Weil group; E045 used only the first three)"
          % NMAX)
    sys.stdout.flush()

    print("")
    print("=== 2. reduction data ===")
    data, orders = {}, []
    for p in [q for q in prime_range(5, PBOUND) if good(q)]:
        K = FunctionField(GF(p), 't')
        t = K.gen()
        R = PolynomialRing(K, 'w')
        w = R.gen()
        L = K.extension(w^4 - 6*(t - 1)^2*w^2 + 27*t*(t^3 - 4), 'W')
        if L.genus() != 3:
            continue
        J = L.jacobian(model='hess', base_div=3*L.places(1)[0].divisor())
        N = J.group().order()
        D = []
        for (t0, w0) in pts:
            Pp, Pm = place_at(L, t0, w0), place_at(L, t0, -w0)
            if Pp is None or Pm is None:
                D = None
                break
            D.append(J(Pp.divisor() - Pm.divisor()))
        if D is None:
            continue
        data[p] = (N, D)
        orders.append(N)
        print("  p = %3d  #J(F_p) = %-8s orders %s"
              % (p, N, [order_of(x, N) for x in D]))
        sys.stdout.flush()

    tb = 0
    for N in orders:
        tb = gcd(tb, N)
    print("  torsion of Jac(C_4)(Q) divides gcd #J(F_p) = %s = %s" % (tb, factor(tb)))
    if tb != 16:
        print("  *** the argument below hard-codes the multiplier 16")
        nfail += 1

    print("")
    print("=== 3. the relation lattices, intersected ===")
    i4 = [k for k in range(len(pts)) if pts[k][0] not in (-2, -1, 0, 1)]
    if not i4:
        print("  *** FAIL: the new point was not found")
        return nfail + 1
    i4 = i4[0]
    proved = False
    for j in range(len(pts)):
        if j == i4:
            continue
        M = ZZ^2
        for p in sorted(data):
            N, D = data[p]
            M = M.intersection(relation_lattice(16*D[i4], 16*D[j], N))
        c = gcd([ZZ(x) for x in M.basis_matrix().list()])
        print("  pair (D(%s), D(%s)): intersected lattice has content %s"
              % (pts[i4][0], pts[j][0], c))
        if c > 1:
            proved = True
    print("")
    print("=== VERDICT ===")
    if proved:
        print("  Some intersected lattice lies in c*ZZ^2 with c > 1, so it contains")
        print("  no primitive vector, so Lambda = 0:")
        print("  [T(CAS)]  rank P(Q) >= 2.")
        print("")
        print("  With E044(g)'s rank P(Q) <= 3:  rank P(Q) in {2,3}, hence")
        print("  rank Jac(C_4)(Q) = 1 + rank P(Q) >= 3 = g, and CLASSICAL CHABAUTY")
        print("  IS UNAVAILABLE at q = 4.  E038(e) is [P] no longer; E045's")
        print("  reversal is itself reversed, by the point E045 had missed.")
        print("  Quadratic Chabauty's hypothesis rank = g holds iff rank P(Q) = 2,")
        print("  which is now the only case left to decide.")
    else:
        print("  no pair settled by these primes")
        nfail += 1
    print("")
    print("  failures: %d" % nfail)
    return nfail


run()
