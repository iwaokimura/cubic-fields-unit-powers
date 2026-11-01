## check-e029-dtilde.sage --- E029 Phase 1: the base curve D~ of the tower
##
## E029, Step 1.  Let T = {(e1,e2,e3) : e1 e2 e3 = 1} = G_m^2 and
## let A^2_{A,B} = T/S_3 be the adjoint quotient (X^3 - B X^2 + A X - 1).  The
## family of units eta_b has minimal polynomial
##       X^3 - 3(b^2+b+1) X^2 + 3(b+1) X - 1,
## so B = 3(b^2+b+1), A = 3(b+1), and eliminating b gives the parabola
##       D :  A^2 - 3A + 9 - 3B = 0   in A^2_{A,B},   D = A^1_b.
## D~ is its preimage in T, i.e. the curve of ORDERED triples of conjugates of
## eta_b; D~ -> A^1_b is the Galois closure, of degree 6.  D~_1 is the degree-3
## curve obtained by choosing one root.
##
## Run with:  PYTHONUNBUFFERED=1 sage check-e029-dtilde.sage
## Runtime: about a minute (Sage 10.7).
##
## RESULT: g(D~_1) = 0 and g(D~) = 1, matching the Riemann-Hurwitz computation
## of E029 Step 1.  The script also certifies each ingredient of that
## hand computation separately: the rational parametrisation of D~_1, the
## Newton polygon at b = 0 (monodromy = a transposition), the simplicity of the
## zeros of the discriminant at b^3 = 4, unramifiedness at b = infinity, and
## Gal = S_3 over Q(b).  Khovanskii's lattice-point bound for D~ is 4, so it is
## NOT attained: D~ is degenerate for its Newton polygon.

import sys
## --- E119 gate harness (added 2026-08-19; see E119) ---
import sys as _sys
FAIL = []
def check(c, msg):
    if not c:
        print("   [FAIL] %s" % msg)
        FAIL.append(msg)
    _sys.stdout.flush()
    return c
def gate(tag):
    print("")
    print("%s GATE: %s   (%d failures)"
          % (tag, "*** RED ***" if FAIL else "GREEN", len(FAIL)))
    for m in FAIL:
        print("   FAILED: %s" % m)
    _sys.stdout.flush()
## --- end gate harness ---

print("=== (0) the family and the parabola D ===")
Rb.<x, b> = QQ[]
f = x^3 - 3*(b^2+b+1)*x^2 + 3*(b+1)*x - 1
print("D~_1 :", f)
check(len(f.factor()) == 1 and f.factor()[0][1] == 1, "E029(1): D~_1 is irreducible over QQ")
## the elimination: B = 3(b^2+b+1), A = 3(b+1) satisfy A^2-3A+9-3B = 0
RAB.<A, B> = QQ[]
Ab, Bb = 3*(b+1), 3*(b^2+b+1)
elim = (A^2 - 3*A + 9 - 3*B).subs({A: Ab, B: Bb})
print("A^2 - 3A + 9 - 3B  at (A,B) = (3(b+1), 3(b^2+b+1)) :", elim)
check(elim == 0, "E029(1): D is the parabola A^2 - 3A + 9 - 3B = 0, and b |-> A is injective")
sys.stdout.flush()

print()
print("=== (1a) D~_1 is rational: b solved for, and s^2 = 3(4x-1) ===")
## collect f in b:  -3x^2 b^2 + 3x(1-x) b + (x-1)^3
c2 = f.coefficient({b: 2}); c1 = f.coefficient({b: 1}); c0 = f.coefficient({b: 0})
print("coefficients in b :  b^2:", c2, "   b^1:", c1, "   b^0:", c0)
check(c2 == -3*x^2 and c1 == -3*x^2 + 3*x and c0 == (x-1)^3,
      "E029(1a): f = -3x^2 b^2 + 3x(1-x) b + (x-1)^3")
disc_b = c1^2 - 4*c2*c0
print("discriminant in b :", disc_b.factor())
check(disc_b == 3*x^2*(x-1)^2*(4*x-1),
      "E029(1a): disc_b(f) = 3 x^2 (x-1)^2 (4x-1), so the double cover is s^2 = 3(4x-1)")
## the parametrisation x = (s^2+3)/12,  b = (s-3)^2 (s+3) / (6 (s^2+3))
Fs.<s> = FunctionField(QQ)
xs = (s^2 + 3)/12
bs = (s - 3)^2 * (s + 3) / (6 * (s^2 + 3))
val = f.subs({x: xs, b: bs})
print("f( (s^2+3)/12, (s-3)^2(s+3)/(6(s^2+3)) ) =", val)
check(val == 0, "E029(1a): (x,b) = ((s^2+3)/12, (s-3)^2(s+3)/(6(s^2+3))) parametrises D~_1")
print("=> D~_1 is rational; predicted g(D~_1) = 0.")
sys.stdout.flush()

print()
print("=== (1b) branching of D~_1 -> A^1_b: disc, and the Newton polygon at b = 0 ===")
Pb.<bb> = QQ[]
Rx.<X> = Pb[]
fb = X^3 - 3*(bb^2+bb+1)*X^2 + 3*(bb+1)*X - 1
dsc = Pb(fb.discriminant())
print("disc_X(f) as a polynomial in b :", dsc.factor())
check(dsc == -27*bb^3*(bb^3 - 4),
      "E029(1b): disc_X(f) = -27 b^3 (b^3 - 4)  (b^3-4, not b^3-1)")
print("  v_0(disc) = 3 (odd)  =>  the monodromy at b = 0 is odd, i.e. a transposition.")
print("  b^3 - 4 is separable :", (bb^3-4).is_squarefree(),
      " => the three zeros b^3 = 4 are simple zeros of disc, monodromy a transposition.")
check((bb^3-4).is_squarefree() and gcd(bb^3-4, bb) == 1,
      "E029(1b): the branch locus of D~_1 -> A^1_b is {0} u {b^3 = 4}, four points")
## Newton polygon at b = 0: put X = 1 + u.
Ru.<u, bp> = QQ[]
g0 = f.subs({x: 1 + u, b: bp})
print("f(1+u, b) =", g0)
lowterms = [(e[0], e[1]) for e in g0.exponents()]
print("  exponents (u-degree, b-degree) :", sorted(lowterms))
## lower Newton polygon in (i, v) with term u^i b^v: vertices (3,0), (1,1), (0,2)
print("  lower hull vertices : (3,0), (1,1), (0,2)  => slopes 1/2 (twice) and 1 (once)")
check(g0.coefficient({u: 3, bp: 0}) == 1 and g0.coefficient({u: 1, bp: 1}) == -3
      and g0.coefficient({u: 0, bp: 2}) == -3,
      "E029(1b): f(1+u,b) = u^3 - 3 b u - 3 b^2 + (higher), Newton polygon has slopes 1/2, 1/2, 1")
print("  => two roots u ~ +-sqrt(3b) (ramified, e=2) and one root u ~ -b (unramified).")
print("  => the monodromy at b = 0 is a TRANSPOSITION.  Consistent with v_0(disc) = 3 odd.")
sys.stdout.flush()

print()
print("=== (1c) b = infinity is unramified: three points, e = 1 ===")
## Work in the local parameter t = 1/b.  Clearing denominators,
##      t^2 f(Y, 1/t) = t^2 Y^3 - 3(1+t+t^2) Y^2 + 3t(1+t) Y - t^2.
Rt.<Y, t> = QQ[]
ft = t^2*Y^3 - 3*(1 + t + t^2)*Y^2 + 3*t*(1 + t)*Y - t^2
print("  t^2 f(Y, 1/t) =", ft)
## verify the substitution honestly: f(Y, 1/t) * t^2, cleared in the fraction field
Ft = Rt.fraction_field()
lhs = Ft(t)^2 * f.subs({x: Ft(Y), b: 1/Ft(t)})
check(lhs == Ft(ft), "E029(1c): t^2 f(Y,1/t) = t^2 Y^3 - 3(1+t+t^2) Y^2 + 3t(1+t) Y - t^2")
print("  Newton polygon in (Y-degree, t-valuation): (3,2), (2,0), (1,1), (0,2)")
print("  lower hull (3,2)-(2,0)-(0,2): slopes -2 (once) and +1 (twice)")
print("  => ord_t(e_1) = -2, ord_t(e_2) = ord_t(e_3) = +1, sum 0 (the product is 1).")
check([(int(e[0]), int(e[1])) for e in ft.exponents()].count((3,2)) == 1,
      "E029(1c): the vertex (3,2) of the Newton polygon gives the single root of order -2")
## the two slope-+1 roots: put Y = tZ and divide by t^2.
Z = Rt.gen(0)
h = Ft(ft.subs({Y: Ft(t)*Ft(Z)}) / Ft(t)^2)
h = Rt(h)
print("  after Y = tZ and dividing by t^2 :", h)
check(h == t^3*Z^3 - 3*(1+t+t^2)*Z^2 + 3*(1+t)*Z - 1,
      "E029(1c): the slope-+1 part is t^3 Z^3 - 3(1+t+t^2) Z^2 + 3(1+t) Z - 1")
res = h.subs({t: 0})
print("  at t = 0 :", res, "  discriminant :", 9 - 12)
check(res == -3*Z^2 + 3*Z - 1 and (9 - 12) != 0,
      "E029(1c): the residual quadratic -3Z^2+3Z-1 has nonzero discriminant -3")
print("  => the two small roots stay distinct; separating them needs sqrt(-3), a CONSTANT")
print("     field extension, which is unramified at t = 0.  So b = infinity is unramified")
print("     in D~_1 and in D~: D~ has exactly 6 points over b = infinity (= T \\ T boundary).")
sys.stdout.flush()

print()
print("=== (1d) the Galois group over Q(b) is S_3 ===")
Kb.<bt> = FunctionField(QQ)
Rk.<T> = Kb[]
fk = T^3 - 3*(bt^2+bt+1)*T^2 + 3*(bt+1)*T - 1
print("f over Q(b) is irreducible :", fk.is_irreducible())
d = fk.discriminant()
print("disc =", d.factor())
issq = d.is_square()
print("is disc a square in Q(b)? :", issq)
check(fk.is_irreducible() and not issq,
      "E029(1d): f is irreducible over Q(b) with non-square discriminant, so Gal = S_3")
print("  => D~ -> A^1_b is Galois of degree 6 with group S_3, and D~ -> D~_1 has degree 2.")
sys.stdout.flush()

print()
print("=== (2) the genus of D~_1 (predicted 0) ===")
A2b = AffineSpace(2, QQ, names=['x', 'b'])
g1 = Curve(f, A2b).genus()
print("g(D~_1) =", g1)
check(g1 == 0, "E029(1a): g(D~_1) = 0, as the parametrisation predicts")
sys.stdout.flush()

print()
print("=== (3) the genus of D~ (predicted 1) ===")
## D~ inside T: coordinates (e1,e2), e3 = 1/(e1 e2).
R2.<e1, e2> = QQ[]
FF = R2.fraction_field()
E1, E2 = FF(e1), FF(e2)
E3 = 1/(E1*E2)
P = E1 + E2 + E3
Q = E1*E2 + E1*E3 + E2*E3
G = (Q^2 - 3*Q + 9 - 3*P) * (E1*E2)^2
G = R2(G.numerator()) if G.denominator() == 1 else R2(G.numerator()/G.denominator())
G = R2(G)
print("D~ :", G)
print("  total degree =", G.degree(), "  deg_e1 =", G.degree(e1), "  deg_e2 =", G.degree(e2))
print("  factorisation over QQ :", G.factor())
check(len(G.factor()) == 1 and G.factor()[0][1] == 1, "E029(1): the plane model of D~ is irreducible over QQ")
sys.stdout.flush()
A2e = AffineSpace(2, QQ, names=['e1', 'e2'])
gD = Curve(G, A2e).genus()
print("  g(D~) =", gD)
print("  Riemann-Hurwitz prediction (E029 Step 1): 2g-2 = 6(-2) + 3 + 3*3 = 0, g = 1")
check(gD == 1, "E029(1): g(D~) = 1, matching Riemann-Hurwitz over the four branch points")
sys.stdout.flush()

print()
print("=== (4) Khovanskii's bound is NOT attained (E029 sec.1(d)) ===")
from sage.geometry.polyhedron.constructor import Polyhedron
expo = [(int(e[0]), int(e[1])) for e in G.exponents()]
Pgon = Polyhedron(vertices=expo)
allpts = Pgon.integral_points()
inte = [p for p in allpts if Pgon.interior_contains(p)]
print("  Newton polygon vertices :", sorted([tuple(v) for v in Pgon.vertices_list()]))
print("  interior lattice points I =", len(inte), "   boundary lattice points =",
      len(allpts) - len(inte))
check(sorted([tuple(v) for v in Pgon.vertices_list()]) == [(0,2), (2,0), (4,4)]
      and len(inte) == 4 and len(allpts) - len(inte) == 6,
      "E029(1d'): the Newton polygon of D~ has vertices (0,2),(2,0),(4,4), I = 4, B = 6")
check(gD < len(inte),
      "E029(1d'): g(D~) = 1 < 4 = I, so D~ is DEGENERATE for its Newton polygon and "
      "Khovanskii's bound is not attained")
print("  => the toric genus formula cannot be used as a black box; E029 runs")
print("     Riemann-Hurwitz on the S_3-cover instead.")
sys.stdout.flush()

print()
print("=== summary of Phase 1 ===")
print("  g(D~_1) = %s (predicted 0),  g(D~) = %s (predicted 1)" % (g1, gD))
print("  branch locus of D~ -> A^1_b : b = 0 and b^3 = 4, four points, monodromy a")
print("  transposition at each; b = infinity unramified, 6 points on D~.")
print("  These are exactly the inputs Step 2 of E029 needs.")

gate("E029")
