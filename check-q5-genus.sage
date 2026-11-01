## check-q5-genus.sage --- E021: the genus of the q=5 curve
##
##   C : u^2 - u + 1 - v = 0,  i.e.  (2u-1)^2 = 4v-3,   where
##   u = 81x^5-135x^3y+45xy^2+15x^2-5y,   v = 81y^5-135xy^3+45x^2y+15y^2-5x
##
## Here (x,y) = (A/3,B/3), where X^3-BX^2+AX-1 is the minimal polynomial of a
## unit u>1 with eta_b = u^5; see check-q5.gp for the derivation.  Run with
##     sage check-q5-genus.sage
## Runtime: under a minute (Sage 10.7).
##
## RESULT: the genus is 6, computed three ways (in (x,y), with the variables
## interchanged, and on the projective closure).  Since 6 >= 2, Faltings'
## theorem gives finitely many rational points on the smooth model, hence
## finitely many integral points on C, hence only finitely many b with eta_b a
## fifth power of a unit.
##
## NOTE: the function-field route (K.<x>=FunctionField(QQ); L=K.extension(f);
## L.genus()) did NOT terminate here -- killed after 25 minutes, both over QQ
## and over GF(p).  The plane-curve route via Singular's normal.lib works.

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

R.<x, y> = QQ[]
u = 81*x^5 - 135*x^3*y + 45*x*y^2 + 15*x^2 - 5*y
v = 81*y^5 - 135*x*y^3 + 45*x^2*y + 15*y^2 - 5*x
C = u^2 - u + 1 - v
A2 = AffineSpace(2, QQ, names=['x', 'y'])

print("=== the curve ===")
print("total degree, deg_x, deg_y  :", C.degree(), C.degree(x), C.degree(y))
check(C.degree() == 10 and C.degree(x) == 10 and C.degree(y) == 5 and len(C.factor()) == 1,
      "E021(c): C is irreducible over QQ of total degree 10, deg_x = 10, deg_y = 5")
print("factorisation over QQ       :", C.factor()); sys.stdout.flush()

print()
print("=== genus, three ways ===")
print("genus, variables (x,y)      :", Curve(C, A2).genus()); sys.stdout.flush()
print("genus, variables swapped    :", Curve(C.subs({x: y, y: x}), A2).genus()); sys.stdout.flush()
check(Curve(C, A2).genus() == 6 and Curve(C.subs({x: y, y: x}), A2).genus() == 6,
      "E021(g): g(C_5) = 6 in (x,y) and with the variables interchanged")

P2 = ProjectiveSpace(2, QQ, names=['X', 'Y', 'Z'])
X, Y, Z = P2.gens()
Ch = sum(c * X^e[0] * Y^e[1] * Z^(10 - e[0] - e[1])
         for e, c in zip(C.exponents(), C.coefficients()))
PC = Curve(Ch, P2)
g = PC.genus()
print("genus of the projective closure :", g); sys.stdout.flush()
check(g == 6, "E021(g): g(C_5) = 6 on the projective closure -- the third computation")
print("sum of the delta invariants = (d-1)(d-2)/2 - g = 36 - g =", 36 - g)

print()
print("=== the singular locus ===")
print("rational singular points of the projective closure :", PC.singular_points())
print("rational singular points of the affine model       :", Curve(C, A2).singular_points())
print("(Sage lists only the points rational over the base field!)"); sys.stdout.flush()
I = R.ideal([C, C.derivative(x), C.derivative(y)])
print("dimension of the affine singular locus (0 = finite, nonempty) :", I.dimension())
print("its degree (points counted with multiplicity)                 :",
      I.vector_space_dimension()); sys.stdout.flush()
check(I.dimension() == 0 and I.vector_space_dimension() == 12
      and Curve(C, A2).singular_points() == [],
      "E021(g): the affine singular locus is 0-dimensional of degree 12 with NO QQ-rational point "
      "(singular_points() returning [] is NOT smoothness)")
for gg in I.elimination_ideal([y]).gens():
    if gg != 0:
        print("eliminant in x, factored :", gg.factor())
print("note 9x^2-3x-1 has roots (1 +- sqrt5)/6: the sqrt5 of the fifth power.")

print()
print("=== consequence ===")
if g >= 2:
    print("g =", g, ">= 2, so by Faltings' theorem the smooth model has only finitely")
    print("many rational points; hence C has finitely many integral points and only")
    print("finitely many b can have eta_b a fifth power.  (Non-effective.)")

gate("E021")
