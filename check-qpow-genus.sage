## check-qpow-genus.sage --- E022: the genus of the q-th power curve C_q, q = 7, 11
##
## Same construction as check-q5-genus.sage, made uniform in q.  If eta_b = e^q with
## e>1 a unit of minimal polynomial X^3-BX^2+AX-1, Newton's identities give
##     p_q(A,B) = P = 3(b^2+b+1),      p_q(B,A) = Q = 3(b+1),
## where p_q(A,B) is the sum of the q-th powers of the roots of X^3-BX^2+AX-1
## (e1=B, e2=A, e3=1).  For every prime q not equal to 13 the system forces
## A = B = 0 mod 3 (check-qpow.gp section (1), exhaustive over the 9 classes), so we
## may put A = 3x, B = 3y and divide by 3:
##     U(x,y) = p_q(3y,3x)/3 = b+1,    V(x,y) = p_q(3x,3y)/3 = b^2+b+1,
## and eliminating b leaves
##     C_q : U^2 - U + 1 - V = 0,   equivalently (2U-1)^2 = 4V-3.
## For q=5 this is exactly the curve of check-q5-genus.sage (genus 6).
##
## Run with:  sage check-qpow-genus.sage
##
## The genus is computed by the plane-curve route (Singular's normal.lib), which is
## the one that worked for q=5; the function-field route does not terminate.  Every
## print is flushed, because a SIGKILL otherwise loses the earlier output (E021).

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

def power_sums(q):
    """p_k(A,B) for k <= q as polynomials in A=3x, B=3y, divided by nothing yet:
    returns the list [p_0, ..., p_q] with e1 = B = 3y, e2 = A = 3x, e3 = 1."""
    A, B = 3*x, 3*y
    p = [R(3), B, B^2 - 2*A]
    for k in range(3, q+1):
        p.append(B*p[k-1] - A*p[k-2] + p[k-3])
    return p

def curve(q):
    """C_q in the coordinates (x,y) = (A/3,B/3)."""
    pA = power_sums(q)[q]                       # p_q(A,B) with A=3x, B=3y
    pB = pA.subs({x: y, y: x})                  # p_q(B,A)
    assert all(c % 3 == 0 for c in pA.coefficients()), "p_q(A,B) not divisible by 3"
    assert all(c % 3 == 0 for c in pB.coefficients()), "p_q(B,A) not divisible by 3"
    U = pB / 3                                  # = b+1
    V = pA / 3                                  # = b^2+b+1
    return R(U^2 - U + 1 - V), R(U), R(V)

A2 = AffineSpace(2, QQ, names=['x', 'y'])

def analyse(q, do_genus=True):
    C, U, V = curve(q)
    print("=" * 62)
    print("q =", q)
    print("  total degree, deg_x, deg_y :", C.degree(), C.degree(x), C.degree(y))
    F = C.factor()
    print("  irreducible over QQ        :", len(list(F)) == 1 and list(F)[0][1] == 1)
    print("  arithmetic genus (d-1)(d-2)/2 :", (C.degree()-1)*(C.degree()-2)//2)
    sys.stdout.flush()

    I = R.ideal([C, C.derivative(x), C.derivative(y)])
    print("  affine singular locus: dimension", I.dimension(), end="")
    if I.dimension() == 0:
        print(", degree", I.vector_space_dimension())
    else:
        print()
    sys.stdout.flush()
    print("  rational singular points (base field only!) :",
          Curve(C, A2).singular_points())
    sys.stdout.flush()
    for gg in I.elimination_ideal([y]).gens():
        if gg != 0:
            print("  eliminant in x, factored :", gg.factor())
            sys.stdout.flush()

    if not do_genus:
        print("  (genus computation skipped)")
        return None
    g = Curve(C, A2).genus()
    print("  GENUS, variables (x,y)     :", g); sys.stdout.flush()
    g2 = Curve(C.subs({x: y, y: x}), A2).genus()
    print("  GENUS, variables swapped   :", g2); sys.stdout.flush()
    print("  sum of delta invariants    :", (C.degree()-1)*(C.degree()-2)//2 - g)
    if g >= 2:
        print("  => g >= 2: by Faltings only finitely many rational points on the")
        print("     smooth model, hence finitely many integral points on C_q, hence")
        print("     only finitely many b with eta_b a q-th power.  (Non-effective.)")
    sys.stdout.flush()
    return g

## q=5 first, as a calibration: check-q5-genus.sage got 6.
print("### calibration: q = 5 must give genus 6 ###"); sys.stdout.flush()
g5 = analyse(5)
print("calibration passed:", g5 == 6); sys.stdout.flush()
check(g5 == 6, "E022(e): calibration -- q=5 reproduces E021's g(C_5) = 6")

print()
print("### q = 7 ###"); sys.stdout.flush()
g7 = analyse(7)

print()
print("### q = 11 ###"); sys.stdout.flush()
g11 = analyse(11)

print()
print("### summary ###")
print("genus of C_q :", {5: g5, 7: g7, 11: g11})
check(g7 == 15 and g11 == 45, "E022(e): g(C_7) = 15 and g(C_11) = 45, so Faltings applies at q = 7 and q = 11")

## The observed values 6, 15, 45 are exactly (q-1)(q-2)/2, the genus of a SMOOTH
## PLANE CURVE OF DEGREE q -- even though C_q has degree 2q and arithmetic genus
## (2q-1)(q-1).  Set CHECK_PATTERN = True to test q=17 and q=19 as well; those two
## take about 45 minutes together, which is why they are off by default.  Recorded
## result (E022(f)):
##     q      5   7   11   17   19
##     g(C_q) 6  15   45  120  153      = (q-1)(q-2)/2 in every case.
CHECK_PATTERN = False
if CHECK_PATTERN:
    print()
    print("### genus pattern: is g(C_q) = (q-1)(q-2)/2 ? ###")
    print("  q   deg   arith genus   genus   (q-1)(q-2)/2   match"); sys.stdout.flush()
    for q in [5, 7, 11, 17, 19]:
        C = curve(q)[0]
        d = C.degree()
        g = Curve(C, A2).genus()
        pred = (q-1)*(q-2)//2
        print("  %2d  %4d   %8d    %6d   %8d      %s"
              % (q, d, (d-1)*(d-2)//2, g, pred, g == pred))
        sys.stdout.flush()

gate("E022")
