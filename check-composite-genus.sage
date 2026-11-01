## check-composite-genus.sage --- E026 (d): the genus of C_q for COMPOSITE q, and
## for q = 2 and q = 3, in the raw coordinates (A,B).
##
## CONTEXT.  check-qpow-genus.sage (E022) computed g(C_q) for the primes q = 5,7,11
## after the substitution A = 3x, B = 3y, which is legitimate there because the
## mod-3 step of E022(a) forces (A,B) = (0,0) mod 3.  For composite q that step is
## weaker (for q = 4 the admissible classes are (0,0),(1,1),(2,2)), so the raw
## curve must be used; the genus is unaffected, a substitution A = 3x being a linear
## change of coordinates.  q = 5 is recomputed raw as a calibration: it must again
## give 6.
##
## WHAT IS AT STAKE.  g(C_q) >= 2 gives, by Faltings, that only finitely many b have
## q | n(b).  For q = 4 and q = 6 that is exactly the statement that Umemoto's
## observation -- the fundamental unit of an exceptional K_b is the root of the
## Lucas-type cubic X^3-BX^2+AX-1 of thm:iff -- holds for all but finitely many
## members of the Pell family.
##
## RESULT.  g(C_2) = 0, g(C_3) = 1, g(C_4) = 3, g(C_5) = 6, g(C_6) = 10, g(C_8) = 21,
## so the conjectural formula g(C_q) = (q-1)(q-2)/2 of E022(f) -- stated there for
## the primes 5,7,11,17,19 -- holds for composite q and for q = 2,3 as well.  The
## three regimes of paper 1, Remark 5.8, are exactly the three genus regimes:
##      q = 2  : g = 0, rational  -> infinitely many b   (the Pell family, paper 1, Theorem 5.1)
##      q = 3  : g = 1, elliptic  -> finitely many integral points, in fact b = 9
##                                   only (paper 1, Lemma 5.3), effectively by Siegel
##      q >= 4 : g >= 2           -> finitely many, by Faltings (non-effective)
##
## Run with:  sage check-composite-genus.sage        (about 7 seconds)

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


R.<A, B> = QQ[]
A2 = AffineSpace(2, QQ, names=['A', 'B'])

def curve(q):
    """C_q in the raw coordinates (A,B): p_q(B,A)^2 - 3 p_q(B,A) + 9 - 3 p_q(A,B)."""
    p = [R(3), B, B^2 - 2*A]
    for k in range(3, q+1):
        p.append(B*p[k-1] - A*p[k-2] + p[k-3])
    pA = p[q]
    pB = pA.subs({A: B, B: A})
    return R(pB^2 - 3*pB + 9 - 3*pA)

def analyse(q):
    C = curve(q)
    d = C.degree()
    print("=" * 64)
    print("q =", q, "  deg =", d, "  deg_A =", C.degree(A), "  deg_B =", C.degree(B))
    F = list(C.factor())
    irr = (len(F) == 1 and F[0][1] == 1)
    print("  irreducible over QQ :", irr)
    print("  arithmetic genus    :", (d-1)*(d-2)//2)
    sys.stdout.flush()
    g = sum(Curve(f, A2).genus() for f, e in F)
    for f, e in F:
        if len(F) > 1 or e != 1:
            print("   component of degree", f.degree(), "multiplicity", e,
                  " genus", Curve(f, A2).genus())
    print("  GENUS               :", g, "   predicted (q-1)(q-2)/2 =", (q-1)*(q-2)//2,
          "  ", "MATCH" if g == (q-1)*(q-2)//2 else "*** MISMATCH ***")
    check(irr and d == 2*q, "E026(d): C_q is irreducible over QQ of degree 2q, q = %d" % q)
    check(g == (q-1)*(q-2)//2, "E026(d): g(C_q) = (q-1)(q-2)/2, q = %d" % q)
    print("  sum of delta invariants :", (d-1)*(d-2)//2 - g)
    if g == 0:
        print("  => rational: infinitely many rational points are possible.")
    elif g == 1:
        print("  => elliptic: finitely many INTEGRAL points, effectively (Siegel/Baker).")
    else:
        print("  => g >= 2: by Faltings only finitely many rational points on the smooth")
        print("     model, hence finitely many b with q | n(b).  (Non-effective.)")
    sys.stdout.flush()
    return g

print("### calibration: q = 5 in raw (A,B) must reproduce E021/E022's genus 6 ###")
sys.stdout.flush()
g5 = analyse(5)
print("calibration passed:", g5 == 6)
check(g5 == 6, "E026(d): calibration -- q=5 in raw (A,B) reproduces E021/E022's genus 6")
print()

gs = {5: g5}
for q in [2, 3, 4, 6, 8]:
    gs[q] = analyse(q)

print()
print("### summary ###")
print("  q        :", sorted(gs))
print("  g(C_q)   :", [gs[q] for q in sorted(gs)])
print("  (q-1)(q-2)/2 :", [(q-1)*(q-2)//2 for q in sorted(gs)])
print("  all match:", all(gs[q] == (q-1)*(q-2)//2 for q in gs))
check(gs[4] == 3 and gs[6] == 10,
      "E026(d): g(C_4) = 3 and g(C_6) = 10, both >= 2 -- the CAS input to the Faltings finiteness of E026(d)")
check(gs[2] == 0 and gs[3] == 1,
      "E026(d): the genus trichotomy -- C_2 is rational (Pell) and C_3 is elliptic (b = 9)")
print()
print("  Together with E022(f) (q = 7,11,17,19 give 15,45,120,153) the conjecture")
print("  g(C_q) = (q-1)(q-2)/2 is now supported by q = 2,3,4,5,6,7,8,11,17,19.")

gate("E026")
