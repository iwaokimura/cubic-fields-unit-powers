## check-c4-autgroup.sage --- E037: Aut(C_4) is EXACTLY Z/2.
##
## check-c4-aut.gp exhibits one involution, so |Aut(C_4)| >= 2.  This script
## supplies the upper bound.
##
## THE SET-UP.  For the canonical smooth plane quartic Q,
##        Aut(X) = { M in PGL_3 : Q(Mv) = lambda Q(v) }.
## Rescaling M by c sends lambda to c^4 lambda, so over an algebraically closed
## field we may normalise lambda = 1, and then the solution set of
##        Q(Mv) = Q(v)      in GL_3
## is exactly Aut(X) x mu_4.  Hence the 0-dimensional scheme it cuts out has
##        degree  =  4 * |Aut(X)| ,
## provided it is reduced -- and reducedness comes for free from the count: we
## already KNOW 8 distinct solutions (c*I and c*M for c^4 = 1, M the involution
## of check-c4-aut.gp), so if the degree is 8 there are exactly 8 points and
## |Aut| = 2 on the nose.
##
## WHY MOD p IS ENOUGH.  At a prime of good reduction the specialisation map
## Aut(X_Qbar) -> Aut(X_Fpbar) is injective (Aut(X) embeds in the automorphisms
## of the principally polarised Jacobian, and endomorphisms of an abelian variety
## with good reduction inject under reduction).  Good reduction at p = 5, 7 is
## checked in check-c4-quartic.sage section 5 -- the quartic stays smooth.  So an
## upper bound mod p is an upper bound over Qbar.
##
## RUNTIME.  p = 5 takes about 5 minutes, essentially all of it in the Groebner
## basis behind I.dimension().  p = 7 takes about 16 minutes and gives the same
## answer; it is left switched off here, exactly as E035 ran p <= 13 in the
## repository script and 17, 19, 23 separately.  Set PRIMES = [5, 7] to redo it.
##
## The 15 equations are built by direct monomial expansion rather than through
## Sage's polynomial tower; both routes were run and agree.
import sys, time
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


PRIMES = [5]          # [5, 7] to reproduce the longer run

## the canonical quartic, from check-c4-quartic.sage
QC = {(4,0,0): 27, (3,1,0): -108, (2,2,0): 156, (1,3,0): -96, (0,4,0): 22,
      (3,0,1): -108, (2,1,1): 312, (1,2,1): -276, (0,3,1): 76,
      (2,0,2): 156, (1,1,2): -264, (0,2,2): 90,
      (1,0,3): -192, (0,1,3): 148, (0,0,4): 112}

## the known involution, from check-c4-aut.gp
INV = matrix(ZZ, 3, 3, [1, -2, -2, 0, -1, -2, 0, 0, 1])


def mul(d1, d2, P):
    out = {}
    for k1, v1 in d1.items():
        for k2, v2 in d2.items():
            k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
            out[k] = out.get(k, P.zero()) + v1 * v2
    return out


def aut_equations(P, g):
    """coefficients of Q(Mv) - Q(v), as polynomials in the 9 entries of M"""
    L = [{(1,0,0): g[3*i], (0,1,0): g[3*i+1], (0,0,1): g[3*i+2]} for i in range(3)]
    pw = []
    for i in range(3):
        row = [{(0,0,0): P.one()}]
        for e in range(1, 5):
            row.append(mul(row[e-1], L[i], P))
        pw.append(row)
    total = {}
    for (a, b, c), coef in QC.items():
        term = mul(mul(pw[0][a], pw[1][b], P), pw[2][c], P)
        for kk, vv in term.items():
            total[kk] = total.get(kk, P.zero()) + P.base_ring()(coef) * vv
    for (a, b, c), coef in QC.items():
        total[(a,b,c)] = total.get((a,b,c), P.zero()) - P.base_ring()(coef)
    return [e for e in total.values() if e != 0]


print("=== 0. CALIBRATION: the known solutions must satisfy the equations ===")
for p in PRIMES:
    k = GF(p)
    P = PolynomialRing(k, ['m%d%d' % (i, j) for i in range(3) for j in range(3)],
                       order='degrevlex')
    eqs = aut_equations(P, P.gens())
    ok = True
    npts = 0
    for c in k.list():
        if c == 0 or c**4 != 1:
            continue
        for base in [identity_matrix(ZZ, 3), INV]:
            sub = {P.gen(3*i + j): k(c * base[i][j]) for i in range(3) for j in range(3)}
            npts += 1
            if any(e.subs(sub) != 0 for e in eqs):
                ok = False
    print("  p = %d : the %d matrices c*I, c*M with c^4 = 1 all solve the system : %s"
          % (p, npts, ok))
    check(ok and npts == 8,
          "E037(g): calibration -- the 8 matrices c*I, c*M with c^4 = 1 all solve the system at p = %d" % p)
    if not ok:
        print("  *** CALIBRATION FAILED -- do not trust the degree below. ***")
sys.stdout.flush()

print("")
print("=== 1. the automorphism scheme, degree = 4 * |Aut| ===")
for p in PRIMES:
    k = GF(p)
    P = PolynomialRing(k, ['m%d%d' % (i, j) for i in range(3) for j in range(3)],
                       order='degrevlex')
    eqs = aut_equations(P, P.gens())
    I = P.ideal(eqs)
    print("  p = %d : %d equations in 9 unknowns" % (p, len(eqs)))
    sys.stdout.flush()
    t0 = time.time()
    d = I.dimension()
    print("     dimension = %d   (%.1f s)" % (d, time.time() - t0))
    sys.stdout.flush()
    check(d == 0, "E037(g): the scheme { M : Q(Mv) = Q(v) } is 0-dimensional at p = %d" % p)
    if d != 0:
        print("     *** not finite -- the normalisation argument is wrong ***")
        continue
    t0 = time.time()
    n = I.vector_space_dimension()
    print("     degree    = %d   (%.1f s)" % (n, time.time() - t0))
    check(n == 8,
          "E037(g): that scheme has degree 8 = 4*|Aut| at p = %d, so |Aut(C_4 over Fpbar)| = 2" % p)
    if n == 8:
        print("     8 known points and degree 8 => exactly 8 points, all reduced")
        print("     => |Aut(X over Fpbar)| = 2")
    else:
        print("     => 4*|Aut| = %d, i.e. |Aut| = %s" % (n, n / 4))
    sys.stdout.flush()

print("")
print("=== VERDICT ===")
print("  |Aut(C_4 over Qbar)| <= |Aut(C_4 mod p over Fpbar)| = 2 at a good prime,")
print("  and check-c4-aut.gp exhibits an involution over Q, so")
print("      Aut(C_4) = Z/2,  generated by  [1,-2,-2; 0,-1,-2; 0,0,1].")
print("  Epistemic status [T(CAS)], not [T]: the bound comes from a Groebner-basis")
print("  degree computation, not from a written deduction.  (See E119 for the")
print("  [T(CAS)] label.)")
print("  In particular C_4 has exactly ONE quotient of lower genus: the elliptic")
print("  curve y^2 = x^3 - 36x of check-c4-aut.gp section 4.")

gate("E037")
