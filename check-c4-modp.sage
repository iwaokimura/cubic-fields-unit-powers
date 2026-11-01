## check-c4-modp.sage --- E035: C_4 is not hyperelliptic, decided modulo p.
##
## WHY SAGE.  PARI/GP has no function-field-over-F_p machinery (genus, spaces of
## holomorphic differentials), so this is one of the places where Sage is needed,
## like check-q5-genus.sage and check-qpow-genus.sage.
##
## WHY MOD P.  Over QQ, Singular's normalisation of the degree-8 plane model C_4
## does not terminate: a run was killed after 5h13m on 2026-08-12, and an earlier
## one after 30 min (E026 Next Steps (iii), and the same trap in E021(g)).  Over
## F_p the function field is built by Hess's algorithm and the whole test takes
## seconds for small p.
##
## THE TEST.  Let w1,w2,w3 be a basis of holomorphic differentials of a genus-3
## curve and put u = w2/w1, v = w3/w1, so the canonical map is [1:u:v].  Then
##      rank_{F_p} {1, u, v, u^2, uv, v^2} = 6  <=>  no quadric vanishes on the
##          canonical image  <=>  smooth plane quartic  <=>  NOT hyperelliptic,
##      rank = 5  <=>  the image is a conic  <=>  hyperelliptic.
## Matrix rank is invariant under field extension, so this decides
## hyperellipticity geometrically (over Fbar_p), not merely over F_p.
##
## WHAT IT BUYS.  Genus is preserved and gonality can only DROP under
## specialisation at a prime of good reduction.  So one good prime whose
## reduction is non-hyperelliptic of genus 3 forces C_4/QQ to be
## non-hyperelliptic -- CONDITIONAL on good reduction at that prime, which this
## script does NOT prove (see E035, the flagged [GAP]).
##
## Runtime: ~4 min for PRIMES = [5,7,11,13] (the cost of the differentials grows
## steeply: 2.6s, 9.9s, 63s, 143s).  Raising the bound is expensive and buys
## nothing: a single good prime already gives the conclusion.

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


PRIMES = [5, 7, 11, 13]
DEG = 8              # deg C_4, hence the bound on the number of components


def curve_poly(q, R, A, B):
    p = [R(3), B, B^2 - 2*A]
    for k in range(3, q+1):
        p.append(B*p[k-1] - A*p[k-2] + p[k-3])
    pA = p[q]
    pB = pA.subs({A: B, B: A})
    return R(pB^2 - 3*pB + 9 - 3*pA)


def fp_rank(elts, F, p):
    """F_p-linear rank of a list of function field elements."""
    coeffs = [e.list() for e in elts]
    D = lcm([c.denominator() for co in coeffs for c in co])
    polyrows, N = [], 0
    for co in coeffs:
        pr = []
        for c in co:
            num = c.numerator() * (D // c.denominator())
            pr.append(num)
            N = max(N, num.degree() + 1 if num != 0 else 1)
        polyrows.append(pr)
    M = []
    for pr in polyrows:
        row = []
        for num in pr:
            cl = list(num.list())
            row.extend(cl + [0] * (N - len(cl)))
        M.append(row)
    return matrix(GF(p), M).rank()


def canonical_rank(F, p):
    """(genus, rank of the 6 quadratic monomials in canonical coordinates)."""
    W = F.basis_of_holomorphic_differentials()
    g = len(W)
    if g != 3:
        return g, None
    u, v = W[1] / W[0], W[2] / W[0]
    return g, fp_rank([F.one(), u, v, u*u, u*v, v*v], F, p)


def verdict(rk):
    return {6: "NOT hyperelliptic", 5: "hyperelliptic"}.get(rk, "?? rank %s" % rk)


fail = 0

# --------------------------------------------------- 1. calibrate the test
print("=" * 72)
print("1. CALIBRATION on curves of known type (Commandment X)")
print("=" * 72)

K.<x> = FunctionField(GF(11)); RY.<Y> = K[]
Fh.<y> = K.extension(Y^2 - (x^7 + 1))
g, rk = canonical_rank(Fh, 11)
print("  y^2 = x^7+1 over F_11    (hyperelliptic, genus 3)")
print("     genus %s  rank %s  -> %-18s [expect 3, 5]" % (g, rk, verdict(rk)))
fail += (g, rk) != (3, 5)
check((g, rk) == (3, 5), "E035(a): calibration -- y^2 = x^7+1 over F_11 is hyperelliptic of genus 3, Noether rank 5")

Rq = PolynomialRing(GF(11), ['A', 'B']); Aq, Bq = Rq.gens()
A2q = AffineSpace(2, GF(11), names=['A', 'B'])
g, rk = canonical_rank(Curve(Aq^4 + Bq^4 + 1, A2q).function_field(), 11)
print("  A^4+B^4+1=0 over F_11    (smooth plane quartic, genus 3)")
print("     genus %s  rank %s  -> %-18s [expect 3, 6]" % (g, rk, verdict(rk)))
fail += (g, rk) != (3, 6)
check((g, rk) == (3, 6), "E035(a): calibration -- the smooth plane quartic A^4+B^4+1 over F_11 has Noether rank 6")
sys.stdout.flush()

# ------------------------------------- 2. is the reduction absolutely irreducible?
print()
print("=" * 72)
print("2. C_4 mod p is absolutely irreducible")
print("=" * 72)
print("   (a curve with m geometric components splits into m conjugate factors")
print("    over F_{p^m}, and m <= deg C_4 = %d, so k = 1..%d suffices)" % (DEG, DEG))
for p in PRIMES:
    line = "  p = %2d :" % p
    ok = True
    for k in range(1, DEG + 1):
        Rk = PolynomialRing(GF(p^k, 'w'), ['A', 'B']); Ak, Bk = Rk.gens()
        nf = len([1 for f, e in curve_poly(4, Rk, Ak, Bk).factor() if f.degree() > 0])
        line += " k=%d:%d" % (k, nf)
        ok = ok and nf == 1
    print(line, " ->", "absolutely irreducible" if ok else "SPLITS")
    fail += not ok
    check(ok, "E035(b): C_4 mod %d stays irreducible over F_{p^k} for every k <= deg C_4 = 8" % p)
    sys.stdout.flush()

# ------------------------------------------------ 3. genus and hyperellipticity
print()
print("=" * 72)
print("3. C_4 mod p: genus and hyperellipticity")
print("=" * 72)
print("%5s %8s %7s %6s  %s" % ("p", "constF", "genus", "rank", "verdict"))
for p in PRIMES:
    t0 = time.time()
    R = PolynomialRing(GF(p), ['A', 'B']); A, B = R.gens()
    A2 = AffineSpace(2, GF(p), names=['A', 'B'])
    C = curve_poly(4, R, A, B)
    if C.degree() != DEG:
        print("%5d  degree drops to %d -- bad reduction, skipped" % (p, C.degree()))
        continue
    F = Curve(C, A2).function_field()
    kk = F.exact_constant_field()
    kk = kk[0] if isinstance(kk, tuple) else kk
    g, rk = canonical_rank(F, p)
    print("%5d %8s %7d %6s  %s   (%.1fs)"
          % (p, "F_%d" % kk.cardinality(), g, rk,
             verdict(rk) if g == 3 else "genus != 3", time.time() - t0))
    fail += not (kk.cardinality() == p and g == 3 and rk == 6)
    check(kk.cardinality() == p and g == 3 and rk == 6,
          "E035(b),(c): C_4 mod %d has exact constant field F_p and is a non-hyperelliptic curve of genus 3 (Noether rank 6)" % p)
    sys.stdout.flush()

print()
print("FAILURES:", fail)
check(fail == 0, "E035: the script's own failure counter is 0")

gate("E035")
