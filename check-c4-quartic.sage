## check-c4-quartic.sage --- E037: the canonical model of C_4 OVER Q, by adjoints.
##
## THE POINT.  E035 spent 5h13m failing to normalise C_4 over Q and concluded the
## characteristic-0 route was dead.  That conclusion was too broad: what is dead
## is Singular's normal(), not characteristic 0.  The ADJOINT IDEAL (Boehm-Decker-
## Laplagne-Pfister, Singular's paraplanecurves.lib) is a different algorithm and
## returns in HALF A SECOND on the same curve.  Since the degree-(d-3) part of the
## adjoint ideal of a degree-d plane curve cuts out the canonical system, that is
## all that is needed: the canonical map, and with it the hyperelliptic question,
## decided in characteristic 0 with no reduction mod p at all.
##
## WHAT THIS GIVES, INDEPENDENTLY OF E035 AND E036.
##   deg-2 relations among the adjoints, modulo F  ->  dim 0  =>  NOT hyperelliptic
##                                                     (dim 1 would be the conic,
##                                                      i.e. the hyperelliptic case)
##   deg-4 relations                              ->  dim 1  =>  the canonical model
##                                                     is that plane quartic
## and the quartic is then checked to be smooth.  So "C_4/Q is not hyperelliptic"
## is [T] by a second, characteristic-0 route, and "C_4 has good reduction at p"
## reduces to "the quartic stays smooth mod p", which is a one-line check.
##
## Runtime: a few seconds.  Sage is needed only for Singular's adjointIdeal; the
## consequences (the involution, the quotient elliptic curve) are in
## check-c4-aut.gp, in PARI/GP.
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


def curve_poly(q, R, A, B):
    p = [R(3), B, B^2 - 2*A]
    for k in range(3, q+1):
        p.append(B*p[k-1] - A*p[k-2] + p[k-3])
    pA = p[q]
    pB = pA.subs({A: B, B: A})
    return R(pB^2 - 3*pB + 9 - 3*pA)

print("=== 1. C_4 and its homogenisation ===")
R2 = PolynomialRing(QQ, ['A', 'B']); A, B = R2.gens()
C = curve_poly(4, R2, A, B)
DEG = C.degree()
S = PolynomialRing(QQ, ['x', 'y', 'z']); x, y, z = S.gens()
F = sum(c * x^e[0] * y^e[1] * z^(DEG - e[0] - e[1])
        for (e, c) in zip(C.exponents(), C.coefficients()))
print("  deg C_4 = %d,  p_a = %d" % (DEG, (DEG-1)*(DEG-2)//2))
print("  F =", F)
sys.stdout.flush()

print("")
print("=== 2. the adjoint ideal over Q ===")
singular.lib("paraplanecurves.lib")
singular.setring(singular.ring(0, '(x,y,z)', 'dp'))
t0 = time.time()
I = singular.adjointIdeal(singular(F))
print("  adjointIdeal returned in %.2f s   <-- against 5h13m for normal() in E035"
      % (time.time() - t0))
gens = [S(str(I[i])) for i in range(1, int(I.size()) + 1)]
print("  generator degrees:", [g.degree() for g in gens])
G = [g for g in gens if g.degree() == DEG - 3]
print("  degree-%d adjoints: %d   (must equal the genus, 3)" % (DEG - 3, len(G)))
check(len(G) == 3, "E037(a): adjointIdeal gives exactly 3 adjoints of degree 5, and 3 = g")
for g in G:
    print("     ", g)
assert len(G) == 3, "expected exactly 3 adjoints of degree d-3"
sys.stdout.flush()

Fid = S.ideal(F)
T = PolynomialRing(QQ, ['X', 'Y', 'Z']); X, Y, Z = T.gens()

def relations(k):
    """basis of the degree-k forms Q with Q(g1,g2,g3) == 0 in S/(F)"""
    mons = [X^a * Y^b * Z^(k - a - b)
            for a in range(k + 1) for b in range(k + 1 - a)]
    imgs = [Fid.reduce(G[0]^m.degree(X) * G[1]^m.degree(Y) * G[2]^m.degree(Z))
            for m in mons]
    allm = sorted(set(sum([list(p.monomials()) for p in imgs], [])))
    idx = {mm: i for i, mm in enumerate(allm)}
    M = matrix(QQ, len(mons), len(allm))
    for r, p in enumerate(imgs):
        for cc, mm in zip(p.coefficients(), p.monomials()):
            M[r, idx[mm]] = cc
    return mons, M.kernel()

print("")
print("=== 3. the hyperelliptic question, IN CHARACTERISTIC 0 ===")
mons2, K2 = relations(2)
print("  degree 2: relation space has dimension %d" % K2.dimension())
print("     dim 1 would be a conic through the canonical image  = hyperelliptic")
print("     dim 0 means no conic                                = NOT hyperelliptic")
check(K2.dimension() == 0,
      "E037(b): the degree-2 relation space has dimension 0 -- no conic through the canonical image, so C_4/Q is NOT hyperelliptic, in characteristic 0")
print("  => C_4/Q is NOT hyperelliptic." if K2.dimension() == 0
      else "  => C_4/Q IS hyperelliptic (contradicts E035!)")
sys.stdout.flush()

print("")
print("=== 4. the canonical model ===")
mons4, K4 = relations(4)
print("  degree 4: relation space has dimension %d  (expect 1)" % K4.dimension())
v = K4.basis()[0]
Qc = sum(QQ(v[i]) * mons4[i] for i in range(len(mons4)))
Qc = Qc * lcm([c.denominator() for c in Qc.coefficients()])
Qc = Qc / gcd([ZZ(c) for c in Qc.coefficients()])
print("  QUARTIC Q =", Qc)
J = T.ideal([Qc.derivative(v) for v in T.gens()])
print("  singular locus of the affine cone has dimension %d" % J.dimension())
print("     0 = only the origin = the projective quartic is SMOOTH")
check(K4.dimension() == 1 and J.dimension() == 0,
      "E037(c): the degree-4 relation space is 1-dimensional and the quartic Q is smooth")
print("  => the canonical model of C_4 is a smooth plane quartic, so g = 3.")
sys.stdout.flush()

print("")
print("=== 5. good reduction, read off the quartic ===")
print("  the canonical model is smooth <=> good reduction, so this is one line:")
bad, good = [], []
for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
    Tp = PolynomialRing(GF(p), ['X', 'Y', 'Z'])
    Qp = Tp(Qc)
    d = Tp.ideal([Qp.derivative(u) for u in Tp.gens()]).dimension()
    (good if d == 0 else bad).append(p)
print("  smooth (good reduction) :", good)
print("  singular (bad)          :", bad)
check(bad == [2, 3] and 5 in good,
      "E037(d): Q mod p is smooth for every tested p except 2 and 3 -- good reduction at 5, i.e. the whole of E036 in one line")
print("  p = 5 is good, which re-derives E036's main result in one line.")

gate("E037")
