## check-e029-descent.sage --- E029 Phase 3: the S_3 descent C~_q -> C_q
##
## E029, Step 3.  S_3 acts on T by permuting (e_1,e_2,e_3), the
## quotient is the adjoint quotient A^2_{A,B} (coefficients of X^3-BX^2+AX-1),
## and C_q = Phi_q^{-1}(D) is the image of C~_q = [q]^{-1}(D~).  The claim is
##       C~_q -> C_q  is of degree 6 with total ramification R = 12q,
## whence Riemann-Hurwitz turns g(C~_q) = 3q^2-3q+1 (Phase 2) into
##       2(3q^2-3q+1) - 2 = 6(2 g(C_q) - 2) + 12q,   g(C_q) = (q-1)(q-2)/2.
##
## The hand proof of R = 12q:  a point of C~_q = D~ x_{T,[q]} T is a pair
## (Ptilde, t); a transposition (ij) fixes it iff it fixes Ptilde and t_i = t_j.
## The points of D~ with nontrivial stabiliser are the 12 ramification points of
## D~ -> P^1_b (three over each of b = 0 and the three b with b^3 = 4, each with
## e = 2 and stabiliser a transposition -- check-e029-dtilde.sage).  Over each,
## the fibre is a T[q]-torsor, and t_i = t_j cuts out exactly q of its q^2
## points (fix t_i = t_j = z, then t_k = z^{-2}, and z ranges over mu_q).  So
## there are 12q points with stabiliser of order 2, each of ramification index
## 2, and no point has a larger stabiliser (the stabiliser of (Ptilde,t) is
## contained in that of Ptilde, of order at most 2).  Hence R = 12q.
##
## This script checks the CONCLUSION end to end: it recomputes g(C_q) from the
## defining polynomial and verifies the Riemann-Hurwitz identity with R = 12q,
## together with the reducedness of the defining polynomial that makes
## C~_q -> C_q a degree-6 map.
##
## Run with:  PYTHONUNBUFFERED=1 sage check-e029-descent.sage
## Runtime: about a minute (Sage 10.7).
##
## RESULT: for q = 2,...,10 the polynomial is squarefree and irreducible,
## g(C_q) = (q-1)(q-2)/2, and 2g(C~_q)-2 = 6(2g(C_q)-2) + 12q holds exactly.

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

R2.<A, B> = QQ[]
A2 = AffineSpace(2, QQ, names=['A', 'B'])

def pq(q):
    """p_q(A,B) = sum e_i^q for the roots of X^3 - B X^2 + A X - 1."""
    v = [R2(3), B, B^2 - 2*A]
    for k in range(3, q + 1):
        v.append(B*v[k-1] - A*v[k-2] + v[k-3])
    return v[q]

def swap(f):
    return f.subs({A: B, B: A})

print("=== (0) Newton's identities: p_q(A,B) = sum e_i^q, p_q(B,A) = sum (e_i e_j)^q ===")
## sanity check against explicit roots over a finite field
k = GF(10007)
Rk.<X> = k[]
bad = 0
for (a0, b0) in [(3, 5), (11, 2), (100, 7)]:
    f = X^3 - b0*X^2 + a0*X - 1
    rts = [r for r, m in f.roots(GF(10007^6)) for _ in range(m)]
    if len(rts) != 3:
        continue
    for q in [2, 3, 5, 7]:
        s1 = sum(r^q for r in rts)
        s2 = sum(rts[i]^q * rts[j]^q for i in range(3) for j in range(i+1, 3))
        if k(pq(q).subs({A: a0, B: b0})) != s1 or k(swap(pq(q)).subs({A: a0, B: b0})) != s2:
            bad += 1
print("  failures over F_10007^6 :", bad)
check(bad == 0, "E029(3): p_q(A,B) and p_q(B,A) are the q-th power sums of the e_i and of the e_i e_j")
sys.stdout.flush()

print()
print("=== (1) C_q, its reducedness, and the Riemann-Hurwitz identity ===")
print("   q  deg   squarefree  irreducible   g(C_q)  (q-1)(q-2)/2   g(C~_q)   R = 12q   RH")
allok = True
for q in range(2, 11):
    P = pq(q)
    F = swap(P)^2 - 3*swap(P) + 9 - 3*P
    fac = F.factor()
    sqfree = all(m == 1 for t, m in fac)
    irred = (len(fac) == 1 and fac[0][1] == 1)
    t0 = time.time(); g = Curve(F, A2).genus(); dt = time.time() - t0
    gt = 3*q^2 - 3*q + 1
    pred = (q-1)*(q-2)//2
    rh = (2*gt - 2 == 6*(2*g - 2) + 12*q)
    print("  %2d %4d   %10s   %11s  %6d  %12d  %8d  %8d   %s   (%.1fs)"
          % (q, F.degree(), sqfree, irred, g, pred, gt, 12*q, rh, dt)); sys.stdout.flush()
    check(F.degree() == 2*q, "E029(3): deg C_%d = 2q = %d" % (q, 2*q))
    check(sqfree, "E029(3): the defining polynomial of C_%d is squarefree" % q)
    check(irred, "E029(3): C_%d is irreducible over Q" % q)
    check(g == pred, "E029(3): g(C_%d) = (q-1)(q-2)/2 = %d" % (q, pred))
    check(rh, "E029(3): Riemann-Hurwitz for C~_%d -> C_%d holds with R = 12q" % (q, q))
    allok = allok and rh

print()
print("=== (2) deg(C_q -> A^1_b) = q^2, so deg(C~_q -> C_q) = 6 ===")
## b is recovered from A_q = p_q(B,A) by A_q = 3(b+1); eliminate B.
print("   q   deg_A Res_B(F_q, p_q(B,A) - 3(b_0+1))    q^2")
b0 = 7919
for q in range(2, 8):
    P = pq(q)
    F = swap(P)^2 - 3*swap(P) + 9 - 3*P
    Res = F.resultant(swap(P) - 3*(b0 + 1), B)
    d = Res.degree(A)
    print("  %2d %38d %6d" % (q, d, q^2)); sys.stdout.flush()
    check(d == q^2, "E029(3): deg(C_%d -> A^1_b) = q^2 = %d" % (q, q^2))
print("  deg(C~_q -> A^1_b) = 6 q^2 (Phase 2), so deg(C~_q -> C_q) = 6.")

print()
print("=== summary of Phase 3 ===")
print("  The 12 points of D~ with nontrivial stabiliser each carry exactly q")
print("  points of C~_q fixed by the same transposition, each with e = 2:")
print("       R = 12 * q * (2-1) = 12q,")
print("  and no stabiliser is larger than order 2.  Riemann-Hurwitz then gives")
print("       g(C_q) = (q-1)(q-2)/2   for every q >= 1,")
print("  verified above for q = 2,...,10.")

gate("E029")
