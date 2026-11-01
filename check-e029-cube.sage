## check-e029-cube.sage --- E029: u = e_2/e_3 is NOT a cube in Qbar(D~)
##
## This is the step that E029 first recorded as [T(CAS)], settled there by the
## good-reduction computation ell(D_0) = 0 of check-e029-kummer.sage.  It now
## has a paper proof, and this script only certifies the proof's ingredients.
##
## THE PROOF.  Suppose u = h^3 with h in Qbar(D~)^x.  Write iota = (23) in
## S_3 = Gal(Qbar(D~)/Qbar(b)).
##
##  (1) At the six points over b = infinity the order vector is a permutation of
##      (-2,1,1), so ord(u) = ord(e_2) - ord(e_3) takes the values 0,0,-3,-3,3,3
##      and deg div_inf(u) = 6.  Since div(h) = (1/3) div(u), deg h = 2.
##  (2) iota(u) = e_3/e_2 = u^{-1}, so (iota(h) h)^3 = 1.  A function whose cube
##      is 1 is one of the three constants 1, z_3, z_3^2, so iota(h) h = z with
##      z^3 = 1.
##  (3) D~ -> D~/iota = D~_1 is degree 2 with g(D~) = 1 and g(D~_1) = 0, so by
##      Riemann-Hurwitz iota has exactly FOUR fixed points F_1,...,F_4.
##  (4) None of them is one of the six points over b = infinity: that fibre is
##      unramified in a Galois cover of degree 6, so S_3 acts on it simply
##      transitively and no nontrivial element fixes a point of it.  Hence each
##      F_i lies over a finite b, where the e_i -- units over Qbar[b] -- have
##      neither zeros nor poles, and h(F_i) is finite and nonzero.
##  (5) iota fixes F_i and swaps e_2, e_3, so e_2(F_i) = e_3(F_i) and u(F_i) = 1.
##      Thus h(F_i)^3 = 1; and evaluating (2) at F_i gives h(F_i)^2 = z.  So
##          h(F_i) = h(F_i)^3 / h(F_i)^2 = z^{-1}    for EVERY i.
##  (6) A map of degree 2 takes any value at at most 2 points.  Four is too many.
##      Contradiction; u is not a cube.  [QED]
##
## WHAT THIS SCRIPT CHECKS.  Steps (2), (4), (5), (6) are formal.  The two facts
## with content are the order vectors of (1) -- certified by
## check-e029-dtilde.sage -- and the count of four in (3).  Here we verify (3)
## twice: by Riemann-Hurwitz, and by exhibiting the branch points explicitly.
## D~_1 is the s-line, and e_2, e_3 are the roots of Z^2 - (B-x)Z + 1/x over it,
## so the branch points are the places of P^1_s where
##      Delta := (B - x)^2 - 4/x,     x = e_1 = (s^2+3)/12,
##      b = (s-3)^2(s+3) / (6(s^2+3)),   B = 3(b^2+b+1)
## has ODD order.  We also check they lie over b = 0 and b^3 = 4, as they must.
##
## Run with:  PYTHONUNBUFFERED=1 sage check-e029-cube.sage
## Runtime: a few seconds (Sage 10.7).
##
## RESULT: exactly four branch points -- s = -3 (over b = 0) and the three roots
## of the irreducible cubic s^3 - 15s^2 + 27s - 45 (over b^3 = 4).  Four fixed
## points, degree two: the proof closes, and E029(e) is [T], not [T(CAS)].

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

print("=== (0) the parametrisation of D~_1 (from check-e029-dtilde.sage) ===")
Rp.<sp> = QQ[]
Kf.<s> = FunctionField(QQ)
x = (s^2 + 3)/12
b = (s - 3)^2*(s + 3)/(6*(s^2 + 3))
B = 3*(b^2 + b + 1)
## sanity: (x,b) satisfies the minimal polynomial of eta_b
f_at = x^3 - 3*(b^2 + b + 1)*x^2 + 3*(b + 1)*x - 1
print("  x = (s^2+3)/12,   b = (s-3)^2(s+3)/(6(s^2+3))")
print("  x^3 - 3(b^2+b+1)x^2 + 3(b+1)x - 1 =", f_at)
check(f_at == 0, "E029(e): the s-parametrisation lies on D~_1")
sys.stdout.flush()

print()
print("=== (1) Riemann-Hurwitz: iota has exactly four fixed points ===")
print("  D~ -> D~_1 is degree 2, g(D~) = 1, g(D~_1) = 0 (check-e029-dtilde.sage):")
print("      2*1 - 2 = 2*(2*0 - 2) + r   =>   r = 4.")
check(2*1 - 2 == 2*(2*0 - 2) + 4, "E029(e): Riemann-Hurwitz gives r = 4 fixed points for iota")

print()
print("=== (2) the same four, exhibited: the odd-order places of Delta ===")
Delta = (B - x)^2 - 4/x
num = Delta.numerator(); den = Delta.denominator()
print("  Delta = (B-x)^2 - 4/x")
print("    numerator   :", num.factor())
print("    denominator :", den.factor())
sys.stdout.flush()
odd = []
for g_, m in num.factor():
    if m % 2 == 1:
        odd.append(("zero", g_, m, g_.degree()))
for g_, m in den.factor():
    if m % 2 == 1:
        odd.append(("pole", g_, m, g_.degree()))
ord_inf = den.degree() - num.degree()
print("  deg num = %d, deg den = %d, order at s = infinity = %d"
      % (num.degree(), den.degree(), ord_inf))
if ord_inf % 2 == 1:
    odd.append(("s=infinity", None, ord_inf, 1))
print("  places of ODD order (= the branch points of D~ -> D~_1):")
total = 0
for kind, g_, m, d in odd:
    total += d
    print("     %-11s %-30s multiplicity %2d, degree %d"
          % (kind, g_ if g_ is not None else "-", m, d))
print("  total number of geometric branch points :", total)
check(total == 4,
      "E029(e): Delta has exactly four odd-order places, matching Riemann-Hurwitz")
check(ord_inf % 2 == 0, "E029(e): s = infinity is NOT a branch point")
sys.stdout.flush()

print()
print("=== (3) they lie over b = 0 and b^3 = 4, as the branch locus requires ===")
nb = (sp - 3)^2*(sp + 3); db = 6*(sp^2 + 3)
cub = sp^3 - 15*sp^2 + 27*sp - 45
print("  b at s = -3 :", nb(-3)/db(-3))
check(nb(-3)/db(-3) == 0, "E029(e): the branch point s = -3 lies over b = 0")
r = (nb^3 - 4*db^3) % cub
print("  num_b^3 - 4 den_b^3   mod   s^3-15s^2+27s-45  =", r)
check(r == 0, "E029(e): on the cubic branch points, b^3 = 4")
check(cub.is_irreducible(),
      "E029(e): s^3-15s^2+27s-45 is irreducible over Q, so its three roots are "
      "three distinct branch points")
check(len([1 for kind, g_, m, d in odd]) == 2,
      "E029(e): the four branch points are exactly s = -3 and the three roots of "
      "the cubic (two Q-irreducible places)")
sys.stdout.flush()

print()
print("=== (4) deg h = 2, from the order vectors ===")
## ord(u) = ord(e_2) - ord(e_3) over the six boundary points, whose order
## vectors are the six permutations of (-2,1,1).
from itertools import permutations
ords = sorted(p[1] - p[2] for p in permutations((-2, 1, 1)))
print("  ord(e_2) - ord(e_3) over the six boundary points :", ords)
polar = -sum(o for o in ords if o < 0)
print("  deg div_inf(u) =", polar, "   deg h = deg div_inf(u)/3 =", polar // 3)
check(ords == [-3, -3, 0, 0, 3, 3], "E029(e): ord(u) takes the values -3,-3,0,0,3,3")
check(polar == 6 and polar // 3 == 2, "E029(e): deg div_inf(u) = 6, so deg h = 2")

print()
print("=== conclusion ===")
print("  h would take the single value z^{-1} at 4 distinct points while having")
print("  degree 2.  Contradiction: u = e_2/e_3 is NOT a cube in Qbar(D~).")
print("  Hence the Kummer kernel of check-e029-lattice.gp is trivial for every q,")
print("  C~_q is connected, and E029(b),(c),(d),(e),(f) are [T] with no CAS step")
print("  and no restriction on q.")

gate("E029")
