## check-e029-kummer.sage --- E029 Phase 2: the Kummer cover C~_q -> D~
##
## E029, Step 2.  With T = {e_1 e_2 e_3 = 1} and [q] : T -> T the
## q-power map (etale of degree q^2 in characteristic 0), set
##       C~_q := [q]^{-1}(D~) = D~ x_{T,[q]} T,
## the (Z/q)^2-Kummer cover of D~ obtained by adjoining e_1^{1/q}, e_2^{1/q}.
## Phase 1 gives g(D~) = 1, six boundary points over b = infinity, and order
## vectors there equal to the permutations of (-2,1,1).  Riemann-Hurwitz then
## predicts
##       chi(C~_q) = q^2 * chi(D~ \ 6 points) + 6q = -6q^2 + 6q,
##       g(C~_q) = 3q^2 - 3q + 1,
## PROVIDED C~_q is connected -- step (2d).
##
## check-e029-lattice.gp reduces (2d) to one q-independent question: is
## u := e_2/e_3 = e_1 e_2^2 a cube in Qbar(D~)?  Equivalently, is the degree-0
## divisor D_0 := (1/3) div(u) principal?  D_0 is 3-torsion in Pic^0(D~), and
## specialisation Pic^0[3] -> Pic^0(D~ mod p)[3] is injective at a prime p != 3
## of good reduction.  So it is enough to show D_0 is NOT principal after
## reduction, where the Riemann-Roch dimension is computable exactly.
##
## Run with:  PYTHONUNBUFFERED=1 sage check-e029-kummer.sage
## Runtime: about three minutes (Sage 10.7); the good-reduction test dominates.
## (Measured at 188s in suite-run-2026-08-19.txt.)
##
## RESULT: (i) g(C~_q) = 3q^2 - 3q + 1 for q = 2,...,9, and the plane model of
## C~_q is irreducible over Q, over Q(zeta_3) and over Q(zeta_9);
## (ii) ell(D_0) = 0 at p = 7, 13, 31, 37, so u is not a cube geometrically,
## the Kummer kernel is trivial, and C~_q is connected for EVERY q >= 1.

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

## The plane model of D~ inside T, from check-e029-dtilde.sage.
def Dtilde(ring, a, c):
    return (a^4*c^4 - 3*a^3*c^3 - a^3*c^2 - a^2*c^3 + 9*a^2*c^2
            - 3*a^2*c - 3*a*c^2 + a^2 - a*c + c^2)

print("=== (1) the genus of C~_q, q = 2,...,9 ===")
R2.<e1, e2> = QQ[]
G = Dtilde(R2, e1, e2)
A2e = AffineSpace(2, QQ, names=['e1', 'e2'])
print("  D~ :", G)
check(Curve(G, A2e).genus() == 1, "E029(2): g(D~) = 1 (as in check-e029-dtilde.sage)")
print("   q   deg C~_q   irreducible/Q   g(C~_q)   3q^2-3q+1")
for q in range(2, 10):
    H = G.subs({e1: e1^q, e2: e2^q})
    fac = H.factor()
    irr = (len(fac) == 1 and fac[0][1] == 1)
    check(irr, "E029(2d): the plane model of C~_%d is irreducible over Q" % q)
    t0 = time.time(); g = Curve(H, A2e).genus(); dt = time.time() - t0
    print("  %2d   %8d   %13s   %7d   %9d   (%.1fs)"
          % (q, H.degree(), irr, g, 3*q^2 - 3*q + 1, dt)); sys.stdout.flush()
    check(g == 3*q^2 - 3*q + 1,
          "E029(2): g(C~_%d) = 3q^2-3q+1 = %d" % (q, 3*q^2 - 3*q + 1))

print()
print("=== (2) geometric irreducibility over the relevant cyclotomic fields ===")
## Irreducibility over Q alone does not exclude a splitting over Qbar.  If the
## Kummer kernel were nontrivial it would be the order-3 group of
## check-e029-lattice.gp, so the components would already be visible over
## Q(zeta_3); we also test Q(zeta_9) for q = 3, 9.
for (name, Fld, qs) in [("Q(zeta_3)", CyclotomicField(3), [2, 3, 6, 9]),
                        ("Q(zeta_9)", CyclotomicField(9), [3, 9])]:
    Rf = PolynomialRing(Fld, 2, names=['f1', 'f2'])
    f1, f2 = Rf.gens()
    Gf = Dtilde(Rf, f1, f2)
    check(len(Gf.factor()) == 1, "E029(2): D~ stays irreducible over %s" % name)
    for q in qs:
        Hf = Gf.subs({f1: f1^q, f2: f2^q})
        fac = Hf.factor()
        irr = (len(fac) == 1 and fac[0][1] == 1)
        print("  q = %d over %-10s : factors %s" % (q, name, [(t.degree(), m) for t, m in fac]))
        sys.stdout.flush()
        check(irr, "E029(2d): C~_%d is irreducible over %s" % (q, name))

print()
print("=== (3) step (2d): u = e_2/e_3 is not a cube in Qbar(D~) ===")
print("  D_0 := (1/3) div(u) is 3-torsion in Pic^0(D~).  Specialisation is")
print("  injective on prime-to-p torsion at a prime p of good reduction, so it")
print("  suffices to show ell(D_0) = 0 after reduction mod one such p.")
print("   p  const.field(D~ mod p)  g   div(u) coefficients   ell(D_0)")
ok_one = False
for p in [7, 13, 31, 37]:
    k = GF(p)
    K = FunctionField(k, names=('x',)); (x,) = K.gens()
    Rp = PolynomialRing(K, names=('T',)); (T,) = Rp.gens()
    Gp = Dtilde(Rp, K(x), T)
    if not Gp.is_irreducible():
        print("  p = %2d : the plane model is reducible over F_p(e_1) -- skipped" % p)
        continue
    L = K.extension(Gp, names=('y',)); (y,) = L.gens()
    ecf = L.exact_constant_field()[0]
    gL = L.genus()
    u = x * y^2                              # e_2/e_3, since e_3 = 1/(e_1 e_2)
    Du = u.divisor()
    supp = Du.support()
    coeffs = [Du.multiplicity(P) for P in supp]
    degs = [P.degree() for P in supp]
    check(gL == 1 and ecf.cardinality() == p,
          "E029(2d): D~ mod %d has genus 1 and exact constant field F_%d (good reduction)" % (p, p))
    check(all(c % 3 == 0 for c in coeffs),
          "E029(2d): div(u) is divisible by 3 at p = %d" % p)
    D0 = sum((c // 3) * P for P, c in zip(supp, coeffs))
    ell = D0.dimension()
    print("  %2d  F_%-19d %d   %-20s %d   (place degrees %s)"
          % (p, ecf.cardinality(), gL, coeffs, ell, degs)); sys.stdout.flush()
    check(D0.degree() == 0, "E029(2d): deg D_0 = 0 at p = %d" % p)
    if check(ell == 0,
             "E029(2d): ell(D_0) = 0 at p = %d, so u is not a cube in Fbar_p(D~ mod p)" % p):
        ok_one = True
check(ok_one, "E029(2d): at least one prime of good reduction gave ell(D_0) = 0")
print("  => D_0 is not principal in characteristic 0 either, so u is not a cube in")
print("     Qbar(D~), the Kummer kernel is trivial for every q, and C~_q is connected.")

print()
print("=== (4) why the S_3-action gives no shortcut ===")
## D~/A_3 is the quadratic subextension Q(b, sqrt(disc)), disc = -27 b^3 (b^3-4);
## with w = 3 b v this is v^2 = -3b(b^3-4) = -3b^4 + 12b.
Rq.<bq, vq> = QQ[]
A2q = AffineSpace(2, QQ, names=['bq', 'vq'])
Fq = vq^2 + 3*bq^4 - 12*bq
gq = Curve(Fq, A2q).genus()
print("  D~/A_3 :", Fq, "  genus =", gq)
check((-3*bq^4 + 12*bq).univariate_polynomial().is_squarefree(),
      "E029(2d): -3b^4+12b is squarefree, so D~/A_3 is a smooth genus-1 quartic model")
check(gq == 1, "E029(2d): g(D~/A_3) = 1")
print("  Riemann-Hurwitz for the degree-3 map D~ -> D~/A_3 :")
print("      2*1-2 = 3*(2*1-2) + R   =>   R = 0,")
print("  so a 3-cycle acts on D~ WITHOUT fixed points, i.e. as a translation by a")
print("  3-torsion point -- and a translation acts trivially on Pic^0.  Likewise a")
print("  transposition is the involution of the degree-2 map D~ -> D~_1 = P^1, so it")
print("  acts on Pic^0 as -1.  Hence the S_3-action puts NO condition on D_0 beyond")
print("  the one that is automatic for the sign character, and the cube test of (3)")
print("  cannot be replaced by representation theory.")
check(2*1 - 2 == 3*(2*gq - 2), "E029(2d): D~ -> D~/A_3 is unramified (R = 0)")

print()
print("=== summary of Phase 2 ===")
print("  (2a) [q] : T -> T is etale of degree q^2 in characteristic 0.")
print("  (2b) inertia at a boundary point P is cyclic of order q / gcd(q, content(v_P)).")
print("  (2c) v_P is a permutation of (-2,1,1), primitive, so the order is exactly q.")
print("  (2d) the Kummer kernel is trivial: lattice index 3 (check-e029-lattice.gp)")
print("       plus ell(D_0) = 0 above.  Hence C~_q is connected and")
print("            g(C~_q) = 3q^2 - 3q + 1   for every q >= 1.")

gate("E029")
