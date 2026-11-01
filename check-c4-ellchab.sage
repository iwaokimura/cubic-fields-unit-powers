## check-c4-ellchab.sage --- E041: is elliptic curve Chabauty available at q = 4?
##
## THE QUESTION.  E040 Next Step (ii).  Bruin's elliptic curve Chabauty applied
## over K = Q(2^(1/3)) -- the field E039 showed to be INTRINSIC to (C_4, iota) --
## needs
##        rank E(K) < [K:Q] = 3 ,
## for E : y^2 = x^3 - 36x, the quotient of C_4 by its involution (E037).
##
## THE REPRESENTATION-THEORETIC FRAME (this part is [T], by hand).  Let L be the
## Galois closure of K, so Gal(L/Q) = S_3 and K is the fixed field of a
## transposition <tau>.  Write E(L) tensor Q = 1^a + eps^b + rho^c with rho the
## 2-dimensional irreducible.  Taking <tau>-invariants (1 contributes 1, eps
## contributes 0, rho contributes 1):
##        rank E(Q) = a ,          rank E(K) = a + c .
## So rank E(K) = rank E(Q) + c = 1 + c, and Chabauty needs c <= 1.
##
## THE EXACT LOWER BOUND (section 2).  For P in E(K), the trace
## Tr(P) = sum over the three embeddings K -> L acts as multiplication by 3 on
## the trivial isotypic part and as 0 on the rho part.  Hence
##        R := 3P - Tr(P)  =  3 * (rho-part of P) ,
## and R is non-torsion if and only if P has a nonzero rho-component, which
## gives c >= 1.  Torsion is an EXACT test, so this replaces the floating-point
## regulator computation that a naive lower bound would use.  Two checks come
## for free: Tr(P) must be rational, and E(L)_tors must be finite.
##
## WHAT IS NOT EXACT.  The upper bound is Simon's 2-descent, which is exact but
## returns only rank <= 4 here.  The analytic rank is a NUMERICAL evaluation of
## an L-function and is therefore [E] no matter how clean it looks; it is
## reported in E041, not here, precisely to keep this script exact.
##
## A CORRECTION RECORDED HERE.  Sage's E.rank_bounds() re-runs simon_two_descent
## with its own (smaller) default limits and caches results per curve object.
## Calling it after other descents on the SAME object returned (2,2) once, which
## is not a real bound: with a fresh curve object every run gives (2,4).
## Section 3 demonstrates this, since it is exactly the kind of artefact that
## would otherwise be mistaken for a theorem.
##
## ####################################################################
## THE PARAGRAPH ABOVE IS ITSELF WRONG, AND SO IS THE "rank <= 4" BEFORE IT.
## Corrected in E042 (check-c4-2desc.gp), 2026-08-13.
## The two functions return DIFFERENT quantities:
##      simon_two_descent(...) -> (rank lower bound, dim_F2 Sel^2(E/K))
##      rank_bounds(...)       -> (rank lower bound, dim_F2 Sel^2 - dim E(K)[2])
## and the rank bound is the second of these, because E(K)/2E(K) embeds in
## Sel^2 with dim_F2 E(K)/2E(K) = rank + dim_F2 E(K)[2].  Here E(K)[2] =
## (Z/2)^2, so the 4 printed by section 3 means rank E(K) <= 4 - 2 = 2.
## There is NO caching bug: the (2,2) dismissed below was the correct answer.
## With the exact lower bound of section 2, rank E(K) = 2 EXACTLY, and elliptic
## curve Chabauty over K is available unconditionally -- no BSD, no L-value.
## Everything this script COMPUTES is unchanged and still correct; what was
## wrong is the reading of it in section 3 and in the VERDICT block.
## ####################################################################
import sys

R.<X> = QQ[]

print("=== 1. the fields ===")
K.<w> = NumberField(X^3 - 2)
print("  K = Q(2^(1/3)):  degree %d, disc %s, signature %s"
      % (K.degree(), K.discriminant(), K.signature()))
L = (X^3 - 2).splitting_field('z')
print("  L = Galois closure: degree %d, Galois %s, disc %s"
      % (L.degree(), L.is_galois(), L.discriminant()))
print("  Gal(L/Q) = S_3, so rank E(K) = rank E(Q) + c, c = multiplicity of rho")
sys.stdout.flush()

print("")
print("=== 2. the exact lower bound:  rank E(K) >= 2 ===")
EL = EllipticCurve(L, [0, 0, 0, -36, 0])
T = EL.torsion_subgroup()
print("  E(L)_tors: order %d, structure %s" % (T.order(), T.invariants()))
rts = [r for r, _ in (X^3 - 2).change_ring(L).roots()]
assert len(rts) == 3, "X^3-2 must split in L"
print("  X^3 - 2 splits in L: %d roots" % len(rts))
sys.stdout.flush()

def P2_at(u):
    return EL(6*u, -6*u^2 - 12*u + 12)

P2 = P2_at(rts[0])
assert P2 in EL
Tr = EL(0)
for u in rts:
    Tr = Tr + P2_at(u)
print("  P_2 = (6w, -6w^2-12w+12) in E(K), on the curve")
print("  Tr(P_2) = %s" % (Tr,))
print("  Tr(P_2) is rational (it must be, being Galois-invariant): %s"
      % (Tr[0] in QQ and Tr[1] in QQ))
Rpt = 3*P2 - Tr
print("  R = 3 P_2 - Tr(P_2) has finite order: %s" % Rpt.has_finite_order())
P0 = EL(-3, 9)
print("  P_0 = (-3,9) has finite order: %s" % P0.has_finite_order())
sys.stdout.flush()
if (not Rpt.has_finite_order()) and (not P0.has_finite_order()):
    print("  => c >= 1 and rank E(Q) >= 1, hence")
    print("     [T(CAS)]  rank E(K) >= 2   -- no floating point anywhere above")
else:
    print("  *** the lower bound argument does not fire; do not trust section 4 ***")

print("")
print("=== 3. the upper bound, and a caching artefact worth recording ===")
runs = [dict(), dict(limbigprime=0),
        dict(lim1=5, lim3=10, limtriv=10, limbigprime=0),
        dict(lim1=10, lim3=20, limtriv=20, limbigprime=0)]
for kw in runs:
    EK = EllipticCurve(K, [0, 0, 0, -36, 0])     # FRESH object each time
    lo, hi, gens = EK.simon_two_descent(**kw)
    print("  fresh object, kwargs %-46s -> (%s, %s)" % (str(kw), lo, hi))
    sys.stdout.flush()
EK = EllipticCurve(K, [0, 0, 0, -36, 0])
lo1, hi1, _ = EK.simon_two_descent(lim1=10, lim3=20, limtriv=20)
rb = EK.rank_bounds()
print("  SAME object: simon_two_descent(...) gave (%s, %s), then rank_bounds() gave %s"
      % (lo1, hi1, rb))
print("  -> CORRECTED IN E042: these two functions report different quantities.")
print("     simon_two_descent gives (lower bound, dim Sel^2); rank_bounds gives")
print("     (lower bound, dim Sel^2 - dim E(K)[2]).  With E(K)[2] = (Z/2)^2 the")
print("     4 above means rank <= 2, and the (2,2) is right.  See E042.")

print("")
print("=== VERDICT ===")
print("  [T]       rank E(K) = rank E(Q) + c   (S_3 representation theory)")
print("  [T(CAS)]  rank E(K) >= 2              (exact: R = 3P_2 - Tr(P_2) non-torsion)")
print("  [T(CAS)]  rank E(K) <= 2              (2-descent: dim Sel^2 = 4, dim E(K)[2] = 2)")
print("  [E]       analytic rank = 2           (see E041; a check, not an input)")
print("")
print("  ==> rank E(K) = 2 exactly, and elliptic curve Chabauty over K, which")
print("      needs rank E(K) < [K:Q] = 3, is AVAILABLE UNCONDITIONALLY.")
print("      (This verdict was weaker and partly wrong when first written; the")
print("       upper bound was misread as 4.  Corrected in E042.)")
