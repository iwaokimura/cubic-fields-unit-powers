# check-index-x.sage --- E049: the index of X/K, and what it does to E047(ii).
#
# THE QUESTION.  E047 Next Step (ii) proposes to make rank P(Q) <= 2
# unconditional by a sharper descent on Jac X / K than E044(d).  Before paying
# for that, decide whether such a descent can possibly help.
#
# THE ARITHMETIC.  E044(d),(e) give dim Sel^2(Jac X/K) = 5 and
# dim Jac X(K)[2] = 2, so from 0 -> J(K)/2J(K) -> Sel^2 -> Sha[2] -> 0,
#
#       rank_K + dim_F2 Sha(Jac X/K)[2] = 5 - 2 = 3.
#
# E046(b) gives rank_Q P >= 2 and hence rank_K = rank_K Jac X >= 2.  So only
# two cases survive:
#
#   (A)  rank_K = 3, dim Sha[2] = 0   -- the E044(g) bound is already SHARP,
#                                        and no refinement of descent over K
#                                        can ever lower it;
#   (B)  rank_K = 2, dim Sha[2] = 1   -- a second descent would prove
#                                        rank_K = 2 and hence rank_Q P = 2.
#
# So E047(ii) is worth paying for only in case (B), i.e. only if dim Sha[2] is
# ODD.  By Tate's theorem, quoted in the introduction of Poonen-Stoll (Ann. of
# Math. 150 (1999), 1109--, p.1110), the Cassels-Tate pairing on Sha is
# ALTERNATING as soon as the polarization arises from a k-rational divisor --
# and Poonen-Stoll's own criterion (p.1111) is that their canonical class c
# vanishes, i.e. the pairing is alternating, if and only if that happens.  For
# J = Jac(X) of a genus-2 curve with a K-RATIONAL POINT P_0, the theta divisor
# is the image of P |-> [P - P_0], which is K-rational, so the hypothesis holds.
# A finite abelian group with a nondegenerate alternating pairing has every
# elementary divisor with even multiplicity, so dim_F2 Sha[2] is then EVEN and
# case (B) is dead.
#
# Hence the whole question reduces to: DOES X HAVE A K-RATIONAL POINT?
# That is what this script decides, and it decides it by exhibiting one.
#
# WHAT THIS SCRIPT DOES.
#   1. Rebuilds X/K from Ritzenthaler-Romagny Thm 1.1 and calibrates it against
#      E039(e) and E044(e).
#   2. Certifies that the construction really produces the Prym, by comparing
#      the mod-p Frobenius trace of Theorem 1.1's curve with E038's
#      a_p(P) = a_p(C_4) - a_p(E) at every usable p < PMAX.
#   3. Exhibits a K-rational point of X and verifies y^2 - S(x) = 0 EXACTLY in
#      K (no p-adics, no floating point).  Also records that the points at
#      infinity are NOT K-rational, so the point found is genuinely affine.
#   4. Prints the consequence for E047 Next Step (ii).
#
# WHAT THIS SCRIPT DOES NOT ESTABLISH.  Section 4's conclusion is NOT [T].  It
# rests on (i) the finiteness of Sha (weakenable to: Sha has 2-corank 0), which
# is unproven, and (ii) dim Sel^2 = 5, which is a single remote evaluation of
# Magma's TwoSelmerGroup on the free calculator, read with a convention that
# E044(f) calibrated on genus-2 curves over Q and then applied over the cubic
# field K -- an unperformed check, flagged [GAP] in E049(j).  Unconditionally
# only 2 <= rank_K <= 3 stands; the equality rank_K = 3 is [C(Sha finite), CAS].
#
# Failure counts are printed explicitly; the run ends with a VERDICT block.

import sys


def say(s=""):
    print(s)
    sys.stdout.flush()


PMAX = 60           # primes for the identity check of section 2 (O(p^2) each)

fails = 0

# ============================================================ 1. X over K

R0 = PolynomialRing(QQ, 't')
t = R0.gen()
Kw = NumberField(t^3 - 4, 'w')
w = Kw.gen()
RK = PolynomialRing(Kw, 'x')
x = RK.gen()


def rr_curve(F, cuberoot, var):
    """Theorem 1.1 of Ritzenthaler-Romagny for
       C_4 : W^4 - 6(T-Z)^2 W^2 + 27 T (T^3 - 4 Z^3) = 0,
    over any field F containing a cube root of 4.  Returns (det A, sextic)."""
    cr = cuberoot
    A = matrix(F, [[27, -27*cr, 0],
                   [6, -12, 6],
                   [1, cr, cr^2]])
    if A.determinant() == 0:
        return A.determinant(), None
    Ai = A.inverse()
    a = Ai[0, 0] + 2*Ai[1, 0]*var + Ai[2, 0]*var^2
    b = Ai[0, 1] + 2*Ai[1, 1]*var + Ai[2, 1]*var^2
    c = Ai[0, 2] + 2*Ai[1, 2]*var + Ai[2, 2]*var^2
    return A.determinant(), b*(b^2 - a*c)


say("=== 1. the genus-2 curve X over K = Q(w), w^3 = 4  (calibration) ===")
say()

detA, S = rr_curve(Kw, w, x)
say("  det A = %s" % detA)
if detA != -324*w^2 - 324*w + 648:
    say("  *** FAIL: det A disagrees with E039(e) ***")
    fails += 1
else:
    say("  ok: agrees with E039(e)")

degs = sorted([g.degree() for g, e in S.factor() for _ in range(e)])
say("  sextic degree %s, discriminant nonzero: %s" % (S.degree(), S.discriminant() != 0))
say("  irreducible factors over K, degrees: %s" % degs)
if S.degree() != 6 or S.discriminant() == 0 or degs != [2, 2, 2]:
    say("  *** FAIL: not the curve of E039(e)/E044(e) ***")
    fails += 1
else:
    say("  ok: three irreducible quadratics -- E044(e) reproduced")
say()


# ================================================ 2. it really is the Prym

def count_C4(p):
    """#C_4(F_p) for C_4 : W^4 - 6(T-Z)^2 W^2 + 27 T (T^3 - 4 Z^3) = 0."""
    F = GF(p)
    tot = 0
    for T in F:                                   # affine patch Z = 1
        for W in F:
            if W^4 - 6*(T-1)^2*W^2 + 27*T*(T^3-4) == 0:
                tot += 1
    RF = PolynomialRing(F, 's')
    s = RF.gen()
    tot += len((s^4 - 6*s^2 + 27).roots())        # Z = 0, T = 1
    return tot


E36 = EllipticCurve([0, 0, 0, -36, 0])

say("=== 2. the construction really produces the Prym (E038/E039 route) ===")
say("    left : trace of Frobenius on Jac X, X from Theorem 1.1 mod p")
say("    right: a_p(P) = a_p(C_4) - a_p(E),  E : y^2 = x^3 - 36x")
say()

n2 = ok2 = 0
for p in prime_range(5, PMAX):
    F = GF(p)
    RF = PolynomialRing(F, 'z')
    z = RF.gen()
    rts = (z^3 - 4).roots()
    if not rts:
        continue
    d, Sp = rr_curve(F, rts[0][0], z)
    if Sp is None or Sp.degree() < 5 or Sp.discriminant() == 0:
        continue
    apX = -HyperellipticCurve(Sp).frobenius_polynomial()[3]
    apP = (p + 1 - count_C4(p)) - E36.ap(p)
    n2 += 1
    if apX == apP:
        ok2 += 1
    say("  p = %3d :  a_p(Jac X) = %4d    a_p(P) = %4d    %s"
        % (p, apX, apP, "ok" if apX == apP else "*** MISMATCH ***"))
say()
say("  %d primes, %d agreements, %d mismatches" % (n2, ok2, n2 - ok2))
if n2 == 0 or n2 != ok2:
    fails += 1
say()


# ================================================ 3. a K-rational point

say("=== 3. does X have a K-rational point? ===")
say()

lc = S.leading_coefficient()
say("  leading coefficient  : %s" % lc)
say("  is it a square in K? : %s" % lc.is_square())
say("  => the two points at infinity are %s"
    % ("K-rational" if lc.is_square() else "NOT K-rational, they are conjugate"))
say()

# the point, and its exact verification
x0 = Kw([0, 0, 1]) / 2                     # w^2/2
y0 = (Kw([0, 0, 1]) - Kw([0, 1, 0])) / 36  # (w^2 - w)/36
say("  candidate point  (x0, y0) = (%s,  %s)" % (x0, y0))
resid = y0^2 - S(x0)
say("  y0^2 - S(x0)     = %s     (exact in K, no p-adics, no floats)" % resid)
if resid != 0:
    say("  *** FAIL: not a point of X ***")
    fails += 1
elif S(x0) == 0:
    say("  *** FAIL: Weierstrass point, y0 = 0 ***")
    fails += 1
else:
    say("  ok: X(K) is NON-EMPTY, and the point is not a Weierstrass point")

# a second, independent one
x1 = Kw([2, 1, 0]) + Kw([0, 0, 1])/2
v1 = S(x1)
say("  a second point at x = %s : S(x) a square in K = %s" % (x1, v1.is_square()))
say()
say("  => index(X/K) = period(X/K) = 1: X has a K-rational divisor class of")
say("     degree 1 = g - 1, so the theta divisor is K-rational and the")
say("     canonical principal polarization arises from a K-rational divisor.")
say()


# ================================================ 4. the consequence

say("=== 4. consequence for E047 Next Step (ii) ===")
say()
say("  Tate (quoted in Poonen-Stoll, p.1110): a polarization arising from a")
say("  k-rational divisor induces an ALTERNATING Cassels-Tate pairing on Sha;")
say("  Poonen-Stoll (p.1111): their canonical c vanishes -- equivalently the")
say("  pairing is alternating -- IF AND ONLY IF that happens.  Section 3 shows")
say("  the hypothesis holds for Jac X / K.")
say()
say("  Assuming Sha(Jac X/K) finite, the pairing is nondegenerate alternating,")
say("  so every elementary divisor occurs with even multiplicity and")
say("  dim_F2 Sha[2] is EVEN.  With E044(d),(e):")
say()
say("      rank_K + dim Sha[2] = dim Sel^2 - dim J(K)[2] = 5 - 2 = 3,")
say("      dim Sha[2] even,  rank_K >= 2  (E046(b))")
say("      ==>  rank_K = 3  and  Sha(Jac X/K)[2] = 0.")
say()
say("  So case (B) is excluded: the E044(g) bound rank_K <= 3 is SHARP, and no")
say("  refinement of descent over K can lower it.  E047 Next Step (ii) is not")
say("  expensive, it is IMPOSSIBLE.")
say()
say("  What remains.  rank_K = rank_Q P + c_P with c_P the rank of the")
say("  rho-isotypic part, so rank_Q P + c_P = 3 with rank_Q P >= 2:")
say("      rank_Q P = 2 and c_P = 1   (quadratic Chabauty's hypothesis holds)")
say("   or rank_Q P = 3 and c_P = 0   (it fails).")
say("  Hence rank_Q P = 2  <=>  c_P = 1  <=>  some class in P(K) has nonzero")
say("  rho-component.  The isotypic search of E046(d) is now the ONLY route --")
say("  and if the answer is 2 then a witnessing class MUST exist, so that")
say("  search is guaranteed to succeed if carried far enough.")
say()

say("=== VERDICT ===")
say("  failures: %d" % fails)
if fails == 0:
    say("  [T(CAS)] X(K) is non-empty: (x,y) = (w^2/2, (w^2-w)/36) exactly.")
    say("  [C(Sha finite), CAS] rank_K Jac X = 3 and Sha(Jac X/K)[2] = 0.")
    say("           NOT [T]: see the header.  Unconditionally only 2 <= rank_K <= 3.")
    say("  ==> E047 Next Step (ii) is impossible; the isotypic route is the only")
    say("      way to make rank_Q P <= 2 unconditional.")
    say("  [GAP] E049(j): the Selmer convention was calibrated over Q, used over K.")
else:
    say("  a step failed; see the *** FAIL *** lines above.")
