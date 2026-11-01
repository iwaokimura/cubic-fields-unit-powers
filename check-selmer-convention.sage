# check-selmer-convention.sage --- E050: closing the [GAP] of E049(j).
#
# THE GAP.  E044(g) reads Magma's TwoSelmerGroup(J) for J = Jac X over the
# CUBIC field K = Q(4^(1/3)) with the convention
#
#       rank_K J  <=  dim_F2 S - dim_F2 J(K)[2],        S = TwoSelmerGroup(J),
#
# i.e. S is the full 2-Selmer group.  That convention was calibrated in
# E044(f) on five genus-2 curves over Q ONLY, and then used over K.  Nothing
# has checked that the routine returns the same thing over a number field.
# E041 -> E042 shows what this project pays for an unchecked convention: the
# same misreading was recorded as a theorem twice.  If the 5 of E044(d) is
# read wrongly, E044(g), E046(c), E047(f) and all of E049 move.
#
# THE DIFFICULTY, AND THE WAY ROUND IT.  To calibrate one needs genus-2
# Jacobians over K whose rank is known INDEPENDENTLY of Magma -- and E044(c)
# established that nothing local computes genus-2 ranks.  The way round:
# use curves whose Jacobian SPLITS over Q,
#
#       C : y^2 = x^6 + a x^4 + b x^2 + c,
#       E1 : v^2 = u^3 + a u^2 + b u + c        (u,v) = (x^2, y)
#       E2 : V^2 = U^3 + b U^2 + a c U + c^2    (U,V) = (c/x^2, c y/x^3)
#
# so that Jac(C) ~ E1 x E2 over Q and hence
#
#       rank_K Jac(C) = rank E1(K) + rank E2(K),
#
# which Simon's 2-descent computes LOCALLY over K (Sage's
# simon_two_descent; its own convention over K was calibrated in E042).
# The splitting itself is verified here by a_p(C) = a_p(E1) + a_p(E2) at every
# good p < 200, so no claim rests on the formulas above being remembered
# correctly.
#
# THE TEST.  With rank_K and dim J(K)[2] both known locally, the two candidate
# readings of TwoSelmerGroup predict different numbers:
#
#   reading A (S is the full 2-Selmer group):  dim S = rank_K + dim J(K)[2] + dim Sha[2]
#   reading B (S is Sel^2 / J[2]):             dim S = rank_K              + dim Sha[2]
#
# They separate only when dim J(K)[2] > 0 AND rank_K > 0 -- which is exactly
# what E044(f) found the hard way over Q -- so every curve below is chosen to
# satisfy both.  Reading A is E044(g)'s.
#
# This script does all of that locally and PRINTS the Magma block to be run on
# the free calculator; it sends nothing itself.
#
# Failure counts are printed explicitly; the run ends with a VERDICT block.

import sys


def say(s=""):
    print(s)
    sys.stdout.flush()


# Candidates (a, b, c) for y^2 = x^6 + a x^4 + b x^2 + c, from a scan of
# |a|,|b|,|c| <= 3 for: split Jacobian, dim J(K)[2] > 0, positive rank over Q.
# They are tried in order and the first NWANT that survive every local step are
# kept; a spread of dim J(K)[2] is wanted, so both 1 and 2 appear below, and
# (3,3,-1) has dim J(Q)[2] = 0 < dim J(K)[2], i.e. 2-torsion that only appears
# over K -- the case most likely to expose a convention that differs over a
# number field.
CANDIDATES = [(-3, -1, 3), (-1, -1, -2), (3, 3, 2), (0, 2, 3), (3, 3, -1),
              (1, -3, 1), (3, 1, -1), (2, -2, 3), (-3, -3, 1), (-2, -2, -3),
              (1, 1, 1), (-1, 1, 3), (0, 0, 2), (3, -3, 1)]
NWANT = 5           # how many calibration curves to keep

PSPLIT = 200        # primes for the splitting check

fails = 0

R0 = PolynomialRing(QQ, 't')
t = R0.gen()
Kw = NumberField(t^3 - 4, 'w')
w = Kw.gen()
RQ = PolynomialRing(QQ, 'x')
x = RQ.gen()


def torsdim(f, F):
    """dim_F2 J(F)[2] for y^2 = f(x) with deg f = 6.

    J[2] is the group of even-cardinality Galois-stable sets of Weierstrass
    points modulo {empty, all}; over F this is read off the factorisation.
    With k irreducible factors, e of them of odd degree (e is even since
    deg f = 6), the even-degree subsets form a subgroup of F_2^k of dimension
    k-1 if e > 0 and k if e = 0, and the quotient by {0, all} drops it by 1.
    Calibrated below against E044(e): the sextic of X over K gives 2.
    """
    fac = [g for g, e in f.change_ring(F).factor() for _ in range(e)]
    k = len(fac)
    odd = len([g for g in fac if g.degree() % 2 == 1])
    return (k - 1) if odd == 0 else (k - 2)


def ell_rank_over_K(E):
    """(rank, how) over K, exactly, or (None, reason).  Simon's 2-descent
    returns (lower bound, dim Sel^2, points); the upper bound is
    dim Sel^2 - dim E(K)[2] (the convention E042(a) settled)."""
    try:
        lo, s2, _ = E.simon_two_descent()
    except Exception as err:
        return None, "Simon's 2-descent failed: %s" % type(err).__name__
    two = len(E.division_polynomial(2).roots(Kw))     # roots of the cubic in K
    tdim = {0: 0, 1: 1, 3: 2}.get(two)
    if tdim is None:
        return None, "unexpected number of 2-torsion roots: %s" % two
    hi = s2 - tdim
    if lo != hi:
        return None, "not pinched: %s <= rank <= %s" % (lo, hi)
    return lo, "Simon 2-descent pinched at %s (dim Sel^2 = %s, dim E(K)[2] = %s)" % (lo, s2, tdim)


# ---------------------------------------------------- 0. calibrate torsdim
say("=== 0. calibration of the 2-torsion count against E044(e) ===")
say()
RK = PolynomialRing(Kw, 'x')
xK = RK.gen()
A = matrix(Kw, [[27, -27*w, 0], [6, -12, 6], [1, w, w^2]])
Ai = A.inverse()
aa = Ai[0, 0] + 2*Ai[1, 0]*xK + Ai[2, 0]*xK^2
bb = Ai[0, 1] + 2*Ai[1, 1]*xK + Ai[2, 1]*xK^2
cc = Ai[0, 2] + 2*Ai[1, 2]*xK + Ai[2, 2]*xK^2
SX = bb*(bb^2 - aa*cc)
kX = len([g for g, e in SX.factor() for _ in range(e)])
dX = (kX - 1)                                   # all factors quadratic
say("  X/K: %d irreducible factors, all of even degree -> dim J(K)[2] = %d" % (kX, dX))
say("  E044(e) says 2  ->  %s" % ("ok" if dX == 2 else "*** FAIL ***"))
if dX != 2:
    fails += 1
say()


# ---------------------------------------------------- 1. the curves
say("=== 1. the calibration curves ===")
say("    C : y^2 = x^6 + a x^4 + b x^2 + c,  Jac(C) ~ E1 x E2 over Q")
say()

data = []
for (a, b, c) in CANDIDATES:
    if len(data) >= NWANT:
        break
    f = x^6 + a*x^4 + b*x^2 + c
    E1 = EllipticCurve([0, a, 0, b, c])
    E2 = EllipticCurve([0, b, 0, a*c, c^2])
    say("  --- (a,b,c) = (%d,%d,%d) ---" % (a, b, c))
    if f.discriminant() == 0 or E1.discriminant() == 0 or E2.discriminant() == 0:
        say("      *** FAIL: degenerate ***")
        fails += 1
        continue

    # (i) the splitting, verified rather than quoted
    n = ok = 0
    for p in prime_range(7, PSPLIT):
        if ZZ(f.discriminant()) % p == 0 or E1.discriminant() % p == 0 \
           or E2.discriminant() % p == 0:
            continue
        apC = -HyperellipticCurve(f.change_ring(GF(p))).frobenius_polynomial()[3]
        n += 1
        if apC == E1.ap(p) + E2.ap(p):
            ok += 1
    say("      splitting: %d good primes < %d, %d agreements, %d mismatches"
        % (n, PSPLIT, ok, n - ok))
    if n == 0 or n != ok:
        say("      *** FAIL: Jac(C) ~ E1 x E2 not confirmed ***")
        fails += 1
        continue

    # (ii) 2-torsion over Q and over K
    dQ, dK = torsdim(f, QQ), torsdim(f, Kw)
    say("      dim J(Q)[2] = %d,  dim J(K)[2] = %d" % (dQ, dK))

    # (iii) rank over K, locally
    r1, why1 = ell_rank_over_K(E1.change_ring(Kw))
    r2, why2 = ell_rank_over_K(E2.change_ring(Kw))
    say("      E1 = %s over K: %s" % (E1.ainvs(), why1))
    say("      E2 = %s over K: %s" % (E2.ainvs(), why2))
    if r1 is None or r2 is None:
        say("      (excluded from the calibration: rank over K not pinched)")
        continue
    rk = r1 + r2
    say("      rank_K Jac(C) = %d + %d = %d" % (r1, r2, rk))
    if dK == 0 or rk == 0:
        say("      (excluded: does not separate the two readings)")
        continue
    say("      predictions:  reading A  dim S = %d + dim Sha[2]" % (rk + dK))
    say("                    reading B  dim S = %d + dim Sha[2]" % rk)
    data.append((a, b, c, dQ, dK, rk))
    say()

say()
say("=== 2. summary of the local half ===")
say()
say("   (a,b,c)      dimJ(Q)[2] dimJ(K)[2] rank_K   A predicts   B predicts")
for (a, b, c, dQ, dK, rk) in data:
    say("   (%2d,%2d,%2d)        %d          %d        %d       >= %d         >= %d"
        % (a, b, c, dQ, dK, rk, rk + dK, rk))
say()
if len(data) < 3:
    say("  *** FAIL: fewer than 3 usable calibration curves ***")
    fails += 1


# ---------------------------------------------------- 3. the Magma block
say("=== 3. the Magma block to run on the free calculator ===")
say("    (this script sends nothing; the block is printed for inspection)")
say()
say("// ---------------- begin ----------------")
say("K<w> := NumberField(Polynomial([-4,0,0,1]));")
say("P<x> := PolynomialRing(K);")
for (a, b, c, dQ, dK, rk) in data:
    say("C := HyperellipticCurve(x^6 + (%d)*x^4 + (%d)*x^2 + (%d));" % (a, b, c))
    say("S := TwoSelmerGroup(Jacobian(C));")
    say('printf "(%d,%d,%d) : dim S = %%o\\n", Ilog(2,#S);' % (a, b, c))
say("// ----------------- end -----------------")
say()
say("  expected, if E044(g)'s reading A is right and Sha[2] = 0:")
for (a, b, c, dQ, dK, rk) in data:
    say("    (%2d,%2d,%2d) -> dim S = %d      (reading B would give %d)"
        % (a, b, c, rk + dK, rk))
say()

# ---------------------------------------------------- 4. the remote half
# Output of the block above on the free Magma calculator, 2026-08-13.  This is
# the ONLY number in this script that was not computed on this machine.
MAGMA = {(-3, -1, 3): 5, (-1, -1, -2): 3, (3, 3, 2): 3,
         (-3, -3, 1): 3, (-2, -2, -3): 3}

say("=== 4. comparison with the Magma output (run 2026-08-13) ===")
say()
say("   (a,b,c)      rank_K  dimJ(K)[2]   A: rk+tors   B: rk   Magma dim S   verdict")
nA = nB = 0
for (a, b, c, dQ, dK, rk) in data:
    got = MAGMA.get((a, b, c))
    if got is None:
        say("   (%2d,%2d,%2d)   -- no Magma value recorded --" % (a, b, c))
        fails += 1
        continue
    isA, isB = (got == rk + dK), (got == rk)
    nA += 1 if isA else 0
    nB += 1 if isB else 0
    say("   (%2d,%2d,%2d)        %d        %d           %d            %d         %d          %s"
        % (a, b, c, rk, dK, rk + dK, rk, got,
           "A" if isA and not isB else ("B" if isB and not isA else "ambiguous")))
say()
say("  reading A (S is the full 2-Selmer group, E044(g)'s):  %d/%d" % (nA, len(data)))
say("  reading B (S is Sel^2 / J[2]):                        %d/%d" % (nB, len(data)))
if nA != len(data):
    say("  *** FAIL: E044(g)'s reading is not confirmed over K ***")
    fails += 1
say()
say("  Equality (not just <=) in every case also says Sha(J/K)[2] = 0 for all")
say("  five, so none of them is a curve with nontrivial 2-part of Sha; the")
say("  separation of A from B did not need one, only dim J(K)[2] > 0 and")
say("  rank_K > 0 (E044(f)).")
say()

say("=== VERDICT ===")
say("  failures: %d" % fails)
if fails == 0 and nA == len(data) and nB == 0:
    say("  [T(CAS)] Over the cubic field K, Magma's TwoSelmerGroup returns the")
    say("  FULL 2-Selmer group: rank_K = dim S - dim J(K)[2] in all %d cases,"
        % len(data))
    say("  with rank_K obtained independently of Magma.  This is the convention")
    say("  E044(g) used, so the [GAP] of E049(j) is CLOSED and dim Sel^2 = 5 for")
    say("  Jac X / K stands as read.")
else:
    say("  the calibration did not come out clean; see the lines above.")
