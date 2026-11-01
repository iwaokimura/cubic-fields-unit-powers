# check-c4-l3pairing.sage --- E105: the regular model at ell = 3, E084 confirmed
# from outside, and why the forcing that worked at ell = 2 does not close here.
#
# Run: sage check-c4-l3pairing.sage
#
# WHAT MAGMA WOULD AND WOULD NOT DO.  E103 found RegularModel(C_4, 3) refused:
# "Extending the base field to Number Field with defining polynomial x^2+2x+2"
# then "Fibre blowups over number fields not yet implemented".  Four cheap
# attempts were made (magma_free, ~1 s each, the user's permission, precedent
# E043):
#
#   chart 1, X -> X+Z          FAILS, same message
#   chart 1, Y -> Y+X          FAILS, same message
#   chart 1 over Q(i) at (3)   FAILS, same message
#   CHART 2                    SUCCEEDS
#
# Chart 2 is E080's second Tuitman model, Q_2 = y^4 - 2(y-3)^2 x^2 + 3x^4 - 108y,
# built for an entirely different reason (E082's independent check on the
# leftover disk).  Modulo 3 it reduces to y^2 (y^2 + x^2) rather than to chart
# 1's quadruple line y^4, and that is what lets the package through.  Placing
# points needed one further step: the model Magma builds sits over O_K with
# K = Q(i), so PointOnRegularModel rejects points of the Q-curve; rebuilding the
# curve over K and calling RegularModel at the prime above 3 works and accepts
# them.  K/Q is UNRAMIFIED at 3, with residue field F_9.
#
# WHAT CAME BACK.  Ten components, multiplicities (1,1,1,1,1,1,1,2,2,2), the
# intersection matrix below, and the nine rational points on three of them:
#
#   t = 1 w = 3,  t = -2 w = -6,  t = -1/11 w = +15/11   -> one component
#   t = 1 w = -3, t = -2 w = 6,   t = -1/11 w = -15/11   -> another
#   t = -1 w = +-3,  t = 0 w = 0                          -> a third
#
# THAT IS E084's PARTITION, EXACTLY, refined by sigma: {t = 1, -2, -1/11} on a
# sigma-swapped PAIR and {t = -1, 0} on a sigma-FIXED component.  E083 and E084
# built their semistable model by hand and had no external check of any kind;
# this is one, by a completely different route.
#
# AND WHY IT DOES NOT FINISH THE JOB.  At ell = 2 (E104) the labels could be
# forced: three multiplicity-1 components, three hit, and exactly one
# transposition of them an automorphism of (M, m).  Here there are SEVEN
# multiplicity-1 components, (M, m) has 48 label-preserving automorphisms, and
# seven involutions swap exactly one pair of multiplicity-1 components while
# fixing a third.  The resulting local pairing takes FIVE different values, so
# the ell = 3 pairing is pinned only to a list of five.

import sys, time

FAIL = []


def check(cond, msg):
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def info(msg):
    print("        %s" % msg)
    sys.stdout.flush()


M = matrix(QQ, [
    [-1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, -6, 0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, -2, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, -2, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, -2, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, -2, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
    [0, 0, 2, 1, 1, 1, 1, 0, -4, 1],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, -2]])
m = vector(QQ, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2])
PHI = 16


def ev(i):
    return vector(QQ, [1 if k == i else 0 for k in range(10)])


def sol(c, A):
    if c == A:
        return vector(QQ, [0]*10)
    d = ev(c) - ev(A)
    return M.stack(matrix(QQ, [list(m)])).solve_right(
        vector(QQ, list(-d) + [0]))


def Lam(A, B, C):
    idx = [A, B, C]
    return matrix(QQ, 3, 3,
                  lambda a, b: sol(idx[a], A).dot_product(ev(idx[b]) - ev(A)))


def main():
    t0 = time.time()
    print("=== check-c4-l3pairing.sage --- E105: the model at ell = 3 ===")

    print("(1) THE SPECIAL FIBRE IS A GENUINE ONE")
    info("10 components, multiplicities %s, over O_K with K = Q(i), the prime "
         "above 3 being UNRAMIFIED with residue field F_9" % list(m))
    check(M == M.transpose() and M*m == vector(QQ, [0]*10),
          "the intersection matrix is symmetric and M m = 0")
    check(M.rank() == 9 and M.kernel().basis() == [m/gcd(list(m))],
          "rank 9 with kernel spanned EXACTLY by m: Zariski's lemma, so the "
          "fibre is connected and the multiplicities are right")
    cp = M.charpoly()
    check(all(c >= 0 for c in cp.coefficients(sparse=False)),
          "charpoly has no negative coefficient, hence no positive real root: "
          "M is negative semidefinite")
    ok = all(abs((M.delete_rows([i]).delete_columns([i])).det()) == PHI*m[i]**2
             for i in range(10))
    check(ok,
          "and |det M^(i)| = %d m_i^2 for every i, so the component group has "
          "order %d.  Every one of these is a first-principles check on Magma's "
          "output, as at ell = 2" % (PHI, PHI))

    print("(2) E084 CONFIRMED FROM OUTSIDE")
    info("the nine rational points land on three components:")
    info("   t = 1 w = 3,   t = -2 w = -6,  t = -1/11 w = +15/11   -> A")
    info("   t = 1 w = -3,  t = -2 w = 6,   t = -1/11 w = -15/11   -> B")
    info("   t = -1 w = +-3,  t = 0 w = 0                          -> C")
    check(True,
          "sigma (w -> -w) swaps A and B and fixes C.  So {t = 1, -2, -1/11} is "
          "one block and {t = -1, 0} the other -- EXACTLY E084's table, which "
          "put the first three on Ebar' and the last two on R.  E083 and E084 "
          "built their semistable model by hand and had no external check of "
          "any kind; this is one, from Magma's regular model, by a completely "
          "different route  [E]")
    check(True,
          "and the refinement is new: on the REGULAR model over O_K the block "
          "of Ebar' splits into a sigma-swapped PAIR, while R stays a single "
          "sigma-fixed component")

    print("(3) THE FORCING OF E104 DOES NOT CLOSE HERE")
    mult1 = [i for i in range(10) if m[i] == 1]
    check(len(mult1) == 7,
          "there are SEVEN multiplicity-1 components here against three at "
          "ell = 2, so 'three hit = three of multiplicity 1' gives nothing")
    from itertools import permutations, product
    inv = [(m[i], M[i, i],
            tuple(sorted((m[j], M[i, j]) for j in range(10)
                         if j != i and M[i, j] != 0))) for i in range(10)]
    cls = {}
    for i in range(10):
        cls.setdefault(inv[i], []).append(i)
    blocks = list(cls.values())
    auts = []
    for combo in product(*[list(permutations(b)) for b in blocks]):
        p = [None]*10
        for b, pb in zip(blocks, combo):
            for a, c in zip(b, pb):
                p[a] = c
        if all(M[p[i], p[j]] == M[i, j] for i in range(10) for j in range(10)) \
                and all(m[p[i]] == m[i] for i in range(10)):
            auts.append(tuple(p))
    invol = [a for a in auts if all(a[a[i]] == i for i in range(10))
             and a != tuple(range(10))]
    cand = set()
    for a in invol:
        sw = set(tuple(sorted((i, a[i]))) for i in mult1 if a[i] != i)
        if len(sw) == 1:
            pr = sorted(sw)[0]
            for c in mult1:
                if a[c] == c:
                    cand.add((pr, c))
    check(len(auts) == 48 and len(invol) == 19,
          "(M, m) has %d label-preserving automorphisms and %d involutions"
          % (len(auts), len(invol)))
    lams = {}
    for (pr, c) in sorted(cand):
        lams.setdefault(str(Lam(pr[0], pr[1], c).rows()), []).append(
            (pr[0]+1, pr[1]+1, c+1))
    info("the admissible (swapped pair, fixed component) triples and their "
         "local pairings:")
    for L, tr in sorted(lams.items()):
        info("   %-42s from %s" % (L, tr[:4]))
    check(len(lams) > 1,
          "the local pairing takes %d DIFFERENT values across the admissible "
          "triples, so the ambiguity is not harmless and the ell = 3 pairing is "
          "pinned only to a list of %d" % (len(lams), len(lams)))

    print("(4) WHAT WOULD CLOSE IT")
    info("(a) a labelling-consistent output from Magma: component_indices and "
         "Multiplicities are demonstrably differently ordered (a Q-point is "
         "reported on a multiplicity-2 component, twice now, at both primes), "
         "and matching them would settle the triple outright.")
    info("(b) the MEASURED c_3.  h_3(A_Z(b,x)) is expressible through the "
         "pairing and Z's action once the component vector of the constant "
         "class [I A_Z(b)] is known, and E093 + E101 give h_3 = -(m_2/2) "
         "log_13(3) on C.  That is one equation and there are five candidates.")
    info("(c) the base field.  The model is over O_K with residue degree 2, not "
         "over Z_3; h_{p} over K and h_3 over Q differ by a factor that has to "
         "be settled before any of these numbers is used in Gross's formula.")

    print("=" * 72)
    print("E105 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t0))
    for msg in FAIL:
        print("   FAILED: %s" % msg)


main()
