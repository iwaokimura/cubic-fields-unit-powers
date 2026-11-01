# check-phase2-froblift.sage --- E057 (E048 Phase 2) GATE, part 2.
#
# The Frobenius lift of Theorem 2.6 in the r-adic representation of Section 4.2.
# Every check here is an identity modulo p^N: no external data is needed, and
# nothing is compared against a floating-point or heuristic quantity.
#
#   (1) alpha * r(x^p) == 1                  (alpha = F_p(1/r))
#   (2) Q(x^p, beta) == 0                    (beta  = F_p(y))
#   (3) beta == y^p and alpha*r^p == 1 modulo p: F_p really is a lift of the
#       p-th power Frobenius, not merely some ring map.
#   (4) F_p(fg) == F_p(f) F_p(g) on pseudo-random pairs.  F_p is DEFINED by
#       substitution, so this tests the r-adic arithmetic itself -- the carry
#       between digits, the reduction modulo Q, the normal form.
#   (5) Proposition 2.12: the observed r-adic range of F_p(y^i) against the
#       paper's bound max J <= p(N-1), and the digit degrees against deg(r).
#
# Run: sage check-phase2-froblift.sage

import sys
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.radic import RAdicRing
from padic.froblift import FrobeniusLift

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()

# (curve label, Q, list of (p, N)).  p is chosen away from the bad primes:
# for the hyperelliptic curves p must not divide disc(r), for C_4 the bad
# primes are exactly {2,3} (E055).
CASES = [
    ("y^2 = x^5-1", y**2 - (x**5 - 1), [(7, 3), (11, 3)]),
    ("y^2 = x^6-x-1", y**2 - (x**6 - x - 1), [(5, 3), (7, 3)]),
    ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
     y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), [(5, 3), (11, 3)]),
]


def random_elements(RR, n, seed):
    """Pseudo-random elements of R with a few r-adic digits."""
    set_random_seed(seed)
    out = []
    for _ in range(n):
        d = {}
        for j in [-1, 0, 1, 2]:
            a = RR.Ry.zero()
            for k in range(RR.dx):
                c = RR.Rx([RR.base(ZZ.random_element(0, RR.p**RR.N))
                           for _ in range(RR.degr)])
                a += c * RR.y**k
            d[j] = a
        out.append(RR.normalize(d))
    return out


def one(label, Qxy, p, N):
    import time
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    RR = RAdicRing(C, p, N)
    F = FrobeniusLift(RR)
    ok = True

    a_ok = F.check_alpha()
    b_ok = F.check_beta()
    mb, ma = F.check_mod_p()
    els = random_elements(RR, 6, 12345 + p)
    pairs = list(zip(els[:3], els[3:]))
    bad = F.check_multiplicative(pairs)
    bounds = F.prop212_bounds()

    print("  p = %-3d N = %d   alpha*r(x^p)=1: %-5s  Q(x^p,beta)=0: %-5s  "
          "beta=y^p mod p: %-5s  alpha*r^p=1 mod p: %-5s"
          % (p, N, a_ok, b_ok, mb, ma))
    print("       multiplicativity: %d/%d pairs fail" % (bad, len(pairs)))
    Ja = RR.J_range(F.alpha)
    print("       J(alpha) = %s  (Prop 2.12(1): p..pN = %d..%d)"
          % (Ja, p, p * N))
    okJ = True
    for i, Jr, degmax in bounds["observed"]:
        good = (Jr is None) or (Jr[1] <= bounds["maxJ_bound"])
        okJ = okJ and good and degmax <= bounds["degree_bound"]
        print("       F(y^%d): J = %-12s max J bound %-4d  max digit deg %d (< %d)  %s"
              % (i, Jr, bounds["maxJ_bound"], degmax, RR.degr,
                 "ok" if good else "*** OUT OF RANGE ***"))
    ok = a_ok and b_ok and mb and ma and (bad == 0) and okJ
    print("       %s   (%.1f s)" % ("ok" if ok else "*** FAILS ***",
                                    time.time() - t0))
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase2-froblift.sage --- E057 gate (Theorem 2.6) ===")
    print("")
    allok = True
    for label, Qxy, pns in CASES:
        print("=" * 72)
        print(label)
        sys.stdout.flush()
        for (p, N) in pns:
            try:
                allok = one(label, Qxy, p, N) and allok
            except Exception as e:
                print("  *** EXCEPTION at p = %d, N = %d: %s: %s"
                      % (p, N, type(e).__name__, e))
                allok = False
            sys.stdout.flush()
        print("")
    print("=" * 72)
    print("E058 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
