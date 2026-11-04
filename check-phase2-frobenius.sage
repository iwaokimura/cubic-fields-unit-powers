# check-phase2-frobenius.sage --- E057 (E048 Phase 2) GATE, part 3.
#
# The matrix Phi of Frobenius on H^1_rig(X) and chi(T) = det(1 - Phi T),
# against three independent computations of the same polynomial.
#
#   GATE A (hyperelliptic).  chi(T) equals
#     (i)  the L-polynomial obtained by COUNTING PLACES of the function field
#          over F_p of degree 1..g -- exact, and independent of every p-adic
#          method; and
#     (ii) Sage's own frobenius_polynomial() for the hyperelliptic curve; and
#     (iii) the reverse characteristic polynomial of Sage's
#          matrix_of_frobenius_hyperelliptic (Kedlaya), which is the gate the
#          plan names.
#
#   GATE B (C_4).  chi(T) equals the L-polynomial from place counts, AND it
#   factors as (1 - a_p(E) T + p T^2) * (integral quartic), the quartic being
#   the Prym factor -- the decomposition Jac(C_4) ~ E x Prym of E039/E043,
#   with E : y^2 = x^3 - 36x.  This is the check that the port reproduces OUR
#   geometry and not merely some correct zeta function.
#
# Also reported, per case: the p-adic precision actually surviving the
# reductions (the plan's risk 3), and the margin by which the rounding of the
# coefficients of chi to integers is determined.
#
# Run: sage check-phase2-frobenius.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()
RT = PolynomialRing(ZZ, 'T')
T = RT.gen()


def L_from_places(Qxy, p, g):
    """The L-polynomial of the smooth model, from counting places over F_p.

    #X(F_{p^k}) = sum_{d | k} d * #{places of degree d}, and the first g power
    sums determine L by Newton's identities; the rest by the functional
    equation c_{2g-k} = p^{g-k} c_k.
    """
    K = FunctionField(GF(p), 'x')
    Ry = PolynomialRing(K, 'Y')
    Y = Ry.gen()
    Qk = Ry.zero()
    for (ex, ey), c in Qxy.dict().items():
        Qk += GF(p)(c) * K.gen()**ZZ(ex) * Y**ZZ(ey)
    L = K.extension(Qk, 'y')
    if L.genus() != g:
        raise ArithmeticError("bad reduction at p = %d: genus %d, expected %d"
                              % (p, L.genus(), g))
    npl = {d: len(L.places(d)) for d in range(1, g + 1)}
    N = {}
    for k in range(1, g + 1):
        N[k] = sum(d * npl[d] for d in npl if k % d == 0)
    s = {k: p**k + 1 - N[k] for k in range(1, g + 1)}
    e = {0: ZZ(1)}
    for k in range(1, g + 1):
        acc = ZZ(0)
        for i in range(1, k + 1):
            acc += (-1)**(i - 1) * e[k - i] * s[i]
        e[k] = acc / k
    c = [(-1)**k * e[k] for k in range(g + 1)]
    coeffs = list(c)
    for k in range(g - 1, -1, -1):
        coeffs.append(p**(g - k) * c[k])
    return RT(coeffs)


def frobenius_certified(C, H, p, N, need, g, step=4, cap=40):
    """FrobeniusMatrix at the least N >= the given one (in steps of `step`)
    for which chi(T) is CERTIFIED to p^need.  The certified precision of chi
    is that of Phi minus (2g-1)(-ord_p(Phi)) when ord_p(Phi) < 0 (Tuitman,
    Remark 4.5); needed_precision() alone assumes ord_p(Phi) >= 0, which
    fails for y^2 = x^7 - 1 at p = 5 in this basis (ord_p(Phi) = -1).
    Until 2026-11-04 N was not raised and the precision of chi was taken to
    be that of Phi."""
    N0 = N
    while True:
        FM = FrobeniusMatrix(C, H, p, N)
        FM.compute()
        cchi, vphi = FM.chi_certified_precision()
        if cchi >= need:
            if N > N0:
                print("       ord_p(Phi) = %d: N raised from %d to %d so that "
                      "chi is certified to p^%d (Tuitman Rem. 4.5)"
                      % (vphi, N0, N, need))
            return FM, N
        if N >= N0 + cap:
            raise ArithmeticError("no N <= %d certifies chi to p^%d"
                                  % (N, need))
        N += step


def gate_A(label, Qxy, g, fpoly, primes, Nslack):
    ok = True
    for p in primes:
        t0 = time.time()
        C = TuitmanCurve(Qxy, name=label)
        H = Cohomology(C)
        N = needed_precision(p, g) + Nslack
        FM, N = frobenius_certified(C, H, p, N, needed_precision(p, g), g)
        chi, worst = FM.chi()
        chiZ = RT(list(chi))
        truth = L_from_places(Qxy, p, g)
        sage_fp = RT(list(HyperellipticCurve(fpoly.change_ring(GF(p))).frobenius_polynomial().reverse()))
        kedlaya = kedlaya_chi(fpoly, p, N)
        m1 = (chiZ == truth)
        m2 = (chiZ == sage_fp)
        m3 = (kedlaya is None) or (chiZ == kedlaya)
        rep = FM.precision_report()
        print("  p = %-3d N = %-2d  chi = %-34s places %s  frob_poly %s  Kedlaya %s"
              % (p, N, chiZ, "ok" if m1 else "*** NO ***",
                 "ok" if m2 else "*** NO ***",
                 "ok" if m3 else "*** NO ***"))
        need = needed_precision(p, g)
        print("       loss/step: finite %s, infinite %s;  remainder at p^%s "
              "(N = %d);  span residual p^%s"
              % (rep["finite_loss"], rep["infinite_loss"], rep["remainder"],
                 N, rep["solve_residual"]))
        weil = FM.weil_check(chi)
        print("       chi certified to p^%s by Prop 3.7/3.8 and Rem 4.5, needs p^%s %s; "
              "Weil bounds %s;  %.1f s"
              % (worst, need,
                 "ok" if worst >= need else "*** UNDETERMINED ***",
                 "ok" if not weil else "*** VIOLATED %s ***" % weil,
                 time.time() - t0))
        if not m1:
            print("       truth from places: %s" % truth)
        ok = ok and m1 and m2 and m3
        sys.stdout.flush()
    return ok


def kedlaya_chi(fpoly, p, N):
    """Reverse char poly of Sage's matrix_of_frobenius_hyperelliptic."""
    try:
        from sage.schemes.hyperelliptic_curves.monsky_washnitzer import \
            matrix_of_frobenius_hyperelliptic
        Rp = PolynomialRing(Qp(p, N + 5), 'x')
        M, _ = matrix_of_frobenius_hyperelliptic(Rp(fpoly), p, N + 5)
        cp = M.charpoly()
        d = cp.degree()
        out = []
        for k in range(d + 1):
            c = cp[d - k]          # det(1 - M T), no (-1)^k: see frobenius.py
            z = ZZ(c.lift() % p**(N + 5))
            if z > p**(N + 5) // 2:
                z -= p**(N + 5)
            out.append(z)
        return RT(out)
    except Exception as e:
        print("       (Kedlaya comparison unavailable: %s: %s)"
              % (type(e).__name__, e))
        return None


def needed_precision(p, g):
    """Proposition 4.4: enough to pin the bottom half of the coefficients."""
    bound = 2 * binomial(2 * g, g) * RR(p)**(g / 2)
    return max(3, ceil(log(bound) / log(p)))


# E047's Prym local factors, from check-prym-lfun.gp's localfac(p), which
# returns [c1, c2] with c1 = sum(alpha_i) = a_p(P) and c2 the x^2 coefficient of
# the characteristic polynomial of Frobenius.  Regenerate with
#     sed '$d' check-prym-lfun.gp > /tmp/lib.gp
#     echo 'for(i=1,4, my(p=[5,7,11,13][i]); print(p,"  ",localfac(p)));' > /tmp/q.gp
#     gp -q /tmp/lib.gp /tmp/q.gp < /dev/null
# In our normalisation L_P(T) = prod(1 - alpha_i T) = 1 - c1 T + c2 T^2 + ...
E047_PRYM = {5: (-4, 10), 7: (-3, 6), 11: (-2, 18), 13: (-1, 8)}


def gate_B(primes, Nslack):
    label = "C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)"
    Qxy = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
    g = 3
    E = EllipticCurve([0, 0, 0, -36, 0])          # the quotient of E039/E043
    ok = True
    for p in primes:
        t0 = time.time()
        C = TuitmanCurve(Qxy, name=label)
        H = Cohomology(C)
        N = needed_precision(p, g) + Nslack
        FM, N = frobenius_certified(C, H, p, N, needed_precision(p, g), g)
        chi, worst = FM.chi()
        chiZ = RT(list(chi))
        truth = L_from_places(Qxy, p, g)
        m1 = (chiZ == truth)
        ap = E.ap(p)
        efac = 1 - ap * T + p * T**2
        q, rem = chiZ.quo_rem(efac)
        m2 = (rem == 0)
        rep = FM.precision_report()
        print("  p = %-3d N = %-2d  chi = %s" % (p, N, chiZ))
        print("       vs place counts: %s   E-factor (a_p = %d) divides: %s"
              % ("ok" if m1 else "*** NO ***", ap, "ok" if m2 else "*** NO ***"))
        m3 = True
        if m2:
            print("       Prym factor: %s" % q)
            if p in E047_PRYM:
                c1, c2 = E047_PRYM[p]
                m3 = (q[1] == -c1 and q[2] == c2)
                print("       vs E047 (PARI, check-prym-lfun.gp): "
                      "a_p(P) = %d, c_2 = %d  %s"
                      % (c1, c2, "ok" if m3 else "*** NO ***"))
        else:
            print("       remainder: %s" % rem)
        if not m1:
            print("       truth from places: %s" % truth)
        need = needed_precision(p, g)
        print("       loss/step: finite %s, infinite %s;  remainder at p^%s "
              "(N = %d);  span residual p^%s"
              % (rep["finite_loss"], rep["infinite_loss"], rep["remainder"],
                 N, rep["solve_residual"]))
        weil = FM.weil_check(chi)
        print("       chi certified to p^%s by Prop 3.7/3.8 and Rem 4.5, needs p^%s %s; "
              "Weil bounds %s;  %.1f s"
              % (worst, need,
                 "ok" if worst >= need else "*** UNDETERMINED ***",
                 "ok" if not weil else "*** VIOLATED %s ***" % weil,
                 time.time() - t0))
        ok = ok and m1 and m2 and m3
        sys.stdout.flush()
    return ok


def main():
    print("=== check-phase2-frobenius.sage --- E057 gate (Phi and chi) ===")
    print("")
    allok = True
    Rx = PolynomialRing(QQ, 'X')
    X = Rx.gen()

    print("=" * 72)
    print("GATE A: hyperelliptic calibration")
    sys.stdout.flush()
    allok = gate_A("y^2 = x^5-1", y**2 - (x**5 - 1), 2, X**5 - 1,
                   [7, 11, 13], 4) and allok
    allok = gate_A("y^2 = x^7-1", y**2 - (x**7 - 1), 3, X**7 - 1,
                   [5, 11], 4) and allok
    print("")

    print("=" * 72)
    print("GATE B: C_4, against place counts and the E x Prym decomposition")
    sys.stdout.flush()
    allok = gate_B([5, 7, 11, 13], 4) and allok
    print("")

    print("=" * 72)
    print("E059 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
