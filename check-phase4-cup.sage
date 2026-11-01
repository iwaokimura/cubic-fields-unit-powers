# check-phase4-cup.sage --- E065 (E048 Phase 4) GATE, part 1.
#
# The cup product on H^1_rig(X) and a symplectic basis: step (2) of
# Balakrishnan-Dogra-Mueller-Tuitman-Vonk Algorithm 3.12, and the pairing that
# their §3.3 needs ker(s) to be isotropic for.
#
# E065(d) showed the cheap route is closed: Phi^T M Phi = p M does not
# DETERMINE M when End(J) is bigger than Z, which is our case.  So M is
# computed honestly and exactly over Q, and that identity becomes an
# independent CHECK linking this rational computation to E059's p-adic Phi.
#
#   (1) M is antisymmetric.
#   (2) WELL-DEFINEDNESS: exact forms pair to zero, <d(x^d y^i), omega_j> = 0.
#       This is what makes the pairing descend to cohomology, and it tests the
#       primitives and the residues together with no external data.
#   (3) NONDEGENERATE, AND A UNIT AT THE PRIMES WE USE.  det M is NOT +-1 on
#       our lattice -- the saturated lattice of H1X_basis is not the integral
#       structure for which Poincare duality is perfect -- but quadratic
#       Chabauty works over Z_p, so what it needs is v_p(det M) = 0 at the
#       primes in use.  Both numbers are printed.
#   (4) Fil^1 ISOTROPIC (Riemann bilinear relations): E064's regular
#       differentials must pair to zero among themselves.  This is the link
#       between E064's output and the hypothesis §3.3 puts on the splitting.
#   (5) FROBENIUS COMPATIBILITY: Phi^T M Phi = p M for E059's Phi.  The two
#       sides share NO step -- one is exact over Q through function field
#       completions, the other is a p-adic Frobenius matrix from Tuitman's
#       algorithm -- so this is the strongest calibration available for either.
#       NOTE THE CONVENTION: Phi as STORED by frobenius.py (columns = images),
#       not the transpose that Algorithm 3.7 wants.  Measured: with the
#       transpose the identity holds on y^2=x^5-1 and FAILS on y^2=x^7-1, so
#       one curve alone would not have caught the wrong choice.  Third time in
#       this port that a transpose has had to be pinned down by experiment.
#   (6) A symplectic basis over Z_p: T with T M T^T the standard form,
#       p-integral and with det T a p-adic unit.
#
# Run: sage check-phase4-cup.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def primitive(g):
    F = g.parent().zero()
    for k in range(g.valuation(), g.prec()):
        if k != -1 and g[k] != 0:
            F += g[k] / QQ(k + 1) * g.parent().gen()**(k + 1)
    return F


def tr(c):
    return QQ(c.trace()) if hasattr(c, "trace") else QQ(c)


def pairings(H, prec):
    """M on the basis, and the pairings of the exact forms against it.

    Every completion is built ONCE per place and reused for all the forms;
    doing it per pair made C_4 unusably slow.
    """
    C = H.C
    L, xL = C.L, C.L(C.x)
    basis, _ = H.H1X_basis()
    forms = [H.differential_of(v) for v in basis]
    dM = H.d_matrix()
    exact = [H.differential_of(dM.column(j)) for j in range(dM.ncols())]
    exact = [o for o in exact if not o.is_zero()]     # d of a constant
    poles = H._pole_places(forms + exact)
    n = len(forms)
    M = matrix(QQ, n, n)
    ex_pairs = [[QQ(0)] * n for _ in exact]
    for P in poles:
        m = L.completion(P, prec=prec)
        t = P.local_uniformizer()
        dtdx = t.derivative()
        ser = [m(o / xL.differential() / dtdx) for o in forms]
        exser = [m(o / xL.differential() / dtdx) for o in exact]
        for g in ser:
            if g[-1] != 0:
                raise ArithmeticError("basis form with a residue at %s" % P)
        prim = [primitive(g) for g in ser]
        for i in range(n):
            for j in range(n):
                M[i, j] += tr((prim[i] * ser[j])[-1])
        for c, ge in enumerate(exser):
            Fe = primitive(ge)
            for j in range(n):
                ex_pairs[c][j] += tr((Fe * ser[j])[-1])
    return M, ex_pairs, len(poles)


def one(label, Qxy, primes, prec=40):
    print("-" * 72)
    print(label)
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)
    ok = True

    M, ex_pairs, npoles = pairings(H, prec)
    print("   cup product over Q in %.0f s (%d pole place%s, t-adic prec %d)"
          % (time.time() - t0, npoles, "" if npoles == 1 else "s", prec))
    if n <= 4:
        print("   M = %s" % M.list())

    m1 = (M.transpose() == -M)
    print("   (1) antisymmetric: %s" % m1)
    ok = ok and m1

    nbad = sum(1 for q in ex_pairs if any(c != 0 for c in q))
    m2 = (nbad == 0)
    print("   (2) exact forms pair to zero: %d/%d %s"
          % (len(ex_pairs) - nbad, len(ex_pairs), "ok" if m2 else "*** NO ***"))
    ok = ok and m2

    d = M.determinant()
    m3 = (d != 0)
    print("   (3) det M = %s (nonzero: %s); valuations at the primes in use: %s"
          % (d, m3, {p: QQ(d).valuation(p) for p in primes}))
    m3 = m3 and all(QQ(d).valuation(p) == 0 for p in primes)
    print("       => unit at every prime in use: %s" % m3)
    ok = ok and m3

    T = H.holomorphic_classes()
    m4 = (T * M * T.transpose() == 0)
    print("   (4) Fil^1 isotropic (Riemann bilinear relations): %s" % m4)
    ok = ok and m4

    for p in primes:
        t1 = time.time()
        N = 8
        FM = FrobeniusMatrix(C, H, p, N)
        FM.compute(primitives=True)
        cert = FM.certified_precision()[0]
        K = FM.base
        MK = matrix(K, n, n, [K(M[i][j]) for i in range(n) for j in range(n)])
        res = {}
        for nm, Phi in [("stored", FM.Phi), ("transposed", FM.Phi.transpose())]:
            D = Phi.transpose() * MK * Phi - K(p) * MK
            vals = [D[i][j].valuation() if D[i][j] != 0 else N
                    for i in range(n) for j in range(n)]
            res[nm] = min(vals)
        m5 = res["stored"] >= cert
        print("   (5) Phi^T M Phi = p M at p = %2d: stored p^%s, transposed "
              "p^%s (need p^%s) %s   (%.0f s)"
              % (p, res["stored"], res["transposed"], cert,
                 "ok" if m5 else "*** NO ***", time.time() - t1))
        ok = ok and m5
        sys.stdout.flush()

    F, Tc = M.symplectic_form()
    ent_ok = all(QQ(c).denominator() % p != 0
                 for c in Tc.list() for p in primes)
    det_ok = all(QQ(Tc.determinant()).valuation(p) == 0 for p in primes)
    m6 = (Tc * M * Tc.transpose() == F) and ent_ok and det_ok
    print("   (6) symplectic basis: T M T^T = standard form: %s; T p-integral: "
          "%s; det T = %s, unit at the primes in use: %s"
          % (Tc * M * Tc.transpose() == F, ent_ok, Tc.determinant(), det_ok))
    ok = ok and m6
    return ok


def main():
    print("=== check-phase4-cup.sage --- E065 gate: cup product ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), [11]),
        ("y^2 = x^7-1", y**2 - (x**7 - 1), [11]),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), [11, 13]),
    ]
    for (label, Qxy, primes) in cases:
        t0 = time.time()
        try:
            r = one(label, Qxy, primes)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s  (%.0f s)" % ("ok" if r else "*** FAILS ***",
                                   time.time() - t0))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E066 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
