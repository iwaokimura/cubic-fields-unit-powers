# check-phase3-basis.sage --- E062 (E048 Phase 3) GATE, part 5.
#
# Balakrishnan-Tuitman Definition 2.16(1): the first g elements of the basis of
# H^1_rig(X) must be a basis of H^0(X, Omega^1).  Phase 4 (quadratic Chabauty)
# needs this -- the Hodge filtration is exactly that subspace -- and E060
# recorded it as an open assumption: our basis is a basis of the saturated
# lattice, which says nothing about regularity.
#
#   (1) POLE CENSUS.  For each basis element, the divisor of the differential
#       over Q (Sage's function field, exact -- no p-adics anywhere in this
#       gate), and whether it is regular.
#   (2) THE HOLOMORPHIC SUBSPACE.  Sage's basis of holomorphic differentials,
#       matched against ours MODULO THE IMAGE OF d, must have rank exactly g.
#   (3) THE MATCH IS EXACT.  Each holomorphic differential minus its
#       reconstruction must lie in the image of d -- checked as an identity in
#       E-coordinates, not up to a tolerance (this gate is over Q).
#   (4) THE ADAPTED BASIS EXISTS: S invertible, first g rows spanning the
#       holomorphic subspace.
#   (5) IS A REORDERING ENOUGH?  Reported per curve, because the answer differs:
#       for a hyperelliptic model it is (S is a permutation), for C_4 it is not.
#
# Run: sage check-phase3-basis.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def one(label, Qxy):
    print("-" * 72)
    print(label)
    sys.stdout.flush()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    basis, _ = H.H1X_basis()
    g = ZZ(C.genus)
    L, xL, yL = C.L, C.L(C.x), C.y
    dxL = xL.differential()
    ok = True

    # (1) pole census
    def form_of(vec):
        f = L.zero()
        for c, (i, d) in zip(vec, H.E_basis):
            if c != 0:
                f += QQ(c) * xL**d * yL**i
        return (f / L(C.r)) * dxL

    poles, nreg = [], 0
    for v in basis:
        D = form_of(v).divisor()
        neg = [(pl, m) for pl, m in D.list() if m < 0]
        poles.append(sorted(m for _, m in neg))
        if not neg:
            nreg += 1
    print("   (1) genus %d, basis of size %d; polar parts %s; regular members: "
          "%d" % (g, len(basis), poles, nreg))
    sys.stdout.flush()

    # (2),(3) the holomorphic subspace
    T = H.holomorphic_classes()
    m2 = (T.nrows() == g and T.rank() == g)
    print("   (2) holomorphic classes: %d of them, rank %d (need %d) %s"
          % (T.nrows(), T.rank(), g, "ok" if m2 else "*** NO ***"))
    ok = ok and m2

    dM = H.d_matrix()
    im = dM.column_space()
    nfail = 0
    hol = list(L.basis_of_holomorphic_differentials())
    idx = {mm: k for k, mm in enumerate(H.E_basis)}
    for j, om in enumerate(hol):
        gg = (om / dxL) * L(C.r)
        vec = vector(QQ, H.dim_E)
        for i, c in enumerate(gg.list()):
            num, den = c.numerator(), c.denominator()
            for d, cc in enumerate(num.list()):
                if cc != 0:
                    vec[idx[(i, d)]] += QQ(cc) / QQ(den)
        recon = vector(QQ, H.dim_E)
        for k in range(len(basis)):
            recon += T[j, k] * vector(QQ, list(basis[k]))
        if (vec - recon) not in im:
            nfail += 1
    m3 = (nfail == 0)
    print("   (3) each holomorphic form minus its reconstruction lies in "
          "d(B_0 cap B_inf): %d/%d %s"
          % (len(hol) - nfail, len(hol), "ok" if m3 else "*** NO ***"))
    ok = ok and m3

    # (4) the adapted basis
    S = H.adapted_change_of_basis()
    m4 = (S.determinant() != 0 and S.nrows() == 2 * g
          and (QQ**(2 * g)).span([S.row(i) for i in range(g)])
          == (QQ**(2 * g)).span([T.row(i) for i in range(g)]))
    print("   (4) adapted basis S: %dx%d, det = %s, first %d rows span the "
          "holomorphic subspace: %s"
          % (S.nrows(), S.ncols(), S.determinant(), g,
             "ok" if m4 else "*** NO ***"))
    ok = ok and m4

    # (5) would a reordering have sufficed?
    is_perm = all(sorted(T.row(i).list()).count(0) == 2 * g - 1
                  for i in range(g))
    print("   (5) a REORDERING of the computational basis would suffice: %s"
          % ("yes" if is_perm else
             "NO -- every basis element has a pole, the regular subspace is "
             "spanned by no subset of them"))
    sys.stdout.flush()
    return ok


def main():
    print("=== check-phase3-basis.sage --- E062 gate (BT Def 2.16(1)) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1)),
        ("y^2 = x^7-1", y**2 - (x**7 - 1)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)),
    ]
    for (label, Qxy) in cases:
        t0 = time.time()
        try:
            r = one(label, Qxy)
        except Exception as ex:
            print("   *** EXCEPTION: %s: %s" % (type(ex).__name__, ex))
            r = False
        print("   %s  (%.1f s)" % ("ok" if r else "*** FAILS ***",
                                   time.time() - t0))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E064 GATE: %s" % ("GREEN" if allok else "*** RED ***"))
    sys.stdout.flush()


main()
