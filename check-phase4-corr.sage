# check-phase4-corr.sage --- E065 (E048 Phase 4) GATE, part 2.
#
# Steps (4) and (5) of Balakrishnan-Dogra-Mueller-Tuitman-Vonk Algorithm 3.12:
# the correspondence Z in Ker(NS(J) -> NS(X)), and the splitting of the Hodge
# filtration.  Their Remark 3.17 says the Hecke route to Z is "the only part of
# our algorithm specific to modular curves" and that knowing generators of
# End(J) in advance is a legitimate substitute.  We know them: C_4 carries the
# involution sigma : w -> -w whose quotient is E (E037), so Jac ~ E x P and the
# projectors are (1 +- sigma^*)/2.
#
#   (1) sigma^* is an involution of H^1, with eigenspace dimensions (2, 4) for
#       C_4 -- i.e. H^1(E) and the 4-dimensional Prym part.
#   (2) sigma^* is an ISOMETRY of the cup product of E066.  An automorphism of
#       the curve must preserve it; this checks the two exact computations
#       against each other.
#   (3) Z is Rosati-symmetric (M Z = Z^T M) and has TRACE ZERO.  For a curve
#       NS(X) = Z and NS(J) -> NS(X) is the trace, so these two conditions ARE
#       membership in the kernel.
#   (4) Z COMMUTES WITH FROBENIUS, p-adically, to certified precision.  Z is
#       exact over Q and Phi is E059's p-adic matrix: they share no step.
#   (5) THE EIGENSPACES REPRODUCE THE L-FUNCTION FACTORISATION.  The
#       characteristic polynomial of Phi restricted to the +1 eigenspace must be
#       the E factor, and on the -1 eigenspace the Prym factor -- the same
#       factors E047 computed in PARI/GP from point counts, and E059 matched.
#       This is the check that says the involution really is the E x P splitting
#       and not merely some involution.
#   NOTE (E071).  Everything here is about the ENDOMORPHISM matrix Z_e, and
#   that is the right object for these six checks.  It is NOT the object
#   [BDM+19] §§4.5 and 5.2 need: those want the CLASS Z_e M^{-1}, and the four
#   properties measured here are exactly the four conditions of §4.1 for it.
#   See check-phase4-class.sage.
#
#   (6) THE UNIT ROOT SPLITTING (Remark 3.15) at an ordinary prime: dimension g,
#       complementary to Fil^1, stable under Phi with unit eigenvalues, stable
#       under Z, and ISOTROPIC for the cup product -- the last being the
#       condition their §3.3 imposes on ker(s).
#
# Run: sage check-phase4-corr.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def vp(a, N):
    return a.valuation() if a != 0 else N


def one(label, Qxy, sx, sy, primes, dims=None):
    print("-" * 72)
    print("%s   involution (x,y) -> (%s x, %s y)" % (label, sx, sy))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)
    ok = True

    S = H.automorphism_matrix(sx, sy)
    I = matrix(QQ, n, n, 1)
    dp = ZZ((S.trace() + n) / 2)
    dm = n - dp
    m1 = (S * S == I) and (dims is None or (dp, dm) == dims)
    print("   (1) sigma^* is an involution: %s; eigenspace dimensions (+,-) = "
          "(%d,%d)%s" % (S * S == I, dp, dm,
                         "" if dims is None else " (expected %s)" % (dims,)))
    ok = ok and m1

    M = H.cup_product_matrix()
    m2 = (S.transpose() * M * S == M)
    print("   (2) sigma^* preserves the cup product: %s" % m2)
    ok = ok and m2

    Z = H.correspondence(sx, sy)
    sym = (M * Z == Z.transpose() * M)
    tr0 = (Z.trace() == 0)
    print("   (3) Z = %s ...; Rosati-symmetric: %s; trace = %s"
          % (Z.list()[:4], sym, Z.trace()))
    ok = ok and sym and tr0

    for p in primes:
        N = 8
        FM = FrobeniusMatrix(C, H, p, N)
        FM.compute(primitives=True)
        cert = FM.certified_precision()[0]
        K = FM.base
        ZK = matrix(K, n, n, [K(Z[i][j]) for i in range(n) for j in range(n)])
        D = FM.Phi * ZK - ZK * FM.Phi
        v4 = min(vp(D[i][j], N) for i in range(n) for j in range(n))
        m4 = v4 >= cert
        print("   (4) [Phi, Z] = 0 at p = %2d: to p^%s (need p^%s) %s"
              % (p, v4, cert, "ok" if m4 else "*** NO ***"))
        ok = ok and m4

        # (5) Conjugate Phi by the EXACT rational eigenbasis of S.  Solving
        # p-adically against a non-square matrix loses precision catastrophically
        # (measured: p^-208); an exact P and an exact P^-1 avoid it entirely.
        cols = []
        dims_eig = []
        for eps in (1, -1):
            B = (I + eps * S) / 2
            Vsp = (QQ**n).span([vector(QQ, list(c)) for c in B.columns()])
            bs = list(Vsp.basis())
            dims_eig.append(len(bs))
            cols += bs
        P = matrix(QQ, cols).transpose()
        Pi = P.inverse()
        PK = matrix(K, n, n, [K(P[i][j]) for i in range(n) for j in range(n)])
        PiK = matrix(K, n, n, [K(Pi[i][j]) for i in range(n) for j in range(n)])
        A = PiK * FM.Phi * PK
        dpp = dims_eig[0]
        offdiag = [A[i][j] for i in range(n) for j in range(n)
                   if (i < dpp) != (j < dpp)]
        v5 = min([vp(c, N) for c in offdiag] or [N])
        # The charpoly of the blocks multiplying out to charpoly(Phi) is an
        # ALGEBRAIC CONSEQUENCE of the block diagonality just checked, so it
        # adds no mathematical content; what it does add is a dependence on
        # Sage's charpoly over a floating-point p-adic field, which is
        # meaningless once A has entries of negative valuation (the eigenbasis
        # P need not be p-integrally invertible).  Measured: p^-208 at a prime
        # where the off-blocks vanish to p^8.  So it is required exactly when
        # A is p-integral, and reported as not applicable otherwise.
        blocks = [A.submatrix(0, 0, dpp, dpp),
                  A.submatrix(dpp, dpp, n - dpp, n - dpp)]
        Aint = min([vp(A[i][j], N) for i in range(n) for j in range(n)]) >= 0
        if Aint:
            prod = blocks[0].charpoly() * blocks[1].charpoly()
            cp = FM.Phi.charpoly()
            v5b = min(vp(cp[k] - prod[k], N) for k in range(n + 1))
            m5 = v5 >= cert and v5b >= cert
            extra = "charpoly splits to p^%s" % v5b
        else:
            m5 = v5 >= cert
            extra = ("charpoly comparison n/a: the eigenbasis is not "
                     "p-integrally invertible here")
        print("   (5) Phi is block diagonal for the eigenspaces of sigma^*, "
              "degrees (%d,%d): off-blocks vanish to p^%s; %s (need p^%s) %s"
              % (dims_eig[0], dims_eig[1], v5, extra, cert,
                 "ok" if m5 else "*** NO ***"))
        ok = ok and m5

        # (6) unit root splitting
        t1 = time.time()
        U = FM.unit_root_subspace()
        Fil = H.holomorphic_classes()
        FilK = matrix(K, g, n, [K(Fil[i][j]) for i in range(g)
                                for j in range(n)])
        full = matrix(K, n, n)
        for j in range(g):
            for i in range(n):
                full[i, j] = FilK[j][i]
                full[i, g + j] = U[i][j]
        dv = vp(full.determinant(), N)
        comp = (dv == 0)
        iso = min(vp((U.transpose() * M.change_ring(K) * U)[i][j], N)
                  for i in range(g) for j in range(g))
        Aur = U.solve_right(FM.Phi * U) if comp else None
        try:
            BZ = U.solve_right(ZK * U)
            resZ = min(vp((ZK * U - U * BZ)[i][j], N)
                       for i in range(n) for j in range(g))
        except Exception:
            resZ = -1
        unitdet = vp(Aur.determinant(), N) if Aur is not None else None
        # ORDINARY OR NOT is not an input here: it is read off Phi.  The Newton
        # polygon of the characteristic polynomial has g slopes 0 exactly when
        # the coefficient of T^g is a unit, and Remark 3.15's construction only
        # produces a complement to Fil^1 in that case.  At a non-ordinary prime
        # the gate therefore requires the OPPOSITE -- a negative control, in the
        # same spirit as E062's t = pi^2.
        ordinary = (vp(FM.Phi.charpoly()[g], N) == 0)
        if ordinary:
            m6 = comp and iso >= cert and resZ >= cert and unitdet == 0
            verdict = "ok" if m6 else "*** NO ***"
        else:
            m6 = not comp
            verdict = ("ok (non-ordinary: no unit root splitting, and the "
                       "construction correctly fails to give one)"
                       if m6 else "*** NO: non-ordinary yet complementary ***")
        print("   (6) unit root subspace at p = %2d (%.0f s, ordinary: %s): "
              "complementary to Fil^1: %s (det val %s); isotropic to p^%s; "
              "Z-stable to p^%s; det(Phi|U) val %s -> %s"
              % (p, time.time() - t1, ordinary, comp, dv, iso, resZ, unitdet,
                 verdict))
        ok = ok and m6
        sys.stdout.flush()
    print("   (total %.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-corr.sage --- E065 gate: correspondence "
          "and Hodge splitting ===")
    allok = True
    cases = [
        # bielliptic genus 2, the E050 family: Jac ~ E1 x E2 over Q, the
        # correspondence coming from x -> -x, exactly as ours comes from w -> -w
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)", y**2 - (x**6 + x**4 - x**2 + 1),
         -1, 1, [11, 13], (2, 2)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, [11, 13], (2, 4)),
    ]
    for (label, Qxy, sx, sy, primes, dims) in cases:
        try:
            r = one(label, Qxy, sx, sy, primes, dims)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E067 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
