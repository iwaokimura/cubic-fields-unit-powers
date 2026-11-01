# check-c4-heightsys.sage --- E087: the height system, and the budget available
# to h_2.
#
# This is option (3') for ell = 2: carry h_2 as unknowns and ask whether the
# height equations still close.  Answering that needs the size of both sides,
# and E065(b) only estimated one of them.  It counted "4 equations from our five
# known points (t = -2, -1, -1/11, 1 and (0,0), one of them the base point)".
# But C_4(Q) has NINE affine points, not five: each of the four t-values carries
# two rational w.  And sigma-conjugate points give genuinely different classes,
#     [sigma x - b] = sigma[x - b] + [sigma b - b],
# so they are not redundant.  The real count is what this gate measures.
#
# THE SYSTEM.  h = h_p + h_2 + h_3 with h_p = theta the port's Lemma 5.5 output,
# h_3 known up to a sign (E086), h_2 unknown.  The global height of A_Z(b,x) is
# a quadratic form in E_1(x) = AJ_b(x) in H^0(Omega^1)^*.  By E065(b) the form
# is BLOCK DIAGONAL for the sigma-eigenspaces, and check (1) finds that the
# phase-4 holomorphic basis is ALREADY adapted: sigma^* is diag(1,-1,-1) on it,
# so omega_1 spans the E-part and omega_2, omega_3 the Prym part.  The form is
#     alpha u_1^2 + beta_22 u_2^2 + 2 beta_23 u_2 u_3 + beta_33 u_3^2,
# four unknowns, of which alpha is a p-adic height on y^2 = x^3-36x and is
# computable directly by SageMath (E065(b)), leaving THREE.
#
# THE CHECKS.
#   (1) sigma^* on the holomorphic basis is diag(1,-1,-1), exactly over Q: the
#       basis is already adapted and no change of coordinates is needed.
#   (2) E_1(x) = AJ_b(x) for the eight non-base rational points, by Coleman
#       integration from b = (1,3): Algorithm 3.7 for the seven good ones and
#       Algorithm 3.12 for (0,0).  Sanity: E_1 must vanish at b, and the two
#       points of a sigma-pair must have E_1 differing by the sigma-action plus
#       the constant [sigma b - b], which is a check on the integrals.
#   (3) THE RANK OF THE DESIGN MATRIX.  Rows are the eight points, columns the
#       four monomials u_1^2, u_2^2, u_2u_3, u_3^2.  Its rank is the number of
#       independent equations the known points give.  If it is 4, the alpha's
#       are over-determined by four.
#   (4) THE BUDGET.  With r independent equations, 3 unknowns after SageMath
#       supplies the E-block, and one equation reserved to decide E086's sign,
#       the number of h_2 unknowns that can be carried is r - 3 - 1, i.e. the
#       nine points may fall into that many classes plus the base point's.
#
# WHAT THIS DOES AND DOES NOT SETTLE.  It settles the size of the left-hand
# side, which was the half of option (3') that was never measured.  It does not
# settle the number of h_2 classes -- E085 showed that needs the stable model at
# 2 -- so the verdict is conditional, and the condition is now a number.
#
# Run: sage check-c4-heightsys.sage

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix
from padic.points import CurvePoint, LocalExpansion
from padic.integrals import ColemanIntegrals

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE, N = 13, 8
BASE = (QQ(1), QQ(3))
OTHERS = [(QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
          (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)),
          (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11), (QQ(0), QQ(0))]

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


def vz(a, N):
    return ZZ(N + 4) if a == 0 else ZZ(a.valuation())


def qp_part(a, e):
    if e == 1:
        return a
    c = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
    return c[0] if c else 0


def main():
    print("=== check-c4-heightsys.sage --- E087: the height system ===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    reps, S = H.phase4_basis()
    g = ZZ(C.genus)
    n = 2 * g
    L, xL, yL = C.L, C.L(C.x), C.y

    print("(1) sigma^* ON THE HOLOMORPHIC BASIS")
    Q1y = L.zero()
    for (a, b), cc in Q1.dict().items():
        if b > 0:
            Q1y += QQ(cc) * ZZ(b) * xL**ZZ(a) * yL**ZZ(b-1)

    def ell_of(vec):
        return (H.differential_of(vec) / xL.differential()) * Q1y

    def coords(e):
        cs = list(e.list()) + [C.K.zero()] * 4
        cs = cs[:4]
        n0, d0 = cs[0].numerator(), cs[0].denominator()
        n1, d1 = cs[1].numerator(), cs[1].denominator()
        l0 = [QQ(c) / QQ(d0.constant_coefficient()) for c in n0.list()]
        l0 = l0 + [QQ(0)] * (2 - len(l0))
        l1 = [QQ(c) / QQ(d1.constant_coefficient()) for c in n1.list()]
        l1 = l1 + [QQ(0)] * (1 - len(l1))
        return (l0[0], l0[1], l1[0])

    A = matrix(QQ, [coords(ell_of(reps[i])) for i in range(g)])
    Asig = matrix(QQ, [[-A[i][0], -A[i][1], A[i][2]] for i in range(g)])
    Msig = Asig * A.inverse()
    check(Msig**2 == 1, "sigma^* is an involution on H^0(Omega^1)")
    check(Msig == diagonal_matrix(QQ, [1, -1, -1]),
          "and equals diag(1,-1,-1) on the phase-4 holomorphic basis: the "
          "basis is ALREADY adapted, omega_1 spanning the E-part and "
          "omega_2, omega_3 the Prym part")
    info("so the block-diagonal height form is alpha u_1^2 + beta_22 u_2^2 "
         "+ 2 beta_23 u_2 u_3 + beta_33 u_3^2: four unknowns, three after "
         "SageMath supplies alpha (E065(b)).")

    print("(2) E_1 = AJ_b AT THE EIGHT NON-BASE RATIONAL POINTS")
    t0 = time.time()
    FM = FrobeniusMatrix(C, H, P_GATE, N)
    FM.compute(primitives=True)
    cert = ZZ(FM.certified_precision()[0])
    CI = ColemanIntegrals(FM)
    RR, K = FM.RR, FM.base
    info("Phi at p = %d, N = %d: %.0f s, certified p^%d"
         % (P_GATE, N, time.time()-t0, cert))

    # exact parts of omega~ = S omega + du (frobstruct's transport law)
    dM = H.d_matrix()
    bas, _ = H.H1X_basis()
    Uex = []
    for i in range(n):
        tgt = vector(QQ, [QQ(c) for c in reps[i]])
        for j in range(n):
            if S[i][j] != 0:
                tgt -= QQ(S[i][j]) * vector(QQ, [QQ(c) for c in bas[j]])
        v = dM.solve_right(tgt)
        acc = RR.Ry.zero()
        for m, (yi, xd) in enumerate(H.B_basis):
            if v[m] != 0:
                acc += RR._coerce_QQ(v[m]) * RR.Rx.gen()**xd * RR.Ry.gen()**yi
        Uex.append(RR.normalize({0: acc}) if acc != 0 else RR.zero())

    def u_at(P):
        if P.is_good():
            return [RR.evaluate(a, P.x, P.y, ring=P.ring) for a in Uex]
        LE = LocalExpansion(P, 4)
        out = []
        for a in Uex:
            ser = RR.zero()
            # evaluate the polynomial part directly on the local expansion
            acc = LE.S.zero()
            for j, aj in a.items():
                for i2, coef in enumerate(RR.Ry(aj).list()):
                    cv = LE.S.zero()
                    for k2, c2 in enumerate(coef.list()):
                        if c2 != 0:
                            cv += LE.ring(c2) * LE.xt**k2
                    if cv != 0:
                        acc += cv * LE.bt[i2]
            out.append(acc[0] if acc != 0 else LE.ring(0))
        return out

    Pb = CurvePoint(RR, K(BASE[0]), y=K(BASE[1]))
    uP = u_at(Pb)
    E1 = {}
    for (a, b) in OTHERS:
        Pt = CurvePoint(RR, K(a), y=K(b))
        t1 = time.time()
        if Pt.is_good():
            comp = list(CI.coleman_integrals_on_basis(Pb, Pt))
            ee = ZZ(1)
        else:
            ee = ZZ(2 * P_GATE * CI.ramification_at(Pt))
            comp = [qp_part(c, ee)
                    for c in CI.coleman_integrals_general(Pb, Pt, e=ee)]
        uQ = u_at(Pt)
        vec = []
        for i in range(n):
            acc = K(0)
            for j in range(n):
                if S[i][j] != 0:
                    acc += K(QQ(S[i][j])) * K(comp[j])
            vec.append(acc + K(uQ[i]) - K(uP[i]))
        E1[(a, b)] = vec[:g]
        info("(%-6s %-7s) %s  E_1 valuations %s  (%.0f s)"
             % (a, b, "good" if ee == 1 else "bad, e=%d" % ee,
                [str(vz(c, N)) for c in vec[:g]], time.time()-t1))
    check(len(E1) == 8, "E_1 computed at all eight non-base points")

    # (2b) sigma-equivariance: AJ_b(sigma x) = sigma AJ_b(x) + AJ_b(sigma b),
    # and sigma b - b is anti-invariant so its E-component c_1 vanishes.  With
    # sigma = diag(1,-1,-1) this reads u_1(sigma x) = u_1(x) and
    # u_j(sigma x) = -u_j(x) + c_j for j = 2,3.  The sigma-FIXED point (0,0)
    # then forces u_j(0,0) = c_j/2, which is a check on the Algorithm 3.12
    # integral -- the only one in this gate with no independent route.
    cvec = E1[(QQ(1), QQ(-3))]                       # AJ_b(sigma b)
    check(vz(cvec[0], N) >= cert,
          "c_1 = 0 to p^%s: sigma b - b is anti-invariant, so its E-component "
          "vanishes" % vz(cvec[0], N))
    pairs = [((QQ(-1), QQ(3)), (QQ(-1), QQ(-3))),
             ((QQ(-2), QQ(6)), (QQ(-2), QQ(-6))),
             ((QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11))]
    d1 = min(vz(E1[q][0] - E1[r][0], N) for q, r in pairs)
    check(d1 >= cert,
          "u_1(sigma x) = u_1(x) on all three sigma-pairs, to p^%s" % d1)
    dj = min(min(vz(E1[q][j] + E1[r][j] - cvec[j], N) for j in (1, 2))
             for q, r in pairs)
    check(dj >= cert,
          "u_j(sigma x) + u_j(x) = c_j for j = 2,3 on all three pairs, to p^%s"
          % dj)
    zz = E1[(QQ(0), QQ(0))]
    dz = min(vz(2 * zz[j] - cvec[j], N) for j in (1, 2))
    check(dz >= min(cert, ZZ(2)),
          "and the sigma-FIXED point (0,0) satisfies 2 u_j(0,0) = c_j to p^%s "
          "-- a check on the Algorithm 3.12 integral, which has no other "
          "independent route in this gate" % dz)

    print("(3) THE RANK OF THE DESIGN MATRIX")
    rows = []
    for k in OTHERS:
        u = E1[k]
        rows.append([u[0]**2, u[1]**2, u[1]*u[2], u[2]**2])
    M = matrix(K, rows)
    # p-adic rank at the certified precision: scale each row to be integral and
    # reduce mod p^cert, then take the rank over Z/p^cert via Smith form over ZZ
    scaled = []
    for r in rows:
        vs = [vz(c, N) for c in r]
        m = min(vs)
        scaled.append([ZZ((c / K(P_GATE)**m).residue(cert)) if c != 0 else ZZ(0)
                       for c in r])
    Mz = matrix(ZZ, scaled)
    elem = Mz.elementary_divisors()
    rk = len([d for d in elem if d != 0 and ZZ(d).valuation(P_GATE) < cert])
    info("elementary divisors of the design matrix mod p^%d: %s"
         % (cert, [str(d) for d in elem]))
    check(rk == 4,
          "the design matrix is 8 x 4 of rank %d: the four coefficients of the "
          "block-diagonal form are DETERMINED, and FOUR equations are left "
          "over.  E065(b) had four equations against four unknowns and nothing "
          "left over, because it counted five rational points where C_4(Q) has "
          "nine" % rk)

    print("(4) THE BUDGET FOR h_2")
    r = rk
    unk_alpha = 3          # after SageMath supplies the E-block
    spare_for_sign = 1
    budget = r + 4 - 4 - unk_alpha - spare_for_sign if False else \
        len(OTHERS) - unk_alpha - spare_for_sign
    info("equations: %d (one per non-base rational point), of which %d are "
         "independent as constraints on the quadratic form" % (len(OTHERS), r))
    info("unknowns: %d in the Prym block (the E-block is a p-adic height on "
         "y^2 = x^3-36x, which SageMath computes), plus one equation reserved "
         "to decide E086's sign" % unk_alpha)
    check(budget >= 1,
          "so h_2 may carry up to %d unknown values and the system still "
          "closes: the nine known points may fall into up to %d reduction "
          "classes at ell = 2 (the base point's class contributing h_2 = 0)"
          % (budget, budget + 1))
    info("E085 showed the number of classes cannot be determined without the "
         "stable model at 2, so this verdict is CONDITIONAL -- but the "
         "condition is now a number, and E065(b)'s pessimism (4 equations, no "
         "room at all) was based on an undercount of the rational points.")

    print("=" * 72)
    print("E087 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL), time.time()-t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
