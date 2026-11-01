r"""
check-c4-hp.sage --- E111 (Tier 3): the Coleman integral that finishes b.

E108 left  b = h_p(kappa', delta_11) - (5/2) log_13(2) + log_13(3)  with the
two ell-adic terms computed.  E109 built omega_0 with residue divisor kappa'
and showed that Algorithm 3.7 applies on the 7-dimensional Phi-stable space
V = H^1_dR(X) (+) Q_p[omega_0] of the curve with r enlarged by (x-1).  E110
pinned the Coleman-Gross representative,

    omega_{kappa'} = omega_0 + c_1 dx/Q_y + c_2 x dx/Q_y.

This script evaluates

    h_p(kappa', delta_11) = int_{sigma x_11}^{x_11} omega_{kappa'}
       = (1/12) int (12 omega_0) + c_1 I_1 + c_2 I_2

by running Algorithm 3.7 once, with primitives, on the 7-element basis.

WHAT CHECKS THE ANSWER, and what does not.  (B5) says the nine rational points
impose no condition on b (E098), so there is no check from them; that is the
whole reason b had to be computed.  What is available here:
  - the sigma-EVEN holomorphic form must integrate to zero between sigma x_11
    and x_11, as it did between b and sigma b in E110;
  - I_1 and I_2 are computed twice, on the enlarged curve and on the plain one,
    which are different affine curves with different E, different d(B) and
    different Frobenius matrices;
  - E110's normalisation is recomputed here from the same 7 x 7 matrix and its
    Abel-Jacobi check re-run, so the c_i are not imported by hand.
The one check this does NOT do is the symmetry h_p(D_1,D_2) = h_p(D_2,D_1),
which would need omega_{delta_11} and a second enlargement; it is named in the
Next Steps.
"""

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix
from padic.integrals import ColemanIntegrals
from padic.points import CurvePoint

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
Rx = PolynomialRing(QQ, 'x')
X = Rx.gen()
P_GATE = 13
N = ZZ(os.environ.get("E111_N", 12))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
P11 = (QQ(-1)/11, QQ(15)/11)
S11 = (QQ(-1)/11, QQ(-15)/11)

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


class FrobeniusOnV(FrobeniusMatrix):
    """FrobeniusMatrix with a basis of any size (E109's V, seven elements).

    Only the shape of the stored matrix differs from the parent: compute()'s
    step 5 already solves against basis + d(B) and does not care how many
    basis vectors there are.  The parent hard-codes 2g twice, in __init__'s
    consistency check and in the shape of Phi, and nothing else.
    """

    def __init__(self, C, H, p, N, extra):
        FrobeniusMatrix.__init__(self, C, H, p, N)
        self.basis = list(self.basis) + [list(extra)]

    def compute(self, primitives=False):
        n = self.H.dim_E
        K = self.base
        cols = [vector(K, [K(QQ(c)) for c in b]) for b in self.basis]
        dcols = [vector(K, [K(QQ(c)) for c in b]) for b in self.im_basis]
        m = len(cols)
        A = matrix(K, n, m + len(dcols),
                   lambda i, j: (cols[j][i] if j < m else dcols[j - m][i]))
        out = []
        self.f = []
        self.min_solve_residual = None
        Bsol = self._dB_preimages() if primitives else None
        for b in self.basis:
            u = self._form_coefficients(b)
            Fw = self.frobenius_of_form(u)
            if primitives:
                coords, fi = self.reduce_to_E(Fw, primitives=True)
            else:
                coords = self.reduce_to_E(Fw)
            sol = A.solve_right(coords)
            res = A*sol - coords
            vals = [c.valuation() for c in res if c != 0]
            v = min(vals) if vals else self.N
            self.min_solve_residual = v if self.min_solve_residual is None \
                else min(self.min_solve_residual, v)
            if primitives:
                acc = self.RR.Ry.zero()
                for k in range(len(dcols)):
                    c = sol[m + k]
                    if c == 0:
                        continue
                    for j, z in enumerate(Bsol[k]):
                        if z != 0:
                            (bi, bd) = self.H.B_basis[j]
                            acc += (c * self.RR._coerce_QQ(z)
                                    * self.RR.Rx.gen()**bd
                                    * self.RR.Ry.gen()**bi)
                if acc != 0:
                    fi = self.RR.add(fi, self.RR.normalize({0: acc}))
                self.f.append(fi)
            out.append([sol[j] for j in range(m)])
        self.Phi = matrix(K, m, m, lambda i, j: out[j][i])
        return self.Phi


def enlarged(name):
    C = TuitmanCurve(Q1, name=name)
    C.r = C.r * (X - 1)
    C.degr = C.r.degree()
    return C


def omega0(C):
    L = C.L
    xL, yL = L(C.x), C.y
    Qy = 4*yL**3 - 12*(xL - 1)**2*yL
    return (-6*(yL**2 + 9) / ((xL - 1) * Qy)) * xL.differential()


def class_and_exact(H, basis, target, pts):
    """(coefficients on `basis`, value of the exact part between two points).

    target = sum_i lam_i basis_i + d(u) with u in B; the points are RATIONAL,
    so u is evaluated exactly over Q.
    """
    dM = H.d_matrix()
    M = matrix(QQ, [vector(QQ, list(b)) for b in basis]
               + [dM.column(j) for j in range(dM.ncols())]).transpose()
    sol = M.solve_right(vector(QQ, target))
    lam = list(sol)[:len(basis)]
    (Pa, Pb) = pts
    dv = QQ(0)
    for m, (i, d) in enumerate(H.B_basis):
        c = QQ(list(sol)[len(basis) + m])
        if c != 0:
            dv += c * (Pb[0]**d * Pb[1]**i - Pa[0]**d * Pa[1]**i)
    return lam, dv


def main():
    print("=== check-c4-hp.sage --- E111: h_p(kappa', delta_11), and b ===")
    t00 = time.time()
    g = ZZ(3)

    C0 = TuitmanCurve(Q1, name="C_4")
    C = enlarged("C_4 minus x=1")
    H0, H = Cohomology(C0), Cohomology(C)
    om0 = omega0(C)
    w0 = vector(QQ, H.form_in_E(om0)) * 12
    reps, S4 = H.phase4_basis()
    reps0, S40 = H0.phase4_basis()

    # ------------------------------------------------------------ group (1)
    print("(1) THE SEVEN-DIMENSIONAL FROBENIUS, WITH PRIMITIVES")
    t0 = time.time()
    FM = FrobeniusOnV(C, H, P_GATE, N, w0)
    K = FM.base
    Phi7 = FM.compute(primitives=True)
    cert = ZZ(FM.certified_precision()[0])
    info("Phi on V with the functions f_i: %.0f s at N = %s, certified p^%s, "
         "solve residual p^%s" % (time.time() - t0, N, cert,
                                  FM.min_solve_residual))
    check(all(Phi7[2*g, j] == 0 for j in range(2*g))
          and (Phi7[2*g, 2*g] - K(P_GATE)).valuation() >= cert,
          "E109's structure survives the primitives: the last row of Phi is "
          "(0,...,0,p) to p^%s" % cert)
    PhiI = Phi7.transpose() - identity_matrix(K, 2*g + 1)
    check(PhiI.determinant().valuation() == 0,
          "and Phi - I is invertible on all seven dimensions, which is what "
          "Algorithm 3.7 inverts")

    # ------------------------------------------------------------ group (2)
    print("(2) THE NORMALISATION, RECOMPUTED FROM THIS MATRIX (E110)")
    Phi6 = Phi7[0:2*g, 0:2*g]
    alpha = vector(K, [Phi7[i, 2*g] for i in range(2*g)])
    D = Phi6 - K(P_GATE)*identity_matrix(K, 2*g)
    vdet = ZZ(D.determinant().valuation())
    prec = cert - vdet
    u = D.solve_right(alpha)
    T4 = matrix(K, S4).transpose().inverse()
    u4 = T4 * u
    Sm = matrix(K, H.automorphism_matrix(sx=1, sy=-1))
    vodd = min([c.valuation() for c in (Sm*u + u) if c != 0] + [FM.N])
    check(vodd >= prec and all(u4[i] == 0 or u4[i].valuation() >= prec
                               for i in (0, g)),
          "Psi(omega_0) is sigma-odd and has no elliptic component, to p^%s: "
          "E110 reproduced from a matrix computed with primitives" % vodd)
    Sc = H.adapted_change_of_basis()
    Ucols = []
    for k in range(g, 2*g):
        v = vector(K, [K(QQ(c)) for c in Sc.row(k)])
        for _ in range(cert):
            v = Phi6 * v
        Ucols.append(v)
    U = T4 * matrix(K, Ucols).transpose()
    bot = U[g:2*g, :]
    check(ZZ(bot.determinant().valuation()) == 0,
          "the unit root subspace is still complementary to Fil^1 (p = 13 is "
          "ordinary)")
    tau = (U * bot.inverse())[0:g, :].transpose()
    hfil = vector(K, [u4[i] for i in range(g)]) \
        - tau.transpose()*vector(K, [u4[g+i] for i in range(g)])
    c2 = -hfil[1]*324/12
    c1 = -hfil[2]*324/12
    info("c_1 = %s" % c1)
    info("c_2 = %s" % c2)
    check(hfil[0] == 0 or hfil[0].valuation() >= prec,
          "the correction is sigma-odd, so omega_{kappa'} stays in the Prym "
          "part; c_1, c_2 are determined to p^%d" % prec)

    # ------------------------------------------------------------ group (3)
    print("(3) ALGORITHM 3.7 BETWEEN sigma x_11 AND x_11")
    CI = ColemanIntegrals(FM)
    Pm = CurvePoint(FM.RR, K(S11[0]), y=K(S11[1]), ring=K)
    Pp = CurvePoint(FM.RR, K(P11[0]), y=K(P11[1]), ring=K)
    check(CI.f_converges_at(Pm) and CI.f_converges_at(Pp),
          "both endpoints are good points of the ENLARGED affine curve: they "
          "reduce to (7,1) and (7,12) mod 13, and x = 7 is a zero neither of "
          "r nor of the new factor (x-1)")
    t0 = time.time()
    J = CI.coleman_integrals_on_basis(Pm, Pp)
    info("seven Coleman integrals in %.0f s" % (time.time() - t0))
    lamr, dvr = [], []
    for j in range(g):
        lam, dv = class_and_exact(H, FM.basis, list(reps[j]), (S11, P11))
        lamr.append(lam)
        dvr.append(dv)
    Ir = [sum(K(QQ(lamr[j][i])) * J[i] for i in range(2*g + 1)) + K(dvr[j])
          for j in range(g)]
    for j in range(g):
        info("int_{sigma x_11}^{x_11} reps[%d] = %s" % (j, Ir[j]))
    check(Ir[0] == 0 or Ir[0].valuation() >= cert,
          "the sigma-EVEN holomorphic form integrates to 0 between the two "
          "points, to p^%s: they have the same image on the quotient elliptic "
          "curve.  Same check as E110's at b, sigma b, on new endpoints"
          % (cert if Ir[0] == 0 else Ir[0].valuation()))

    # ------------------------------------------------------------ group (4)
    print("(4) THE SAME TWO INTEGRALS FROM THE PLAIN CURVE")
    t0 = time.time()
    FM0 = FrobeniusMatrix(C0, H0, P_GATE, N)
    FM0.compute(primitives=True)
    CI0 = ColemanIntegrals(FM0)
    Pm0 = CurvePoint(FM0.RR, K(S11[0]), y=K(S11[1]), ring=K)
    Pp0 = CurvePoint(FM0.RR, K(P11[0]), y=K(P11[1]), ring=K)
    J0 = CI0.coleman_integrals_on_basis(Pm0, Pp0)
    Ir0 = []
    for j in range(g):
        lam, dv = class_and_exact(H0, FM0.basis, list(reps0[j]), (S11, P11))
        Ir0.append(sum(K(QQ(lam[i])) * J0[i] for i in range(2*g)) + K(dv))
    info("plain-curve Frobenius and integrals in %.0f s" % (time.time() - t0))
    vd = [((Ir[j] - Ir0[j]).valuation() if Ir[j] - Ir0[j] != 0 else FM.N)
          for j in range(g)]
    check(min(vd) >= cert,
          "the three holomorphic integrals agree to p^%s between the enlarged "
          "and the plain curve -- different E, different d(B), different "
          "Frobenius matrix, same numbers" % min(vd))

    # ------------------------------------------------------------ group (5)
    print("(5) h_p, AND b")
    Iom0 = J[2*g] / 12
    I1, I2 = Ir[2]/324, Ir[1]/324           # dx/Q_y and x dx/Q_y
    hp = Iom0 + c1*I1 + c2*I2
    info("int omega_0            = %s" % Iom0)
    info("int dx/Q_y             = %s" % I1)
    info("int x dx/Q_y           = %s" % I2)
    info("h_p(kappa', delta_11)  = %s" % hp)
    l2, l3 = K(2).log(), K(3).log()
    bval = hp - K(5)/K(2)*l2 + l3
    info("log_p(2) = %s" % l2)
    info("log_p(3) = %s" % l3)
    check(l2.valuation() >= 1 and l3.valuation() >= 1,
          "log_p(2) and log_p(3) are the Iwasawa branch values (log p = 0) at "
          "units, so they have positive valuation")
    print()
    print("        b = h_p(kappa', delta_11) - (5/2) log_13(2) + log_13(3)")
    print("          = %s" % bval)
    print("        certified to p^%d" % prec)
    print()

    # ------------------------------------------------------------ group (6)
    print("(6) WHAT REMAINS")
    info("b is the last entry of B_P = [[H_1, b], [b, H_2]] (E093, E098), so "
         "the quadratic Chabauty function rho is now a known function on all "
         "twenty-one residue disks.")
    info("The check this experiment does NOT do is the symmetry "
         "h_p(kappa', delta_11) = h_p(delta_11, kappa'), which needs "
         "omega_{delta_11} -- poles at the two points over x = -1/11 -- and a "
         "second enlargement r |-> (11x+1) r.  It is the only external test of "
         "b there is, (B5) having removed the rational points as witnesses.")
    info("Then: rho - v over Upsilon on the 20 good disks and the bad one "
         "(E098, E099), and E054's Mordell-Weil sieve.")

    print("=" * 72)
    print("E111 GATE: %s   (%d failures, %.0f s)"
          % ("*** GREEN ***" if not FAIL else "*** RED ***",
             len(FAIL), time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    return 1 if FAIL else 0


sys.exit(int(main()))  # int(): a Sage Integer here makes sys.exit report failure
