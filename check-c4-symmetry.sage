r"""
check-c4-symmetry.sage --- E112: the one external test of b.

Coleman-Gross's local height at p is SYMMETRIC, h_p(D_1,D_2) = h_p(D_2,D_1).
E111 computed h_p(kappa', delta_11) by building omega_{kappa'} and integrating
over delta_11.  This script computes h_p(delta_11, kappa') the other way round
-- omega_{delta_11}, integrated over kappa' -- and compares.

WHY THIS AND NOT SOMETHING CHEAPER.  (B5), the observation of E088/E098 that
lambda vanishes at every one of the nine rational points, says precisely that
the rational points impose NO condition on b.  That is why b had to be computed
and why none of them can test it.  The two computations here share the curve,
the prime and the phase-4 basis, and NOTHING else: different affine curve
(r enlarged by (x-1) against (x+1/11)), different differential, different
Frobenius matrix, different endpoints.

THE FORM, IN CLOSED FORM AND IN GENERAL [T].  Let a, y_0 in Q with (a, y_0) on
the curve and y_0 != 0, and let sigma be y |-> -y.  Among the four points over
x = a the two rational ones are (a, +-y_0), and the y-coordinates of the other
two satisfy y^2 = z_2 with

    z_1 := y_0^2,   z_1 + z_2 = 6(a-1)^2   (the quartic in y^2 has that trace).

The adjoint ansatz G(x,y) dx / ((x-a) Q_y) with deg G <= 2 and G even in y --
forced exactly as in E109 -- becomes G = S + eps y^2, and

    res at the degree-2 place = 0        <==>  S + eps z_2 = 0,
    res_{(a,y_0)} = G(a,y_0)/Q_y(a,y_0)  with  Q_y(a,y_0) = 2 y_0 (z_1 - z_2),

so asking for residue +1 at (a, y_0) gives eps = 2 y_0, S = -2 y_0 z_2 and

    omega^{(0)}_{[(a,y_0)] - [(a,-y_0)]} = 2 y_0 (y^2 - z_2) dx / ((x-a) Q_y).

At (a, y_0) = (1, -3) this is -6(y^2+9)dx/((x-1)Q_y), which is E109's omega_0
on the nose; the gate checks that rather than trusting it.
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
N = ZZ(os.environ.get("E112_N", 12))
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
    """FrobeniusMatrix with a basis of any size; see E111 for why this is all."""

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
            Fw = self.frobenius_of_form(self._form_coefficients(b))
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


def enlarged(a):
    """The plane model with r multiplied by (x - a)."""
    C = TuitmanCurve(Q1, name="C_4 minus x=%s" % a)
    C.r = C.r * (X - QQ(a))
    C.degr = C.r.degree()
    return C


def third_kind(C, a, y0):
    """omega with residue +1 at (a, y0) and -1 at (a, -y0); see the header."""
    L = C.L
    xL, yL = L(C.x), C.y
    Qy = 4*yL**3 - 12*(xL - 1)**2*yL
    z1 = QQ(y0)**2
    z2 = 6*(QQ(a) - 1)**2 - z1
    return (2*QQ(y0)*(yL**2 - z2) / ((xL - QQ(a)) * Qy)) * xL.differential()


def class_and_exact(H, basis, target, pts):
    """(coefficients on `basis`, exact part evaluated between two RATIONAL points)."""
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


def local_height(a, y0, endpoints, tag):
    """h_p(D_1, D_2) with D_1 = [(a,y0)] - [(a,-y0)] and D_2 = [Q] - [P].

    The whole of E109 + E110 + E111 for one divisor pair.  Returns
    (h_p, certified exponent, diagnostics).
    """
    g = ZZ(3)
    C = enlarged(a)
    H = Cohomology(C)
    reps, S4 = H.phase4_basis()
    om = third_kind(C, a, y0)
    v0 = vector(QQ, H.form_in_E(om))
    mult = lcm([QQ(c).denominator() for c in v0])
    w0 = v0 * mult
    info("[%s] r enlarged by (x - %s); omega has %s as a primitive multiple"
         % (tag, a, mult))

    t0 = time.time()
    FM = FrobeniusOnV(C, H, P_GATE, N, w0)
    K = FM.base
    Phi7 = FM.compute(primitives=True)
    cert = ZZ(FM.certified_precision()[0])
    info("[%s] Phi on V with primitives: %.0f s, certified p^%s"
         % (tag, time.time() - t0, cert))
    ok = check(all(Phi7[2*g, j] == 0 for j in range(2*g))
               and (Phi7[2*g, 2*g] - K(P_GATE)).valuation() >= cert,
               "[%s] the last row of Phi is (0,...,0,p) to p^%s: the four "
               "points over x = %s reduce to F_13-rational points and a place "
               "that Frobenius fixes, so E109's seven-dimensional collapse "
               "applies here too" % (tag, cert, a))

    Phi6 = Phi7[0:2*g, 0:2*g]
    alpha = vector(K, [Phi7[i, 2*g] for i in range(2*g)])
    D = Phi6 - K(P_GATE)*identity_matrix(K, 2*g)
    prec = cert - ZZ(D.determinant().valuation())
    u = D.solve_right(alpha)
    T4 = matrix(K, S4).transpose().inverse()
    u4 = T4 * u
    Sm = matrix(K, H.automorphism_matrix(sx=1, sy=-1))
    check(min([c.valuation() for c in (Sm*u + u) if c != 0] + [FM.N]) >= prec
          and all(u4[i] == 0 or u4[i].valuation() >= prec for i in (0, g)),
          "[%s] Psi(omega) is sigma-odd with no elliptic component" % tag)
    Sc = H.adapted_change_of_basis()
    Ucols = []
    for k in range(g, 2*g):
        v = vector(K, [K(QQ(c)) for c in Sc.row(k)])
        for _ in range(cert):
            v = Phi6 * v
        Ucols.append(v)
    U = T4 * matrix(K, Ucols).transpose()
    bot = U[g:2*g, :]
    tau = (U * bot.inverse())[0:g, :].transpose()
    hfil = vector(K, [u4[i] for i in range(g)]) \
        - tau.transpose()*vector(K, [u4[g+i] for i in range(g)])
    c2 = -hfil[1]*324/mult
    c1 = -hfil[2]*324/mult
    info("[%s] c_1 = %s" % (tag, c1))
    info("[%s] c_2 = %s" % (tag, c2))

    CI = ColemanIntegrals(FM)
    (Pa, Pb) = endpoints
    Pstart = CurvePoint(FM.RR, K(Pa[0]), y=K(Pa[1]), ring=K)
    Pend = CurvePoint(FM.RR, K(Pb[0]), y=K(Pb[1]), ring=K)
    check(CI.f_converges_at(Pstart) and CI.f_converges_at(Pend),
          "[%s] both endpoints are good points of this enlarged curve" % tag)
    J = CI.coleman_integrals_on_basis(Pstart, Pend)
    Ir = []
    for j in range(g):
        lam, dv = class_and_exact(H, FM.basis, list(reps[j]), endpoints)
        Ir.append(sum(K(QQ(lam[i])) * J[i] for i in range(2*g + 1)) + K(dv))
    check(Ir[0] == 0 or Ir[0].valuation() >= cert,
          "[%s] the sigma-EVEN holomorphic form integrates to 0 between the "
          "endpoints: they have the same image on the quotient elliptic curve"
          % tag)
    hp = J[2*g]/mult + c1*Ir[2]/324 + c2*Ir[1]/324
    info("[%s] h_p = %s   (certified p^%d)" % (tag, hp, prec))
    return hp, prec


def main():
    print("=== check-c4-symmetry.sage --- E112: h_p(D_1,D_2) = h_p(D_2,D_1) ===")
    t00 = time.time()

    # ------------------------------------------------------------ group (1)
    print("(1) THE GENERAL THIRD-KIND FORM, AND E109 AS A SPECIAL CASE")
    Ck = enlarged(1)
    Hk = Cohomology(Ck)
    L = Ck.L
    xL, yL = L(Ck.x), Ck.y
    Qy = 4*yL**3 - 12*(xL - 1)**2*yL
    omk = third_kind(Ck, QQ(1), QQ(-3))
    check(omk._f == (-6*(yL**2 + 9) / ((xL - 1) * Qy)),
          "the general formula 2 y_0 (y^2 - z_2) dx / ((x-a) Q_y) with "
          "z_2 = 6(a-1)^2 - y_0^2 gives E109's omega_0 exactly at "
          "(a, y_0) = (1, -3): same element of the function field, not the "
          "same class")
    pl = Hk.candidate_places()
    Pb = [P for P in pl if P.degree() == 1 and (xL - 1).valuation(P) > 0
          and (yL - 3).valuation(P) > 0]
    Ps = [P for P in pl if P.degree() == 1 and (xL - 1).valuation(P) > 0
          and (yL + 3).valuation(P) > 0]
    check(len(Pb) == 1 and len(Ps) == 1
          and omk.residue(Pb[0]) == -1 and omk.residue(Ps[0]) == 1
          and all(omk.residue(P) == 0 for P in pl if P not in Pb + Ps),
          "and its residue divisor is kappa' = [sigma b] - [b], checked with "
          "Sage's residue() over Q")

    Cd = enlarged(QQ(-1)/11)
    Hd = Cohomology(Cd)
    Ld = Cd.L
    xd, yd = Ld(Cd.x), Cd.y
    omd = third_kind(Cd, QQ(-1)/11, QQ(15)/11)
    pld = Hd.candidate_places()
    Pp = [P for P in pld if P.degree() == 1 and (xd + QQ(1)/11).valuation(P) > 0
          and (yd - QQ(15)/11).valuation(P) > 0]
    Pm = [P for P in pld if P.degree() == 1 and (xd + QQ(1)/11).valuation(P) > 0
          and (yd + QQ(15)/11).valuation(P) > 0]
    check(len(Pp) == 1 and len(Pm) == 1
          and omd.residue(Pp[0]) == 1 and omd.residue(Pm[0]) == -1
          and all(omd.residue(P) == 0 for P in pld if P not in Pp + Pm),
          "the same formula at (a, y_0) = (-1/11, 15/11) has residue divisor "
          "EXACTLY delta_11 = [x_11] - [sigma x_11]: +1, -1, and 0 at every "
          "other place, including the degree-2 place y^2 = 639/121 over "
          "x = -1/11")
    z2d = 6*(QQ(-1)/11 - 1)**2 - (QQ(15)/11)**2
    check(z2d == QQ(639)/121 and not QQ(639).is_square(),
          "that degree-2 place is genuinely of degree 2 over Q -- "
          "z_2 = 639/121 and 639 = 9*71 is not a square -- so it carries no "
          "rational point to spoil the residue divisor")
    rd = Cd.r.change_ring(GF(P_GATE))
    check(rd.is_squarefree(),
          "and (x + 1/11) r stays separable mod 13 (Tuitman's Assumption 1), "
          "so the second enlargement is as legitimate as the first")

    # ------------------------------------------------------------ group (2)
    print("(2) h_p(kappa', delta_11): E111's ROUTE, RERUN HERE")
    hp1, pr1 = local_height(QQ(1), QQ(-3), (S11, P11), "kappa'")

    # ------------------------------------------------------------ group (3)
    print("(3) h_p(delta_11, kappa'): THE OTHER WAY ROUND")
    hp2, pr2 = local_height(QQ(-1)/11, QQ(15)/11, (BASE, SIGB), "delta_11")

    # ------------------------------------------------------------ group (4)
    print("(4) THE SYMMETRY")
    prec = min(pr1, pr2)
    d = hp1 - hp2
    vd = d.valuation() if d != 0 else N
    info("h_p(kappa', delta_11) = %s" % hp1)
    info("h_p(delta_11, kappa') = %s" % hp2)
    check(vd >= prec,
          "the two agree to p^%s, where p^%d was certified.  Coleman-Gross's "
          "pairing IS symmetric, and the two sides of this identity share the "
          "curve, the prime and the phase-4 basis and nothing else: different "
          "affine curve, different differential, different Frobenius matrix, "
          "different endpoints.  This is the only external test of b there is"
          % (vd, prec))
    K = hp1.parent()
    bval = hp1 - K(5)/K(2)*K(2).log() + K(3).log()
    print()
    print("        b = %s" % bval)
    print("          certified to p^%d" % prec)
    print()

    # ------------------------------------------------------------ group (5)
    print("(5) WHAT REMAINS")
    info("Nothing in the inputs.  B_P is complete and checked, rho is a known "
         "function on all twenty-one residue disks (E098, E099), Upsilon is "
         "closed at four elements (E104).")
    info("The endgame: solve rho = v for each of the four v in Upsilon on the "
         "twenty good disks and the bad one, and cut the solution set down to "
         "C_4(Q) with E054's Mordell-Weil sieve.")

    print("=" * 72)
    print("E112 GATE: %s   (%d failures, %.0f s)"
          % ("*** GREEN ***" if not FAIL else "*** RED ***",
             len(FAIL), time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    return 1 if FAIL else 0


sys.exit(int(main()))  # int(): a Sage Integer here makes sys.exit report failure
