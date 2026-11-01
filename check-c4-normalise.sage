r"""
check-c4-normalise.sage --- E110 (Tier 2): the Coleman-Gross normalisation of
the third-kind differential with residue divisor kappa' = [sigma b] - [b].

E109 built omega_0 with residue divisor exactly kappa' and showed that
V = H^1_dR(X) (+) Q_p [omega_0] is Phi-stable with Phi[omega_0] = p[omega_0]
modulo H^1_dR(X).  omega_0 is only one representative of a two-parameter
family; Coleman-Gross needs the one whose class lies in the unit root subspace.
This script fixes it.

THE MAP Psi, DERIVED BEFORE ANY SOURCE WAS OPENED.  Let eta be a class in
H^1_dR(X) and F_eta its global Coleman primitive.  For omega with poles only at
S the assignment

    <omega, eta> := - sum_P Res_P (F_eta omega)

is well defined (the constant in F_eta cancels because the residues of omega
sum to zero), is linear in omega, and restricts to the cup product on
H^1_dR(X); so it defines Psi : H^1_dR(U) -> H^1_dR(X) by duality, with
Psi | H^1_dR(X) = id.  Since phi^* scales the cup product by p on both sides,

    <Psi(phi^* omega), phi^* eta> = <phi^* omega, phi^* eta>
                                  = p <omega, eta> = <phi^* Psi(omega), phi^* eta>,

so Psi is Frobenius-equivariant.  Applying it to alpha := phi^* omega_0 -
p omega_0, which HAS NO RESIDUES and is therefore its own Psi:

    alpha = Psi(alpha) = phi^* Psi(omega_0) - p Psi(omega_0),

    ==>   Psi(omega_0) = (Phi - p)^{-1} alpha,

and alpha is exactly the H^1_dR(X)-part of the last column of E109's 7 x 7
matrix.  The normalisation is then omega_{kappa'} = omega_0 - h with h the
Fil^1-component of Psi(omega_0) in Fil^1 (+) W, because Psi(h) = h.

SOURCE CONSULTED AFTERWARDS, per the project's method policy: [BDMTV2023,
Algorithm 3.5] (arXiv:2101.01862v4) states exactly this -- its step 2
computes Psi(omega) by residues and subtracts sum_{i<g} b_i omega_i, and its
step 3 records the Frobenius equivariance Psi(phi^* omega - p omega) =
phi^* Psi(omega) - p Psi(omega).  We use step 3 to do step 2's job, which
avoids the residue computation entirely.  Their step 2 assumes a basis in which
W is spanned by omega_g, ..., omega_{2g-1}; ours is the graph of tau over the
phase-4 basis, so the Fil^1-component is taken with respect to that splitting.
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
N = ZZ(os.environ.get("E110_N", 12))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))

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


def tau_of(FM, H, K, R=None):
    """tau: the unit root subspace as a graph over Fil^1 in the phase-4 basis.

    R, if given, converts phase-4 coordinates of H's curve into those of
    another curve's phase-4 basis, so that the two runs can be compared.
    """
    g = ZZ(FM.C.genus)
    _, S4 = H.phase4_basis()
    U = matrix(K, S4).transpose().inverse() * matrix(K, FM.unit_root_subspace())
    if R is not None:
        U = matrix(K, R) * U
    bot = U[g:2*g, :]
    return (U * bot.inverse())[0:g, :].transpose(), bot


def main():
    print("=== check-c4-normalise.sage --- E110: the Coleman-Gross "
          "normalisation of omega_{kappa'} ===")
    t00 = time.time()
    g = ZZ(3)

    C0 = TuitmanCurve(Q1, name="C_4")
    C = enlarged("C_4 minus x=1")
    H0, H = Cohomology(C0), Cohomology(C)
    L = C.L
    xL, yL = L(C.x), C.y
    Qy = 4*yL**3 - 12*(xL - 1)**2*yL
    om0 = omega0(C)
    w0 = vector(QQ, H.form_in_E(om0)) * 12          # primitive integral
    reps, S4 = H.phase4_basis()
    reps0, S40 = H0.phase4_basis()

    # ------------------------------------------------------------ group (1)
    print("(1) Psi FROM FROBENIUS EQUIVARIANCE")
    check([H.differential_of(vector(QQ, reps[i]))._f * Qy for i in range(g)]
          == [-72*yL, 324*xL, L(324)]
          and [H0.differential_of(vector(QQ, reps0[i]))._f
               * (4*C0.y**3 - 12*(C0.L(C0.x)-1)**2*C0.y)
               for i in range(g)]
          == [-72*C0.y, 324*C0.L(C0.x), C0.L(324)],
          "the first g of the phase-4 basis are the SAME holomorphic forms on "
          "both curves -- -72 y, 324 x, 324 over dx/Q_y -- so the enlarged and "
          "plain runs are directly comparable, and Fil^1 is spanned by them")
    Mcup = matrix(QQ, H.cup_product_matrix(basis=reps))
    check(Mcup == matrix(QQ, H0.cup_product_matrix(basis=reps0))
          and Mcup == block_matrix([[matrix(QQ, g, g, 0), identity_matrix(QQ, g)],
                                    [-identity_matrix(QQ, g), matrix(QQ, g, g, 0)]]),
          "and the cup product is the standard symplectic form in that basis, "
          "identically on both curves")

    t0 = time.time()
    FM = FrobeniusMatrix(C, H, P_GATE, N)
    K = FM.base
    hb, ib = list(FM.basis), list(FM.im_basis)
    bas = hb + [list(w0)]
    ncols, nE = len(bas), H.dim_E
    cols = [vector(K, [K(QQ(c)) for c in b]) for b in bas]
    dcols = [vector(K, [K(QQ(c)) for c in b]) for b in ib]
    A = matrix(K, nE, ncols + len(dcols),
               lambda i, j: (cols[j][i] if j < ncols
                             else dcols[j - ncols][i]))
    out, worst = [], None
    for b in bas:
        coords = FM.reduce_to_E(FM.frobenius_of_form(FM._form_coefficients(b)))
        sol = A.solve_right(coords)
        rr = A*sol - coords
        vs = [c.valuation() for c in rr if c != 0]
        v = min(vs) if vs else FM.N
        worst = v if worst is None else min(worst, v)
        out.append([sol[j] for j in range(ncols)])
    Phi7 = matrix(K, ncols, ncols, lambda i, j: out[j][i])
    cert = ZZ(FM.certified_precision()[0])
    info("Phi on V computed at N = %s in %.0f s; solve residual p^%s, "
         "certified p^%s" % (N, time.time() - t0, worst, cert))
    Phi6 = Phi7[0:2*g, 0:2*g]
    alpha = vector(K, [Phi7[i, 2*g] for i in range(2*g)])
    check((Phi7[2*g, 2*g] - K(P_GATE)).valuation() >= cert
          and all(Phi7[2*g, j] == 0 for j in range(2*g)),
          "E109's structure reproduced at N = %s: Phi[omega_0] = p [omega_0] + "
          "alpha with alpha in H^1_dR(X), so alpha = phi^* omega_0 - p omega_0 "
          "has no residues and is its own Psi" % N)
    D = Phi6 - K(P_GATE)*identity_matrix(K, 2*g)
    vdet = ZZ(D.determinant().valuation())
    check(vdet < cert,
          "det(Phi - p) has valuation %d < %d, so Psi(omega_0) = (Phi-p)^{-1} "
          "alpha exists and is determined to p^%d.  (p IS an eigenvalue of Phi "
          "in the weight sense -- three eigenvalues have valuation 1 -- which "
          "is why this costs digits and is not free)" % (vdet, cert, cert-vdet))
    prec = cert - vdet

    # ------------------------------------------------------------ group (2)
    print("(2) Psi(omega_0), MEASURED")
    u = D.solve_right(alpha)                        # = Psi(12 omega_0)
    Sm = matrix(K, H.automorphism_matrix(sx=1, sy=-1))
    dodd = [(Sm*u)[i] + u[i] for i in range(2*g)]
    vodd = min([c.valuation() for c in dodd if c != 0] + [FM.N])
    check(vodd >= prec,
          "sigma^* Psi(omega_0) = -Psi(omega_0) to p^%s.  Nothing in "
          "(Phi-p)^{-1} alpha enforced this: it is a check on the whole chain, "
          "and it says Psi(omega_0) lies in the Prym part where kappa' lives"
          % vodd)
    T4 = matrix(K, S4).transpose().inverse()
    u4 = T4 * u                                     # phase-4 coordinates
    vell = min([u4[i].valuation() for i in (0, g) if u4[i] != 0] + [FM.N])
    check(vell >= prec,
          "and its two sigma-EVEN phase-4 coordinates (the elliptic ones, "
          "positions 0 and %d) vanish to p^%s" % (g, vell))
    info("Psi(12 omega_0) in the phase-4 basis:")
    for i in range(2*g):
        info("    b_%d = %s" % (i, u4[i]))

    # ------------------------------------------------------------ group (3)
    print("(3) THE UNIT ROOT SPLITTING ON THE ENLARGED CURVE")
    tau, bot = tau_of(FM, H, K)
    check(ZZ(bot.determinant().valuation()) == 0,
          "the unit root subspace is complementary to Fil^1 (its lower block "
          "is invertible): p = 13 is ordinary, as E094 found on the plain curve")
    vsym = min([(tau[i][j] - tau[j][i]).valuation()
                for i in range(g) for j in range(g)
                if tau[i][j] - tau[j][i] != 0] + [FM.N])
    voff = min([tau[i][j].valuation() for (i, j) in
                [(0, 1), (0, 2), (1, 0), (2, 0)] if tau[i][j] != 0] + [FM.N])
    check(vsym >= cert - 2 and voff >= cert - 2,
          "tau is symmetric to p^%s and block diagonal for sigma to p^%s -- "
          "the two properties E094 measured on the plain curve, reproduced "
          "here, so the enlargement has not moved W" % (vsym, voff))

    t0 = time.time()
    FM0 = FrobeniusMatrix(C0, H0, P_GATE, N)
    FM0.compute(primitives=True)
    info("plain-curve Frobenius with primitives in %.0f s" % (time.time() - t0))
    # The two phase-4 bases agree on Fil^1 but NOT above it: measured, the
    # plain reps 3..5 differ from the enlarged ones by a holomorphic shift.
    dM = H.d_matrix()
    Mf = matrix(QQ, [vector(QQ, list(b)) for b in reps]
                + [dM.column(j) for j in range(dM.ncols())]).transpose()
    Rcols = [list(Mf.solve_right(vector(QQ, H.form_in_E(
        H0.differential_of(vector(QQ, rr))))))[:2*g] for rr in reps0]
    R = matrix(QQ, Rcols).transpose()
    Bsh = R[0:g, g:2*g]
    check(R[0:g, 0:g] == identity_matrix(QQ, g)
          and R[g:2*g, 0:g] == matrix(QQ, g, g, 0)
          and R[g:2*g, g:2*g] == identity_matrix(QQ, g)
          and Bsh.transpose() == Bsh,
          "the plain and enlarged phase-4 bases differ by [[I,B],[0,I]] with B "
          "SYMMETRIC -- the only shape that fixes Fil^1 and the symplectic "
          "form -- so the two runs are comparable only after conjugating by it")
    info("B = %s" % [[str(Bsh[i][j]) for j in range(g)] for i in range(g)])
    tau0, _ = tau_of(FM0, H0, K, R=R)
    vtau = min([(tau[i][j] - tau0[i][j]).valuation()
                for i in range(g) for j in range(g)
                if tau[i][j] - tau0[i][j] != 0] + [FM.N])
    check(vtau >= cert - 2,
          "and then tau agrees with the PLAIN curve's to p^%s: the SAME unit "
          "root subspace, computed twice from two different affine curves.  "
          "Equivalently tau_enlarged = tau_plain + B, an exact rational shift "
          "between two p-adic matrices" % vtau)

    # ------------------------------------------------------------ group (4)
    print("(4) THE NORMALISATION")
    u1 = vector(K, [u4[i] for i in range(g)])
    u2 = vector(K, [u4[g + i] for i in range(g)])
    hfil = u1 - tau.transpose()*u2                  # Fil^1 part of Psi(12 om0)
    info("Fil^1-component of Psi(12 omega_0): %s" % [str(c) for c in hfil])
    vh0 = hfil[0].valuation() if hfil[0] != 0 else FM.N
    check(vh0 >= prec,
          "its elliptic coordinate vanishes to p^%s, so the correction h is "
          "sigma-odd -- it has to be, and nothing imposed it" % vh0)
    # omega_{kappa'} = omega_0 - h/12,  h = sum_{i<g} hfil_i reps[i],
    # reps = (-72 y, 324 x, 324) over dx/Q_y
    c2 = -hfil[1]*324/12
    c1 = -hfil[2]*324/12
    info("omega_{kappa'} = omega_0 + c_1 dx/Q_y + c_2 x dx/Q_y with")
    info("    c_1 = %s" % c1)
    info("    c_2 = %s" % c2)
    psi_new = vector(K, [u4[i] - (hfil[i] if i < g else 0)
                         for i in range(2*g)])
    resid = vector(K, [psi_new[i] for i in range(g)]) \
        - tau.transpose()*vector(K, [psi_new[g+i] for i in range(g)])
    vw = min([c.valuation() for c in resid if c != 0] + [FM.N])
    check(vw >= prec,
          "Psi(omega_{kappa'}) lies in W to p^%s: its Fil^1-component along W "
          "vanishes, which is the Coleman-Gross condition" % vw)

    # ------------------------------------------------------------ group (5)
    print("(5) THE INDEPENDENT CHECK: ABEL-JACOBI")
    info("For eta HOLOMORPHIC the primitive F_eta is analytic everywhere, so "
         "only the two poles of omega_0 contribute and")
    info("    <Psi(omega_0), eta> = -(F_eta(sigma b) - F_eta(b)) "
         "= -int_b^{sigma b} eta.")
    info("In the phase-4 basis the cup product is symplectic, so the left side "
         "is -b_{j+g}: the LAST THREE coordinates of Psi are Coleman integrals.")
    CI = ColemanIntegrals(FM0)
    Pb = CurvePoint(FM0.RR, K(BASE[0]), y=K(BASE[1]), ring=K)
    Ps = CurvePoint(FM0.RR, K(SIGB[0]), y=K(SIGB[1]), ring=K)
    t0 = time.time()
    Ib = CI.coleman_integrals_on_basis(Pb, Ps)
    info("int_b^{sigma b} on the H^1 basis in %.0f s" % (time.time() - t0))
    dM0 = H0.d_matrix()
    Mfull = matrix(QQ, [vector(QQ, list(b)) for b in FM0.basis]
                   + [dM0.column(j) for j in range(dM0.ncols())]).transpose()
    AJ = []
    for j in range(g):
        sol = Mfull.solve_right(vector(QQ, reps0[j]))
        lam = list(sol)[:2*g]
        # sum lam_i omega_i + d(uex) = reps0[j], uex = sum c_m x^d y^i in B;
        # both endpoints are RATIONAL, so uex is evaluated exactly over Q.
        dv = QQ(0)
        for m, (i, d) in enumerate(H0.B_basis):
            c = QQ(list(sol)[2*g + m])
            if c != 0:
                dv += c * (SIGB[0]**d * SIGB[1]**i - BASE[0]**d * BASE[1]**i)
        AJ.append(sum(K(QQ(lam[i])) * Ib[i] for i in range(2*g)) + K(dv))
        info("int_b^{sigma b} reps[%d] = %s" % (j, AJ[j]))
    vE = AJ[0].valuation() if AJ[0] != 0 else FM.N
    check(vE >= prec,
          "the ELLIPTIC form integrates to 0 from b to sigma b, to p^%s: b and "
          "sigma b have the same image on the quotient elliptic curve, and the "
          "Frobenius side said the same thing in group (2)" % vE)
    sgn = None
    devs = []
    for j in (1, 2):
        lhs = -u4[g + j] / 12
        for s in (1, -1):
            d = lhs - s*AJ[j]
            if (d.valuation() if d != 0 else FM.N) >= prec:
                sgn = s if sgn is None else sgn
        devs.append(max([(lhs - s*AJ[j]).valuation()
                         for s in (1, -1)
                         if lhs - s*AJ[j] != 0] + [FM.N]))
    info("best agreement per Prym coordinate: p^%s" % devs)
    ok5 = sgn is not None and all(
        ((-u4[g+j]/12 - sgn*AJ[j]).valuation()
         if -u4[g+j]/12 - sgn*AJ[j] != 0 else FM.N) >= prec for j in (1, 2))
    check(ok5 and sgn == -1,
          "and <Psi(omega_0), reps[j]> = %sint_b^{sigma b} reps[j] for BOTH "
          "Prym coordinates, agreeing to p^%s where p^%d was required.  That "
          "is the sign the derivation predicts, and the two sides come from "
          "two independent routes: (Phi-p)^{-1} alpha on the enlarged curve, "
          "and Algorithm 3.7 on the plain one"
          % ("-" if sgn == -1 else "+", min(devs), prec))

    # ------------------------------------------------------------ group (6)
    print("(6) WHAT REMAINS")
    info("omega_{kappa'} is now pinned.  Tier 3 is the integral")
    info("    h_p(kappa', delta_11) = int_{sigma x_11}^{x_11} omega_{kappa'}")
    info("      = int_{sigma x_11}^{x_11} omega_0 + c_1 I_1 + c_2 I_2,")
    info("with I_1, I_2 the Coleman integrals of dx/Q_y and x dx/Q_y between "
         "the two points -- available from the plain curve as here.  Only the "
         "first term is new, and E109 showed Algorithm 3.7 solves for it on "
         "the 7 x 7 system.")
    info("[BDMTV2023, Algorithm 3.5 step 5] takes a different route to the "
         "same number, via Balakrishnan-Besser Remark 4.9: it needs a second "
         "third-kind differential beta with residue divisor delta_11 and a "
         "sum of residues over X(C_p).  Ours needs neither.")

    print("=" * 72)
    print("E110 GATE: %s   (%d failures, %.0f s)"
          % ("*** GREEN ***" if not FAIL else "*** RED ***",
             len(FAIL), time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    return 1 if FAIL else 0


sys.exit(int(main()))  # int(): a Sage Integer here makes sys.exit report failure
