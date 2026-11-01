# check-xs13-frob.sage --- E065 (E048 Phase 4) GATE, part 11.
#
# E076.  §5 of [BDM+19] on X = X_s(13) at p = 17: the FROBENIUS half.  E075
# reproduced §6.1's published Hodge data exactly over Q; everything p-adic in
# §5 -- the Frobenius matrix, (22), (23), (24) and Lemma 5.4 -- was untouched
# there, and this gate runs it on somebody else's curve, basis and
# correspondences for the first time.
#
# WHAT IS NEW HERE, and why it is worth a section of its own.  E066-E074 were
# checked against themselves, against point counts, against Sage and against
# internal consistency; E075 added §6.1's printed numbers, but those test only
# the Hodge side.  The Frobenius side has exactly two external tests available
# without §6.2's second chart, and both are run here:
#
#   * §4.1(a), F^T Z F = p Z.  Our F comes from our port of [Tui16, Tui17];
#     Z_1 and Z_2 are printed in §6.1 and were produced from Hecke operators by
#     somebody else.  The identity is a genuine coincidence test, and it is the
#     one condition of §4.1 that E075 could not run.  It also re-tests E071 (Z
#     is the CLASS Z_e M^-1, not the endomorphism) on a second curve: with the
#     endomorphism matrix the (3,2) block of the gauge equation does not close.
#
#   * THE QUADRATIC CHABAUTY RELATION ITSELF.  For x in X(Q),
#         theta_Z(x) = B(E_1(x) (x)_{K_p} E_{2,Z}(x)),
#     with E_1 = AJ_b, E_{2,Z} = E_Z(AJ_b) + c (Lemma 4.9 = ht_qcpair), and
#     -- this is the point -- with ONE B for BOTH correspondences, B being
#     Nekovar's global height, which does not depend on Z.  X_s(13) has
#     potentially good reduction everywhere, so Upsilon = {0} and there is no
#     unknown constant.  So every row (theta_Z(x), Psi(Z,x)) in Q_p^4 built
#     from a rational point x lies in the SAME 3-dimensional subspace
#     {(B(v), psi(v)) : v in E}, whichever x and whichever Z it came from:
#     dim_{Q_p} E = 3.  ]U_1[ has four rational points, of which the base
#     point gives the zero row, so there are 6 rows of rank 3: THREE FREE
#     CHECKS.  They test gamma_phi, the normalisation of theta and the
#     K-equivariance of the splitting at once, and nothing before E076 tested
#     any of them.
#
#     Stating it as a rank rather than as "solve for B from three rows and
#     check the other three" costs nothing and does not depend on which three
#     rows happen to span: with m nonzero rows it is exactly m - 3 free checks,
#     however the rank is distributed over the two correspondences.  Check (7)
#     also measures the determinant of the three Z_1 rows on their own, which
#     is what [BDM+19]'s own T_i needs to be nonzero.
#
# THE FOUR RATIONAL POINTS OF ]U_1[.  Of the seven known points, P_4 and P_6
# are at infinity of the chart and P_0 = (1,1) is the branch point x = 1 (both
# Q_y and r vanish there), so ]U_1[ contains P_1, P_2 = b, P_3, P_5 -- exactly
# the four rows §6.1's table prints in bold.  [BDM+19] build their T_i from
# P_1, P_3, P_4 and get their free checks at P_2 and P_5; we cannot reach P_4
# without §6.2's second chart, and the rank formulation above is what makes
# that harmless.
#
# THE SPLITTING.  Remark 4.11 (rk:ht_equiv) needs a K-EQUIVARIANT splitting of
# the Hodge filtration, K = Q(zeta_7)^+, or the height does not factor through
# (x)_{K_p} and B has 6 unknowns instead of 3 -- and then the 6 equations
# determine it and there is nothing left to check.  §6.1.1 says a K-equivariant
# splitting was used but not WHICH: check (6) measures that the K-equivariant
# splittings form a 3-PARAMETER family, so the choice is an input the paper
# does not print.  Two members are run here (the unit root splitting, which is
# canonical, and the trace-averaged coordinate splitting, which is rational and
# is what "use iota to compute a K-equivariant splitting" most plausibly
# means); both must pass, with DIFFERENT B, and the coordinate splitting of
# §6.1's own basis -- which is not K-equivariant -- must fail.
#
# THE CHECKS.
#   (1) SETUP, exact: the published basis, the published Z_i, and the eta_i
#       E075 settled (eta_{Z_2} as CORRECTED there, the printed one being a
#       misprint).  The Hodge side must reproduce §6.1's beta_Fil and
#       gamma_Fil -- E075's result, re-run here through LocalHeight's sign
#       convention rather than through the raw solver.
#   (2) THE FROBENIUS MATRIX: chi(T) against #X(F_q) for q = 17, 17^2, 17^3,
#       and the Weil functional equation.  Independent of everything else.
#   (3) §4.1(a) F^T Z F = p Z, for both correspondences.
#   (4) (22), (23), (24): the gauge equation checked locally, g's constant c
#       (E072: the paper omits it), the residual mu = 0, and theta(b) = 0.
#   (5) E_2 = E_Z(E_1) + c AS AN IDENTITY OF FUNCTIONS on ]U_1[ (Lemma 4.9
#       (ii)): solve for the matrix from four Teichmuller points, check it on
#       three more, and compare it with the endomorphism Z M that §6.1's own
#       matrices define.  This is the first test of beta_phi against anything
#       outside the pipeline that produced it.
#   (6) THE K-STRUCTURE, exact over Q: Z_1 M and Z_2 M generate the cyclic
#       cubic field of discriminant 49, i.e. Q(zeta_7)^+; Fil^1 is stable; the
#       K-equivariant complements of Fil^1 form a 3-parameter family and every
#       one of them is automatically isotropic for the cup product.
#   (7) THE QUADRATIC CHABAUTY RELATION as a rank, for each of the two
#       K-equivariant splittings, with the coordinate splitting of §6.1's own
#       basis -- which is NOT K-equivariant, check (6) measures that -- as the
#       NEGATIVE CONTROL, where the rank must come out 4.
#
# NOT DONE HERE: §6.1's table of the zeroes of det T_i to O(17^5).  That needs
# theta as a power series on all 17 disks of U_1 and a root count, and -- see
# check (6) -- it needs [BDM+19]'s splitting, which §6 does not print.  It is
# E077.  §6.2's second chart and §6.3's leftover disk remain out of scope.
#
# Run: sage check-xs13-frob.sage        (E076_N=<n> to change the precision)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, teichmuller_point

t_start = time.time()
fails = []


def check(ok, msg):
    print("   %s  %s" % (msg, "ok" if ok else "*** NO ***"))
    if not ok:
        fails.append(msg)
    sys.stdout.flush()
    return ok


def vz(a, N):
    """Valuation of a p-adic number, N for an exact zero."""
    return ZZ(N) if a == 0 else ZZ(a.valuation())


# ------------------------------------------------------------------ the data

P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
QUARTIC = (Y**4 + 5*X**4 - 6*X**2*Y**2 + 6*X**3*Z + 26*X**2*Y*Z + 10*X*Y**2*Z
           - 10*Y**3*Z - 32*X**2*Z**2 - 40*X*Y*Z**2 + 24*Y**2*Z**2 + 32*X*Z**3
           - 16*Y*Z**3)
R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Qxy = QUARTIC(x, y, 1)

OMEGA_NUM = [R2(1), x, y,
             -160*x**4/3 + 736*x**3/3 - 16*x**2*y/3 + 436*x**2/3 - 440*x*y/3
             + 68*y**2/3,
             -80*x**3/3 + 44*x**2 - 40*x*y/3 + 68*y**2/3 - 32,
             -16*x**2*y + 28*x**2 + 72*x*y - 4*y**2 - 160*x/3 + 272/3]
Z1 = matrix(QQ, [[0, -976, -1104, 10, -6, 18], [976, 0, -816, -3, 1, 3],
                 [1104, 816, 0, -3, 3, -11], [-10, 3, 3, 0, 0, 0],
                 [6, -1, -3, 0, 0, 0], [-18, -3, 11, 0, 0, 0]])
Z2 = matrix(QQ, [[0, 112, -656, -6, 6, 6], [-112, 0, -2576, 15, 9, 27],
                 [656, 2576, 0, 3, 3, -3], [6, -15, -3, 0, 0, 0],
                 [-6, -9, -3, 0, 0, 0], [-6, -27, 3, 0, 0, 0]])
# eta as E075 settled it: eta_{Z_1} exactly as printed, eta_{Z_2} corrected.
ETA_NUM = {"Z_1": -(44*x**2 + 148*x*y/3 + 8*y**2),
           "Z_2": -(40*x**2 - 148*x*y - 36*y**2)}
BETA_FIL_PUB = {"Z_1": [QQ(0), QQ(1)/2, QQ(1)/2],
                "Z_2": [QQ(0), QQ(-1)/2, QQ(-5)/2]}
GAMMA_FIL_PUB = {"Z_1": 5*y/6 + 3*x/2, "Z_2": -5*y/6 - 15*x/2}

BASE = (QQ(0), QQ(0))                       # P_2
# the rational points of ]U_1[; P_0 is the branch point x = 1, P_4 and P_6 are
# at infinity of this chart.
RAT = [("P_1", (QQ(1)/2, QQ(1)/2)), ("P_3", (QQ(-3)/2, QQ(3)/2)),
       ("P_5", (QQ(0), QQ(2)))]

p = 17
N = ZZ(os.environ.get("E076_N", 10))
# The smallest thing this gate has to resolve is a determinant of valuation 3
# (the three Z_1 rows, and the four Teichmuller points of check (5)), and the
# negative control has to be told apart from a vanishing 4x4 minor, which sits
# at v_p = 3 as well.  With the two digits Propositions 3.7 and 3.8 allow the
# reduction to lose, N = 8 is the first precision at which any of that is
# meaningful: below it the gate goes red on arithmetic, not on mathematics.
if N < 8:
    raise ValueError(
        "N = %s is too small for this gate: the quantities it has to resolve "
        "have valuation 3 and the certified precision would be %s.  Use "
        "E076_N >= 8 (the recorded runs are N = 8 and N = 10)." % (N, N - 2))

# ------------------------------------------------------------- (1) the setup

print("=" * 72)
print("=== check-xs13-frob.sage --- E076: [BDM+19] §5 on X_s(13) at p = 17 ===")
print("=" * 72)
print("(1) the setup: §6.1's basis, correspondences and eta")

t0 = time.time()
C = TuitmanCurve(Qxy, name="X_s(13)")
H = Cohomology(C)
g, n = ZZ(C.genus), 2 * ZZ(C.genus)
L, xL, yL = C.L, C.L(C.x), C.y
dxL = xL.differential()


def toL(f):
    return sum(QQ(c) * xL**ZZ(e[0]) * yL**ZZ(e[1]) for e, c in f.dict().items())


QyL = toL(Qxy.derivative(y))


def omega_of(fnum):
    return (toL(fnum) / QyL) * dxL


reps = [H.form_in_E(omega_of(f)) for f in OMEGA_NUM]
bas, _ = H.H1X_basis()
dM = H.d_matrix()
cols = [vector(QQ, list(b)) for b in bas] \
    + [dM.column(j) for j in range(dM.ncols())]
Msolve = matrix(QQ, cols).transpose()
S = matrix(QQ, [list(Msolve.solve_right(vector(QQ, v)))[:n] for v in reps])
check(S.determinant() != 0, "the six printed differentials are a basis")
ETA = dict((k, H.form_in_E(omega_of(v))) for k, v in ETA_NUM.items())
print("   genus %s, deg r = %s, d_x = %s, p = %s, N = %s  (%.1f s)"
      % (g, C.degr, C.dx, p, N, time.time() - t0))
check(QQ(C.r(BASE[0])).valuation(p) == 0,
      "the base point b = P_2 = (0,0) is a good point (v_p(r(0)) = 0)")

# the cup product on this basis (E075: it is -J here)
t0 = time.time()
Mcup = H.cup_product_matrix(basis=reps)
J = matrix(QQ, n, n, lambda i, j: QQ(1) if (i < g and j == i + g) else
           (QQ(-1) if (i >= g and j == i - g) else QQ(0)))
check(Mcup == J or Mcup == -J, "the cup product is the standard symplectic form")
print("   cup product = %sJ  (%.0f s)"
      % ("" if Mcup == J else "-", time.time() - t0))

# --------------------------------------------------- (6) the K-structure, exact

print("-" * 72)
print("(6) the K-structure of §6.1.1, exact over Q")

AZ = {"Z_1": Z1 * Mcup, "Z_2": Z2 * Mcup}
Kcyc = CyclotomicField(7).subfields(3)[0][0]
for nm in ("Z_1", "Z_2"):
    A = AZ[nm]
    mp = A.minpoly()
    check(mp.degree() == 3 and mp.is_irreducible(),
          "%s M has an irreducible cubic minimal polynomial (%s)" % (nm, mp))
    Kf = NumberField(mp.change_ring(QQ), 'a')
    check(Kf.discriminant() == 49 and Kf.is_isomorphic(Kcyc),
          "%s M generates the cyclic cubic field of discriminant 49 = "
          "Q(zeta_7)^+" % nm)
    check(A.submatrix(g, 0, g, g) == 0,
          "%s M preserves Fil^1 = <omega_0, omega_1, omega_2>" % nm)
alg = matrix(QQ, [matrix.identity(QQ, n).list(), AZ["Z_1"].list(),
                  AZ["Z_2"].list()])
prods = matrix(QQ, [matrix.identity(QQ, n).list(), AZ["Z_1"].list(),
                    AZ["Z_2"].list()]
               + [(AZ[a] * AZ[b]).list()
                  for a in ("Z_1", "Z_2") for b in ("Z_1", "Z_2")])
check(alg.rank() == 3 and prods.rank() == 3
      and AZ["Z_1"] * AZ["Z_2"] == AZ["Z_2"] * AZ["Z_1"],
      "span(I, Z_1 M, Z_2 M) is a commutative cubic algebra = K")


def complement_system(A, isotropic):
    """The linear system for W = <columns [C; I]> stable under A.

    W is a complement of Fil^1 in H^1_dR; A-stability is the Sylvester
    equation A11 C - C A22 = -A12, and isotropy for J is C = C^T.
    """
    A11, A12 = A.submatrix(0, 0, g, g), A.submatrix(0, g, g, g)
    A22 = A.submatrix(g, g, g, g)
    rows, rhs = [], []
    for i in range(g):
        for j in range(g):
            row = [QQ(0)] * (g * g)
            for k in range(g):
                row[k * g + j] += A11[i, k]
                row[i * g + k] -= A22[k, j]
            rows.append(row)
            rhs.append(-A12[i, j])
    if isotropic:
        for i in range(g):
            for j in range(i + 1, g):
                row = [QQ(0)] * (g * g)
                row[i * g + j], row[j * g + i] = QQ(1), QQ(-1)
                rows.append(row)
                rhs.append(QQ(0))
    return matrix(QQ, rows), vector(QQ, rhs)


A1, b1 = complement_system(AZ["Z_1"], False)
A2, b2 = complement_system(AZ["Z_1"], True)
sol1 = A1.solve_right(b1)
sol2 = A2.solve_right(b2)
d1 = A1.right_kernel().dimension()
d2 = A2.right_kernel().dimension()
check(d1 == 3, "the K-equivariant complements of Fil^1 form a 3-parameter "
      "family (so §6.1.1's splitting is an unprinted input)")
check(d2 == 3, "every K-equivariant complement is automatically ISOTROPIC for "
      "the cup product (Rosati symmetry), so symmetry of the height costs "
      "nothing")


def splitting_from_C(Cm, ring=QQ):
    """(s_1, s_2) on V_dR from a complement W = <[C; I]> of Fil^1.

    Fil^0 V_dR = Ann(Fil^1) is the last g coordinates and Ann(W) is a
    complement of it; s_2 projects onto Fil^0 V_dR along Ann(W), s_1 = 1 - s_2.
    """
    Wm = matrix(ring, n, g, lambda i, j:
                Cm[i, j] if i < g else (ring(1) if i - g == j else ring(0)))
    Fil1 = matrix(ring, n, g, lambda i, j: ring(1) if i == j else ring(0))
    Pm = Fil1.augment(Wm)                       # H^1_dR = Fil^1 (+) W
    B = Pm.inverse().transpose()                # columns: the dual basis
    Qm = matrix(ring, n, n, lambda i, j: ring(1) if (i == j and i >= g)
                else ring(0))
    s2 = B * Qm * B.inverse()
    return matrix.identity(ring, n) - s2, s2


C_rat = matrix(QQ, g, g, list(sol2))
s1_rat, s2_rat = splitting_from_C(C_rat)
check(s2_rat * s2_rat == s2_rat and s1_rat + s2_rat == matrix.identity(QQ, n),
      "the rational K-equivariant splitting is a pair of projectors")
BA = AZ["Z_1"].transpose()                      # the action on V_dR
check(s2_rat * BA == BA * s2_rat,
      "it commutes with the action of K on V_dR")
s2_coord = matrix(QQ, n, n, lambda i, j: QQ(1) if (i == j and i >= g)
                  else QQ(0))
check(s2_coord * BA != BA * s2_coord,
      "the coordinate splitting of §6.1's basis is NOT K-equivariant "
      "(the negative control of check (8) is not vacuous)")

# ------------------------------------------------ (2) the Frobenius matrix

print("-" * 72)
print("(2) the Frobenius matrix of X_s(13) at p = 17")
t0 = time.time()
FM = FrobeniusMatrix(C, H, p, N)
FM.compute(primitives=True)
cert = ZZ(FM.certified_precision()[0])
print("   Phi computed (%.0f s), N = %s, certified precision %s"
      % (time.time() - t0, N, cert))
sys.stdout.flush()

chi = FM.chi()
chi = chi[0] if isinstance(chi, tuple) else chi
rev = chi.parent()(list(reversed(chi.list())))
co = rev.list()
if check(rev.degree() == n, "chi(T) has degree 2g = %s (the rounding of Phi "
         "to Z succeeded)" % n):
    check(co[n] == 1 and co[0] == p**g
          and all(co[g - k] == p**k * co[g + k] for k in (1, 2, 3)),
          "the Weil functional equation holds for chi")
    rts = rev.roots(QQbar, multiplicities=False)
    for k in (1, 2, 3):
        q = p**k
        Sq = PolynomialRing(GF(q), ['X', 'Y', 'Z'])
        cnt = ZZ(len(Curve(Sq(QUARTIC)).rational_points()))
        pred = q + 1 - sum(a**k for a in rts)
        check(pred == cnt, "#X(F_%s) = %s matches chi" % (q, cnt))
print("   chi(T) = %s  (%.0f s)" % (rev, time.time() - t0))
sys.stdout.flush()

Kp = FM.base
Sk = matrix(Kp, [[Kp(QQ(c)) for c in row] for row in S.rows()])
Sik = matrix(Kp, [[Kp(QQ(c)) for c in row] for row in S.inverse().rows()])
Fmat = Sk * FM.Phi.transpose() * Sik


def toKp(Mq):
    return matrix(Kp, [[Kp(QQ(c)) for c in row] for row in Mq.rows()])


# THE UNIT ROOT SPLITTING.  phi acts on coordinates in the basis omega by
# F^T, so iterating it kills the slope 1 part; at an ordinary prime the limit
# of (F^T)^m applied to the last g basis vectors spans the unit root subspace,
# which is Frobenius-stable, hence stable under End(J) (o) Q -- so it is
# K-equivariant for free, and it is the one canonical choice.
Ft = Fmat.transpose()
Wur = matrix(Kp, [list(Ft**cert * vector(Kp, [Kp(1) if k == g + j else Kp(0)
                                              for k in range(n)]))
                  for j in range(g)]).transpose()
bot = Wur.submatrix(g, 0, g, g)
check(vz(bot.determinant(), N) < cert,
      "the unit root subspace is complementary to Fil^1 (p = 17 is ordinary)")
C_ur = Wur.submatrix(0, 0, g, g) * bot.inverse()
s1_ur, s2_ur = splitting_from_C(C_ur, ring=Kp)
Aur = toKp(AZ["Z_1"])
dev = (Aur.submatrix(0, 0, g, g) * C_ur + Aur.submatrix(0, g, g, g)
       - C_ur * Aur.submatrix(g, g, g, g))
check(min([N] + [vz(c, N) for c in dev.list()]) >= cert - 2,
      "the unit root subspace is K-stable, so the unit root splitting is "
      "K-equivariant (Sylvester residual v_p = %s)"
      % min([N] + [vz(c, N) for c in dev.list()]))
check(min([N] + [vz(c, N) for c in (C_ur - C_ur.transpose()).list()])
      >= cert - 2,
      "and isotropic for the cup product, as check (6) predicts")

# ------------------------------------------------------------ (3) §4.1 (a)

print("-" * 72)
print("(3) §4.1 (a): F^T Z F = p Z  -- the condition E075 could not run")
for nm, Zm in (("Z_1", Z1), ("Z_2", Z2)):
    Zk = matrix(Kp, [[Kp(QQ(c)) for c in row] for row in Zm.rows()])
    D = Fmat.transpose() * Zk * Fmat - p * Zk
    v = min([N] + [vz(c, N) for c in D.list()])
    check(v >= cert, "%s: v_p(F^T Z F - p Z) = %s >= %s" % (nm, v, cert))

# ---------------------------------------------- the Frobenius structure itself

print("-" * 72)
print("(4) (22), (23), (24) and the Hodge side")
FS, LH = {}, {}
for nm, Zm in (("Z_1", Z1), ("Z_2", Z2)):
    t0 = time.time()
    fs = FrobeniusStructure(C, H, p, N, BASE, FM=FM, reps=reps, S=S, Z=Zm,
                            eta=ETA[nm])
    fs.solve()
    FS[nm] = fs
    print("   %s: (22) solved (%.0f s), Zscale = %s" % (nm, time.time() - t0,
                                                        fs.Zscale))
    sys.stdout.flush()
    check(fs.mu is None or all(vz(c, N) >= cert for c in fs.mu),
          "%s: the third-kind residual mu of (22) vanishes" % nm)
    check(any(c != 0 for c in fs.c),
          "%s: g's integration constant c is NONZERO (E072: (22) omits it)"
          % nm)
    t0 = time.time()
    lh = LocalHeight(fs, base=BASE, s1=s1_rat, s2=s2_rat)
    LH[nm] = lh
    check([QQ(c) for c in lh.beta_fil][g:] == BETA_FIL_PUB[nm],
          "%s: beta_Fil = %s reproduces §6.1" % (nm, BETA_FIL_PUB[nm]))
    check(lh.gamma_fil == toL(GAMMA_FIL_PUB[nm]),
          "%s: gamma_Fil reproduces §6.1" % nm)
    print("   %s: gamma_Fil = %s   (%.0f s)"
          % (nm, lh.gamma_fil, time.time() - t0))
    sys.stdout.flush()


def point_of(fs, xy):
    return CurvePoint(fs.RR, fs.K(xy[0]), y=fs.K(xy[1]))


t0 = time.time()
bp = FS["Z_1"].base_point
for nm in ("Z_1", "Z_2"):
    th = LH[nm].theta(bp)
    check(vz(th, N) >= cert, "%s: theta(b) = 0 (v_p = %s)" % (nm, vz(th, N)))
print("   theta(b) (%.0f s)" % (time.time() - t0))
sys.stdout.flush()

# ------------------------------------------- (5) E_2 = E_Z(E_1) + c on ]U_1[

print("-" * 72)
print("(5) E_2 = E_Z(E_1) + c as an identity of functions on ]U_1[")

# seven Teichmuller points of U_1 disks, avoiding the branch disk (1,1)
DISKS = [(0, 2), (4, 1), (5, 15), (7, 6), (8, 0), (9, 13), (13, 9)]
teich = []
for (a, b) in DISKS:
    P0 = CurvePoint(FS["Z_1"].RR, FS["Z_1"].K(a), y=FS["Z_1"].K(b))
    teich.append(FS["Z_1"].teichmuller(P0))
print("   %d Teichmuller points built (%.0f s)" % (len(teich),
                                                   time.time() - t0))
sys.stdout.flush()

RAW = {}                 # (name of Z) -> [(label, alpha, beta, gamma, gfil)]
allpts = [("T%d" % i, P) for i, P in enumerate(teich)] \
    + [(nm, point_of(FS["Z_1"], xy)) for nm, xy in RAT]
for nm in ("Z_1", "Z_2"):
    lh, out = LH[nm], []
    for lab, P in allpts:
        t1 = time.time()
        out.append((lab,) + tuple(lh.frob_data(P)))
        print("      %s at %s (%.0f s)" % (nm, lab, time.time() - t1))
        sys.stdout.flush()
    RAW[nm] = out


def E1E2(nm, row):
    """(E_1, E_2) in H^0(X, Omega^1)^*, in the basis dual to omega_0..omega_2.

    E_1 = AJ_b(x) is alpha_phi restricted to Fil^1, i.e. its first g
    coordinates in the dual basis of §4.2.  E_2 is the class of the extension
    of V_dR by Q_p(1), i.e. of beta_phi - beta_Fil in H^1_dR/Fil^1 -- the LAST
    g coordinates -- carried into (Fil^1)^* by the cup product, which is +-J
    here and so contributes an overall sign that B absorbs.
    """
    _, alpha, beta_phi, _, _ = row
    bf = LH[nm].beta_fil
    return (vector(Kp, [alpha[i] for i in range(g)]),
            vector(Kp, [beta_phi[g + i] - Kp(QQ(bf[g + i]))
                        for i in range(g)]))


for lab in [r[0] for r in RAW["Z_1"]][len(teich):]:
    r = [q for q in RAW["Z_1"] if q[0] == lab][0]
    E1, E2 = E1E2("Z_1", r)
    print("   %s: v_p(E_1) = %s, v_p(E_2) = %s"
          % (lab, [vz(c, N) for c in E1], [vz(c, N) for c in E2]))

for nm in ("Z_1", "Z_2"):
    rows = RAW[nm]
    dat = [(r[0],) + E1E2(nm, r) for r in rows]
    # solve E_2 = R E_1 + c from four of the points, the best conditioned four
    best, bv = None, N + 1
    for sub in Subsets(range(len(dat)), 4):
        Am = matrix(Kp, [list(dat[i][1]) + [Kp(1)] for i in sub])
        v = vz(Am.determinant(), N)
        if v < bv:
            best, bv = list(sub), v
    Amat = matrix(Kp, [list(dat[i][1]) + [Kp(1)] for i in best])
    Bmat = matrix(Kp, [list(dat[i][2]) for i in best])
    check(bv < cert - 1,
          "%s: four of the %d points give an invertible system, %s "
          "(v_p(det) = %s)"
          % (nm, len(dat), [dat[i][0] for i in best], bv))
    Xsol = Amat.solve_right(Bmat)
    R = Xsol.submatrix(0, 0, g, g).transpose()
    cvec = vector(Kp, list(Xsol.row(g)))
    worst = N
    for i in range(len(dat)):
        if i in best:
            continue
        d = dat[i][2] - R * dat[i][1] - cvec
        worst = min([worst] + [vz(cc, N) for cc in d])
    check(worst >= cert - 2,
          "%s: E_2 - E_Z(E_1) - c = 0 at the remaining %d points (v_p = %s)"
          % (nm, len(dat) - 4, worst))
    Rq = toKp(AZ[nm].submatrix(0, 0, g, g).transpose())
    same = min([N] + [vz(c, N) for c in (R - Rq).list()])
    opp = min([N] + [vz(c, N) for c in (R + Rq).list()])
    check(max(same, opp) >= cert - 2,
          "%s: E_Z is %s the endomorphism Z M of §6.1 (v_p = %s)"
          % (nm, "+" if same >= opp else "-", max(same, opp)))

# ----------------------------------------- (7) the quadratic Chabauty relation

print("-" * 72)
print("(7) the quadratic Chabauty relation, three free checks")


def kmodule(Lam):
    """A generator u of W = Q_p^g over K_p = Q_p[Lam], and the coordinates."""
    for i in range(g):
        u = vector(Kp, [Kp(1) if k == i else Kp(0) for k in range(g)])
        Bs = matrix(Kp, [list(u), list(Lam * u), list(Lam * Lam * u)])
        if vz(Bs.determinant(), N) < cert:
            return u, Bs.transpose()
    raise ArithmeticError("no K_p-generator of H^0(Omega^1)^* found")


Lam = matrix(Kp, [[Kp(QQ(c)) for c in row]
                  for row in AZ["Z_1"].submatrix(0, 0, g, g).transpose().rows()])
mpol = AZ["Z_1"].minpoly()
uvec, Ubas = kmodule(Lam)


def kcoords(v):
    """v in W as a polynomial in Lam applied to u: the K_p-coordinate."""
    return Ubas.solve_right(v)


def kmult(a, b):
    """The product of two K_p-coordinates, in the basis 1, Lam, Lam^2."""
    Rt = PolynomialRing(Kp, 't')
    t = Rt.gen()
    pa = sum((a[i] * t**i for i in range(g)), Rt.zero())
    pb = sum((b[i] * t**i for i in range(g)), Rt.zero())
    m = Rt([Kp(QQ(c)) for c in mpol.change_ring(QQ).list()])
    r = (pa * pb) % m
    cl = r.list() + [Kp(0)] * g
    return vector(Kp, cl[:g])


def qc_rows(splitting):
    """The rows (theta_Z(x), Psi_1, Psi_2, Psi_3) for both Z and all of RAT.

    frob_data is NOT recomputed: alpha_phi, beta_phi and gamma_phi do not
    depend on the splitting, only (14)'s assembly does.

    THE TEST IS A RANK.  Lemma 4.9 says every one of these rows is
    (B(v), psi(v)) for the SAME functional B and v = E_1 (x)_{K_p} E_{2,Z} in
    the 3-dimensional E, so all of them lie in one 3-dimensional subspace of
    Q_p^4 -- whichever rational points and whichever correspondences they came
    from.  Stating it as "rank <= 3" rather than as "solve for B from three of
    them and check the rest" costs nothing and does not depend on which rows
    happen to be usable: with m nonzero rows it is exactly m - 3 free checks.
    """
    s1m, s2m = splitting
    out = []
    for nm in ("Z_1", "Z_2"):
        lh = LH[nm].with_splitting(s1=s1m, s2=s2m)
        for r in RAW[nm][len(teich):]:
            E1, E2 = E1E2(nm, r)
            th = lh._assemble(r[1], r[2], r[3], r[4])
            psi = kmult(kcoords(E1), kcoords(E2))
            out.append(("%s at %s" % (nm, r[0]),
                        vector(Kp, [th] + list(psi))))
    return out


def normalise(v):
    """A row scaled to be primitive, and its original valuation."""
    m = min([vz(c, N) for c in v])
    if m >= cert:
        return None, m
    return vector(Kp, [c / Kp(p)**m for c in v]), m


for label, spl in (("unit root", (s1_ur, s2_ur)),
                   ("rational K-equivariant", (s1_rat, s2_rat)),
                   ("coordinate (NEGATIVE CONTROL)",
                    (matrix.identity(QQ, n) - s2_coord, s2_coord))):
    t0 = time.time()
    rows = qc_rows(spl)
    live, dead = [], []
    for lab, v in rows:
        w, m = normalise(v)
        print("      %-18s %-14s row = %s" % (label, lab,
                                              [vz(c, N) for c in v]))
        (dead if w is None else live).append((lab, w if w is not None else v))
    if dead:
        print("      %s: %d row(s) vanish identically: %s"
              % (label, len(dead), [d[0] for d in dead]))
    Rm = matrix(Kp, [w for _, w in live])
    # the three Z_1 rows on their own: [BDM+19] need these to be a basis of E
    # because their T_i is built from three points and one correspondence.
    if len(live) == 6:
        d1 = Rm.matrix_from_rows([0, 1, 2]).matrix_from_columns([1, 2, 3])
        print("      %s: v_p(det) of the three Z_1 rows' Psi = %s -- P_1, P_3, "
              "P_5 %s a basis of E, so B could also be pinned down from Z_1 "
              "alone, at that cost in precision"
              % (label, vz(d1.determinant(), N),
                 "are NOT" if vz(d1.determinant(), N) >= cert - 1 else "ARE"))
    minors4 = [Rm.matrix_from_rows(list(s)).determinant()
               for s in Subsets(range(len(live)), 4)] if len(live) >= 4 else []
    minors3 = [Rm.matrix_from_rows(list(s)).matrix_from_columns(list(t))
               .determinant()
               for s in Subsets(range(len(live)), 3)
               for t in Subsets(range(4), 3)] if len(live) >= 3 else []
    v4 = min([N] + [vz(m, N) for m in minors4]) if minors4 else None
    v3 = min([N] + [vz(m, N) for m in minors3]) if minors3 else None
    free = len(live) - 3
    print("      %s: %d live rows, min v_p(3x3 minor) = %s, "
          "min v_p(4x4 minor) = %s, free checks = %d"
          % (label, len(live), v3, v4, max(free, 0)))
    ok = (v4 is not None and v4 >= cert - 2 and v3 is not None
          and v3 < cert - 1 and free > 0)
    if "NEGATIVE" in label:
        check(not ok, "%s: rank > 3, i.e. NO single B exists -- as it must be, "
              "the splitting not being K-equivariant" % label)
    else:
        check(ok, "%s: the %d rows have rank exactly 3, i.e. ONE B "
              "reproduces theta for BOTH correspondences (%d free checks)"
              % (label, len(live), max(free, 0)))
    print("   (%.0f s)" % (time.time() - t0))
    sys.stdout.flush()

# ------------------------------------------------------------------- verdict

print("=" * 72)
print("total %.0f s, %d failure(s)" % (time.time() - t_start, len(fails)))
for m in fails:
    print("   FAILED: %s" % m)
print("E076 GATE: %s" % ("GREEN" if not fails else "RED"))
print("=" * 72)
