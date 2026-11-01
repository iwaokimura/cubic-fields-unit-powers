# check-xs13-table.sage --- E065 (E048 Phase 4) GATE, part 12.
#
# E077.  The TABLE of [BDM+19] §6.1: the zeroes of det(T_1) and det(T_2) on
# ]U_1[ to O(17^5).  It is the last published number the port has not met, and
# it is the only one that exercises theta as a FUNCTION rather than at a point.
#
# WHAT THE TABLE IS.  §6.1.1 builds, from three rational points, a 4x4 matrix
# T_i(x) whose first row is (theta_{Z_i}(x), Psi_1, Psi_2, Psi_3) and whose
# other three rows are the same expressions at the three points.  Lemma 1.4
# (qc_pair) says det T_i vanishes on X(Q_p)_2, hence on X(Q).  The table lists,
# disk by disk, the x-coordinates of every zero of each determinant.  Four of
# them are in bold: the rational points P_2, P_5, P_3, P_1 of ]U_1[, which is
# the Diophantine conclusion.
#
# WHAT E076 SETTLED THAT MATTERS HERE.
#   * The row space {(B(v), psi(v)) : v in E} is 3-dimensional and does NOT
#     depend on which rational points exhibit it, so the zero set of det T_i is
#     the same whether the last three rows come from P_1, P_3, P_4 (as §6.1.1
#     has it, using a point outside this chart) or from P_1, P_3, P_5 (which is
#     what ]U_1[ gives us).  E076 measured the rank to be exactly 3.
#   * The splitting is NOT determined by §6.1.1: the K-equivariant splittings
#     form a 3-parameter family and theta depends on the choice.  E076
#     concluded from this that the table is not reproducible without knowing
#     which one was used.  THAT WAS WRONG, and the correction is a theorem:
#
#       [T] det T_i does not depend on the K-equivariant splitting at all.
#       Two K-equivariant splittings differ by s_2 -> s_2 + delta with delta
#       K-equivariant, killing Fil^0 and landing in it, so by Lemma 5.4 theta
#       moves by (beta_phi - beta_Fil) . delta(alpha_phi).  That is bilinear in
#       E_2 and E_1 and K-bilinear because delta is K-equivariant, hence equals
#       B_delta(E_1 (x)_{K_p} E_2) for some B_delta in E^*.  So the first column
#       of T moves by a fixed linear combination of the other three, in EVERY
#       row at once -- a column operation, which leaves the determinant alone.
#
#     Check (6) runs two splittings (the unit root one, canonical and needing
#     no input beyond the curve and p, and the rational one E076 built from the
#     Sylvester equation) and check (8) verifies that they agree exactly.  This
#     also explains why §6.1.1 could get away with not saying which.
#
# THE PREDICTIONS, fixed before the gate was run.
#   (P1) The four rational points of ]U_1[ are common zeroes of det T_1 and
#        det T_2, for BOTH splittings.  This is choice-independent and is the
#        Diophantine content; it must hold or something upstream is wrong.
#   (P2) There is NO other common zero, for either splitting.  That is the
#        statement "X(Q) cap ]U_1[ = {P_1, P_2, P_3, P_5}", which is [BDM+19]'s
#        Theorem restricted to this chart, and it is choice-independent too.
#   (P3) The individual zero lists reproduce the table.  This is a statement
#        ABOUT THE PRINTED TABLE, not about the mathematics, and it is declared
#        here -- before the gate was run -- to be the one prediction allowed to
#        fail without the gate going red.  What P1 and P2 assert is the theorem;
#        what P3 asserts is a transcription.  The outcome is reported either
#        way, and if it fails the disagreement is printed in full.
#
# ROOT FINDING.  On the disk of a good point x_0 the local coordinate is
# t = x - x_0 with v_p(t) >= 1 (Prop 3.2 with dQ/dy a unit), so with t = p s the
# problem is the roots in Z_p of a power series whose coefficients grow in
# valuation.  The series is truncated where the discarded terms cannot move a
# root modulo p^5 -- MEASURED, not assumed -- and the roots are found by the
# standard lifting recursion (reduce mod p, substitute s = a + p s', renormalise
# by the content).  Every root is then verified against the UNtruncated series,
# and its multiplicity is checked to be one, which is what the table asserts.
# The content of det T_i is divided out first, so the ill-conditioning of the
# three rows (E076: v_p(det) = 3) costs nothing: it is an overall factor.
#
# Run: sage check-xs13-table.sage        (E077_N=<n> to change the precision)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint

t_start = time.time()
fails = []


def check(ok, msg):
    print("   %s  %s" % (msg, "ok" if ok else "*** NO ***"))
    if not ok:
        fails.append(msg)
    sys.stdout.flush()
    return ok


def vz(a, N):
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
ETA_NUM = {"Z_1": -(44*x**2 + 148*x*y/3 + 8*y**2),
           "Z_2": -(40*x**2 - 148*x*y - 36*y**2)}
BASE = (QQ(0), QQ(0))
RAT = [("P_1", (QQ(1)/2, QQ(1)/2)), ("P_3", (QQ(-3)/2, QQ(3)/2)),
       ("P_5", (QQ(0), QQ(2)))]

p = 17
N = ZZ(os.environ.get("E077_N", 10))
PREC = ZZ(5)                       # the table's O(17^5)
if N < 8:
    raise ValueError("N = %s is too small; use E077_N >= 8" % N)

# The 17 residue disks of U_1 = Y_{F_p} cap {Q_y != 0}, as (x, y) in F_17.
# E076 measured that Q_y vanishes only at (1,1) and that r has the single root
# x = 1 mod 17, so these are exactly the good disks of the chart.
DISKS = [(0, 0), (0, 2), (0, 9), (0, 16), (4, 1), (4, 9), (5, 15), (7, 6),
         (7, 10), (8, 0), (8, 3), (9, 9), (9, 13), (10, 3), (10, 4),
         (13, 9), (15, 14)]


def dig(*cs):
    """A p-adic integer from its digits, low first."""
    return sum(ZZ(c) * ZZ(p)**k for k, c in enumerate(cs))


# [BDM+19] §6.1's table, transcribed: disk -> (zeroes of det T_1, of det T_2),
# as x-coordinates mod 17^5.  y-coordinates are reduced into [0,17).
PUBLISHED = {
    (0, 0):   ([dig(0)], [dig(0)]),
    (0, 2):   ([dig(0), dig(0, 9, 11, 11, 0)], [dig(0)]),
    (0, 9):   ([], []),
    (0, 16):  ([], []),
    (4, 1):   ([], [dig(4, 13, 11, 4, 12), dig(4, 15, 4, 2, 11)]),
    (4, 9):   ([], []),
    (5, 15):  ([dig(5, 14, 7, 13, 12)],
               [dig(5, 15, 10, 8, 8), dig(5, 3, 8, 4, 2)]),
    (7, 6):   ([dig(7, 8, 13, 3, 3)], []),
    (7, 10):  ([dig(7, 8, 8, 8, 8), dig(7, 6, 10, 14, 15)],
               [dig(7, 8, 8, 8, 8), dig(7, 7, 0, 8, 7)]),
    (8, 0):   ([dig(8, 8, 12, 16, 7), dig(8, 16, 16, 1, 9)],
               [dig(8, 10, 7, 2, 10), dig(8, 5, 16, 6, 12)]),
    (8, 3):   ([dig(8, 8, 14, 8, 16), dig(8, 10, 12, 2, 8)], []),
    (9, 9):   ([dig(9, 8, 8, 8, 8), dig(9, 0, 6, 6, 3)],
               [dig(9, 8, 8, 8, 8)]),
    (9, 13):  ([dig(9, 10, 8, 4, 6)], []),
    (10, 3):  ([], []),
    (10, 4):  ([], []),
    (13, 9):  ([dig(13, 12, 7, 2, 12), dig(13, 13, 7, 7, 13)],
               [dig(13, 4, 10, 3, 7)]),
    (15, 14): ([dig(15, 8, 9, 4, 16), dig(15, 4, 5, 0, 2)], []),
}
# the bold entries: the rational points of ]U_1[ and the disks they sit in
BOLD = {(0, 0): dig(0), (0, 2): dig(0),
        (7, 10): dig(7, 8, 8, 8, 8), (9, 9): dig(9, 8, 8, 8, 8)}

# --------------------------------------------------------- p-adic root finding


def to_ZZ(a, k):
    """The integer representative of a p-adic integer modulo p^k."""
    m = ZZ(p)**k
    try:
        return ZZ(a.residue(k)) % m
    except (TypeError, ValueError, AttributeError):
        return ZZ(a.lift()) % m


def series_coeffs(ser, K, cap):
    """The coefficients of a power series, as a list, with its length."""
    if ser.is_zero():
        return [], ZZ(0)
    if ZZ(ser.valuation()) < 0:
        raise ArithmeticError("det T has a pole on the disk")
    hi = ser.prec()
    hi = ZZ(cap) if hi is None or hi == +Infinity else min(ZZ(hi), ZZ(cap))
    return [K(ser[k]) for k in range(0, hi)], hi


def to_s_poly(coeffs, K, want):
    """t = p s: the coefficients in s, truncated where the tail cannot matter.

    Returns (list, content, cut) where cut is the number of terms kept and the
    discarded ones all have v_p >= content + want.  MEASURED: nothing here
    assumes the estimate of §6.1.1, it checks the coefficients it has.
    """
    d = [coeffs[k] * K(p)**k for k in range(len(coeffs))]
    vs = [vz(c, N + len(d)) for c in d]
    cont = min(vs) if vs else ZZ(0)
    cut = len(d)
    while cut > 1 and vs[cut - 1] >= cont + want:
        cut -= 1
    return d[:cut], cont, cut


def _reduce_mod_p(cs, K):
    Fp = GF(p)
    return [Fp(to_ZZ(c, 1)) if vz(c, N) == 0 else Fp(0) for c in cs]


def roots_in_Zp(cs, K, prec, want_v):
    """Roots s in Z_p of sum cs[i] s^i, to precision p^prec.

    The standard lifting recursion: divide by the content, reduce mod p, and
    for each root a of the reduction substitute s = a + p s'.  A polynomial
    that becomes indistinguishable from zero stops the branch and is reported,
    since continuing would be inventing digits.
    """
    Rt = PolynomialRing(K, 's')
    out, undecided = [], []
    stack = [(list(cs), ZZ(0), ZZ(0))]
    while stack:
        c, base, lev = stack.pop()
        vs = [vz(a, want_v) for a in c]
        m = min(vs) if vs else ZZ(want_v)
        if m >= want_v:
            undecided.append((base, lev))
            continue
        c = [a / K(p)**m for a in c]
        if lev >= prec:
            out.append(base)
            continue
        fb = PolynomialRing(GF(p), 's')(_reduce_mod_p(c, K))
        if fb.is_zero():
            undecided.append((base, lev))
            continue
        for a, _ in fb.roots():
            a = ZZ(a)
            g = Rt(c)(Rt.gen() * K(p) + K(a))
            stack.append((g.list(), base + a * ZZ(p)**lev, lev + 1))
    return sorted(set(ZZ(r) % ZZ(p)**prec for r in out)), undecided


def newton_count(d, K, cap):
    """How many roots the Newton polygon of sum d[n] s^n puts in Z_p.

    Roots of valuation >= 0 are the segments of slope <= 0, so the count is
    the largest index at which v_p(d_n) attains its minimum.  This is an
    INDEPENDENT count of what roots_in_Zp should find, and the gate prints
    both: a mismatch means the recursion lost or invented a branch.
    """
    vs = [vz(c, cap) for c in d]
    m = min(vs)
    return max(i for i in range(len(vs)) if vs[i] == m)


def eval_series(coeffs, K, t0):
    """Horner, from the untruncated coefficient list."""
    f = K(0)
    for k in range(len(coeffs) - 1, -1, -1):
        f = f * t0 + coeffs[k]
    return f


def verify_root(coeffs, K, s0):
    """(v_p(f(t)), v_p(f'(t))) at t = p*s0, from the UNtruncated series."""
    t0 = K(p) * K(s0)
    f = K(0)
    fp = K(0)
    for k in range(len(coeffs) - 1, -1, -1):
        f = f * t0 + coeffs[k]
    for k in range(len(coeffs) - 1, 0, -1):
        fp = fp * t0 + K(k) * coeffs[k]
    return vz(f, N), vz(fp, N)


# ------------------------------------------------------------- (1) the setup

print("=" * 72)
print("=== check-xs13-table.sage --- E077: the table of [BDM+19] §6.1 ===")
print("=" * 72)
print("(1) setup (identical to E076)")

t0 = time.time()
C = TuitmanCurve(Qxy, name="X_s(13)")
H = Cohomology(C)
g, n = ZZ(C.genus), 2 * ZZ(C.genus)
L, xL, yL = C.L, C.L(C.x), C.y
dxL = xL.differential()


def toL(f):
    return sum(QQ(c) * xL**ZZ(e[0]) * yL**ZZ(e[1]) for e, c in f.dict().items())


QyL = toL(Qxy.derivative(y))
reps = [H.form_in_E((toL(f) / QyL) * dxL) for f in OMEGA_NUM]
bas, _ = H.H1X_basis()
dM = H.d_matrix()
cols = [vector(QQ, list(b)) for b in bas] \
    + [dM.column(j) for j in range(dM.ncols())]
Msolve = matrix(QQ, cols).transpose()
S = matrix(QQ, [list(Msolve.solve_right(vector(QQ, v)))[:n] for v in reps])
ETA = dict((k, H.form_in_E((toL(v) / QyL) * dxL)) for k, v in ETA_NUM.items())
Mcup = H.cup_product_matrix(basis=reps)
AZ = {"Z_1": Z1 * Mcup, "Z_2": Z2 * Mcup}
print("   genus %s, cup product = %sJ, p = %s, N = %s  (%.0f s)"
      % (g, "" if Mcup[0][g] == 1 else "-", p, N, time.time() - t0))
sys.stdout.flush()


def complement_system(A, isotropic):
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


def splitting_from_C(Cm, ring=QQ):
    Wm = matrix(ring, n, g, lambda i, j:
                Cm[i, j] if i < g else (ring(1) if i - g == j else ring(0)))
    Fil1 = matrix(ring, n, g, lambda i, j: ring(1) if i == j else ring(0))
    B = Fil1.augment(Wm).inverse().transpose()
    Qm = matrix(ring, n, n, lambda i, j: ring(1) if (i == j and i >= g)
                else ring(0))
    s2 = B * Qm * B.inverse()
    return matrix.identity(ring, n) - s2, s2


A2m, b2m = complement_system(AZ["Z_1"], True)
C_rat = matrix(QQ, g, g, list(A2m.solve_right(b2m)))
s1_rat, s2_rat = splitting_from_C(C_rat)

# ----------------------------------------------------- (2) the machine of E076

print("-" * 72)
print("(2) Phi, (22), and the two splittings")
t0 = time.time()
FM = FrobeniusMatrix(C, H, p, N)
FM.compute(primitives=True)
cert = ZZ(FM.certified_precision()[0])
Kp = FM.base
print("   Phi (%.0f s), certified precision %s" % (time.time() - t0, cert))
sys.stdout.flush()
check(cert >= PREC + 1,
      "the certified precision %s leaves room for the table's O(17^%s)"
      % (cert, PREC))

Sk = matrix(Kp, [[Kp(QQ(c)) for c in row] for row in S.rows()])
Sik = matrix(Kp, [[Kp(QQ(c)) for c in row] for row in S.inverse().rows()])
Fmat = Sk * FM.Phi.transpose() * Sik
Ft = Fmat.transpose()
Wur = matrix(Kp, [list(Ft**cert * vector(Kp, [Kp(1) if k == g + j else Kp(0)
                                              for k in range(n)]))
                  for j in range(g)]).transpose()
C_ur = Wur.submatrix(0, 0, g, g) * Wur.submatrix(g, 0, g, g).inverse()
s1_ur, s2_ur = splitting_from_C(C_ur, ring=Kp)

FS, LH = {}, {}
for nm, Zm in (("Z_1", Z1), ("Z_2", Z2)):
    t0 = time.time()
    fs = FrobeniusStructure(C, H, p, N, BASE, FM=FM, reps=reps, S=S, Z=Zm,
                            eta=ETA[nm])
    fs.solve()
    FS[nm] = fs
    LH[nm] = LocalHeight(fs, base=BASE, s1=s1_rat, s2=s2_rat)
    print("   %s: (22) solved (%.0f s)" % (nm, time.time() - t0))
    sys.stdout.flush()

# --------------------------------------------- (3) the K-module and Psi

Lam = matrix(Kp, [[Kp(QQ(c)) for c in row]
                  for row in AZ["Z_1"].submatrix(0, 0, g, g).transpose().rows()])
mpol = AZ["Z_1"].minpoly()
Ubas = None
for i in range(g):
    u = vector(Kp, [Kp(1) if k == i else Kp(0) for k in range(g)])
    Bs = matrix(Kp, [list(u), list(Lam * u), list(Lam * Lam * u)])
    if vz(Bs.determinant(), N) < cert:
        Ubas = Bs.transpose()
        break
if Ubas is None:
    raise ArithmeticError("no K_p-generator of H^0(Omega^1)^*")


def kcoords(v):
    return Ubas.solve_right(v)


def kmult(a, b, ring):
    Rt = PolynomialRing(ring, 'T')
    T = Rt.gen()
    pa = sum((a[i] * T**i for i in range(g)), Rt.zero())
    pb = sum((b[i] * T**i for i in range(g)), Rt.zero())
    m = Rt([ring(Kp(QQ(c))) for c in mpol.change_ring(QQ).list()])
    r = (pa * pb) % m
    cl = r.list() + [ring(0)] * g
    return list(cl[:g])


def E1E2(nm, alpha, beta_phi, ring):
    bf = LH[nm].beta_fil
    E1 = [ring(alpha[i]) for i in range(g)]
    E2 = [ring(beta_phi[g + i]) - ring(Kp(QQ(bf[g + i]))) for i in range(g)]
    return E1, E2


def psi_of(nm, alpha, beta_phi, ring):
    """Psi_1, Psi_2, Psi_3 from alpha_phi and beta_phi, over any ring."""
    E1, E2 = E1E2(nm, alpha, beta_phi, ring)
    UbR = matrix(ring, [[ring(c) for c in row] for row in Ubas.rows()])
    k1 = UbR.solve_right(vector(ring, E1))
    k2 = UbR.solve_right(vector(ring, E2))
    return kmult(k1, k2, ring)


# -------------------------------------------- (4) the three constant rows

print("-" * 72)
print("(4) the three rational rows of T (P_1, P_3, P_5)")
RATROW = {}
for nm in ("Z_1", "Z_2"):
    lh = LH[nm]
    rows = []
    for lab, xy in RAT:
        P = CurvePoint(FS[nm].RR, Kp(xy[0]), y=Kp(xy[1]))
        d = lh.frob_data(P)
        rows.append((lab, d))
    RATROW[nm] = rows
print("   done (%.0f s)" % (time.time() - t_start))
sys.stdout.flush()

SPLITTINGS = [("unit root", (s1_ur, s2_ur)),
              ("rational K-equivariant", (s1_rat, s2_rat))]


def const_rows(spl):
    out = []
    for nm in ("Z_1", "Z_2"):
        lh = LH[nm].with_splitting(s1=spl[0], s2=spl[1])
        for lab, d in RATROW[nm]:
            alpha, beta_phi, gamma_phi, gfil = d
            th = lh._assemble(alpha, beta_phi, gamma_phi, gfil)
            out.append(("%s at %s" % (nm, lab),
                        vector(Kp, [th] + psi_of(nm, alpha, beta_phi, Kp))))
    return out


# ------------------------------------------------------ (5) the disks

print("-" * 72)
print("(5) theta and Psi as series on the 17 disks of U_1")
TPREC = 4 * N + 20
SER = {}
for nm in ("Z_1", "Z_2"):
    for (a, b) in DISKS:
        t0 = time.time()
        P0 = CurvePoint(FS[nm].RR, Kp(a), y=Kp(b))
        x0 = FS[nm].teichmuller(P0)
        LE, alpha, beta_phi, gamma_phi, gfil = \
            LH[nm].frob_data_series(x0, tprec=TPREC)
        SER[(nm, a, b)] = (LE, x0, alpha, beta_phi, gamma_phi, gfil)
        print("      %s on (%s,%s): %.0f s" % (nm, a, b, time.time() - t0))
        sys.stdout.flush()

# ------------------------------------------------------- (6) the determinants

print("-" * 72)
print("(6) det T_i and its zeroes, per splitting")
RESULT = {}
for label, spl in SPLITTINGS:
    print("   --- splitting: %s" % label)
    rows = const_rows(spl)
    # scaled to be primitive, as in E076: a 3x3 minor of the raw rows carries
    # their contents as an overall factor and would misreport independence.
    prim = []
    for lab, v in rows:
        m = min([vz(c, N) for c in v])
        prim.append(vector(Kp, [c / Kp(p)**m for c in v]))
    Rm = matrix(Kp, prim)
    best, bv = None, N + 1
    for sub in Subsets(range(len(rows)), 3):
        v = min([vz(m, N) for m in
                 [Rm.matrix_from_rows(list(sub)).matrix_from_columns(list(cc))
                  .determinant() for cc in Subsets(range(4), 3)]])
        if v < bv:
            best, bv = list(sub), v
    check(bv < cert - 1,
          "%s: three of the six rational rows are independent, %s "
          "(min v_p(3x3) = %s)" % (label, [rows[i][0] for i in best], bv))
    base3 = [rows[i][1] for i in best]
    found = {}
    for nm in ("Z_1", "Z_2"):
        for (a, b) in DISKS:
            LE, x0, alpha, beta_phi, gamma_phi, gfil = SER[(nm, a, b)]
            lh = LH[nm].with_splitting(s1=spl[0], s2=spl[1])
            th = lh._assemble(alpha, beta_phi, gamma_phi, gfil)
            SR = th.parent()
            psi = psi_of(nm, alpha, beta_phi, SR)
            M4 = matrix(SR, [[th] + psi]
                        + [[SR(c) for c in r] for r in base3])
            det = M4.determinant()
            cs, hi = series_coeffs(det, Kp, TPREC)
            if not cs:
                found[(nm, a, b)] = ("IDENTICALLY ZERO", [], [])
                continue
            d, cont, cut = to_s_poly(cs, Kp, PREC + 3)
            rts, undec = roots_in_Zp(d, Kp, PREC, N)
            xs = []
            for s0 in rts:
                vf, vfp = verify_root(cs, Kp, s0)
                xv = (to_ZZ(x0.x, PREC) + ZZ(p) * ZZ(s0)) % ZZ(p)**PREC
                # Hensel: v_p(f) > 2 v_p(f') puts a true root within
                # p^(v_p(f) - v_p(f')) of this one.  Both are measured against
                # the content of det T, which is an overall factor.
                xs.append((xv, vf - cont, vfp - cont))
            found[(nm, a, b)] = (None, sorted(xs), undec, cut)
            for (xv, vf, vfp) in xs:
                if not (vf > 2 * vfp and vf - vfp >= PREC):
                    print("      %s (%s,%s): root %s NOT Hensel-certified "
                          "(v_p(f) = %s, v_p(f') = %s over the content)"
                          % (nm, a, b, xv, vf, vfp))
            # an independent count of the roots in the disk, and the value of
            # our det T at every zero the paper prints there
            nc = newton_count(d, Kp, N)
            pub = PUBLISHED[(a, b)][0 if nm == "Z_1" else 1]
            vals = []
            for z in pub:
                t0v = Kp(ZZ(z) - to_ZZ(x0.x, PREC))
                vals.append((z, vz(eval_series(cs, Kp, t0v), N) - cont))
            if nc != len(xs) or any(v < PREC for _, v in vals) \
                    or len(pub) != len(xs):
                print("      %s (%s,%s): Newton count %s, found %s, "
                      "v_p(det T) at §6.1's zeroes (over the content) %s"
                      % (nm, a, b, nc, len(xs), vals))
    RESULT[label] = (found, best)

# ------------------------------------------------------ (7) against the table

print("-" * 72)
print("(7) against §6.1's table")
P3_RESULT = {}
for label, _ in SPLITTINGS:
    found, best = RESULT[label]
    print("   --- splitting: %s" % label)
    common, mismatch, undecided = {}, [], 0
    for (a, b) in DISKS:
        got = {}
        for nm, i in (("Z_1", 0), ("Z_2", 1)):
            flag, xs, undec, cut = found[(nm, a, b)]
            if flag:
                mismatch.append("(%s,%s) %s: %s" % (a, b, nm, flag))
                got[nm] = None
                continue
            undecided += len(undec)
            got[nm] = [q[0] for q in xs]
        pub = PUBLISHED[(a, b)]
        same1 = got["Z_1"] is not None and sorted(got["Z_1"]) == sorted(pub[0])
        same2 = got["Z_2"] is not None and sorted(got["Z_2"]) == sorted(pub[1])
        if got["Z_1"] is not None and got["Z_2"] is not None:
            common[(a, b)] = sorted(set(got["Z_1"]) & set(got["Z_2"]))
        print("      (%2s,%2s)  T_1 %s %s   T_2 %s %s"
              % (a, b,
                 [q[0] for q in found[("Z_1", a, b)][1]]
                 if not found[("Z_1", a, b)][0] else "??",
                 "=pub" if same1 else "!= %s" % (pub[0],),
                 [q[0] for q in found[("Z_2", a, b)][1]]
                 if not found[("Z_2", a, b)][0] else "??",
                 "=pub" if same2 else "!= %s" % (pub[1],)))
        if not same1:
            mismatch.append("(%s,%s) T_1" % (a, b))
        if not same2:
            mismatch.append("(%s,%s) T_2" % (a, b))
    sys.stdout.flush()
    # (P1) and (P2): the common zeroes, which no choice of splitting can move
    allcommon = dict((k, v) for k, v in common.items() if v)
    check(all(BOLD[k] in v for k, v in allcommon.items() if k in BOLD)
          and all(k in allcommon and BOLD[k] in allcommon[k] for k in BOLD),
          "%s: [P1] the four rational points of ]U_1[ are common zeroes of "
          "det T_1 and det T_2" % label)
    extra = dict((k, [z for z in v if not (k in BOLD and z == BOLD[k])])
                 for k, v in allcommon.items())
    extra = dict((k, v) for k, v in extra.items() if v)
    check(not extra,
          "%s: [P2] there is NO other common zero, i.e. "
          "X(Q) cap ]U_1[ = {P_1, P_2, P_3, P_5}%s"
          % (label, "" if not extra else " -- found %s" % extra))
    # [P3] is declared falsifiable in the header: it is reported, not asserted.
    if mismatch:
        print("   %s: [P3] NOT reproduced -- %d slot(s) of %d differ: %s"
              % (label, len(mismatch), 2 * len(DISKS), mismatch))
    else:
        check(True, "%s: [P3] the individual zero lists reproduce §6.1's table"
              % label)
    P3_RESULT[label] = mismatch
    if undecided:
        print("      %d branch(es) undecided at this precision" % undecided)

# ------------------------------------ (8) the splitting-invariance of det T

print("-" * 72)
print("(8) det T does not depend on the K-equivariant splitting")
lists = []
for label, _ in SPLITTINGS:
    found, _ = RESULT[label]
    lists.append(dict((k, tuple(q[0] for q in v[1]))
                      for k, v in found.items() if not v[0]))
check(lists[0] == lists[1],
      "the two K-equivariant splittings give IDENTICAL zero lists on all %d "
      "disks and both correspondences (the column-operation theorem)"
      % len(DISKS))

print("=" * 72)
print("total %.0f s, %d failure(s)" % (time.time() - t_start, len(fails)))
for m in fails:
    print("   FAILED: %s" % m)
print("E077 GATE: %s" % ("GREEN" if not fails else "RED"))
print("=" * 72)
