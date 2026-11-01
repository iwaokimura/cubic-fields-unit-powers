# check-c4-globalheight.sage --- E088: the shape of the global height side, and
# whether chart 1 alone determines the pairing.
#
# BLOCKER (B2) of E088.  E087 assumed
#       h(A_Z(b,x)) = q(AJ_b(x)),      q a quadratic form,
# i.e. a PURELY QUADRATIC dependence on the Abel-Jacobi image.  That assumption
# was never checked, and the whole of Phase 5 rests on it.  This gate settles it
# from the source and then measures the two things that follow.
#
# THE DERIVATION (published version, Ann. of Math. 189 (2019), NOT arXiv v1).
# Section 1.4 defines a quadratic Chabauty pair by
#       theta(x) - B(AJ_b(x), E(AJ_b(x)) + c)  in  Upsilon      for x in X(Q),
# with E an endomorphism of H^0(Omega^1)^*, c a functional, B a bilinear form.
# Lemma 3.7 identifies all three for our situation: E is induced by Z, the
# constant is c = [I A_Z(b)], and B is the global height h.  Section 6.4.1
# writes the same thing in the notation the port uses,
#       E_1(x) = AJ_b(x),        E_{2,Z}(x) = E(AJ_b(x)) + c .
# So the answer to (B2) is:
#
#   *** the dependence is AFFINE, not quadratic: there IS a linear term.  With
#   *** u = AJ_b(x),   h(A_Z(b,x)) = B(u, E u) + B(u, c),   and no constant
#   *** term (both pieces vanish at x = b, where u = 0).
#
# AND IT COSTS NOTHING.  The linear term is paired by the SAME B, so it adds no
# unknown: only the columns of E087's design matrix change, from u_i u_j to
# sym(E_1 (x) E_2)_ij.  E087's count of four unknowns survives; its columns do
# not.
#
# WHY THE COLUMNS ARE FOUR.  h is symmetric, and if the splitting of the Hodge
# filtration is sigma-equivariant then h(sigma u, v) = h(u, sigma v)
# (Remark 3.9), so the sigma-eigenspaces are h-orthogonal and B is block
# diagonal: B_11 on the elliptic line, B_22, B_23, B_33 on the Prym plane.
# E087 checked the equivariance on the HOLOMORPHIC forms only; the splitting
# lives on all of H^1_dR, so check (1) here does the full 6 x 6.
#
# THE CHECKS.
#   (1) sigma^* on the whole phase-4 basis: an involution, BLOCK DIAGONAL for
#       the splitting (first g | last g), holomorphic block diag(1,-1,-1).
#       Exact over Q, and the holomorphic block is a second, independent route
#       to E087 check (1).  This is what licenses "four unknowns".
#   (2) The correspondence in the phase-4 basis: its top-right block is
#       lambda * diag(2,-1,-1) and the bottom-left block its negative.  The
#       eigenvalue pattern 2, -1, -1 is the endomorphism induced by
#       Z = (1+3 sigma)/2 -- 2 on the sigma-invariant (elliptic) line, -1 on
#       the Prym plane -- so the port's E is lambda times the paper's.  Exact.
#   (3) THE AFFINE LAW, MEASURED.  E_1(b) = 0 and c := E_2(b).  Then
#       E_2(x) = M E_1(x) + c with M the transpose of that top-right block, at
#       all seven good rational points, to certified precision.  Two things
#       matter here: c is NONZERO (so the linear term is real and E087's model
#       was wrong), and M is diagonal (so the affine law respects the blocks).
#       Negative control: dropping c breaks the law.  Cross-check: E_1 from the
#       Frobenius structure against AJ_b from Algorithm 3.7, two different
#       routes to the same vector.
#   (4) THE CORRECTED DESIGN MATRIX.  Rows the seven good non-base points,
#       columns u_1 v_1, u_2 v_2, u_2 v_3 + u_3 v_2, u_3 v_3 with v = E_2.
#   (5) theta at b (must vanish: h(A_Z(b,b)) = B(0,c) = 0 and the local heights
#       away from p vanish there too) and at the seven points -- the input to
#       E089.
#   (6) THE sigma-DEGENERACY.  Found while reading (5)'s output, and it is the
#       main result of this gate.  theta takes the SAME value on the two points
#       of each sigma-pair, to p^7 against a certified p^5.  The reason is
#       visible in (3): rho := E_2(sigma b) = M kappa + c, with
#       kappa = AJ_b(sigma b), has VANISHING PRYM PART.  Since kappa is purely
#       Prym (sigma b - b is anti-invariant) and B is block diagonal, a short
#       computation then gives, for every x,
#           h(A_Z(b,sigma x)) - h(A_Z(b,x)) = -2 B(AJ_b(x), rho') + B(kappa',rho')
#       which vanishes identically when rho' = 0.  So the two points of a
#       sigma-pair give the SAME height equation, and b, sigma b give the
#       trivial one 0 = 0.  The nine rational points carry only FIVE distinct
#       equations, one of which is trivial.
#   (7) THE ORBIT DESIGN MATRIX.  (0,0) is sigma-FIXED, so E_1(0,0) = kappa/2
#       (E087 measured this) and E_2(0,0) = M kappa/2 + c is then known without
#       chart 2.  So all four non-trivial orbit rows can be assembled here.  Is
#       the 4 x 4 matrix invertible?  If it is, B is EXACTLY determined and
#       nothing is left over.
#
#       IT IS NOT, AND THE REASON IS STRUCTURAL.  Check (10) finds that the
#       Prym components of AJ_b are PROPORTIONAL for eight of the nine points:
#           AJ_b(x)' = alpha * kappa',  alpha = 1, 1, 1/2, -1/2 at
#           sigma b, (-1,3), (0,0), (-2,6),
#       and only (-1/11, +-15/11) leaves the line Q kappa'.  Since the Prym row
#       of x is m_2 sym(a (x) (a - kappa')) with a = AJ_b(x)', every point on
#       that line contributes a multiple of sym(kappa' (x) kappa'), one single
#       direction.  So the orbit rows span at most TWO of the three dimensions
#       of Sym^2 of the Prym plane, at any precision.  Raising N does not help:
#       the determinant's valuation rises in step with the precision (14 at
#       N = 8, 17 at N = 12), which is what an exact zero looks like.
#
# A CORRECTION MADE WHILE RUNNING THIS.  Check (4) first used E087's rank
# routine, which scales each row by its own minimum valuation before reducing
# mod p^cert.  That is wrong for a row all of whose entries are zero to
# precision -- and the row of sigma b is exactly that -- because the scaling
# promotes its noise to units.  It reported rank 4 on the seven points.  With a
# single global scaling the rank is 3, which is what (6) predicts.  Both
# numbers are printed below.
#
# Run: sage check-c4-globalheight.sage        (about 3 minutes)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint
from padic.integrals import ColemanIntegrals

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13
# The working precision.  Check (7) is the one that needs it: at N = 8 the
# certified precision is p^5, the Prym determinant has valuation 14 and is
# known only to p^12, so its non-vanishing cannot be decided.  E088_N raises it.
N = ZZ(os.environ.get("E088_N", 8))
BASE = (QQ(1), QQ(3))
GOOD = [(QQ(1), QQ(-3)), (QQ(-1), QQ(3)), (QQ(-1), QQ(-3)),
        (QQ(-2), QQ(6)), (QQ(-2), QQ(-6)),
        (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11)]
# the sigma-pairs among the eight points b, GOOD (the ninth, (0,0), is fixed)
PAIRS = [(BASE, (QQ(1), QQ(-3))),
         ((QQ(-1), QQ(3)), (QQ(-1), QQ(-3))),
         ((QQ(-2), QQ(6)), (QQ(-2), QQ(-6))),
         ((QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11))]

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


def main():
    print("=== check-c4-globalheight.sage --- E088: the global height side ===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)

    print("(1) sigma^* ON THE WHOLE PHASE-4 BASIS, AND THE SPLITTING")
    reps, S = H.phase4_basis()
    S = matrix(QQ, S)
    MA = H.automorphism_matrix(sx=1, sy=-1)      # on H1X-basis coordinates
    # a class with H1X-coordinates v has phase-4 coordinates S^{-T} v
    Sig = S.transpose().inverse() * MA * S.transpose()
    check(Sig**2 == matrix.identity(QQ, n),
          "sigma^* is an involution on H^1_dR")
    top = matrix(QQ, g, g, lambda i, j: Sig[i][j])
    bot = matrix(QQ, g, g, lambda i, j: Sig[i + g][j + g])
    offA = matrix(QQ, g, g, lambda i, j: Sig[i][j + g])
    offB = matrix(QQ, g, g, lambda i, j: Sig[i + g][j])
    check(offA == 0 and offB == 0,
          "and is BLOCK DIAGONAL for the splitting (first g | last g): the "
          "default splitting s_2 of the Hodge filtration is sigma-equivariant, "
          "so by Remark 3.9 the height satisfies h(sigma u, v) = h(u, sigma v) "
          "and the sigma-eigenspaces are h-orthogonal")
    check(top == diagonal_matrix(QQ, [1, -1, -1]),
          "holomorphic block = diag(1,-1,-1), agreeing with E087 check (1), "
          "which reached it by a different route (the linear forms ell)")
    info("last-g block = %s" % [list(r) for r in bot.rows()])
    info("=> B is block diagonal: B_11 on the elliptic line, B_22, B_23, B_33 "
         "on the Prym plane.  FOUR unknowns, and the linear term B(u,c) is "
         "paired by the same four.")

    print("(2) THE CORRESPONDENCE, AND THE ENDOMORPHISM IT INDUCES")
    t0 = time.time()
    FS = FrobeniusStructure(C, H, P_GATE, N, BASE, sx=1, sy=-1)
    cc, mu, resv = FS.solve()
    K, cert = FS.K, FS.cert
    info("(22) solved: certified p^%d, residual p^%s, Z rescaled by %s (%.0f s)"
         % (cert, resv, FS.Zscale, time.time() - t0))
    Zq = FS.Z
    TR = matrix(QQ, g, g, lambda i, j: Zq[i][j + g])
    BL = matrix(QQ, g, g, lambda i, j: Zq[i + g][j])
    check(matrix(QQ, g, g, lambda i, j: Zq[i][j]) == 0
          and matrix(QQ, g, g, lambda i, j: Zq[i + g][j + g]) == 0,
          "Z is off-block-diagonal: as a class it pairs Fil^1 with its "
          "complement, so w^T = U^T Z sends the HOLOMORPHIC half of the "
          "integral to the last g coordinates -- which is why E_2 depends on "
          "E_1 alone")
    check(BL == -TR, "Z is antisymmetric (condition (d) of \\S4.4)")
    lam = TR[1][1]
    Epred = diagonal_matrix(QQ, [2, -1, -1])
    check(TR == lam * (-Epred) and lam != 0,
          "and its top-right block is %s * diag(-2,1,1): the induced "
          "endomorphism has eigenvalue 2 on the sigma-invariant line and -1 on "
          "the Prym plane, which is Z = (1+3 sigma)/2 exactly.  The port's E "
          "is thus -%s times the paper's; every term of the quadratic Chabauty "
          "equation is homogeneous of degree 1 in Z, so this is a global "
          "normalisation and nothing more -- PROVIDED h_2 and h_3 use the same "
          "one (see Next Steps)" % (lam, lam))
    Mmat = TR.transpose()
    info("M := (top-right block)^T = %s" % [list(r) for r in Mmat.rows()])

    print("(3) THE AFFINE LAW E_2 = M E_1 + c, AND c ITSELF")
    LH = LocalHeight(FS, BASE, fil0_correction=True)
    info("beta_Fil = %s  (%.0f s)" % (list(LH.beta_fil), time.time() - t0))

    def E12(P):
        alpha, beta_phi, gamma_phi, gf = LH.frob_data(P)
        return ([alpha[i] for i in range(g)],
                [beta_phi[j] - K(QQ(LH.beta_fil[j])) for j in range(g, n)])

    Pb = CurvePoint(FS.RR, K(BASE[0]), y=K(BASE[1]))
    E1b, cvec = E12(Pb)
    check(min(vz(a, N) for a in E1b) >= cert,
          "E_1(b) = 0 to p^%s: the base point's Abel-Jacobi image vanishes, so "
          "c = E_2(b) reads off the constant of the quadratic Chabauty pair "
          "directly" % min(vz(a, N) for a in E1b))
    vc = [vz(a, N) for a in cvec]
    check(max(vc) < cert,
          "*** c = E_2(b) IS NONZERO ***: valuations %s against certified p^%d."
          "  E087's purely quadratic model of the global height is therefore "
          "WRONG; the linear term B(u,c) is present" % ([str(v) for v in vc],
                                                        cert))

    D = {}
    for pt in GOOD:
        P = CurvePoint(FS.RR, K(pt[0]), y=K(pt[1]))
        D[pt] = E12(P)
    D[BASE] = (E1b, cvec)
    check(len(D) == 8, "E_1 and E_2 at the base point and the seven good ones")

    Mk = matrix(K, [[K(QQ(c)) for c in r] for r in Mmat.rows()])
    worst = ZZ(N + 4)
    for pt in GOOD:
        u = vector(K, D[pt][0])
        pred = Mk * u
        for i in range(g):
            worst = min(worst, vz(pred[i] + cvec[i] - D[pt][1][i], N))
    check(worst >= cert,
          "E_2(x) = M E_1(x) + c at all seven good points, to p^%s (certified "
          "p^%d)" % (worst, cert))
    # negative control: the same law with c dropped
    wnoc = ZZ(N + 4)
    for pt in GOOD:
        pred = Mk * vector(K, D[pt][0])
        for i in range(g):
            wnoc = min(wnoc, vz(pred[i] - D[pt][1][i], N))
    check(wnoc < cert,
          "negative control: dropping c breaks the law at p^%s -- the linear "
          "term is not an artefact of low precision" % wnoc)

    # E_1 against Algorithm 3.7, a second route to the same vector
    CI = ColemanIntegrals(FS.FM)
    Uex = FS.u
    wcol = ZZ(N + 4)
    ub = [FS.evaluate(a, Pb) for a in Uex]
    for pt in GOOD:
        P = CurvePoint(FS.RR, K(pt[0]), y=K(pt[1]))
        comp = list(CI.coleman_integrals_on_basis(Pb, P))
        uP = [FS.evaluate(a, P) for a in Uex]
        for i in range(g):
            acc = K(0)
            for j in range(n):
                if FS.S[i][j] != 0:
                    acc += K(QQ(FS.S[i][j])) * K(comp[j])
            acc += K(uP[i]) - K(ub[i])
            wcol = min(wcol, vz(acc - D[pt][0][i], N))
    check(wcol >= cert,
          "E_1 from the Frobenius structure = AJ_b from Algorithm 3.7 at all "
          "seven points, to p^%s: the identification E_1 = AJ_b of \\S6.4.1 "
          "holds in the port" % wcol)

    # sigma-equivariance of E_2: E_2(sigma x) - sigma E_2(x) is CONSTANT
    sg = diagonal_matrix(K, [K(QQ(c)) for c in [1, -1, -1]])
    diffs = []
    for (a, sa) in PAIRS:
        v1 = vector(K, D[sa][1])
        v2 = sg * vector(K, D[a][1])
        diffs.append(v1 - v2)
    weq = min(min(vz(d[i] - diffs[0][i], N) for i in range(g))
              for d in diffs[1:])
    check(weq >= cert,
          "E_2(sigma x) - sigma E_2(x) is the same constant on all four "
          "sigma-pairs, to p^%s: M commutes with sigma and the constant is "
          "M kappa + c - sigma c with kappa = AJ_b(sigma b)" % weq)

    print("(4) THE CORRECTED DESIGN MATRIX")

    def rows_of(cols):
        out = []
        for pt in GOOD:
            u, v = D[pt][0], D[pt][1]
            out.append(cols(u, v))
        return out

    def rank_of(rows, label, rowwise=False):
        if rowwise:                       # E087's routine, kept as the control
            scaled = []
            for r in rows:
                m = min(vz(c, N) for c in r)
                scaled.append([ZZ((c / K(P_GATE)**m).residue(cert))
                               if c != 0 else ZZ(0) for c in r])
        else:                             # a SINGLE global scaling
            vmin = min(vz(c, N) for r in rows for c in r)
            scaled = [[ZZ((c / K(P_GATE)**vmin).residue(cert))
                       if c != 0 else ZZ(0) for c in r] for r in rows]
        Mz = matrix(ZZ, scaled)
        elem = [d for d in Mz.elementary_divisors()]
        rk = len([d for d in elem if d != 0
                  and ZZ(d).valuation(P_GATE) < cert])
        info("%s: elementary divisor valuations mod p^%d = %s, rank %d"
             % (label, cert,
                [str(ZZ(d).valuation(P_GATE)) if d != 0 else "inf"
                 for d in elem], rk))
        return rk

    COLS = lambda u, v: [u[0]*v[0], u[1]*v[1], u[1]*v[2] + u[2]*v[1],
                         u[2]*v[2]]
    rows7 = rows_of(COLS)
    rk = rank_of(rows7, "columns sym(E_1 (x) E_2), global scaling")
    rkrow = rank_of(rows7, "the same, with E087's row-by-row scaling",
                    rowwise=True)
    rk87 = rank_of(rows_of(lambda u, v: [u[0]**2, u[1]**2, u[1]*u[2],
                                         u[2]**2]),
                   "E087's purely quadratic columns, for comparison")
    info("THE PREDICTION MADE BEFORE THIS RAN was rank 3 (sigma-pairs repeat, "
         "sigma b gives the zero row).  The measurement is %d under global "
         "scaling and %d under E087's row-by-row scaling.  Neither prediction "
         "was right: see (7), where the entries are weighed against their own "
         "absolute precisions instead of a single global one." % (rk, rkrow))
    info("E087's purely quadratic columns give rank %d under the same global "
         "scaling." % rk87)
    # the rows themselves, and the sigma-pairs
    for k, pt in enumerate(GOOD):
        info("row %-16s valuations %s"
             % (pt, [str(vz(c, N)) for c in rows7[k]]))
    idx = {pt: k for k, pt in enumerate(GOOD)}
    wrow = ZZ(N + 4)
    for (a, sa) in PAIRS[1:]:
        for j in range(4):
            wrow = min(wrow, vz(rows7[idx[a]][j] - rows7[idx[sa]][j], N))
    check(wrow >= cert,
          "the design rows of the three sigma-pairs inside chart 1 COINCIDE, to "
          "p^%s: each pair carries one equation, not two" % wrow)
    wzero = min(vz(c, N) for c in rows7[idx[(QQ(1), QQ(-3))]])
    check(wzero >= cert,
          "and the row of sigma b = (1,-3) is ZERO to p^%s: its equation is "
          "0 = 0" % wzero)

    print("(5) theta AT b AND AT THE SEVEN POINTS")
    tb = LH.theta(Pb)
    check(vz(tb, N) >= cert,
          "theta(b) = 0 to p^%s: h(A_Z(b,b)) = B(0,c) = 0, and the local "
          "heights away from p vanish at b as well, so h_2 and h_3 vanish "
          "on b's reduction classes" % vz(tb, N))
    th = {BASE: tb}
    for pt in GOOD:
        P = CurvePoint(FS.RR, K(pt[0]), y=K(pt[1]))
        th[pt] = LH.theta(P)
        info("theta(%-16s) = %s   (valuation %s)"
             % (pt, th[pt], vz(th[pt], N)))

    print("(6) THE sigma-DEGENERACY")
    wth = min(vz(th[a] - th[sa], N) for (a, sa) in PAIRS)
    check(wth >= cert,
          "theta(sigma x) = theta(x) on all four sigma-pairs, to p^%s "
          "(certified p^%d).  This was not expected and is the main finding of "
          "this gate" % (wth, cert))
    rho = D[(QQ(1), QQ(-3))][1]                  # rho = E_2(sigma b) = M kappa + c
    kap = D[(QQ(1), QQ(-3))][0]                  # kappa = AJ_b(sigma b)
    vrho = [vz(a, N) for a in rho]
    check(min(vrho[1], vrho[2]) >= cert,
          "and the reason: rho = E_2(sigma b) has valuations %s, so its PRYM "
          "part VANISHES to certified precision while its elliptic component "
          "does not.  With kappa purely Prym (kappa_1 has valuation %s) and B "
          "block diagonal, h(A_Z(b,sigma x)) - h(A_Z(b,x)) = -2 B(AJ_b(x),rho') "
          "+ B(kappa',rho') = 0 identically"
          % ([str(v) for v in vrho], vz(kap[0], N)))
    info("rho' = 0 is equivalent to c' = -m_2 kappa', i.e. the constant "
         "[I A_Z(b)] is, modulo the elliptic line, MINUS the endomorphism "
         "applied to AJ_b(sigma b).  Nothing in [BDM+19] predicts this; it is "
         "measured here.  Its consequences: the nine rational points carry "
         "only five distinct height equations, and h_2 is sigma-invariant.")

    print("(7) THE ORBIT DESIGN MATRIX, WEIGHED AGAINST ITS OWN PRECISION")
    # (0,0) is sigma-fixed, so AJ_b(0,0) = kappa/2 (E087 check 2b) and
    # E_2(0,0) = M kappa/2 + c follows from (3): chart 2 is not needed for the
    # ROW, only for theta(0,0).
    u00 = [K(QQ(1)/2) * kap[i] for i in range(g)]
    v00 = [sum((Mk[i][j] * u00[j] for j in range(g)), K(0)) + cvec[i]
           for i in range(g)]
    D[(QQ(0), QQ(0))] = (u00, v00)
    orbit = [(QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11),
             (QQ(0), QQ(0))]

    # A product u_i v_j of two quantities each known to ABSOLUTE precision
    # p^cert is known to absolute precision p^(min(v(u_i),v(v_j)) + cert), a
    # valuation of cert or more meaning "zero to precision".
    def vcap(a):
        return min(vz(a, N), cert)

    def entry(u, v, terms):
        val = sum((u[i] * v[j] for (i, j) in terms), K(0))
        pr = min(vcap(u[i]) + cert for (i, j) in terms)
        pr = min(pr, min(vcap(v[j]) + cert for (i, j) in terms))
        return val, ZZ(pr)

    TERMS = [[(0, 0)], [(1, 1)], [(1, 2), (2, 1)], [(2, 2)]]
    print("        %-18s %s" % ("orbit", "entry valuation / precision, "
                                "'.' = zero to precision"))
    ORows, OPrec = [], []
    for pt in orbit:
        u, v = D[pt]
        row, pre = [], []
        for tm in TERMS:
            a, pr = entry(u, v, tm)
            row.append(a)
            pre.append(pr)
        ORows.append(row)
        OPrec.append(pre)
        info("%-18s %s" % (pt, ["%s/%s" % (vz(a, N), pr) if vz(a, N) < pr
                                else "./%s" % pr
                                for a, pr in zip(row, pre)]))

    def sig(k, j):
        return vz(ORows[k][j], N) < OPrec[k][j]

    check(not any(sig(0, j) for j in range(4)),
          "the whole row of (-1,3) is zero to its own precision: E_2(-1,3) = 0 "
          "(valuations %s), so this orbit's equation contains NO unknown of B "
          "at all.  It reads theta(-1,3) + h_2 + h_3 = 0"
          % [str(vz(a, N)) for a in D[(QQ(-1), QQ(3))][1]])
    check(not sig(1, 0) and not sig(3, 0) and sig(2, 0),
          "the elliptic column vanishes on the orbits of (-2,6) and (0,0) and "
          "survives only on that of (-1/11,15/11): B_11 enters exactly ONE "
          "equation")
    # the Prym 3 x 3 of the orbits of (-2,6), (-1/11,15/11), (0,0)
    Pm = matrix(K, 3, 3, lambda i, j: ORows[i + 1][j + 1])
    dt = Pm.determinant()
    # perturbing the (i,j) entry by delta moves the determinant by delta times
    # the (i,j) cofactor, so the determinant is known to
    #     min_{i,j} ( precision of a_ij  +  valuation of the cofactor ).
    pdet = min(OPrec[i + 1][j + 1]
               + vz(Pm.matrix_from_rows_and_columns(
                   [r for r in range(3) if r != i],
                   [c for c in range(3) if c != j]).determinant(), N)
               for i in range(3) for j in range(3))
    info("Prym 3 x 3 determinant: valuation %s, known to p^%s"
         % (vz(dt, N), pdet))
    check(vz(dt, N) < pdet,
          "the Prym block of B is DETERMINED: the 3 x 3 system from the orbits "
          "of (-2,6), (-1/11,15/11) and (0,0) is invertible at the precision "
          "to which its entries are known")

    print("(8) THE BUDGET, CORRECTED")
    info("nine rational points, five sigma-orbits.  The base orbit {b,sigma b} "
         "gives 0 = 0 and the orbit of (-1,3) gives an equation free of B.  "
         "THREE equations carry B, against three Prym unknowns; B_11 appears "
         "in one of them and is supplied by SageMath (E065(b)).")
    info("h_3 costs no continuous unknown but one SIGN (E084, E086); h_2 is "
         "sigma-invariant by (6) and vanishes on the base orbit")
    info("=> the budget for h_2 is ZERO, not four as E087 reported.  And by "
         "(7) and (10) the three B-carrying equations span only TWO "
         "dimensions, so the Prym block is SHORT BY ONE EQUATION.  What is "
         "still gained: the (-1,3) equation is free of B, hence a DIRECT "
         "determination of h_2 + h_3 there; and the orbits of (-2,6) and "
         "(0,0) give proportional rows with different h_3, so once "
         "theta(0,0) is known they are one equation and one CHECK.")

    print("(9) THE B-FREE EQUATION, AGAINST E086")
    lg3 = K(3).log()
    tm1 = th[(QQ(-1), QQ(3))]
    info("theta(-1,3) = %s" % tm1)
    info("log_13(3)   = %s" % lg3)
    rat = -8 * tm1 / lg3
    info("-8 theta(-1,3) / log_13(3) = %s" % rat)
    approx = None
    for cand in [1, -1, 2, -2, 13, -13, 1296, -1296, 16848, -16848,
                 QQ(1)/2, QQ(-1)/2, 8, -8, 4, -4, 3, -3, 6, -6, 12, -12,
                 324, -324, 648, -648, 2592, -2592, 33696, -33696]:
        if vz(rat - K(QQ(cand)), N) >= min(cert, vz(rat, N) + 3):
            approx = cand
            break
    check(approx is not None,
          "and it is the rational number %s (to p^%s): under h_2(-1,3) = 0 the "
          "B-free equation reproduces E086's h_3 exactly, fixing the sign and "
          "the normalisation of Z at once"
          % (approx, vz(rat - K(QQ(approx)), N) if approx is not None else "-"))

    print("(10) DO THE KNOWN POINTS SPAN?  --- the diagnosis for (7)")
    # The Prym row of x is m_2 * sym(a (x) (a - kappa')) with a = AJ_b(x)'.
    # It is a quadratic function of a, so the three rows can only span Sym^2 of
    # the Prym plane if the a's themselves span that plane.
    allpts = [BASE] + GOOD + [(QQ(0), QQ(0))]
    AJ = [D[pt][0] for pt in allpts]
    v1 = min(vz(a, N) for r in AJ for a in r)
    sc = [[ZZ((a / K(P_GATE)**v1).residue(cert - v1)) if a != 0 else ZZ(0)
           for a in r] for r in AJ]
    ev = matrix(ZZ, sc).elementary_divisors()
    rkAJ = len([d for d in ev if d != 0
                and ZZ(d).valuation(P_GATE) < cert - v1])
    info("AJ_b at the nine points: entries of valuation >= %s, known to p^%d, "
         "elementary divisor valuations %s"
         % (v1, cert, [str(ZZ(d).valuation(P_GATE)) if d != 0 else "inf"
                       for d in ev]))
    # and the Prym plane on its own
    scP = [[ZZ((r[j] / K(P_GATE)**v1).residue(cert - v1)) if r[j] != 0
            else ZZ(0) for j in (1, 2)] for r in AJ]
    evP = matrix(ZZ, scP).elementary_divisors()
    rkP = len([d for d in evP if d != 0
               and ZZ(d).valuation(P_GATE) < cert - v1])
    info("the Prym components alone: elementary divisor valuations %s"
         % [str(ZZ(d).valuation(P_GATE)) if d != 0 else "inf" for d in evP])
    # WHICH Prym directions do the orbits use?  The Prym row of x is
    # m_2 * sym(a (x) (a - kappa')) with a = AJ_b(x)'; writing a = alpha kappa'
    # + beta e it is  alpha(alpha-1) kk + beta(2alpha-1) ke + beta^2 ee, so the
    # three rows are dependent as soon as one of the two beta's vanishes, i.e.
    # as soon as one orbit's Prym direction is PROPORTIONAL to kappa'.
    def minor(P, Qd):
        v = D[P][0][1] * D[Qd][0][2] - D[P][0][2] * D[Qd][0][1]
        pr = min(vz(D[P][0][j], N) for j in (1, 2))
        pr = min(pr, min(vz(D[Qd][0][j], N) for j in (1, 2))) + cert
        return v, ZZ(pr)
    sb = (QQ(1), QQ(-3))
    # if AJ(x)' = alpha kappa', alpha is a rational number and the relation
    # alpha [sigma b - b] = [x - b] holds in the Prym, up to torsion
    for pt in [sb, (QQ(-2), QQ(6)), (QQ(0), QQ(0)),
               (QQ(-1), QQ(3)), (QQ(-1)/11, QQ(15)/11)]:
        al = [D[pt][0][j] / kap[j] for j in (1, 2)]
        rec = None
        for num in range(-40, 41):
            for den in [1, 2, 3, 4, 5, 6, 8, 9, 11, 12]:
                q = QQ(num) / QQ(den)
                if all(vz(a - K(q), N) >= cert - 1 for a in al):
                    rec = q
                    break
            if rec is not None:
                break
        info("AJ(%-16s)' / kappa' = %s   %s"
             % (pt, [str(vz(a - al[0], N)) for a in al[1:]],
                "= %s  <-- a Mordell-Weil relation in the Prym" % rec
                if rec is not None else "(not a small rational, or not "
                "proportional)"))
    for (a, bq, nm) in [(sb, (QQ(-2), QQ(6)), "kappa' , AJ(-2,6)'"),
                        (sb, (QQ(-1)/11, QQ(15)/11), "kappa' , AJ(-1/11)'"),
                        ((QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11),
                         "AJ(-2,6)' , AJ(-1/11)'")]:
        v, pr = minor(a, bq)
        info("2x2 Prym minor of %-24s : valuation %s, known to p^%s  %s"
             % (nm, vz(v, N), pr,
                "<-- PROPORTIONAL" if vz(v, N) >= pr else ""))
    check(rkAJ == 3 and rkP == 2,
          "the Abel-Jacobi images of the nine rational points span all of "
          "H^0(Omega^1)^* (rank %d) and their Prym components span the Prym "
          "plane (rank %d).  If they did not, no amount of precision could "
          "make (7) invertible" % (rkAJ, rkP))

    print("=" * 72)
    print("E088 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
