# check-c4-h2.sage --- E092: how much of h_2 the quadratic Chabauty system on
# C_4's rational points actually determines.
#
# Run: sage check-c4-h2.sage          (E092_N, E092_E override N and e)
#
# WHERE THIS STARTS.  E091 computed the global iterated Coleman integral into
# ](0,0)[ and found E090's prediction FALSE by
#     D := theta_b(0,0) - [theta(-1,3) - theta(-2,6)/3] = -2808 log_13(2),
# a unique rational reconstruction at 13^8.  Since [BDMTV2023] Theorem 3.2 makes
# every h_ell a rational multiple of log_p(ell), and since the premises the
# prediction was built from cancel everything else, D is a combination of values
# of h_2 -- so h_2 is NOT zero on C_4, and the assumption every equation of
# Phase 5 rests on is false.  This gate asks the obvious next question: how many
# of the individual h_2(x) does the system pin down?
#
# THE ANSWER, DERIVED HERE BEFORE ANY CODE, IS TWO OF FOUR UNKNOWNS.  Write the
# system out.  With B_11 the elliptic height coefficient, H_1 = hhat_P(kappa'),
# H_2 the remaining Prym height, and h_3* := h_3(-1,3) = h_3(0,0) (E084: the two
# reduce to the same vertex of Gamma_3), the four equations are
#
#   theta(-1,3)   =                                 - h_3* - h_2(-1,3)
#   theta(-2,6)   =            (3 m_2/4) H_1               - h_2(-2,6)
#   theta(-1/11)  = B_11 u0v0 - (m_2/4) H_1 + (m_2/4) H_2  - h_2(-1/11)
#   theta(0,0)    =          - (m_2/4) H_1        - h_3*   - h_2(0,0)
#
# the zeros being E088's E_2((-1,3)) = 0, E088's v_0((-2,6)) = 0, and E090's
# EXACT u_0((0,0)) = 0 in E(Q).  The coefficient matrix of (B_11, H_1, H_2) has
# rank 2 -- H_2 and B_11 occur in the third row only, and the second and fourth
# rows are proportional -- so its LEFT KERNEL is 2-dimensional, spanned by
#
#     A := theta(-1,3),          B := theta(0,0) + theta(-2,6)/3 .
#
# Those are the only two combinations of measured thetas from which the p-adic
# unknowns drop out.  They give
#
#     A = -h_3* - h_2(-1,3),     B = -h_3* - h_2(0,0) - h_2(-2,6)/3 ,
#
# two equations in the four unknowns h_3*, h_2(-1,3), h_2(-2,6), h_2(0,0).
#
# WHAT MAKES THEM WORTH FOUR AND NOT TWO.  h_3* lies in Q log_13(3) and every
# h_2 in Q log_13(2), so EACH relation splits in two along that decomposition --
# provided log_13(2) and log_13(3) are Q-linearly independent, which is a
# transcendence statement nobody can prove and which is assumed here and said so.
# A then gives h_3* AND h_2(-1,3) separately; B gives h_3* again (a check that
# owes nothing to A, since D was measured against log_13(3) and found nothing)
# and one combination of h_2(0,0), h_2(-2,6).  Three of the four unknowns fall
# out; the fourth needs the graph Gamma_2, i.e. the semistable model at 2, which
# is wild and blocked (E085).
#
# HOW THE DECOMPOSITION IS TESTED, and why not by lindep.  A three-term p-adic
# lindep on (theta, log 2, log 3) needs coefficients of size H to satisfy
# H^3 < p^k; at our k = 9 that is H < 2197, below the 4212 we are looking for,
# so lindep returns junk -- check-c4-h2.gp demonstrates that on a SYNTHETIC
# number whose relation is known.  The test that works is the ONE-term
# reconstruction theta/log_13(ell) in Q, unique for heights below
# sqrt(13^9/2) = 7.0e4, and it is the right test precisely because the structure
# above predicts which single log each combination should be a multiple of.
#
# THE CHECKS.
#   (1) The three vanishings and the delta-values that make the matrix what it
#       is, re-measured rather than quoted, and the rank and left kernel
#       computed exactly over Q from them.
#   (2) A and B, the two combinations, with their certificates.
#   (3) A/log_13(3) and (B-A)/log_13(2) by unique rational reconstruction; and
#       A/log_13(2), (B-A)/log_13(3) must FAIL to reconstruct.
#   (4) CONTROLS: theta(-2,6) and theta(-1/11), which contain H_1, H_2, B_11,
#       must admit no small one-term reconstruction against either log.
#   (5) theta(sigma x) = theta(x), hence h_ell is sigma-invariant on Gamma_ell.
#   (6) What remains: the partition of the rational points by t mod 2, and what
#       it would give if it were the reduction partition at 2.  [P], and marked
#       as such -- but NOT numerology.  check-c4-h2.gp derives the SAME
#       partition from the cluster picture of the four branch points of
#       C_4 -> E (t = 0 and t^3 = 4: for t in Q the three cube roots are
#       conjugate, so "t is in the cluster" reads v_ell(t^3-4) > 0), and
#       verifies that the identical rule reproduces E084's j_Gamma table at
#       ell = 3, where the semistable model was computed independently.  That
#       derivation lives there because it is exact arithmetic over Q and
#       belongs in PARI/GP.

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure
from padic.height import LocalHeight
from padic.points import CurvePoint, LocalExpansion
from padic.integrals import ColemanIntegrals, tprec_for, prop46_precision

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
P_GATE = 13
N = ZZ(os.environ.get("E092_N", 12))
# e = 104, not 52: D is what carries the h_2 information, and at e = 52 its
# measured floor is p^{27/4}, giving k = 5 and a height limit 13^{5/2} = 609 --
# below the 2808 E091 found.  e = 104 lifts the floor to p^{67/8}, k = 7, limit
# 13^{7/2} = 8021.  It costs about half an hour more (E091 measured it).
EE = ZZ(os.environ.get("E092_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
ORBITS = [(P13, (QQ(-1), QQ(-3))), (P26, (QQ(-2), QQ(-6))),
          (P11, (QQ(-1)/11, QQ(-15)/11))]

FAIL = []
MEASURED = []


def check(cond, msg):
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def measure(cond, name, msg):
    ok = bool(cond)
    print("   %s %s: %s" % ("[HOLDS ]" if ok else "[REFUTED]", name, msg))
    MEASURED.append((name, ok))
    sys.stdout.flush()
    return ok


def info(msg):
    print("        %s" % msg)
    sys.stdout.flush()


def main():
    print("=== check-c4-h2.sage --- E092: how much of h_2 the system "
          "determines ===")
    t00 = time.time()
    C = TuitmanCurve(Q1, name="C_4")
    H = Cohomology(C)
    g, n = ZZ(C.genus), 2 * ZZ(C.genus)
    t0 = time.time()
    FS = FrobeniusStructure(C, H, P_GATE, N, BASE, sx=1, sy=-1)
    FS.solve()
    K0, cert = FS.K, FS.cert
    LH = LocalHeight(FS, BASE, fil0_correction=True)
    CI = ColemanIntegrals(FS.FM)
    info("(22) solved and the Hodge side built: N = %d, certified p^%d "
         "(%.0f s)" % (N, cert, time.time() - t0))

    def vz(a, e=1):
        return QQ(N + 4) if a == 0 else QQ(a.valuation()) / e

    def qp_floor(a, e):
        if e == 1 or a == 0:
            return QQ(N + 4)
        best = QQ(N + 4)
        for i, c in enumerate(a.polynomial()):
            if i > 0 and c != 0:
                best = min(best, QQ(c.valuation()) + QQ(i) / e)
        return best

    def qp_part(a, e):
        if e == 1:
            return a
        cl = list(a.polynomial()) if a != 0 else [a.parent().base_ring()(0)]
        return cl[0] if cl else 0

    def pt(c, ring=None):
        ring = ring if ring is not None else K0
        return CurvePoint(FS.RR, ring(c[0]), y=ring(c[1]), ring=ring)

    # ------------------------------------------------ theta at the nine points
    TH, E1, E2 = {}, {}, {}
    for c in [BASE, SIGB] + [q for orb in ORBITS for q in orb]:
        P = pt(c)
        al, bp, gp, gf = LH.frob_data(P)
        TH[c] = LH._assemble(al, bp, gp, gf)
        E1[c] = [al[i] for i in range(g)]
        E2[c] = [bp[j] - K0(QQ(LH.beta_fil[j])) for j in range(g, n)]

    # theta at (0,0), by E091's route
    Kx = CI.extension(EE)
    tp = tprec_for(P_GATE, N, EE)
    PzK = pt(BAD).change_ring(Kx)
    t0 = time.time()
    LEb = LocalExpansion(PzK, tp, ring=Kx)
    Pp = LEb.point_at(Kx.gen())
    M, _, IP = FS.frob_triv_general(Pp, at=PzK, LE=LEb)
    alz, bpz, gpz = FS.read_triv(IP.inverse() * M)
    TH[BAD] = LH._assemble(alz, bpz, gpz, LH._fn_at(LH.gamma_fil, PzK))
    kmax = max(ZZ(FS.RR.J_range(a)[1])
               for a in [FS.h] + list(FS.g_vec) + list(FS.f))
    pv = prop46_precision(P_GATE, cert, Pp.vp(Pp.rval), kmax,
                          ZZ(getattr(FS.FM, "e_finite", 1)))
    floorz = qp_floor(TH[BAD], EE)
    info("theta at (0,0) by E091's iterated integral: e = %d, certified p^%s, "
         "measured floor p^%s  (%.0f s)" % (EE, pv, floorz, time.time() - t0))

    print("(1) THE STRUCTURE OF THE SYSTEM")
    e13 = min(vz(a) for a in E2[P13])
    check(e13 >= cert,
          "E_2((-1,3)) = 0 to p^%s: every bilinear term vanishes there, so "
          "that equation carries no p-adic unknown at all (E088)" % e13)
    v026 = vz(E2[P26][0])
    check(v026 >= cert,
          "the elliptic coordinate of E_2((-2,6)) vanishes to p^%s, so B_11 "
          "does not enter that equation (E088)" % v026)
    u000 = vz(alz[0], EE)
    check(u000 >= min(pv, floorz),
          "u_0((0,0)) = 0 to p^%s -- and EXACTLY, since E090 identified "
          "[(0,0)bar - bbar] as 2-torsion in E(Q) = Z + (Z/2)^2 -- so B_11 "
          "does not enter that equation either" % u000)
    m2 = QQ(FS.Z[1][4])
    # the coefficient matrix of (B_11, H_1, H_2), from the vanishings above and
    # E089's delta-form of the Prym height with delta = kappa', -2 kappa', 0.
    Amat = matrix(QQ, [[0, 0, 0],
                       [0, 3 * m2 / 4, 0],
                       [1, -m2 / 4, m2 / 4],
                       [0, -m2 / 4, 0]])
    ker = Amat.left_kernel()
    check(Amat.rank() == 2 and ker.dimension() == 2,
          "the 4x3 coefficient matrix of (B_11, H_1, H_2) has rank %d, so "
          "exactly %d combinations of the four thetas are free of them"
          % (Amat.rank(), ker.dimension()))
    want = matrix(QQ, [[1, 0, 0, 0], [0, QQ(1)/3, 0, 1]])
    check(ker == want.row_space(),
          "and they are spanned by A = theta(-1,3) and "
          "B = theta(0,0) + theta(-2,6)/3 -- the first because that row is "
          "identically zero, the second because rows 2 and 4 are proportional "
          "while H_2 and B_11 live in row 3 alone")

    print("(2) THE TWO COMBINATIONS")
    A = TH[P13]
    B = Kx(TH[BAD]) + Kx(TH[P26]) / Kx(3)
    D = B - Kx(A)
    info("A = theta(-1,3)                    = %s" % A)
    info("B = theta(0,0) + theta(-2,6)/3     = %s" % B)
    info("D = B - A                          = %s" % D)
    info("A is certified to p^%d; B and D to p^%s (measured floor p^%s)"
         % (cert, pv, qp_floor(D, EE)))

    print("(3) THE log DECOMPOSITION")
    L2, L3 = K0(2).log(), K0(3).log()
    info("[BDMTV2023] Thm 3.2: h_3* in Q log_13(3) and every h_2 in "
         "Q log_13(2).  ASSUMED, and unprovable at present: log_13(2) and "
         "log_13(3) are Q-linearly independent.  Without it the split below is "
         "not unique.")

    def recon(val, base, lev, lab):
        """val/base as a rational, and whether the answer means anything.

        WHAT COUNTS AS A HIT, stated before the numbers are looked at.  Rational
        reconstruction below sqrt(13^k/2) is unique, but it is NOT rare: the
        fractions a/b with |a|, b under that bound already occupy about 6/pi^2
        of all residues, so "a reconstruction exists" is close to a coin toss
        and is worthless as evidence.  What is rare is an INTEGER: the residues
        reconstructing to an integer of absolute value below 13^{k/2} are
        2*13^{k/2} out of 13^k, i.e. a fraction 2*13^{-k/2}.  That is the test
        used here -- denominator 1 and height below 13^{k/2} -- and the
        printout gives that fraction so the reader can judge it.
        """
        r = qp_part(val / Kx(base), EE) if val.parent() is Kx \
            else val / base
        k = ZZ(QQ(lev).floor()) - ZZ(QQ(vz(base)).floor())
        if k < 1:
            info("%-30s no precision left (k = %s)" % (lab, k))
            return None, k
        a = ZZ(r.residue(k)) if r != 0 else ZZ(0)
        try:
            out = QQ(Mod(a, ZZ(P_GATE)**k).rational_reconstruction())
        except (ArithmeticError, ValueError, ZeroDivisionError):
            out = None
        lim = ZZ(P_GATE)**(QQ(k) / 2)
        hit = (out is not None and out.denominator() == 1
               and abs(out) < lim and out != 0)
        info("%-30s mod 13^%-2d : %-12s %s"
             % (lab, k, out if out is not None else "(none below bound)",
                ("INTEGER of height %s < 13^(k/2) = %.0f, which %.1e of "
                 "residues do" % (abs(out), float(lim), 2.0 / float(lim)))
                if hit else "-- not an integer below 13^(k/2)"))
        return (out if hit else None), k

    a3, k3 = recon(A, L3, cert, "A / log_13(3)")
    a2, k2 = recon(A, L2, cert, "A / log_13(2)")
    info("D is limited by Proposition 4.6 at the pushed-out point, so it is "
         "quoted at BOTH levels: the certificate p^%s, and the measured floor "
         "p^%s (the first pi-exponent not divisible by e -- everything here is "
         "a Q_p-number merely routed through Q_p(p^{1/e}))"
         % (pv, qp_floor(D, EE)))
    recon(D, L2, pv, "D / log_13(2)  [certified]")
    d2, kd2 = recon(D, L2, qp_floor(D, EE), "D / log_13(2)  [measured]")
    d3, kd3 = recon(D, L3, qp_floor(D, EE), "D / log_13(3)  [measured]")
    check(a3 is not None and a2 is None,
          "A is a rational multiple of log_13(3) and NOT of log_13(2): "
          "A = %s log_13(3).  Hence h_3* = %s log_13(3) and h_2(-1,3) = 0"
          % (a3, -a3 if a3 is not None else "?"))
    check(d2 is not None and d3 is None,
          "D is a rational multiple of log_13(2) and NOT of log_13(3): "
          "D = %s log_13(2) (E091, confirmed here).  Hence "
          "h_2(0,0) + h_2(-2,6)/3 = %s log_13(2)"
          % (d2, -d2 if d2 is not None else "?"))
    if a3 is not None and d2 is not None:
        info("SO: h_3(-1,3) = h_3(0,0) = %s log_13(3)   [E088 got the same "
             "number from theta(-1,3) alone]" % (-a3))
        info("    h_2(-1,3) = 0")
        info("    h_2(0,0) + h_2(-2,6)/3 = %s log_13(2)" % (-d2))
        info("    h_2(-2,6), h_2(0,0) separately: NOT determined by the system")

    print("(4) CONTROLS")
    ok4 = True
    for lab, v in [("theta(-2,6)", TH[P26]), ("theta(-1/11,15/11)", TH[P11])]:
        for bl, base in [("log_13(2)", L2), ("log_13(3)", L3)]:
            r, _ = recon(v, base, cert, "%s / %s" % (lab, bl))
            if r is not None:
                ok4 = False
    check(ok4,
          "neither theta(-2,6) nor theta(-1/11,15/11) is a small rational "
          "multiple of either log: they contain H_1, H_2 and B_11, which are "
          "p-adic heights and have no reason to be.  If one of them had "
          "reconstructed, the reading of the system in (1) would be wrong")

    print("(5) sigma-INVARIANCE, HENCE h_ell IS A FUNCTION ON Gamma_ell/sigma")
    worst = QQ(N + 4)
    for (a, b) in ORBITS:
        worst = min(worst, vz(TH[a] - TH[b]))
    check(worst >= cert,
          "theta(sigma x) = theta(x) at all three good orbits to p^%s (E088).  "
          "E089 derived the bilinear part's sigma-degeneracy from "
          "delta(sigma x) = -delta(x) and hhat_P even, so what is left is "
          "h_ell(sigma x) = h_ell(x): j_{Gamma_2} is sigma-invariant, which is "
          "a fact about Gamma_2 obtained without the model" % worst)

    print("(6) WHAT IS LEFT, AND THE ONLY HANDLE ON IT WITHOUT THE MODEL")
    info("Mod 2 the plane model degenerates completely: "
         "w^4-6(t-1)^2w^2+27t^4-108t = (w+t)^4 over F_2, a quadruple line.  "
         "So the naive special fibre is irreducible and carries no partition; "
         "what it does carry is the value of t.")
    part = {}
    for c in [BASE, SIGB, P13, (QQ(-1), QQ(-3)), P26, (QQ(-2), QQ(-6)),
              P11, (QQ(-1)/11, QQ(-15)/11), BAD]:
        r = ZZ(c[0].numerator() * c[0].denominator().inverse_mod(2)) % 2
        part.setdefault(r, []).append(c)
    for r in sorted(part):
        info("t = %d mod 2 : %s" % (r, ", ".join(str(c) for c in part[r])))
    measure(BASE in part[1] and P13 in part[1] and P11 in part[1]
            and BAD in part[0] and P26 in part[0],
            "H(t mod 2)",
            "the partition by t mod 2 puts b, (-1,3), (-1/11) together and "
            "(-2,6), (0,0) together.  It PREDICTS h_2(-1,3) = 0, which (3) "
            "measured independently -- and if it is the reduction partition "
            "then h_2(0,0) = h_2(-2,6), so both equal (3/4)(%s) log_13(2)"
            % (-d2 if d2 is not None else "?"))
    if d2 is not None and a3 is not None:
        h2 = -d2 * QQ(3) / QQ(4)
        info("[P] under that partition, h_2(0,0) = h_2(-2,6) = %s log_13(2), "
             "and h_3(-1,3) = %s log_13(3): the ratio of the two rationals is "
             "%s" % (h2, -a3, h2 / (-a3)))
        info("[P] this is a HYPOTHESIS about Gamma_2, not a measurement: the "
             "naive fibre is a quadruple line and the components of a "
             "semistable model are created by blow-ups, so t mod 2 is a guess "
             "at which points end up on which component.  Its one piece of "
             "evidence is the confirmed prediction h_2(-1,3) = 0.")

    print("=" * 72)
    print("E092 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    for nm, ok in MEASURED:
        print("   MEASURED: %-24s %s" % (nm, "holds" if ok else "REFUTED"))


main()
