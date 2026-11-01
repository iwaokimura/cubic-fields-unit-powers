# check-c4-phase5.sage --- E093: the Phase 5 accounting, redone with h_2 and
# h_3 in place.
#
# Run: sage check-c4-phase5.sage        (E093_N, E093_E override N and e)
#
# WHY THE OLD ACCOUNTING IS WRONG.  Every number E087-E090 read off the height
# system was read with h_2 assumed zero.  E091 refuted that assumption and E092
# measured what replaces it:
#     h_3(-1,3) = h_3(0,0) = -4212 log_13(3),   h_3 = 0 at b, (-2,6), (-1/11),
#     h_2(-1,3) = h_2(-1/11) = 0,   h_2(0,0) + h_2(-2,6)/3 = 2808 log_13(2),
# the last splitting into h_2(0,0) = h_2(-2,6) = 2106 log_13(2) under E092's
# cluster rule [P].  In particular E090's H_1 = 4 theta(-2,6)/(3 m_2) -- the
# first p-adic height this project ever computed -- was read off an equation
# with a missing term.  This gate redoes the arithmetic.
#
# THE SYSTEM, WITH THE LOCAL HEIGHTS RESTORED.  Write theta_1, theta_2,
# theta_3, theta_4 for theta at (-1,3), (-2,6), (-1/11,15/11), (0,0), and
# c_3 := h_3, c_2 := h_2 on the vertex where each is nonzero (E090's sign
# convention is theta = -h_3 at (-1,3), so c_3 = -theta_1 IS h_3 and not its
# negative -- a slip worth naming, since the two differ by a sign in every
# formula below).  Then
#
#   theta_1 = -c_3                                       [E_2 = 0 there]
#   theta_2 = (3 m_2/4) H_1              - c_2           [v_0 = 0 there]
#   theta_3 = B_11 u0v0 - (m_2/4) H_1 + (m_2/4) H_2      [h_2 = h_3 = 0 there]
#   theta_4 =           - (m_2/4) H_1 - c_3 - c_2        [u_0 = 0 EXACTLY]
#
# Equations 1, 2 and 4 involve only c_3, c_2, H_1 and they DETERMINE all three:
#
#   c_3 = -theta_1 ,
#   H_1 = (theta_1 + theta_2 - theta_4)/m_2 ,            <- eq2 minus eq4
#   c_2 = (3 m_2/4) H_1 - theta_2 = -(3/4) D ,           D = theta_4 + theta_2/3 - theta_1
#
# so H_1 comes out in closed form from three measured numbers and m_2, with no
# assumption about h_2 beyond E092's cluster rule (which is what lets eq2 and
# eq4 share one c_2 rather than carry two unknowns).  Equation 3 is then one
# equation in the two unknowns B_11 and H_2, and that is where Phase 5 stands.
#
# THE SHIFT.  Against E090's reading, H_1 moves by exactly 4 c_2/(3 m_2), and
# every Prym height downstream inherits it.
#
# UPSILON, WHICH IS WHAT CHABAUTY-KIM ACTUALLY CONSUMES.  The finiteness
# statement needs the finite set of values of sum_ell h_ell over X(Q), not the
# values at the points already known.  Two things bound it.
#
#   (a) [T] C_4 has good reduction away from {2,3}.  C_4 -> E' is the double
#       cover (t,w) -> (t,w^2) of v^2 = 9(t-1)^4-27t^4+108t branched at the four
#       points over t = 0 and t^3 = 4.  E' is isomorphic to y^2 = x^3-36x
#       (E037(f)), which is bad only at 2 and 3; the branch divisor t(t^3-4)
#       degenerates only where t and t^3-4 meet (ell | 4) or t^3-4 has a
#       repeated root (disc = -432, so ell in {2,3}).  So no other prime
#       contributes to Upsilon at all.  The gate checks the plane quartic is
#       smooth mod ell for the primes up to 100 as a sanity test on that.
#
#   (b) At ell = 3 the graph is KNOWN (E083, E084): two vertices, so h_3 takes
#       exactly two values and that half of Upsilon is complete.  At ell = 2 the
#       graph is NOT known -- only its values at the nine rational points -- so
#       the set below is a LOWER BOUND on Upsilon, and this gate says so rather
#       than pretending otherwise.
#
# THE CHECKS.
#   (1) The corrected system: the three vanishings re-measured, and c_3, c_2,
#       H_1 solved from equations 1, 2, 4.
#   (2) H_1 against E090's value, with the shift 4 c_2/(3 m_2) confirmed.
#   (3) NEGATIVE CONTROL: with h_2 = 0 the same three equations are
#       INCONSISTENT, and by exactly D -- which is E091's measurement seen from
#       the other side.
#   (4) H_1 and H_2 - H_1 are not rational multiples of log_13(2) or log_13(3):
#       they are p-adic heights of Prym classes and have no reason to be, and if
#       one of them were, the split in (1) would be an artefact.
#   (5) Upsilon: the values of h_2 + h_3 at the nine rational points, the
#       good-reduction statement, and what is still missing from it.
#   (6) What remains: equation 3, and E088's (B5) re-verified -- the obstruction
#       is about the POINTS and is untouched by any of this.

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
N = ZZ(os.environ.get("E093_N", 12))
EE = ZZ(os.environ.get("E093_E", 104))
BASE = (QQ(1), QQ(3))
SIGB = (QQ(1), QQ(-3))
BAD = (QQ(0), QQ(0))
P13, P26, P11 = (QQ(-1), QQ(3)), (QQ(-2), QQ(6)), (QQ(-1)/11, QQ(15)/11)
ORBITS = [(P13, (QQ(-1), QQ(-3))), (P26, (QQ(-2), QQ(-6))),
          (P11, (QQ(-1)/11, QQ(-15)/11))]

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


def main():
    print("=== check-c4-phase5.sage --- E093: the Phase 5 accounting, redone "
          "===")
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

    TH, E1, E2 = {}, {}, {}
    for c in [BASE, SIGB] + [q for orb in ORBITS for q in orb]:
        P = pt(c)
        al, bp, gp, gf = LH.frob_data(P)
        TH[c] = LH._assemble(al, bp, gp, gf)
        E1[c] = [al[i] for i in range(g)]
        E2[c] = [bp[j] - K0(QQ(LH.beta_fil[j])) for j in range(g, n)]

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

    th1, th2, th3 = TH[P13], TH[P26], TH[P11]
    th4 = TH[BAD]
    m2 = QQ(FS.Z[1][4])
    L2, L3 = K0(2).log(), K0(3).log()

    def recon(val, base, lev, lab):
        r = qp_part(val / Kx(base), EE) if val.parent() is Kx else val / base
        k = ZZ(QQ(lev).floor()) - ZZ(QQ(vz(base)).floor())
        if k < 1:
            info("%-32s no precision left" % lab)
            return None
        a = ZZ(r.residue(k)) if r != 0 else ZZ(0)
        try:
            out = QQ(Mod(a, ZZ(P_GATE)**k).rational_reconstruction())
        except (ArithmeticError, ValueError, ZeroDivisionError):
            out = None
        lim = ZZ(P_GATE)**(QQ(k) / 2)
        hit = (out is not None and out.denominator() == 1
               and abs(out) < lim and out != 0)
        info("%-32s mod 13^%-2d : %-12s %s"
             % (lab, k, out if out is not None else "(none)",
                "INTEGER (%.1e of residues)" % (2.0 / float(lim)) if hit
                else "-- not an integer below 13^(k/2)"))
        return out if hit else None

    print("(1) THE CORRECTED SYSTEM")
    check(min(vz(a) for a in E2[P13]) >= cert,
          "E_2((-1,3)) = 0 to p^%s, so equation 1 reads theta_1 = -c_3"
          % min(vz(a) for a in E2[P13]))
    check(vz(E2[P26][0]) >= cert,
          "the elliptic coordinate of E_2((-2,6)) vanishes to p^%s, so "
          "equation 2 has no B_11" % vz(E2[P26][0]))
    check(vz(alz[0], EE) >= min(pv, floorz),
          "u_0((0,0)) = 0 to p^%s (and exactly, E090), so equation 4 has no "
          "B_11 either" % vz(alz[0], EE))
    c3 = -th1
    H1 = (Kx(th1) + Kx(th2) - Kx(th4)) / Kx(QQ(m2))
    c2 = Kx(QQ(3 * m2 / 4)) * H1 - Kx(th2)
    D = Kx(th4) + Kx(th2) / Kx(3) - Kx(th1)
    info("m_2 = %s" % m2)
    info("c_3 = -theta_1                          = %s" % c3)
    info("H_1 = (theta_1+theta_2-theta_4)/m_2     = %s" % H1)
    info("c_2 = (3m_2/4) H_1 - theta_2            = %s" % c2)
    r3 = recon(c3, L3, cert, "c_3 / log_13(3)")
    # c_2 inherits theta_4's precision, so it is quoted at BOTH levels, as E092
    # does: the certificate p^{86/13} leaves k = 5 and a height limit
    # 13^{5/2} = 609, below the 2106 being looked for; the measured floor -- the
    # first pi-exponent not divisible by e, everything here being a Q_p-number
    # merely routed through Q_p(p^{1/e}) -- leaves k = 7 and a limit of
    # 13^{7/2} = 7921.
    recon(c2, L2, min(pv, floorz), "c_2 / log_13(2)  [certified]")
    r2 = recon(c2, L2, qp_floor(c2, EE), "c_2 / log_13(2)  [measured]")
    recon(c2, L3, qp_floor(c2, EE), "c_2 / log_13(3)  [measured]")
    check(r3 == -4212,
          "c_3 = -4212 log_13(3), i.e. h_3(-1,3) = h_3(0,0) = %s log_13(3) "
          "(E092, reconfirmed)" % (r3 if r3 is not None else "?"))
    check(r2 == 2106,
          "c_2 = 2106 log_13(2), i.e. h_2(-2,6) = h_2(0,0) = %s log_13(2) "
          "under E092's cluster rule -- and c_2 = -(3/4) D is the same number "
          "E091 measured, arrived at from the system rather than from the "
          "residual" % (r2 if r2 is not None else "?"))
    check(vz(c2 + Kx(3) * D / Kx(4), EE) >= min(pv, floorz),
          "c_2 = -(3/4) D identically, to p^%s"
          % vz(c2 + Kx(3) * D / Kx(4), EE))

    # THE IDENTIFICATION, VERIFIED RATHER THAN RECONSTRUCTED (2026-09-01).
    # Reconstruction needs a height
    # bound, and at the certificate that bound is 13^(5/2) = 609 -- below the
    # 2106 being looked for.  So the [certified] line above returns nothing and
    # the check on r2 rests on the MEASURED floor, which is one step weaker
    # than everything around it.  E133/E135 derive both rationals from the
    # regular models at 3 and at 2, independently of this system; with the
    # candidate supplied from outside, confirming it costs only precision, and
    # the certificate is enough.  These two checks are that confirmation.
    check(vz(Kx(c3) + Kx(4212) * Kx(L3), EE) >= min(pv, floorz),
          "c_3 = -4212 log_13(3) VERIFIED to p^%s against E133's derived "
          "q_3 = 1/2 -- a verification needs no height bound, only precision"
          % vz(Kx(c3) + Kx(4212) * Kx(L3), EE))
    check(vz(Kx(c2) - Kx(2106) * Kx(L2), EE) >= min(pv, floorz),
          "c_2 = +2106 log_13(2) VERIFIED to p^%s against E135's derived "
          "q_2 = -1/4.  This is the link the certificate could NOT "
          "reconstruct (13^(5/2) = 609 < 2106), and it is now certified"
          % vz(Kx(c2) - Kx(2106) * Kx(L2), EE))
    # NOT looked for in advance: the two rationals turn out to be m_2 itself.
    check(r3 is not None and QQ(-r3) == m2 / 4 and r2 is not None
          and QQ(r2) == m2 / 8,
          "and the two rationals are not arbitrary: c_3 = m_2/4 and "
          "c_2 = m_2/8 EXACTLY, with m_2 = %s = %s.  So "
          "h_3 = -(m_2/4) log_13(3) and h_2 = +(m_2/8) log_13(2) -- same "
          "modulus up to a power of 2, OPPOSITE signs -- on the "
          "vertices where they are nonzero, and E088's M_11 = -33696 is -2 m_2"
          % (m2, factor(ZZ(m2))))

    print("(2) H_1, AND HOW FAR E090 WAS OUT")
    H1_old = K0(4) * th2 / (K0(3) * K0(QQ(m2)))
    shift = Kx(4) * c2 / (Kx(3) * Kx(QQ(m2)))
    info("E090's H_1 = 4 theta(-2,6)/(3 m_2)      = %s" % H1_old)
    info("corrected H_1                           = %s" % H1)
    info("shift  4 c_2/(3 m_2)                    = %s" % shift)
    check(vz(H1 - Kx(H1_old) - shift, EE) >= min(pv, floorz),
          "the corrected H_1 exceeds E090's by exactly 4 c_2/(3 m_2), to p^%s"
          % vz(H1 - Kx(H1_old) - shift, EE))
    info("the shift has valuation %s while H_1 has valuation %s: the "
         "correction is NOT a small perturbation of E090's number"
         % (vz(shift, EE), vz(H1, EE)))

    print("(3) NEGATIVE CONTROL: THE h_2 = 0 SYSTEM IS INCONSISTENT")
    # with c_2 = 0 the same three equations over-determine H_1
    H1_a = K0(4) * th2 / (K0(3) * K0(QQ(m2)))                 # from eq 2
    H1_b = -Kx(4) * (Kx(th4) + Kx(c3)) / Kx(QQ(m2))           # from eq 4
    gap = Kx(H1_a) - H1_b
    info("h_2 = 0 forces H_1 = %s from equation 2" % H1_a)
    info("                and H_1 = %s from equation 4" % H1_b)
    info("the two disagree by %s" % gap)
    check(vz(gap, EE) < min(pv, floorz),
          "they disagree well inside the certificate p^%s: the h_2 = 0 system "
          "is INCONSISTENT, which is E091's refutation seen from the other "
          "side" % min(pv, floorz))
    check(vz(gap - Kx(4) * D / Kx(QQ(m2)), EE) >= min(pv, floorz),
          "and the inconsistency is exactly 4D/m_2 -- eq2 gives "
          "4 theta_2/(3 m_2), eq4 gives -4(theta_4 - theta_1)/m_2, and their "
          "difference is 4/m_2 times theta_4 + theta_2/3 - theta_1 = D.  So it "
          "is E091's ONE number and not a second, independent failure")

    print("(4) CONTROLS: THE PRYM HEIGHTS ARE NOT LOGARITHMS")
    ok4 = True
    for lab, v in [("H_1", H1)]:
        for bl, base in [("log_13(2)", L2), ("log_13(3)", L3)]:
            # the MEASURED floor, i.e. the strongest form of the test
            if recon(v, base, qp_floor(v, EE),
                     "%s / %s" % (lab, bl)) is not None:
                ok4 = False
    check(ok4,
          "H_1 is not a small integer multiple of either log: it is the p-adic "
          "height of [sigma b - b] in the Prym and has no reason to be one.  "
          "Had it reconstructed, the split of (1) would be an artefact")

    print("(5) UPSILON")
    Fh = PolynomialRing(QQ, ['X', 'Y', 'Z'])
    X, Y, Z = Fh.gens()
    F = Y**4 - 6*(X - Z)**2*Y**2 + 27*X**4 - 108*X*Z**3
    bad = []
    for ell in prime_range(3, 100):
        try:
            if not Curve(F.change_ring(GF(ell))).is_smooth():
                bad.append(ell)
        except Exception:
            bad.append(ell)
    check(bad == [3],
          "the plane quartic is smooth mod every prime 3 < ell < 100 and "
          "singular mod 3 (mod 2 it is the quadruple line (Y+X)^4, excluded "
          "from the loop): consistent with C_4 having good reduction away from "
          "{2,3}, which follows from E' = C_4/sigma being bad only at 2, 3 and "
          "the branch divisor t(t^3-4) degenerating only there.  Bad primes "
          "found: %s" % bad)
    # the vertex PATTERNS, which do not depend on the reconstructions:
    # E084's table at ell = 3, E092's cluster rule at ell = 2.
    JG3 = {QQ(1): 0, QQ(-2): 0, QQ(-1)/11: 0, QQ(-1): 1, QQ(0): 1}
    JG2 = {QQ(1): 0, QQ(-1): 0, QQ(-1)/11: 0, QQ(-2): 1, QQ(0): 1}
    pat = dict((t, (JG3[t], JG2[t])) for t in JG3)
    info("(j_3, j_2) at the nine rational points, and h_3 + h_2 there "
         "(c_3 = h_3 and c_2 = h_2, so the entries are j times c):")
    for t in sorted(pat, reverse=True):
        info("   t = %-8s : %s   ->   %s log_13(3) %+d log_13(2)"
             % (t, pat[t],
                pat[t][0] * (r3 if r3 is not None else 0),
                pat[t][1] * (r2 if r2 is not None else 0)))
    check(len(set(pat.values())) == 4,
          "all four (j_3, j_2) patterns occur among the nine rational points, "
          "so Upsilon contains at least the four values 0, c_3, c_2, "
          "c_3+c_2.  At ell = 3 that half is COMPLETE (E083: Gamma_3 has two "
          "vertices, so h_3 takes two values and no more); at ell = 2 the "
          "graph is unknown and only its values at these points are, so four "
          "is a LOWER bound on Upsilon and not its size")

    print("(6) WHAT REMAINS")
    u1, v1 = E1[P11][0], E2[P11][0]
    info("equation 3 reads  theta_3 = B_11 u_0 v_0 - (m_2/4) H_1 "
         "+ (m_2/4) H_2, with u_0 v_0 of valuation %s" % vz(u1 * v1))
    rhs = Kx(th3) + Kx(QQ(m2 / 4)) * H1
    info("so  B_11 u_0 v_0 + (m_2/4) H_2 = %s" % rhs)
    check(vz(u1 * v1) < cert,
          "the elliptic coefficient is a unit-ish %s, so B_11 does not drop "
          "out: one equation, two unknowns, and Phase 5 stops here unless "
          "B_11 comes from outside (Sage's p-adic height on y^2 = x^3-36x)"
          % vz(u1 * v1))
    info("(B5) is untouched by any of this: it is a statement about the "
         "POINTS, not about h_ell.  The Prym classes of eight of the nine "
         "rational points lie on the line Q kappa', so the third Gram entry "
         "of hhat_P -- the pairing <kappa', delta_11> -- appears in NO "
         "equation, whatever the local heights are.")

    print("=" * 72)
    print("E093 GATE: %s   (%d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)


main()
