# check-phase4-fil.sage --- E065 (E048 Phase 4) GATE, part 4.
#
# Steps (ii) and (iii) of the Hodge filtration algorithm, Balakrishnan-Dogra-
# Mueller-Tuitman-Vonk (2019) §4.5: the local solutions g_x, then the constants
# beta_Fil and the function gamma_Fil in H^0(Y, O) with
#
#     g_x - gamma_Fil - beta_Fil^T Omega_x  in  K[[t_x]]   for all x in D.
#
# The checks, and what each would catch:
#
#   (1) SOLVABILITY, and the shape of the system.  The paper calls this a
#       Riemann-Roch problem; we do not solve one.  With W0 = I every place of D
#       lies over x = infinity, so H^0(Y,O) is the integral closure of Q[x],
#       which auxpolys already has as a free module on the b^0_i, and the
#       candidates are x^k b^0_i.  If that were the wrong space the system would
#       be unsolvable -- so solvability IS the check on the claim.
#   (2) THE SOLUTION SPACE HAS DIMENSION g + 1, and its beta-part is exactly
#       Fil^1.  A literal reading of [BDM+19, Lemma 4.7] promises uniqueness;
#       that is false as stated, because a holomorphic differential has a
#       primitive with no principal part and is therefore invisible here.  The
#       claim is checked against E064's holomorphic_classes(), computed by a
#       different route (Sage's basis_of_holomorphic_differentials).
#   (3) THE DEFINING PROPERTY, recomputed AT A DIFFERENT t-adic precision from
#       the solve: g_x - gamma - beta^T Omega_x has non-negative valuation at
#       every place of D.  This does not reuse the linear algebra.
#   (4) gamma REALLY LIES IN H^0(Y, O): its divisor, from Sage's function field,
#       has no pole outside D.  Independent of the construction.
#   (5) gamma(b) = 0 at the base point, evaluated in the function field.
#   (6) PRECISION- AND TRUNCATION-INDEPENDENCE: same beta and gamma at another
#       t-adic precision and another candidate bound kmax.
#   (7) COVARIANCE UNDER THE CONSTANTS OF INTEGRATION.  Omega is defined only up
#       to constants c.  Since dg_x = Omega^T Z omega - eta,
#           dg_x  |-->  dg_x + c^T Z omega,
#       so beta |--> beta + Z^T c and gamma is unchanged.  Checked with a
#       nonzero c: this is a genuine prediction, it fails for any other
#       combination of Z and Z^T, and it is where a transpose error would show.
#       E071 changed the prediction from (2Z - Z^T)c: that was (19) as printed,
#       which the gauge equation (18) does not support unless Z = Z^T.
#   (8) NEGATIVE CONTROL: with the candidate bound kmax cut down so that
#       H^0(Y,O) is no longer reachable, the system must become UNSOLVABLE.  A
#       check that (1) is not passing vacuously.
#
# Run: sage check-phase4-fil.sage

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def one(label, Qxy, sx, sy, base):
    print("-" * 72)
    print(label)
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g = ZZ(C.genus)
    L, xL = C.L, C.L(C.x)
    basis, _ = H.H1X_basis()
    n = len(basis)
    # the CLASS, not the endomorphism matrix (E071); with it Z - Z^T = 2Z, so
    # check (7)'s covariance under the constants of integration is no longer
    # blind to the difference between Z and Z^T
    Z = H.correspondence_class(sx, sy)
    forms = [H.differential_of(v) for v in basis]
    poles = H._pole_places(forms)
    _, eta, _, _ = H.hodge_eta(Z)
    ok = True

    beta, gamma, info = H.hodge_filtration(Z, eta=eta, base=base)
    print("   (1) system %dx%d of rank %d over the %d place(s) of D "
          "(degrees %s), principal parts to t^-%d: SOLVED"
          % (info["system"][0], info["system"][1], info["rank"], len(poles),
             [P.degree() for P in poles], info["depth"]))

    m2 = (info["kernel_dim"] == g + 1) and info["kernel_beta_is_Fil1"]
    print("   (2) solution space has dimension %d, expected g+1 = %d; its "
          "beta-part is Fil^1: %s %s"
          % (info["kernel_dim"], g + 1, info["kernel_beta_is_Fil1"],
             "ok" if m2 else "*** NO ***"))
    ok = ok and m2

    # (3) the defining property, recomputed at another precision.
    #     m(gamma) is the expensive part on C_4 -- gamma's coefficients have
    #     fourteen digits and the place has degree 4 -- and checks (7) and (9)
    #     call this repeatedly, so the expansion of each gamma is memoised.
    #     The differentials come from Cohomology.local_data's own cache.
    gmemo = {}

    def local_defect(beta, gamma, prec, cst=None, tag="", ginfo=None,
                     gextra=None):
        """gamma may be given as a function field element -- expanded through
        L.completion, the route that does not reuse the construction, which is
        what check (3) wants -- or, via ginfo, as the coefficient data
        hodge_filtration returned, rebuilt from the cached candidate series.
        The second route exists because the first costs over eight minutes on
        C_4's shifted gamma; gextra adds a further function-field element."""
        t_a = time.time()
        worst = QQ(0)
        etaform = H.differential_of(eta) if any(c != 0 for c in eta) else None
        for P in poles:
            m, ser, _, _ = H.local_data(P, prec)
            dtdx = P.local_uniformizer().derivative()
            Om = [H._integrate_series(s) for s in ser]
            if cst is not None:
                Om = [Om[i] + Om[i].parent()(QQ(cst[i])) for i in range(n)]
            expr = H._dg_expr(Z, ser, Om, n)
            if etaform is not None:
                expr -= m(etaform / xL.differential() / dtdx)
            gx = H._integrate_series(expr)
            # m(0) raises: the completion map divides by sep^valuation
            t_b = time.time()
            if ginfo is not None:
                gs = H.gamma_series(P, prec, ginfo)
                if gextra is not None and not gextra.is_zero():
                    gs = gs + m(gextra)
                rem = gx - gs
            elif gamma.is_zero():
                rem = gx
            else:
                key = (P, prec, gamma)
                if key not in gmemo:
                    gmemo[key] = m(gamma)
                rem = gx - gmemo[key]
            t_c = time.time()
            for i in range(n):
                if beta[i] != 0:
                    rem -= QQ(beta[i]) * Om[i]
            if not rem.is_zero() and rem.valuation() < 0:
                worst = min(worst, QQ(rem.valuation()))
        if tag and time.time() - t_a > 20:
            print("       [%s: %.0f s, of which expanding gamma %.0f s]"
                  % (tag, time.time() - t_a, t_c - t_b))
            sys.stdout.flush()
        return worst

    # deliberately the same precision check (6) will re-solve at, so that the
    # expansion cache serves both: the two checks differ in content, not in
    # the series they need
    prec3 = info["prec"] + 11
    d3 = local_defect(beta, gamma, prec3, tag="check 3")
    m3 = (d3 == 0)
    print("   (3) g_x - gamma - beta^T Omega is regular at every place of D, "
          "recomputed at t-adic precision %d (solve used %d): %s"
          % (prec3, info["prec"], "ok" if m3 else "*** worst valuation %s ***"
             % d3))
    ok = ok and m3

    # (4) gamma has no pole outside D
    if gamma.is_zero():
        m4 = True
        print("   (4) gamma = 0, trivially in H^0(Y,O)")
    else:
        bad = [P for P, mlt in gamma.divisor().list()
               if mlt < 0 and P not in poles]
        m4 = not bad
        print("   (4) gamma's poles lie in D: %s %s"
              % ([(P.degree(), mlt) for P, mlt in gamma.divisor().list()
                  if mlt < 0], "ok" if m4 else "*** poles outside D: %s ***"
                 % bad))
    ok = ok and m4

    m5 = (H._evaluate(gamma, QQ(base[0]), QQ(base[1])) == 0)
    print("   (5) gamma(b) = 0 at b = %s: %s" % (base, "ok" if m5 else
                                                 "*** NO ***"))
    ok = ok and m5

    b6, g6, i6 = H.hodge_filtration(Z, eta=eta, base=base,
                                    prec=info["prec"] + 11,
                                    kmax=info["kmax"] + 2)
    m6 = (list(b6) == list(beta)) and (g6 == gamma)
    print("   (6) same beta and gamma at precision %d, kmax %d: %s"
          % (i6["prec"], i6["kmax"], "ok" if m6 else "*** NO ***"))
    ok = ok and m6

    # (7) COVARIANCE UNDER THE CONSTANTS OF INTEGRATION.
    #     Omega -> Omega + c changes dg_x = Omega^T Z omega - eta by c^T Z omega,
    #     so
    #         (gamma, beta)  |-->  (gamma, beta + Z^T c)
    #     up to the (g+1)-dimensional ambiguity of the solution.  gamma is NOT
    #     in general unchanged: a beta-direction in Fil^1 makes sum beta_i
    #     omega_i only COHOMOLOGOUS to a holomorphic form, differing by df with
    #     f in H^0(Y,O), and that f moves gamma.  (For a basis whose first g
    #     elements are literally holomorphic differentials -- the bielliptic
    #     curve here -- f = 0 and gamma does stay put.  For C_4 no subset of the
    #     computational basis is holomorphic, as E064 measured, and gamma moves.)
    #     So the honest test is on the PAIR, and it does not go through the
    #     linear algebra at all: correcting the shifted beta by Z^T c must
    #     give a solution of the UNSHIFTED problem.  With (19) as printed the
    #     prediction would be (2Z - Z^T)c instead, which for the antisymmetric
    #     class of E071 is -3 Z c against Z^T c = -Z c, so this check now also
    #     separates the gauge equation from the printed formula.
    c = vector(QQ, [QQ(1 + (i * 5) % 7) for i in range(n)])
    b7, g7, i7 = H.hodge_filtration(Z, eta=eta, base=base, omega_constants=c)
    ZM = matrix(QQ, [[QQ(Z[i][j]) for j in range(n)] for i in range(n)])
    pred = ZM.transpose() * c
    Fil = matrix(QQ, H.holomorphic_classes())
    diff = vector(QQ, b7) - vector(QQ, beta) - pred
    m7 = diff in Fil.row_space()
    print("   (7) beta shifts by Z^T c modulo Fil^1: %s  (residual %s; "
          "gamma moved: %s)"
          % ("ok" if m7 else "*** NO ***", list(diff), g7 != gamma))
    ok = ok and m7
    # at the solve's own precision, not prec3: check (3) is the one that has to
    # be independent of the solve, and expanding the shifted gamma -- whose
    # coefficients have fourteen digits on C_4 -- is the expensive step
    d7 = local_defect(list(vector(QQ, b7) - pred), g7, info["prec"],
                      tag="check 7a", ginfo=i7)
    m7b = (d7 == 0)
    print("       and (gamma_new, beta_new - Z^T c) solves the UNSHIFTED "
          "problem: %s" % ("ok" if m7b else "*** worst valuation %s ***" % d7))
    ok = ok and m7b
    d7c = local_defect(b7, g7, info["prec"], cst=c, tag="check 7b", ginfo=i7)
    m7c = (d7c == 0)
    print("       and the shifted pair solves the shifted problem: %s"
          % ("ok" if m7c else "*** worst valuation %s ***" % d7c))
    ok = ok and m7c

    # (8) NEGATIVE CONTROL A: too few candidates must be unsolvable.  This has
    #     content only when gamma is nonzero -- where gamma = 0 no candidate is
    #     needed at all and kmax = 0 solves it correctly, so scoring it there
    #     would be scoring a vacuous truth.
    try:
        H.hodge_filtration(Z, eta=eta, base=base, kmax=0)
        solved0 = True
    except (ValueError, ArithmeticError):
        solved0 = False
    if gamma.is_zero():
        print("   (8) [negative control, VACUOUS HERE] gamma = 0, so kmax = 0 "
              "needs no candidates and solves it correctly (%s): not scored"
              % ("solved" if solved0 else "unsolvable"))
    else:
        m8 = not solved0
        print("   (8) [negative control] with kmax = 0 the candidates cannot "
              "span H^0(Y,O): %s %s"
              % ("unsolvable, as it must be" if m8 else "solved anyway",
                 "ok" if m8 else "*** NO ***"))
        ok = ok and m8

    # (9) NEGATIVE CONTROL B, which has content on every curve: check (3) must
    #     be SENSITIVE.  Perturb gamma by a candidate with a genuine pole on D
    #     and the defect must become negative.  Without this, a check (3) that
    #     silently measured nothing would pass.
    d9 = local_defect(beta, None, info["prec"], tag="check 9", ginfo=info,
                      gextra=xL)
    m9 = (d9 < 0)
    print("   (9) [negative control] perturbing gamma by x makes check (3) "
          "fail (worst valuation %s): %s" % (d9, "ok" if m9 else "*** NO ***"))
    ok = ok and m9

    print("   beta_Fil = %s" % list(beta))
    print("   gamma_Fil = %s" % gamma)
    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-fil.sage --- E065 gate: beta_Fil, gamma_Fil "
          "(BDMTV 2019 §4.5 steps (ii),(iii)) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1 (D = one rational point)", y**2 - (x**5 - 1),
         1, -1, (1, 0)),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic, D = two rational points)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, (0, 1)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)  (D = one place of degree 4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, (0, 0)),
    ]
    # E069_ONLY=<substring> runs a single curve, for iterating on C_4 without
    # paying for the two that already pass.  The verdict is only meaningful
    # when all three run, and it says so.
    only = os.environ.get("E069_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E069_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
              % (only, len(cases)))
    for (label, Qxy, sx, sy, base) in cases:
        try:
            r = one(label, Qxy, sx, sy, base)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    if only:
        print("E069 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E069 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
