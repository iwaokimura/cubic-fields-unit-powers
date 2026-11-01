# check-phase4-basis.sage --- E065 (E048 Phase 4) GATE, part 5.
#
# E070.  The height of [BDM+19] Lemma 5.4,
#
#   h_p = chi_p( gamma_phi - gamma_Fil - beta_phi^T s1(alpha_phi)
#                                      - beta_Fil^T s2(alpha_phi) ),
#
# uses gamma_Fil and beta_Fil SEPARATELY, and E069 found that neither is
# determined by the algorithm of [BDM+19] §4.5: the solution space is
# (g+1)-dimensional and on C_4 moving beta_Fil moves gamma_Fil by a function.
# This gate establishes the two hypotheses under which the formula is well
# defined, and measures that our computational basis satisfies neither.
#
#   (1) phase4_basis() really is a basis of FORMS: its first g entries have no
#       poles at all.  [BT] Def 2.16(1) asks for a basis of H^0(X, Omega^1),
#       not for classes of one, and E064 measured that no REORDERING of the
#       computational basis can do it for C_4 -- all six elements have a pole
#       of order 3 at infinity.  Changing the representative can.
#   (2) in that basis the holomorphic classes are the first g standard vectors.
#   (3) the cup product in that basis is the STANDARD SYMPLECTIC FORM, which is
#       what [BDM+19] §4.1 requires.  phase4_basis constructs it and raises on
#       failure; here it is recomputed from the returned representatives.
#   (4) Fil^0 is isotropic for the cup product and NOT for the coordinate dot
#       product.  This is the measurement that decides how beta^T . v in (14)
#       must be read: the residual ambiguity of beta_Fil is Fil^0 and so is
#       s2(alpha_phi), so under the cup product the ambiguity cancels and under
#       the dot product it does not.  Since h_p is defined intrinsically by
#       [BDM+19] (13), only the cup-product reading can be correct.
#   (5) the computational basis: kernel of dimension g+1 with beta-part Fil^1
#       (E069's finding, re-measured), and whether gamma moves.
#   (6) THE MAIN CLAIM: in the phase4 basis gamma does NOT move.  On C_4 it
#       does in the computational basis, so this is not vacuous.
#   (7) WHY it moves, checked rather than asserted: writing
#       c^T omega = omega_hol + du, the prediction gamma |--> gamma - (u - u(b))
#       must solve the shifted problem, and the control (gamma unchanged) must
#       fail exactly when u is non-constant.  The prediction comes from
#       holomorphic_exact_parts, which never touches the linear system of
#       §4.5(iii), and is checked at a t-adic precision the solve never used.
#   (8) NEGATIVE CONTROL: without the symplectic step the cup product is not
#       the standard form, so (3) is not passing vacuously.
#
# Run: sage check-phase4-basis.sage       (E070_ONLY=<substring> for one curve)

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
    n = 2 * g
    L = C.L
    # the CLASS, not the endomorphism matrix (E071).  The transport to the
    # phase4 basis below, S^-T Z S^-1, is the change of basis law for a class;
    # with the endomorphism matrix it was the wrong law for the wrong object.
    Z = H.correspondence_class(sx, sy)
    ok = True

    # ------------------------------------------------ (1) a basis of FORMS
    reps, S = H.phase4_basis()
    forms = [H.differential_of(v) for v in reps]
    polefree = [all(m >= 0 for _, m in om.divisor().list())
                for om in forms[:g]]
    m1 = (len(reps) == n) and all(polefree)
    print("   (1) phase4_basis: %d representatives, the first g have no poles "
          "at all: %s" % (len(reps), "ok" if m1 else "*** NO ***"))
    ok = ok and m1

    # ------------------------------- (2) holomorphic classes in that basis
    T = matrix(QQ, H.holomorphic_classes(reps))
    want = matrix(QQ, g, n, lambda a, b: 1 if a == b else 0)
    m2 = (T.row_space() == want.row_space())
    print("   (2) the holomorphic classes are the first g standard vectors: %s"
          % ("ok" if m2 else "*** NO: %s ***" % T))
    ok = ok and m2

    # --------------------------------------------- (3) symplectic, [BDM+19] §4.1
    M = H.cup_product_matrix(basis=reps)
    J = matrix(QQ, n, n, lambda i, j:
               1 if (i < g and j == i + g) else
               (-1 if (i >= g and j == i - g) else 0))
    m3 = (M == J)
    print("   (3) the cup product in the phase4 basis is the standard "
          "symplectic form: %s" % ("ok" if m3 else "*** NO: %s ***" % (M - J)))
    ok = ok and m3

    # ------------------------------------------------------- (4) isotropy
    Fil = matrix(QQ, H.holomorphic_classes())
    Mc = H.cup_product_matrix()
    cup0 = (Fil * Mc * Fil.transpose() == 0)
    dot0 = (Fil * Fil.transpose() == 0)
    m4 = cup0 and not dot0
    print("   (4) Fil^0 isotropic for the cup product: %s, for the dot "
          "product: %s  %s" % (cup0, dot0, "ok" if m4 else "*** NO ***"))
    print("       => beta_Fil^T s2(alpha_phi) must be read as a CUP product; "
          "the dot-product reading leaves h_p undefined")
    ok = ok and m4

    # ---------------------------------- (5)(6) does gamma move, in each basis
    b1, g1, i1 = H.hodge_filtration(Z, base=base)
    m5 = (i1["kernel_dim"] == g + 1) and i1["kernel_beta_is_Fil1"]
    print("   (5) computational basis: kernel %d (expect %d), beta-part Fil^1 "
          "%s, gamma constant %s  %s"
          % (i1["kernel_dim"], g + 1, i1["kernel_beta_is_Fil1"],
             i1["kernel_gamma_is_constant"], "ok" if m5 else "*** NO ***"))
    ok = ok and m5
    sys.stdout.flush()

    Sm = matrix(QQ, S)
    Si = Sm.inverse()
    Zt = Si.transpose() * matrix(QQ, Z) * Si
    Z2 = [[Zt[i][j] for j in range(n)] for i in range(n)]
    b2, g2, i2 = H.hodge_filtration(Z2, base=base, basis=reps)
    m6 = (i2["kernel_dim"] == g + 1) and i2["kernel_beta_is_Fil1"] \
        and i2["kernel_gamma_is_constant"]
    print("   (6) phase4 basis: kernel %d, beta-part Fil^1 %s, "
          "GAMMA CONSTANT %s  %s"
          % (i2["kernel_dim"], i2["kernel_beta_is_Fil1"],
             i2["kernel_gamma_is_constant"], "ok" if m6 else "*** NO ***"))
    if not i1["kernel_gamma_is_constant"]:
        print("       (and it DOES move in the computational basis, so this "
              "is not vacuous)")
    ok = ok and m6
    sys.stdout.flush()

    # ------------------------------- (7) the prediction gamma |-> -(u - u(b))
    eta = H.hodge_eta(Z)[1]
    etaform = H.differential_of(eta) if any(c != 0 for c in eta) else None
    poles = H._pole_places([H.differential_of(v) for v in H.H1X_basis()[0]])
    prec = i1["prec"] + 11
    xL = L(C.x)

    def defect(beta, gextra):
        worst = QQ(0)
        for P in poles:
            m, ser, _, _ = H.local_data(P, prec)
            Om = [H._integrate_series(s) for s in ser]
            expr = H._dg_expr(Z, ser, Om, n)
            if etaform is not None:
                dtdx = P.local_uniformizer().derivative()
                expr -= m(etaform / xL.differential() / dtdx)
            gx = H._integrate_series(expr)
            gs = H.gamma_series(P, prec, i1)
            if gextra is not None and not gextra.is_zero():
                gs = gs + m(gextra)
            rem = gx - gs
            for i in range(n):
                if beta[i] != 0:
                    rem -= QQ(beta[i]) * Om[i]
            if not rem.is_zero() and rem.valuation() < 0:
                worst = min(worst, QQ(rem.valuation()))
        return worst

    m7 = True
    print("   (7) the predicted Delta gamma = -(u - u(b)), at t-adic "
          "precision %d (solve used %d):" % (prec, i1["prec"]))
    for k, (c, u) in enumerate(H.holomorphic_exact_parts()):
        const = u.is_zero() or u.derivative().is_zero()
        ub = H._evaluate(u, QQ(base[0]), QQ(base[1]))
        dg = -(u - L(ub))
        bb = [b1[i] + QQ(c[i]) for i in range(n)]
        d1 = defect(bb, dg)
        d0 = defect(bb, L.zero())
        good = (d1 == 0) and ((d0 == 0) == const)
        print("       c%d: u %s, predicted defect %s, control defect %s  %s"
              % (k, "constant" if const else "NON-constant", d1, d0,
                 "ok" if good else "*** NO ***"))
        m7 = m7 and good
        sys.stdout.flush()
    ok = ok and m7

    # -------------------------------------------------- (8) negative control
    reps0, _ = H.phase4_basis(symplectic=False)
    M0 = H.cup_product_matrix(basis=reps0)
    if M0 == J:
        print("   (8) [negative control, VACUOUS HERE] the unsymplectised "
              "basis already has the standard cup product: not scored")
    else:
        print("   (8) [negative control] without the symplectic step the cup "
              "product is not the standard form: ok")
    print("   beta_Fil (phase4 basis) = %s" % b2)
    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-basis.sage --- E065 gate: the basis the "
          "height formula needs (E070) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 1, -1, (1, 0)),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, (0, 1)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, (0, 0)),
    ]
    only = os.environ.get("E070_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E070_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
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
        print("E070 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E070 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
