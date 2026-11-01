# check-phase4-hodge.sage --- E065 (E048 Phase 4) GATE, part 3.
#
# Step (i) of the Hodge filtration algorithm, Balakrishnan-Dogra-Mueller-
# Tuitman-Vonk (2019) §4.5: the differentials of the third kind extending the
# symplectic basis of H^1_dR(X) to one of H^1_dR(Y), and the differential eta.
#
#   (1) COUNT.  dim of the third-kind space = d - 1, d = deg(X - Y).  For C_4
#       the complement of the affine curve is ONE place of DEGREE 4, so d = 4
#       and the space is 3-dimensional over Q -- a Galois-stable tuple of
#       residues is an element of the residue field, cut down by the residue
#       theorem to its trace-zero part.  For an odd-degree hyperelliptic model
#       D is one rational point and the space is 0: eta = 0 is forced, and the
#       residue must then vanish on its own, which is check (3) in a degenerate
#       but non-vacuous form.
#   (2) UNIQUENESS.  The linear system for eta has a unique solution -- this is
#       [BDM+19, Lemma 4.10] made concrete: d rational conditions, one of them
#       dependent by the residue theorem, against d - 1 unknowns.
#   (3) THE DEFINING PROPERTY.  Omega^T Z omega - eta has vanishing residue at
#       every point of D.  Checked as an exact identity over Q, not to a
#       tolerance.  E071 corrected two things here: Z is the CLASS Z_e M^{-1},
#       not the endomorphism matrix, and the defining expression is the one the
#       gauge equation (18) gives, not the one printed in (19) -- which differ
#       only for a non-symmetric Z, so the earlier run of this gate satisfied
#       both errors at once.
#   (4) INDEPENDENCE OF THE CONSTANTS OF INTEGRATION.  Omega is only defined up
#       to constants; the residues must not move when they are changed.  This is
#       a theorem (the basis differentials have no residues), so a failure would
#       mean the expansions are wrong.
#   (5) PRECISION-INDEPENDENCE: the same eta at two t-adic precisions.
#   (6) THE SYSTEM FOR eta IS CONSISTENT, as a theorem rather than an
#       observation.  With R^P_ij = Res_P(omega_i Omega_j), which is
#       ANTISYMMETRIC because omega_i Omega_j + Omega_i omega_j is exact, the
#       residue of the defining expression is -sum_ij Z_ij R^P_ij; summing over
#       P gives -Tr(Z^T M), and that vanishes precisely by condition (c) of
#       [BDM+19] §4.1.  So the residue theorem's one dependency among the d
#       conditions is exactly the one Lemma 4.10 needs, and it is the CLASS
#       that supplies it.
#   (7) informational: whether the solver is exercised at all.  It is on C_4,
#       whose place at infinity has degree 4 -- (6) kills only the trace of the
#       residue there, leaving three conditions for the three unknowns -- and it
#       is not on the curves whose infinite places are rational.
#
# Run: sage check-phase4-hodge.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def one(label, Qxy, sx, sy, expect_d=None):
    print("-" * 72)
    print(label)
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    g = ZZ(C.genus)
    basis, _ = H.H1X_basis()
    # the CLASS, not the endomorphism matrix: [BDM+19] §4.5 needs the object
    # defined by §4.1 (a)-(d), which is Z_e M^{-1} (E071)
    Z = H.correspondence_class(sx, sy)
    ok = True

    tk = H.third_kind_basis()
    # d = degree of the divisor X - Y = sum of the degrees of the places at
    # infinity, read off the poles of the basis
    forms = [H.differential_of(v) for v in basis]
    poles = H._pole_places(forms)
    d = sum(P.degree() for P in poles) if poles else 1
    m1 = (len(tk) == d - 1) and (expect_d is None or d == expect_d)
    print("   (1) X - Y has degree %d (%d place(s), degrees %s); third-kind "
          "space has dimension %d, expected d-1 = %d %s"
          % (d, len(poles), [P.degree() for P in poles], len(tk), d - 1,
             "ok" if m1 else "*** NO ***"))
    ok = ok and m1

    sol, eta, info, rhs = H.hodge_eta(Z)
    m2 = (len(sol) == len(tk))
    print("   (2) eta = %s in that basis (unique solution: %s); the residues "
          "it has to kill were %s" % (list(sol), m2, rhs))
    if all(c == 0 for c in rhs):
        print("       NOTE: those residues vanish already, so eta = 0 is "
              "forced and the solver is NOT exercised here.  On a curve whose "
              "places at infinity are all RATIONAL, check (6)'s dependency is "
              "one condition per place, and with only one or two of them there "
              "is nothing left for eta to do.")
    ok = ok and m2

    # (3) verify the defining property directly, from the vectors
    L, xL = C.L, C.L(C.x)
    etaform = H.differential_of(eta) if any(c != 0 for c in eta) else None
    prec = 40
    worst = QQ(0)
    for P in poles:
        m = L.completion(P, prec=prec)
        t = P.local_uniformizer()
        dtdx = t.derivative()
        ser = [m(o / xL.differential() / dtdx) for o in forms]
        Om = []
        for gser in ser:
            F = gser.parent().zero()
            for k in range(gser.valuation(), gser.prec()):
                if k != -1 and gser[k] != 0:
                    F += gser[k] / QQ(k + 1) * gser.parent().gen()**(k + 1)
            Om.append(F)
        n = len(basis)
        expr = H._dg_expr(Z, ser, Om, n)
        if etaform is not None:
            expr -= m(etaform / xL.differential() / dtdx)
        r = expr[-1]
        worst = max(worst, QQ(0) if r == 0 else QQ(1))
    m3 = (worst == 0)
    print("   (3) residue of Omega^T Z omega - eta vanishes at every point "
          "of D: %s" % m3)
    ok = ok and m3

    # (4) constants of integration
    m4 = True
    for P in poles:
        m = L.completion(P, prec=prec)
        t = P.local_uniformizer()
        dtdx = t.derivative()
        ser = [m(o / xL.differential() / dtdx) for o in forms]
        shift = [ser[0].parent()(QQ(k + 1)) for k in range(len(ser))]
        n = len(basis)
        delta = H._dg_expr(Z, ser, shift, n)
        if delta[-1] != 0:
            m4 = False
    print("   (4) residues unchanged by the constants of integration: %s" % m4)
    ok = ok and m4

    nb = len(basis)
    prec2 = 30 if len(basis) > 4 else 60
    sol2, eta2, _, _ = H.hodge_eta(Z, prec=prec2)
    m5 = (list(sol2) == list(sol))
    print("   (5) same eta at t-adic precision %d: %s" % (prec2, m5))
    ok = ok and m5

    # (6) THE STRUCTURAL REASON eta = 0, STATED AND CHECKED.
    #     Write R^P_ij = Res_P(omega_i Omega_j).  Since omega_i Omega_j +
    #     Omega_i omega_j = d(Omega_i Omega_j) is exact, R^P is ANTISYMMETRIC,
    #     and expanding the definition gives
    #                 Res_P (dOmega^T Z Omega - Omega^T(Z-Z^T)omega)
    #                       = sum_ij Z_ij R^P_ij .
    #     Summing over P gives sum_ij Z_ij M_ij = Tr(Z^T M), which VANISHES for
    #     Tr(Z^T M), and that vanishes precisely by condition (c) of §4.1: the
    #     class Z dies under the cup product.  So the ONE dependency the residue
    #     theorem imposes among the d conditions is supplied by the class -- not
    #     by anything about the curve -- and d - 1 independent conditions remain
    #     for the d - 1 unknowns, which is Lemma 4.10.  Checked here against
    #     E066's cup product.  (Before E071 this gate ran with the endomorphism
    #     matrix, for which Tr(Z_e^T M) also vanishes, by Rosati symmetry rather
    #     than by (c) -- the same number for a different reason, which is why
    #     the check passed on the wrong input.)
    Mcup = H.cup_product_matrix()
    pred = sum(QQ(Z[i][j]) * Mcup[i][j] for i in range(nb) for j in range(nb))
    m6 = (pred == 0)
    print("   (6) Tr(Z^T M) = sum_ij Z_ij M_ij = %s (must vanish: §4.1 (c)) %s"
          % (pred, "ok" if m6 else "*** NO ***"))
    ok = ok and m6

    # (7) IS THE SOLVER EXERCISED?  Informational, since the answer depends on
    #     the curve and not on the code.  Check (6) kills only the TRACE of the
    #     residue, leaving deg(P) - 1 conditions per place; on a curve whose
    #     places at infinity are rational nothing is left and eta = 0 is forced,
    #     while on C_4, whose place has degree 4, three conditions remain and
    #     the linear algebra inside hodge_eta is genuinely exercised.  A second
    #     class is run here to show that the answer is a fact about the curve
    #     and not about our particular Z.
    #       The test matrix must satisfy (c): with one that does not, the
    #     residues do not sum to zero, no eta exists, and the solver reports
    #     "matrix equation has no solutions" -- measured twice on the way here.
    #     Condition (c) IS the solvability of step (i).
    Sp = matrix(QQ, nb, nb)
    for i in range(nb):
        for j in range(i + 1, nb):
            Sp[i, j] = QQ(1 + (i * nb + j) % 3)
            Sp[j, i] = -Sp[i, j]
    Zt = Mcup.inverse() * Sp
    try:
        sol3, eta3, _, rhs3 = H.hodge_eta(Zt)
        st = ("nonzero, solver exercised" if any(c != 0 for c in rhs3)
              else "zero: eta = 0 forced here too")
    except Exception as ex:
        st = "unsolvable (%s): that Z fails condition (c)" % type(ex).__name__
    print("   (7) [informational, not part of the verdict] a second class "
          "gives residues %s" % st)
    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-hodge.sage --- E065 gate: eta (BDMTV 2019 "
          "§4.5 step (i)) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1 (D = one rational point)", y**2 - (x**5 - 1), 1, -1, 1),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)", y**2 - (x**6 + x**4 - x**2 + 1),
         -1, 1, None),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 4),
    ]
    for (label, Qxy, sx, sy, expect_d) in cases:
        try:
            r = one(label, Qxy, sx, sy, expect_d)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    print("E068 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
