# check-phase4-frobtriv.sage --- E065 (E048 Phase 4) GATE, part 8.
#
# E073.  Equations (23) and (24) of [BDM+19] §5.2: the Frobenius-equivariant
# trivialisation s^phi(b,x) itself, which is what Lemma 5.4 consumes.  E072
# produced the matrix G = [[1,0,0],[f,F,0],[h,g^T,p]] of overconvergent
# functions solving the gauge equation; here G is repackaged into
#
#   (23)  M(x_0) = s_0^{-1}(x_0) o s^phi(b,x_0) at the TEICHMULLER point x_0
#         of a residue disk, determined by G(x_0) M = M diag(1,F,p);
#   (24)  M(x)   = I(x,x_0) M(x_0) for x in ]x_0[, I the parallel transport
#         of the connection d + Lambda of (17).
#
# THE TEICHMULLER POINT COSTS NOTHING.  §5.2 says "let x_0 be the unique
# Teichmuller point in ]x[" and the plan budgeted a Newton iteration on the
# fixed points of phi for it.  None is needed: Tuitman's lift has phi^*x = x^p
# and phi^*y = beta with Q^sigma(x^p,beta) = 0, so in a good disk whose residue
# point is F_p-rational the fixed point is (Teichmuller lift of x, Hensel root
# of Q above it) -- proved in padic/points.teichmuller_point, and CHECKED here
# against phi, which the construction never calls.
#
# WHAT (24) IS.  The paper never displays I(x,x_0).  Horizontality (ds = -Lambda
# s) gives dI = N I with N = [[0,0,0],[omega,0,0],[eta,omega^T Z,0]], hence
#
#     I = [[1,0,0],[u,1,0],[v,w^T,1]],   du = omega,  w^T = u^T Z,
#     dv = eta + omega^T Z u,
#
# so the bottom-left entry is an ITERATED integral -- the only one in the port.
# The paper's own check on this is Lemma 5.5, whose proof writes out the same
# matrix for I(b',b) with Coleman integrals in place of the tiny ones.
#
#   (1) TEICHMULLER: for every good F_p-point, the constructed x_0 is on the
#       curve, in the right disk, and satisfies phi(x_0) = x_0 to the certified
#       precision.  NEGATIVE CONTROL: the point of the same disk at t = p is
#       not fixed.
#   (2) (23) AT A GENERAL x_0: G(x_0) M(x_0) = M(x_0) diag(1,F~,p).  E072's
#       check (7) was this at x_0 = b only, where f(b) = h(b) = 0 make two of
#       the three blocks trivial; here f(x_0), g(x_0), h(x_0) are all nonzero.
#   (3) alpha_phi IS THE COLEMAN INTEGRAL: between two Teichmuller points,
#       alpha_phi(x_0') - alpha_phi(x_0) = int_{x_0}^{x_0'} omega~, the right
#       side computed by Algorithm 3.7 (E061/E063).  The difference form is
#       used because a base point b that is not itself Teichmuller contributes
#       (I-F~)^{-1} int_b^{phi(b)} omega~ to each side separately.
#   (4) beta_phi TRANSPORTS BY Z: beta_phi(x_0') - beta_phi(x_0)
#       = Z^T int_{x_0}^{x_0'} omega~.  This is (24)'s w^T = u^T Z tested
#       ACROSS disks, where (24) itself does not reach; it holds because
#       (g(x_0')-g(x_0))^T = A^T Z (F~ - p) with A the integral, which uses
#       §4.1(a) once more.
#   (5) (24) INSIDE A DISK: I(x_0,x_0) = 1 and the cocycle
#       I(x_2,x_0) = I(x_2,x_1) I(x_1,x_0) for two points of ]x_0[, with
#       I(x_2,x_1) expanded at x_1.  On the bottom-left entry this reads
#       v_20 = v_21 + w_21^T u_10 + v_10, which is a genuine identity between
#       ITERATED integrals: NEGATIVE CONTROL, dropping the omega^T Z u term
#       from dv must break it, and it does.
#   (6) END TO END: alpha_phi at a NON-Teichmuller point, from frob_triv (i.e.
#       (23) composed with (24)), against the Coleman integral to it.
#   (7) VACUITY WARNING for a curve with Z = 0: checks (4) and (5) say nothing
#       there and are reported as skipped, not as passes.
#
# NOT IN SCOPE, AND NOT NEEDED: the cross-disk analogue of (5) would need
# DOUBLE Coleman integrals, which the port does not have.  The algorithm never
# asks for them -- (23) is available in every good disk and (24) only ever
# moves inside one -- so this is a check we cannot run, not a gap in the port.
#
# Run: sage check-phase4-frobtriv.sage    (E073_ONLY=<substring> for one curve)

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobstruct import FrobeniusStructure, _antiderivative
from padic.integrals import ColemanIntegrals
from padic.points import CurvePoint, LocalExpansion, teichmuller_point


R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()


def vz(a, N):
    """Valuation of a p-adic number, N for an exact zero."""
    return ZZ(N) if a == 0 else ZZ(a.valuation())


def vmin(elts, N):
    vs = [vz(a, N) for a in elts]
    return min(vs) if vs else ZZ(N)


def teich_points(FS, p, K, want=3):
    """Teichmuller points of the good degree-one residue disks.

    Brute force over F_p x F_p: p <= 13 here, and doing it this way keeps the
    gate from re-deriving r mod p and dQ/dy mod p, which are exactly what
    CurvePoint already decides.
    """
    out = []
    for xb in range(p):
        for yb in range(p):
            val = QQ(FS.C.Qxy(QQ(xb), QQ(yb)))
            if val.denominator() % p == 0 or val.numerator() % p != 0:
                continue
            P = CurvePoint(FS.RR, K(xb), y=K(yb))
            if not (P.is_good() and P.dQ_dy_is_unit()):
                continue
            out.append((xb, yb, teichmuller_point(P), P))
            if len(out) >= want:
                return out
    return out


def naive_v_series(FS, LE):
    """(24)'s I with the iterated term dropped: dv = eta alone.

    The negative control for check (5).  Everything else about the transport is
    unchanged, so a cocycle failure isolates the iterated integral.
    """
    n = FS.n
    W = [FS.series_of(FS.radic_form(FS.reps[k]), LE) for k in range(n)]
    u = [_antiderivative(s, "omega") for s in W]
    Z = FS._in(FS.Zk, LE.ring)
    w = []
    for j in range(n):
        acc = LE.L.zero()
        for i in range(n):
            if Z[i][j] != 0:
                acc += Z[i][j] * u[i]
        w.append(acc)
    inner = LE.L.zero()
    if any(cc != 0 for cc in FS.eta):
        inner += FS.series_of(FS.radic_form(FS.eta), LE)
    return u, w, _antiderivative(inner, "eta")


def as_matrix(FS, ring, u, w, v, tv):
    return FS._block3(ring, 1, matrix.identity(ring, FS.n), 1,
                      [uu(tv) for uu in u], v(tv), [ww(tv) for ww in w])


def one(label, Qxy, sx, sy, p, N, bpt):
    print("-" * 72)
    print("%s   p = %d, N = %d, base point %s" % (label, p, N, (bpt,)))
    sys.stdout.flush()
    t0 = time.time()
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    n = 2 * ZZ(C.genus)
    ok = True

    FS = FrobeniusStructure(C, H, p, N, bpt, sx=sx, sy=sy)
    K, cert = FS.K, FS.cert
    vacuous = FS.Z == 0
    c, mu, resv = FS.solve()
    print("   (22) solved: certified precision %d, residual p^%s, Z rescaled "
          "by %s  (%.0f s)" % (cert, resv, FS.Zscale, time.time() - t0))
    if vacuous:
        print("   (7) *** Z = 0 on this curve: checks (4) and (5) are VACUOUS "
              "and are skipped ***")
    sys.stdout.flush()

    # ------------------------------------------------------- (1) Teichmuller
    pts = teich_points(FS, p, K)
    if len(pts) < 2:
        raise ArithmeticError("fewer than two good F_p-points found")
    vT, vTneg = ZZ(N), None
    for (xb, yb, x0, seed) in pts:
        Fx = FS.phi_image(x0)
        vT = min(vT, vz(Fx.x - x0.x, N), vz(Fx.y - x0.y, N))
        if not (x0.on_curve() and seed.same_disk(x0)):
            vT = ZZ(0)
    LE0 = LocalExpansion(pts[0][2], 4 * N + 20)
    xoff = LE0.point_at(K(p))                       # same disk, not Teichmuller
    Fo = FS.phi_image(xoff)
    vTneg = min(vz(Fo.x - xoff.x, N), vz(Fo.y - xoff.y, N))
    m1 = (vT >= cert) and (vTneg < cert)
    print("   (1) %d Teichmuller points %s: phi(x_0) = x_0 to p^%s (cert %d); "
          "the t = p point of the same disk is fixed only to p^%s  %s"
          % (len(pts), [(a, b) for (a, b, _, _) in pts], vT, cert, vTneg,
             "ok" if m1 else "*** NO ***"))
    ok = ok and m1
    sys.stdout.flush()

    # ---------------------------------------------- (2) (23) at a general x_0
    D = FS.frobenius_diag(K)
    v2 = ZZ(N)
    Ms = []
    for (xb, yb, x0, _) in pts:
        M = FS.frob_triv_teich(x0)
        Ms.append(M)
        v2 = min(v2, vmin((FS.G_at(x0) * M - M * D).list(), N))
    m2 = v2 >= cert
    # reported at the LAST point, which is not the base point: at b itself
    # f(b) = h(b) = 0 kill two of the three blocks and (2) degenerates into
    # E072's check (7).
    fv, gv, hv = FS.values_at(pts[-1][2])
    print("   (2) (23): G(x_0) M = M diag(1,F~,p) at all %d of them, to p^%s "
          "(cert %d); at the last, min val of (f,g,h)(x_0) = (%s,%s,%s)  %s"
          % (len(pts), v2, cert, vmin(list(fv), N), vmin(list(gv), N),
             vz(hv, N), "ok" if m2 else "*** NO ***"))
    ok = ok and m2
    sys.stdout.flush()

    # ------------------------- (3),(4) alpha and beta against Coleman integrals
    CI = ColemanIntegrals(FS.FM)
    x0, x0b = pts[0][2], pts[1][2]

    def tilde_integrals(P, Q):
        """int_P^Q omega~ in the phase4 basis, from Algorithm 3.7."""
        raw = CI.coleman_integrals_on_basis(P, Q)
        out = []
        for i in range(n):
            acc = K(0)
            for j in range(n):
                if FS.S[i][j] != 0:
                    acc += K(QQ(FS.S[i][j])) * raw[j]
            acc += FS.evaluate(FS.u[i], Q) - FS.evaluate(FS.u[i], P)
            out.append(acc)
        return vector(K, out)

    A = tilde_integrals(x0, x0b)
    # the bar for (3),(4),(6) is Algorithm 3.7's own certificate, not Phi's:
    # the tiny integrals inside it divide by k+1 and lose what they lose.
    certA = ZZ(floor(CI.certified_precision(x0, x0b)))
    a0, b0, g0 = FS.read_triv(Ms[0])
    a1, b1, g1 = FS.read_triv(Ms[1])
    v3 = vmin(list(a1 - a0 - A), N)
    m3 = v3 >= certA
    print("   (3) alpha_phi(x_0') - alpha_phi(x_0) = int omega~ (Alg 3.7) to "
          "p^%s (Alg 3.7 certifies %d, Phi %d)  %s"
          % (v3, certA, cert, "ok" if m3 else "*** NO ***"))
    ok = ok and m3
    if vacuous:
        print("   (4) skipped (Z = 0)")
        m4 = True
    else:
        v4 = vmin(list(b1 - b0 - FS.Zk.transpose() * A), N)
        m4 = v4 >= certA
        print("   (4) beta_phi(x_0') - beta_phi(x_0) = Z^T int omega~ to p^%s "
              "(certified %d)  %s" % (v4, certA, "ok" if m4 else "*** NO ***"))
        ok = ok and m4
    sys.stdout.flush()

    # ------------------------------------------ (5) (24) inside a residue disk
    LE, u, w, v = FS.transport_series(x0, LE=LE0)
    I00 = as_matrix(FS, K, u, w, v, K(0))
    # both offsets of order p exactly: with t_2 - t_1 of order p^2 the negative
    # control's defect w_21^T u_10 sinks to the certified floor and stops being
    # a control at all (measured: p^5 against a certificate of 5).
    t1, t2 = K(p), K(2) * K(p)
    x1, x2 = LE0.point_at(t1), LE0.point_at(t2)
    I10 = as_matrix(FS, K, u, w, v, t1)
    I20 = as_matrix(FS, K, u, w, v, t2)
    LE1 = LocalExpansion(x1, 4 * N + 20)
    _, u1, w1, v1 = FS.transport_series(x1, LE=LE1)
    I21 = as_matrix(FS, K, u1, w1, v1, LE1.t_of(x2))
    v5a = vmin((I00 - matrix.identity(K, n + 2)).list(), N)
    v5 = vmin((I20 - I21 * I10).list(), N)
    if vacuous:
        print("   (5) I(x_0,x_0) = 1 to p^%s; cocycle to p^%s (cert %d); "
              "negative control skipped (Z = 0)" % (v5a, v5, cert))
        m5 = (v5a >= cert) and (v5 >= cert)
        ok = ok and m5
    else:
        nu, nw, nv = naive_v_series(FS, LE0)
        nu1, nw1, nv1 = naive_v_series(FS, LE1)
        J10 = as_matrix(FS, K, nu, nw, nv, t1)
        J20 = as_matrix(FS, K, nu, nw, nv, t2)
        J21 = as_matrix(FS, K, nu1, nw1, nv1, LE1.t_of(x2))
        v5b = vmin((J20 - J21 * J10).list(), N)
        m5 = (v5a >= cert) and (v5 >= cert) and (v5b < cert)
        print("   (5) I(x_0,x_0) = 1 to p^%s; cocycle I(x_2,x_0) = "
              "I(x_2,x_1)I(x_1,x_0) to p^%s (cert %d); without the iterated "
              "term it fails at p^%s  %s"
              % (v5a, v5, cert, v5b, "ok" if m5 else "*** NO ***"))
        ok = ok and m5
    sys.stdout.flush()

    # ------------------------------- (6) end to end at a non-Teichmuller point
    Mx, x0chk = FS.frob_triv(x1)
    ax, bx, gx = FS.read_triv(Mx)
    B = tilde_integrals(x0b, x1)
    certB = ZZ(floor(CI.certified_precision(x0b, x1)))
    v6 = vmin(list(ax - a1 - B), N)
    m6 = x0chk.same_disk(x0) and (v6 >= certB)
    print("   (6) frob_triv at the t = p point: alpha_phi(x) - alpha_phi(x_0') "
          "= int omega~ to p^%s (certified %d)  %s"
          % (v6, certB, "ok" if m6 else "*** NO ***"))
    ok = ok and m6

    print("   (%.0f s)" % (time.time() - t0))
    return ok


def main():
    print("=== check-phase4-frobtriv.sage --- E065 gate: equations (23) "
          "and (24), the Frobenius trivialisation (E073) ===")
    allok = True
    cases = [
        ("y^2 = x^5-1", y**2 - (x**5 - 1), 1, -1, 11, 8, (2, None)),
        ("y^2 = x^6+x^4-x^2+1 (bielliptic)",
         y**2 - (x**6 + x**4 - x**2 + 1), -1, 1, 7, 8, (0, 1)),
        ("C_4 : w^4-6(t-1)^2w^2+27t(t^3-4)",
         y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4), 1, -1, 13, 8, (1, 3)),
    ]
    only = os.environ.get("E073_ONLY", "")
    if only:
        cases = [c for c in cases if only in c[0]]
        print("(E073_ONLY=%s: running %d of 3 curves -- NOT a full gate run)"
              % (only, len(cases)))
    for (label, Qxy, sx, sy, p, N, bpt) in cases:
        try:
            if bpt[1] is None:
                # As in E072: y^2 = x^5-1 has no convenient rational point off
                # the Weierstrass locus, so b is taken over Q_p at x = 2.
                Kp = Qp(p, prec=N, type='floating-point')
                bpt = (bpt[0], Kp(ZZ(bpt[0])**5 - 1).sqrt())
            r = one(label, Qxy, sx, sy, p, N, bpt)
        except Exception:
            import traceback
            traceback.print_exc()
            r = False
        print("   %s" % ("ok" if r else "*** FAILS ***"))
        allok = allok and r
        sys.stdout.flush()
    print("=" * 72)
    if only:
        print("E073 PARTIAL (%s): %s" % (only, "ok" if allok else "*** NO ***"))
    else:
        print("E073 GATE: %s" % ("GREEN" if allok else "*** RED ***"))


main()
